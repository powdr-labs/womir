//! This module flattens the DAG structure, generating an assembly-like representation.
//!
//! The algorithm is straightforward and linear, as most of the complexity was handled
//! in earlier passes (notably register allocation).

mod sequence_parallel_copies;

use itertools::Itertools;
use wasmparser::{FuncType, Operator as Op, ValType};

use crate::{
    loader::{
        FunctionAsm, FunctionRef, LabelGenerator, Module, assert_reg,
        passes::{
            blockless_dag::{BreakTarget, Operation, TargetType},
            dag::{NodeInput, ValueOrigin},
        },
        rwm::{
            flattening::sequence_parallel_copies::Register,
            register_allocation::{self, AllocatedDag, Allocation},
            settings::Settings,
        },
        settings::{
            ComparisonFunction, JumpCondition, LabelType, TrapReason, WasmOpInput, format_label,
        },
        split_func_ref_regs, word_count_type, word_count_types,
    },
    utils::{range_consolidation::RangeConsolidationIterator, tree::Tree},
};
use std::{collections::VecDeque, ops::Range, sync::atomic::AtomicU32};

pub fn flatten_dag<'a, S: Settings<'a>>(
    s: &S,
    prog: &Module<'a>,
    label_gen: &AtomicU32,
    func_idx: u32,
    dag: AllocatedDag<'a>,
) -> FunctionAsm<S::Directive> {
    let common_ctx = CommonContext { prog, label_gen };

    let mut ctrl_stack = VecDeque::new();
    ctrl_stack.push_front(StackEntry {
        loop_label: None,
        allocation: dag.block_data,
    });

    let directives = process_dag(s, &common_ctx, &mut ctrl_stack, dag.nodes, func_idx);

    FunctionAsm {
        func_idx,
        frame_size: None,
        directives: directives.flatten(),
    }
}

struct StackEntry {
    loop_label: Option<String>,
    allocation: Allocation,
}

fn process_dag<'a, 'b, S: Settings<'a>>(
    s: &S,
    ctx: &'b CommonContext<'a, 'b>,
    ctrl_stack: &mut VecDeque<StackEntry>,
    nodes: Vec<register_allocation::Node<'a>>,
    func_idx: u32,
) -> Tree<S::Directive> {
    nodes
        .into_iter()
        .enumerate()
        .map(|(node_idx, node)| process_node(s, ctx, ctrl_stack, node, node_idx, func_idx))
        .collect_vec()
        .into()
}

fn process_node<'a, 'b, S: Settings<'a>>(
    s: &S,
    common_ctx: &'b CommonContext<'a, 'b>,
    ctrl_stack: &mut VecDeque<StackEntry>,
    node: register_allocation::Node<'a>,
    node_idx: usize,
    func_idx: u32,
) -> Tree<S::Directive> {
    let allocation = &ctrl_stack[0].allocation;

    // Resolve all the inputs to register ranges.
    let inputs = node
        .inputs
        .into_iter()
        .map(|input| match input {
            NodeInput::Constant(c) => WasmOpInput::Constant(c),
            NodeInput::Reference(origin) => WasmOpInput::Register(allocation.get(&origin).unwrap()),
        })
        .collect_vec();

    let mut ctx = Context::new(common_ctx, allocation, node_idx, &inputs);
    match node.operation {
        Operation::Inputs => {
            // Inputs node marks the start of the block. If this the toplevel function, we must issue the function label here.
            // Add the function label with the frame size.
            if ctrl_stack.len() == 1 {
                let mut directives = Vec::with_capacity(2);
                directives.push(
                    s.emit_label(&mut ctx, format_label(func_idx, LabelType::Function))
                        .into(),
                );

                if let Some(name) = ctx.common.prog.get_exported_func(func_idx) {
                    // Add an alternative label, using the exported function name.
                    directives.push(s.emit_label(&mut ctx, name.to_string()).into());
                }
                directives.into()
            } else {
                Tree::Empty
            }
        }
        Operation::Label { id } => s
            .emit_label(&mut ctx, format_label(id, LabelType::Local))
            .into(),
        Operation::Loop { sub_dag, .. } => {
            let AllocatedDag {
                nodes: loop_nodes,
                block_data: loop_allocation,
            } = sub_dag;

            // Find where the loop expects its inputs to be.
            let input_ranges = loop_allocation.get_for_node(0);

            // Copy the loop inputs if needed.
            let mut loop_directives = copy_inputs_if_needed(s, &mut ctx, &inputs, input_ranges);

            // Generate loop label.
            let loop_label = ctx.new_label(LabelType::Loop);
            loop_directives.push(s.emit_label(&mut ctx, loop_label.clone()).into());

            // Process the loop body.
            ctrl_stack.push_front(StackEntry {
                loop_label: Some(loop_label),
                allocation: loop_allocation,
            });
            let loop_tree = process_dag(s, common_ctx, ctrl_stack, loop_nodes, func_idx);
            ctrl_stack.pop_front().unwrap();

            // Push the loop directives.
            loop_directives.push(loop_tree);
            loop_directives.into()
        }
        Operation::Br(break_target) => {
            emit_jump(s, &mut ctx, ctrl_stack, break_target, &inputs, func_idx).into_tree(s)
        }
        Operation::BrIf(target) | Operation::BrIfZero(target) => {
            let (cond, inverse_cond) = match node.operation {
                Operation::BrIf(..) => (JumpCondition::IfNotZero, JumpCondition::IfZero),
                Operation::BrIfZero(..) => (JumpCondition::IfZero, JumpCondition::IfNotZero),
                _ => unreachable!(),
            };

            // Get the conditional variable from the inputs.
            let (cond_reg, inputs) = ctx.node_inputs.split_last().unwrap();
            let cond_reg = cond_reg.as_register().unwrap().clone();
            assert_reg::<S>(&cond_reg, ValType::I32);

            let jump_directives = emit_jump(s, &mut ctx, ctrl_stack, target, inputs, func_idx);
            if S::is_jump_condition_available(cond)
                && let JumpResult::PlainJump(target) = jump_directives
            {
                s.emit_conditional_jump(&mut ctx, cond, target, cond_reg)
                    .into()
            } else {
                let jump_directives = jump_directives.into_tree(s);
                if S::is_jump_condition_available(inverse_cond) {
                    // Uses branch on inverse condition for the general case. This is the second best case.
                    let cont_label = ctx.new_label(LabelType::Local);
                    vec![
                        // Emit the jump to continuation if the condition is non-zero.
                        s.emit_conditional_jump(
                            &mut ctx,
                            inverse_cond,
                            cont_label.clone(),
                            cond_reg,
                        )
                        .into(),
                        // Emit the jump to the target label.
                        jump_directives,
                        // Emit the continuation label.
                        s.emit_label(&mut ctx, cont_label).into(),
                    ]
                    .into()
                } else if S::is_jump_condition_available(cond) {
                    // Uses conditional branch for the general case. This is the worst case, because it
                    // it requires two labels and two jumps.
                    let cont_label = ctx.new_label(LabelType::Local);
                    let jump_label = ctx.new_label(LabelType::Local);

                    vec![
                        // Emit the jump to the to the jump code
                        s.emit_conditional_jump(&mut ctx, cond, jump_label.clone(), cond_reg)
                            .into(),
                        // Emit the jump to the continuation label.
                        s.emit_jump(cont_label.clone()).into(),
                        // Emit the jump label.
                        s.emit_label(&mut ctx, jump_label).into(),
                        // Emit the jump code.
                        jump_directives,
                        // Emit the contin\uation label.
                        s.emit_label(&mut ctx, cont_label).into(),
                    ]
                    .into()
                } else {
                    panic!(
                        "Neither branch if zero nor branch if not zero is available in the settings."
                    );
                }
            }
        }
        Operation::BrTable { targets } => {
            let (selector, table_inputs) = inputs.split_last().unwrap();
            let selector = selector.as_register().unwrap().clone();

            let mut choice_inputs = Vec::with_capacity(table_inputs.len());
            let mut jump_instructions = targets
                .into_iter()
                .map(|target| {
                    // The inputs for one particular target are a permutation of the inputs
                    // of the BrTable operation.
                    choice_inputs.clear();
                    for &idx in &target.input_permutation {
                        choice_inputs.push(table_inputs[idx as usize].clone());
                    }

                    // Emit the jump to the target label.
                    emit_jump(
                        s,
                        &mut ctx,
                        ctrl_stack,
                        target.target,
                        &choice_inputs,
                        func_idx,
                    )
                })
                .collect_vec();

            // The last target is special, because it is the default target.
            let default_target = jump_instructions.pop().unwrap();

            // We need to handle the default target separately first, because it will be
            // the target in case the selector is out of bounds.
            let mut directives = Vec::new();
            match default_target {
                JumpResult::PlainJump(target) => {
                    // If the default target is a plain jump to a local label,
                    // just jump if the selector is out of bounds.
                    directives.push(
                        s.emit_conditional_jump_cmp_immediate(
                            &mut ctx,
                            ComparisonFunction::GreaterThanOrEqualUnsigned,
                            selector.clone(),
                            jump_instructions.len() as u32,
                            target,
                        )
                        .into(),
                    );
                }
                JumpResult::Directives(jump_directives) => {
                    // If the default target is a complex jump.
                    let table_label = ctx.new_label(LabelType::Local);
                    directives.extend([
                        // Jump to the table if the selector is in bounds.
                        s.emit_conditional_jump_cmp_immediate(
                            &mut ctx,
                            ComparisonFunction::LessThanUnsigned,
                            selector.clone(),
                            jump_instructions.len() as u32,
                            table_label.clone(),
                        )
                        .into(),
                        // Otherwise fall through to the default target.
                        jump_directives.into(),
                        // Emit the label for the jump table that will follow.
                        s.emit_label(&mut ctx, table_label).into(),
                    ])
                }
            }

            if !S::is_relative_jump_available() {
                // TODO: emit a sequence of conditional jumps if relative jumps are not available.
                todo!();
            } else {
                // TODO: do the way it is currently done below.
            }

            // For robustness, the jump table has two indirections:
            // - jump_offset $selector
            // - jump jump_to_target_0
            // - jump jump_to_target_1
            // - ...
            // - jump jump_to_target_n
            // - jump_to_target_0:
            // - <actual instructions to jump to target 0>
            // - jump_to_target_1:
            // - <actual instructions to jump to target 1>
            // - ...
            // - jump_to_target_n:
            // - <actual instructions to jump to target n>
            //
            // The exception is if the target jump contains one single local jump instruction,
            // which can be embedded in the jump table directly.
            //
            // TODO: theoretically, any single instruction can be embedded in the jump table,
            // but it would require the guarantee that further translations wouldn't implement
            // any of them as multiple ISA instructions. It is safer to assume just Jump will
            // remain a single instruction. Maybe also Return?
            //
            // TODO: if jump_offset can jump $selector * N, where N is some immediate, this
            // can be implemented with a single indirection, but that would also require
            // 1-to-1 mapping in all the instructions belonging to the jump table.
            directives.push(s.emit_relative_jump(&mut ctx, selector).into());

            let jump_instructions = jump_instructions
                .into_iter()
                .filter_map(|jump_directives| match jump_directives {
                    JumpResult::PlainJump(target) => {
                        // This is a plain jump, just emit it directly.
                        directives.push(s.emit_jump(target).into());
                        None
                    }
                    JumpResult::Directives(jump_directives) => {
                        // This is a complex jump, we need to create a new label
                        // and do one indirection.
                        let jump_label = ctx.new_label(LabelType::Local);
                        directives.push(s.emit_jump(jump_label.clone()).into());
                        Some((jump_label, jump_directives))
                    }
                })
                // Collecting here is essential, because of side effects of pushing
                // into `directives`.
                .collect_vec();

            // Finally emit the jump directives for each target.
            for (jump_label, jump_directives) in jump_instructions {
                directives.push(s.emit_label(&mut ctx, jump_label).into());
                directives.push(jump_directives.into());
            }
            directives.into()
        }
        Operation::WASMOp(Op::Call { function_index }) => {
            let curr_entry = ctrl_stack.front().unwrap();

            if let Some((module, function)) = ctx.common.prog.get_imported_func(function_index) {
                // Imported functions are kinda like system calls, and we assume
                // the implementation can access the input and output registers directly,
                // so we just have to emit the call directive.
                let outputs = (0..node.output_types.len())
                    .map(|output_idx| {
                        curr_entry
                            .allocation
                            .get(&ValueOrigin {
                                node: node_idx,
                                output_idx: output_idx as u32,
                            })
                            .unwrap()
                    })
                    .collect_vec();

                s.emit_imported_call(&mut ctx, module, function, &inputs, outputs)
                    .into()
            } else {
                // Normal function calls requires inputs to be copied to where they are needed in the
                // function frame, and also may require outputs to be copied to where the users expect
                // the values.
                let func_type = &ctx.common.prog.get_func_type(function_index).ty;
                let call = prepare_function_call(
                    s,
                    &mut ctx,
                    &curr_entry.allocation,
                    node_idx,
                    &inputs,
                    func_type,
                );

                vec![
                    call.prefix_directives.into(),
                    s.emit_function_call(
                        &mut ctx,
                        format_label(function_index, LabelType::Function),
                        call.frame_start,
                        call.ret_pc,
                        call.ret_fp,
                    )
                    .into(),
                    call.suffix_directives.into(),
                ]
                .into()
            }
        }
        Operation::WASMOp(Op::CallIndirect {
            table_index,
            type_index,
        }) => {
            let curr_entry = ctrl_stack.front().unwrap();

            // The last input of the CallIndirect operation is the table entry, the others are the function arguments.
            let (entry_idx, inputs) = inputs.split_last().unwrap();
            let entry_idx = entry_idx.as_register().unwrap().clone();

            let fn_type = ctx.common.prog.get_type(type_index);
            let call = prepare_function_call(
                s,
                &mut ctx,
                &curr_entry.allocation,
                node_idx,
                inputs,
                &fn_type.ty,
            );

            // We need to load the function reference from the table, so we allocate
            // the space for it and emit the table.get directive.
            let func_ref_reg = ctx.allocate_tmp_type::<S>(ValType::FUNCREF);

            // Split the components of the function reference:
            let split_ref = split_func_ref_regs::<S>(func_ref_reg.clone());

            // Indirect calls require checking the function type first.
            // We need a label for the OK case.
            let ok_label = ctx.new_label(LabelType::Local);

            // The sequence to load the function reference, check the type,
            // and then perform the indirect call.
            vec![
                s.emit_wasm_op(
                    &mut ctx,
                    Op::TableGet { table: table_index },
                    &[WasmOpInput::Register(entry_idx)],
                    Some(func_ref_reg),
                )
                .into(),
                s.emit_conditional_jump_cmp_immediate(
                    &mut ctx,
                    ComparisonFunction::Equal,
                    split_ref[FunctionRef::<S>::TYPE_ID].clone(),
                    fn_type.unique_id,
                    ok_label.clone(),
                )
                .into(),
                s.emit_trap(&mut ctx, TrapReason::WrongIndirectCallFunctionType)
                    .into(),
                s.emit_label(&mut ctx, ok_label).into(),
                call.prefix_directives.into(),
                s.emit_indirect_call(
                    &mut ctx,
                    split_ref[FunctionRef::<S>::FUNC_ADDR].clone(),
                    call.frame_start,
                    call.ret_pc,
                    call.ret_fp,
                )
                .into(),
                call.suffix_directives.into(),
            ]
            .into()
        }
        Operation::WASMOp(Op::Unreachable) => s
            .emit_trap(&mut ctx, TrapReason::UnreachableInstruction)
            .into(),
        Operation::WASMOp(op) => {
            // Normal WASM operations are handled by the ISA emmiter directly.
            let curr_entry = ctrl_stack.front().unwrap();
            let output = match node.output_types.len() {
                0 => None,
                1 => Some(
                    curr_entry
                        .allocation
                        .get(&ValueOrigin {
                            node: node_idx,
                            output_idx: 0,
                        })
                        .unwrap(),
                ),
                _ => {
                    panic!("WASM instructions with multiple outputs! This is a bug.");
                }
            };
            s.emit_wasm_op(&mut ctx, op, &inputs, output).into()
        }
    }
}

enum JumpResult<D> {
    Directives(Vec<Tree<D>>),
    PlainJump(String),
}

impl<D> JumpResult<D> {
    fn into_tree<'a, S: Settings<'a>>(self, s: &S) -> Tree<D>
    where
        Tree<D>: From<S::Directive>,
    {
        match self {
            JumpResult::Directives(directives) => directives.into(),
            JumpResult::PlainJump(target) => s.emit_jump(target).into(),
        }
    }
}

fn emit_jump<'a, S: Settings<'a>>(
    s: &S,
    ctx: &mut Context<'a, '_>,
    ctrl_stack: &VecDeque<StackEntry>,
    target: BreakTarget,
    inputs: &[WasmOpInput],
    func_idx: u32,
) -> JumpResult<S::Directive> {
    // There are 3 different kinds of jumps we have to deal with:
    //
    // 1. Jumps to a forward label in the current function.
    // 2. Jump backwards to a loop iteration.
    // 3. Returns from the function.

    let target_entry = &ctrl_stack[target.depth as usize];
    let (output_node_idx, target) = match target.kind {
        TargetType::FunctionOrLoop => {
            match &target_entry.loop_label {
                Some(loop_label) => {
                    // This is a jump to a new loop iteration.
                    // The node whose outputs we want are the Inputs node of the loop (index 0).
                    (0, loop_label.as_str().into())
                }
                None => {
                    // This is a return from the function.
                    // Calculate the outputs registers from the function type.
                    let func_type = &ctx.common.prog.get_func_type(func_idx).ty;
                    let ret_types = func_type.results();
                    // They are tightly packed at the top of the frame.
                    let mut fn_output_size = 0;
                    let input_ranges = ranges_for_types::<S>(ret_types, &mut fn_output_size);

                    // Use the current block's allocation to source the copied inputs:
                    let mut directives = copy_inputs_if_needed(s, ctx, inputs, input_ranges);

                    // Also calculate the space needed by the function inputs, to calculate where
                    // the return address and caller frame pointer are stored.
                    let fn_input_size = word_count_types::<S>(func_type.params());
                    let (ra, caller_fp) = calculate_ra_and_fp::<S>(fn_input_size, fn_output_size);

                    directives.push(s.emit_return(ctx, ra, caller_fp).into());

                    return JumpResult::Directives(directives);
                }
            }
        }
        TargetType::Label(id) => {
            // This is a jump to a label in the current function.
            // The node we want is the target label's node.
            (
                target_entry.allocation.labels[&id],
                format_label(id, LabelType::Local),
            )
        }
    };

    let input_ranges = target_entry.allocation.get_for_node(output_node_idx);
    let mut directives = copy_inputs_if_needed(s, ctx, inputs, input_ranges);
    if directives.is_empty() {
        JumpResult::PlainJump(target)
    } else {
        directives.push(s.emit_jump(target).into());

        JumpResult::Directives(directives)
    }
}

/// Every control flow that has inputs needs them at specific locations.
///
/// This function emits the copy instructions for the inputs that are not
/// already at the expected locations.
fn copy_inputs_if_needed<'a, S: Settings<'a>>(
    s: &S,
    ctx: &mut Context<'a, '_>,
    node_inputs: &[WasmOpInput],
    expected_locations: impl IntoIterator<Item = Range<u32>>,
) -> Vec<Tree<S::Directive>> {
    let copy_set = node_inputs
        .iter()
        .zip_eq(expected_locations)
        .filter_map(|(input, destiny)| {
            let source = input.as_register().unwrap().clone();
            (source != destiny).then_some((source, destiny))
        })
        .collect_vec();
    parallel_copy(s, ctx, copy_set)
}

/// Given a set of source-destination register ranges, emits the sequence of copy instructions
/// such that all copies are performed correctly, even in presence of overlapping ranges.
fn parallel_copy<'a, S: Settings<'a>>(
    s: &S,
    ctx: &mut Context<'a, '_>,
    copy_set: Vec<(Range<u32>, Range<u32>)>,
) -> Vec<Tree<S::Directive>> {
    // Turn a set of range copies into a set of single register copies.
    let copy_set = copy_set
        .into_iter()
        .flat_map(|(source_range, dest_range)| source_range.into_iter().zip(dest_range));
    let copy_sequence = sequence_parallel_copies::sequence_parallel_copies(copy_set);

    // Just allocate a temporary register if needed.
    let mut tmp_register = None;
    let mut materialize = |ctx: &mut Context<'a, '_>, reg| -> u32 {
        match reg {
            Register::Temp => match tmp_register {
                Some(tmp_reg) => tmp_reg,
                None => {
                    let new_tmp = ctx.allocate_tmp_type::<S>(ValType::I32);
                    assert_eq!(new_tmp.len(), 1);
                    let new_tmp = new_tmp.start;
                    tmp_register = Some(new_tmp);
                    new_tmp
                }
            },
            Register::Given(reg) => reg,
        }
    };

    copy_sequence
        .map(|(src, dest)| {
            let src = materialize(ctx, src);
            let dest = materialize(ctx, dest);
            s.emit_copy(ctx, src, dest).into()
        })
        .collect_vec()
}

/// Calculates the register address for a tightly packed list types.
fn ranges_for_types<'a, S: Settings<'a>>(
    types: &[ValType],
    start_offset: &mut u32,
) -> impl Iterator<Item = Range<u32>> {
    types.iter().scan(start_offset, |offset, ty| {
        let size = word_count_type::<S>(*ty);
        let start = **offset;
        **offset += size;
        Some(start..**offset)
    })
}

fn calculate_ra_and_fp<'a, S: Settings<'a>>(
    input_size: u32,
    output_size: u32,
) -> (Range<u32>, Range<u32>) {
    let ra_ptr = input_size.max(output_size);
    let caller_fp_ptr = ra_ptr + S::words_per_ptr();

    let ra = ra_ptr..caller_fp_ptr;
    let caller_fp = caller_fp_ptr..(caller_fp_ptr + S::words_per_ptr());
    (ra, caller_fp)
}

/// Context for the flattening process of the entire function.
struct CommonContext<'a, 'b> {
    prog: &'b Module<'a>,
    label_gen: &'b AtomicU32,
}

/// A context built per node being processed, that tracks the
/// temporary registers needed when translating just that node.
pub struct Context<'a, 'b> {
    common: &'b CommonContext<'a, 'b>,
    allocation: &'b Allocation,
    node_index: usize,
    node_inputs: &'b [WasmOpInput],
    /// This is needed for the tmp_tracker to work when a tmp is
    /// requested during the translation of a function call.
    /// In that case, most of the register space will be occupied by
    /// the function call frame, but it is fine to allocate tmps in that space,
    /// after the space reserved for the calling convention (inputs,
    /// outputs, return address and caller frame pointer).
    function_call_prelude_size: Option<u32>,
    /// If no temporary registers were allocated yet, this is None.
    /// If some were allocated, this tracks all the holes in the
    /// frame that can be used for further temporary allocations,
    /// kept in reverse sorted order.
    tmp_tracker: Option<Vec<Range<u32>>>,
}

impl<'a, 'b> Context<'a, 'b> {
    fn new(
        common: &'b CommonContext<'a, 'b>,
        allocation: &'b Allocation,
        node_index: usize,
        node_inputs: &'b [WasmOpInput],
    ) -> Self {
        Self {
            common,
            allocation,
            node_index,
            node_inputs,
            function_call_prelude_size: None,
            tmp_tracker: None,
        }
    }

    fn allocate_tmp_words(&mut self, size: u32) -> Range<u32> {
        if self.tmp_tracker.is_none() {
            // This is the first time a temporary is being allocated at this node.
            // We need to figure out what slots are available for temporaries.

            // Get all the occupied ranges for this node.
            let mut occupied_ranges = self.allocation.occupation_for_node(self.node_index);

            // We also need to include the inputs for this node, because in our occupation convention,
            // if this is the last usage of an input, it is already considered free in this node.
            occupied_ranges.extend(
                self.node_inputs
                    .iter()
                    .filter_map(|input| input.as_register().cloned()),
            );

            let mut holes = Vec::new();
            let mut last_occupied = 0..0;
            for occupied in RangeConsolidationIterator::new(occupied_ranges) {
                if occupied.start > last_occupied.end {
                    holes.push(last_occupied.end..occupied.start);
                }
                last_occupied = occupied;
            }

            if let Some(prelude_size) = self.function_call_prelude_size {
                let frame_start = self.allocation.call_frames[&self.node_index];
                // The last occupation must contain the function frame
                assert!(last_occupied.start <= frame_start);
                assert_eq!(last_occupied.end, u32::MAX);

                // We can use the part of the function frame that
                // is not reserved for the calling convention.
                last_occupied.end = frame_start + prelude_size;
            }

            if last_occupied.end < u32::MAX {
                holes.push(last_occupied.end..u32::MAX);
            }
            holes.reverse(); // So we can allocate from the end.
            self.tmp_tracker = Some(holes);
        }

        let tmp_tracker = self.tmp_tracker.as_mut().unwrap();

        for idx in (0..tmp_tracker.len()).rev() {
            let hole = &mut tmp_tracker[idx];
            if hole.len() as u32 >= size {
                let alloc_end = hole.start + size;
                let allocated = hole.start..alloc_end;
                if alloc_end == hole.end {
                    // The hole is fully used up.
                    //
                    // I would like to use a LinkedList here, but Rust has no stable API
                    // to remove an element from the middle of a LinkedList in O(1) time,
                    // (cursor API is unstable) so even Vec's O(n) removal is better here.
                    //
                    // The search is done from the end in order to minimize the number of
                    // of elements shifted when removing. If the first hole is used, no
                    // element needs to be shifted.
                    tmp_tracker.remove(idx);
                } else {
                    // Shrink the hole.
                    hole.start = alloc_end;
                }
                return allocated;
            }
        }
        panic!("Full register space exhausted when allocating temporary registers.");
    }

    /// Allocates a temporary register that is only valid for the sequence of instructions
    /// you are emitting.
    pub fn allocate_tmp_type<S: Settings<'a>>(&mut self, ty: ValType) -> Range<u32> {
        self.allocate_tmp_words(word_count_type::<S>(ty))
    }

    pub fn new_label(&self, label_type: LabelType) -> String {
        format_label(self.common.label_gen.next(), label_type)
    }

    /// Returns a reference to the module being processed.
    ///
    /// The returned reference has lifetime `'b` (independent of the `&self` borrow),
    /// so callers can use it alongside `&mut self` without borrow conflicts.
    pub fn module(&self) -> &'b Module<'a> {
        self.common.prog
    }
}

struct FunctionCall<D> {
    frame_start: u32,
    prefix_directives: Vec<Tree<D>>,
    suffix_directives: Vec<Tree<D>>,
    ret_pc: Range<u32>,
    ret_fp: Range<u32>,
}

fn prepare_function_call<'a, S: Settings<'a>>(
    s: &S,
    ctx: &mut Context<'a, '_>,
    allocation: &Allocation,
    node_idx: usize,
    inputs: &[WasmOpInput],
    func_type: &FuncType,
) -> FunctionCall<S::Directive> {
    // Normal function calls requires inputs to be copied to where they are needed in the
    // function frame, and also may require outputs to be copied to where the users expect
    // the values.

    let frame_start = allocation.call_frames[&node_idx];

    // Get where the inputs should be copied to.
    let mut inputs_offset = frame_start;
    let input_ranges = ranges_for_types::<S>(func_type.params(), &mut inputs_offset).collect_vec();

    // Get where the outputs should be copied from.
    let mut outputs_offset = frame_start;
    let output_copy_set = ranges_for_types::<S>(func_type.results(), &mut outputs_offset)
        .enumerate()
        .filter_map(|(output_idx, src_range)| {
            let output_origin = ValueOrigin {
                node: node_idx,
                output_idx: output_idx as u32,
            };
            let dest_range = allocation.get(&output_origin).unwrap();
            assert_eq!(src_range.len(), dest_range.len());

            (dest_range != src_range).then_some((src_range, dest_range))
        })
        .collect_vec();

    // Calculate where return address and caller frame pointer are stored.
    // Also calculate the space needed by the function inputs, to calculate where
    // the return address and caller frame pointer are stored.
    let input_size = inputs_offset - frame_start;
    let outputs_size = outputs_offset - frame_start;
    let (ret_pc, ret_fp) = calculate_ra_and_fp::<S>(input_size, outputs_size);

    // Set the end of the function call prelude, so tmps can be allocated in the function frame if needed.
    ctx.function_call_prelude_size = Some(ret_fp.end);

    // Generate the actual directives for input and output copy.
    let prefix_directives = copy_inputs_if_needed(s, ctx, inputs, input_ranges);
    let suffix_directives = parallel_copy(s, ctx, output_copy_set);

    FunctionCall {
        frame_start,
        prefix_directives,
        suffix_directives,
        ret_pc,
        ret_fp,
    }
}
