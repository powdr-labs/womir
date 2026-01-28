//! This module flattens the DAG structure, generating an assembly-like representation.
//!
//! The algorithm is straightforward and linear, as most of the complexity was handled
//! in earlier passes (notably register allocation).

use itertools::Itertools;
use wasmparser::{Operator as Op, ValType};

use crate::{
    loader::{
        LabelGenerator, Module, assert_reg,
        passes::{
            blockless_dag::{BreakTarget, Operation, TargetType},
            dag::{NodeInput, ValueOrigin},
        },
        rwm::{
            register_allocation::{self, AllocatedDag, Allocation},
            settings::Settings,
        },
        settings::{ComparisonFunction, JumpCondition, LabelType, format_label},
        word_count_type, word_count_types,
    },
    utils::tree::Tree,
};
use std::{collections::VecDeque, ops::Range, sync::atomic::AtomicU32};

pub struct Asm<D> {
    pub func_idx: u32,
    pub directives: Vec<D>,
}

pub fn flatten_dag<'a, S: Settings<'a>>(
    s: &S,
    prog: &Module<'a>,
    label_gen: &AtomicU32,
    func_idx: u32,
    dag: AllocatedDag<'a>,
) -> Asm<S::Directive> {
    let ctx = CommonContext { prog, label_gen };

    let mut ctrl_stack = VecDeque::new();
    ctrl_stack.push_front(StackEntry {
        loop_label: None,
        allocation: dag.block_data,
    });

    let tree = process_dag(s, &ctx, &mut ctrl_stack, dag.nodes, func_idx);

    Asm {
        func_idx,
        directives: tree.flatten(),
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
    nodes: Vec<register_allocation::Node>,
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
    ctx: &'b CommonContext<'a, 'b>,
    ctrl_stack: &mut VecDeque<StackEntry>,
    node: register_allocation::Node,
    node_idx: usize,
    func_idx: u32,
) -> Tree<S::Directive> {
    let mut ctx = Context::new(ctx, node_idx);
    match node.operation {
        Operation::Inputs => {
            // Inputs does not translate to any assembly directive.
            Tree::Empty
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
            let mut loop_directives = copy_inputs_if_needed(
                s,
                &mut ctx,
                &ctrl_stack[0].allocation,
                &node.inputs,
                input_ranges,
            );

            // Generate loop label.
            let loop_label = ctx.new_label(LabelType::Loop);

            // Process the loop body.
            ctrl_stack.push_front(StackEntry {
                loop_label: Some(loop_label),
                allocation: loop_allocation,
            });
            let loop_tree = process_dag(s, ctx.common, ctrl_stack, loop_nodes, func_idx);
            let StackEntry { loop_label, .. } = ctrl_stack.pop_front().unwrap();

            // Push the loop directives.
            loop_directives.push(s.emit_label(&mut ctx, loop_label.unwrap()).into());
            loop_directives.push(loop_tree);
            loop_directives.into()
        }
        Operation::Br(break_target) => emit_jump(
            s,
            &mut ctx,
            ctrl_stack,
            break_target,
            &node.inputs,
            func_idx,
        )
        .into_tree(s),
        Operation::BrIf(target) | Operation::BrIfZero(target) => {
            let (cond, inverse_cond) = match node.operation {
                Operation::BrIf(..) => (JumpCondition::IfNotZero, JumpCondition::IfZero),
                Operation::BrIfZero(..) => (JumpCondition::IfZero, JumpCondition::IfNotZero),
                _ => unreachable!(),
            };

            // Get the conditional variable from the inputs.
            let mut inputs = node.inputs;
            let cond_origin = inputs.pop().unwrap();
            let cond_reg = ctrl_stack[0].allocation.get_as_reg(&cond_origin).unwrap();
            assert_reg::<S>(&cond_reg, ValType::I32);

            let jump_directives = emit_jump(s, &mut ctx, ctrl_stack, target, &inputs, func_idx);
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
            let curr_entry = &ctrl_stack[0];

            let mut node_inputs = node.inputs;
            let selector = curr_entry
                .allocation
                .get_as_reg(&node_inputs.pop().unwrap())
                .unwrap();

            let mut jump_instructions = targets
                .into_iter()
                .map(|target| {
                    // The inputs for one particular target are a permutation of the inputs
                    // of the BrTable operation.
                    let inputs = target
                        .input_permutation
                        .iter()
                        .map(|&idx| node_inputs[idx as usize].clone())
                        .collect_vec();

                    // Emit the jump to the target label.
                    emit_jump(s, &mut ctx, ctrl_stack, target.target, &inputs, func_idx)
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
                let inputs = map_input_into_regs(node.inputs, &curr_entry.allocation);
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

                s.emit_imported_call(&mut ctx, module, function, inputs, outputs)
                    .into()
            } else {
                // Normal function calls requires inputs to be copied to where they are needed in the
                // function frame, and also may require outputs to be copied to where the users expect
                // the values.

                let frame_start = curr_entry.allocation.call_frames[&node_idx];
                let func_type = &ctx.common.prog.get_func_type(function_index).ty;

                // Generate the copy of the inputs.
                let mut inputs_offset = frame_start;
                let mut directives = copy_inputs_if_needed(
                    s,
                    &mut ctx,
                    &curr_entry.allocation,
                    &node.inputs,
                    ranges_for_types::<S>(func_type.params(), &mut inputs_offset),
                );

                // Generate the copy of the outputs.
                let mut outputs_offset = frame_start;
                let mut output_copy_directives = Vec::new();
                let src_output_ranges =
                    ranges_for_types::<S>(func_type.results(), &mut outputs_offset);
                for (output_idx, src_range) in src_output_ranges.enumerate() {
                    let output_origin = ValueOrigin {
                        node: node_idx,
                        output_idx: output_idx as u32,
                    };
                    let dest_range = curr_entry.allocation.get(&output_origin).unwrap();
                    assert_eq!(src_range.len(), dest_range.len());

                    if dest_range != src_range {
                        output_copy_directives.extend(
                            dest_range
                                .into_iter()
                                .zip(src_range)
                                .map(|(dest, src)| s.emit_copy(&mut ctx, src, dest).into()),
                        );
                    }
                }

                // Calculate where return address and caller frame pointer are stored.
                // Also calculate the space needed by the function inputs, to calculate where
                // the return address and caller frame pointer are stored.
                let input_size = inputs_offset - frame_start;
                let outputs_size = outputs_offset - frame_start;
                let (ra, caller_fp) = calculate_ra_and_fp::<S>(input_size, outputs_size);

                // Emit the function call.
                let func_label = format_label(function_index, LabelType::Function);
                directives.push(
                    s.emit_function_call(&mut ctx, func_label, frame_start, ra, caller_fp)
                        .into(),
                );

                // Append the output copy directives.
                if !output_copy_directives.is_empty() {
                    vec![Tree::Node(directives), output_copy_directives.into()].into()
                } else {
                    directives.into()
                }
            }
        }
        /*Operation::WASMOp(Op::CallIndirect {
            table_index,
            type_index,
        }) => {
            let curr_entry = ctrl_stack.front().unwrap();

            // First, we need to load the function reference from the table, so we allocate
            // the space for it and emit the table.get directive.

            // The last input of the CallIndirect operation is the table entry, the others are the function arguments.
            let mut inputs = map_input_into_regs(node.inputs, curr_entry)?;
            let entry_idx = inputs.pop().unwrap();

            let func_ref_reg = ctx.register_gen.allocate_type(ValType::FUNCREF);

            // Split the components of the function reference:
            let func_ref_regs = split_func_ref_regs::<S>(func_ref_reg.clone());

            let ok_label = ctx.new_label(LabelType::Local);
            let func_frame_ptr = ctx.register_gen.allocate_words(S::words_per_ptr());

            // Perform the function call
            let call = prepare_function_call(
                s,
                ctx,
                inputs,
                node_idx,
                node.output_types.len(),
                curr_entry,
                func_frame_ptr.clone(),
            )?;

            vec![
                s.emit_wasm_op(
                    ctx,
                    Op::TableGet { table: table_index },
                    vec![WasmOpInput::Register(entry_idx)],
                    Some(func_ref_reg),
                )
                .into(),
                s.emit_conditional_jump_cmp_immediate(
                    ctx,
                    ComparisonFunction::Equal,
                    func_ref_regs[FunctionRef::<S>::TYPE_ID].clone(),
                    ctx.program.get_type(type_index).unique_id,
                    ok_label.clone(),
                )
                .into(),
                s.emit_trap(ctx, TrapReason::WrongIndirectCallFunctionType)
                    .into(),
                s.emit_label(ctx, ok_label, None).into(),
                s.emit_allocate_value_frame(
                    ctx,
                    func_ref_regs[FunctionRef::<S>::FUNC_FRAME_SIZE].clone(),
                    func_frame_ptr.clone(),
                )
                .into(),
                call.prefix_directives.into(),
                s.emit_indirect_call(
                    ctx,
                    func_ref_regs[FunctionRef::<S>::FUNC_ADDR].clone(),
                    func_frame_ptr,
                    call.ret_info.ret_pc,
                    call.ret_info.ret_fp,
                )
                .into(),
                call.suffix_directives.into(),
            ]
            .into()
        }
        Operation::WASMOp(Op::Unreachable) => {
            s.emit_trap(ctx, TrapReason::UnreachableInstruction).into()
        }
        Operation::WASMOp(op) => {
            // Normal WASM operations are handled by the ISA emmiter directly.
            let curr_entry = ctrl_stack.front().unwrap();
            let inputs = node
                .inputs
                .into_iter()
                .map(|input| {
                    Ok(match input {
                        NodeInput::Constant(c) => WasmOpInput::Constant(c),
                        NodeInput::Reference(origin) => {
                            WasmOpInput::Register(curr_entry.allocation.get(&origin)?)
                        }
                    })
                })
                .collect::<Result<Vec<_>, Error>>()?;
            let output = match node.output_types.len() {
                0 => None,
                1 => Some(curr_entry.allocation.get(&ValueOrigin {
                    node: node_idx,
                    output_idx: 0,
                })?),
                _ => {
                    panic!("WASM instructions with multiple outputs! This is a bug.");
                }
            };
            s.emit_wasm_op(ctx, op, inputs, output).into()
        }*/
        Operation::WASMOp(_) => todo!(),
    }
}

enum JumpResult<'a, S: Settings<'a>> {
    Directives(Vec<Tree<S::Directive>>),
    PlainJump(String),
}

impl<'a, S: Settings<'a>> JumpResult<'a, S> {
    fn into_tree(self, s: &S) -> Tree<S::Directive> {
        match self {
            JumpResult::Directives(directives) => directives.into(),
            JumpResult::PlainJump(target) => s.emit_jump(target).into(),
        }
    }
}

fn emit_jump<'a, S: Settings<'a>>(
    s: &S,
    ctx: &mut Context,
    ctrl_stack: &VecDeque<StackEntry>,
    target: BreakTarget,
    node_inputs: &[NodeInput],
    func_idx: u32,
) -> JumpResult<'a, S> {
    // There are 3 different kinds of jumps we have to deal with:
    //
    // 1. Jumps to a forward label in the current function.
    // 2. Jump backwards to a loop iteration.
    // 3. Returns from the function.

    let entry = &ctrl_stack[target.depth as usize];
    let (output_node_idx, target) = match target.kind {
        TargetType::FunctionOrLoop => {
            match &entry.loop_label {
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
                    // They are tightly packed at the top of the stack frame.
                    let mut fn_output_size = 0;
                    let input_ranges = ranges_for_types::<S>(ret_types, &mut fn_output_size);
                    let mut directives =
                        copy_inputs_if_needed(s, ctx, &entry.allocation, node_inputs, input_ranges);

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
                entry.allocation.labels[&id],
                format_label(id, LabelType::Local),
            )
        }
    };

    let input_ranges = entry.allocation.get_for_node(output_node_idx);
    let mut directives =
        copy_inputs_if_needed(s, ctx, &entry.allocation, node_inputs, input_ranges);
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
    ctx: &mut Context,
    allocation: &Allocation,
    node_inputs: &[NodeInput],
    expected_locations: impl Iterator<Item = Range<u32>>,
) -> Vec<Tree<S::Directive>> {
    let mut copy_instructions = Vec::new();
    for (input, destiny) in node_inputs.iter().zip(expected_locations) {
        let source = allocation.get_as_reg(input).unwrap();
        if source == destiny {
            continue;
        }
        for (src, dest) in source.into_iter().zip(destiny) {
            copy_instructions.push(s.emit_copy(ctx, src, dest).into());
        }
    }
    copy_instructions
}

fn map_input_into_regs(node_inputs: Vec<NodeInput>, allocation: &Allocation) -> Vec<Range<u32>> {
    node_inputs
        .into_iter()
        .map(|input| allocation.get_as_reg(&input).unwrap())
        .collect()
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
    node_index: usize,
    /// If no temporary registers were allocated yet, this is None.
    /// If some were allocated, this tracks all the holes in the
    /// frame that can be used for further temporary allocations,
    /// kept in reverse sorted order.
    tmp_tracker: Option<Vec<Range<u32>>>,
}

impl<'a, 'b> Context<'a, 'b> {
    fn new(common: &'b CommonContext<'a, 'b>, node_index: usize) -> Self {
        Self {
            common,
            node_index,
            tmp_tracker: None,
        }
    }

    pub fn generate_tmp_var(&mut self, size: u32) -> Range<u32> {
        todo!()
    }

    pub fn new_label(&self, label_type: LabelType) -> String {
        format_label(self.common.label_gen.next(), label_type)
    }
}

fn join_tree<T>(mut tree_vec: Vec<Tree<T>>, elem: Tree<T>) -> Tree<T> {
    // Just avoid allocating the Vec's buffer if not allocated yet.
    if tree_vec.is_empty() {
        elem
    } else {
        tree_vec.push(elem);
        tree_vec.into()
    }
}
