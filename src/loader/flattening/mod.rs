//! This module generates an assembly-like representation, flattening
//! the DAG structure and allocating registers for the operations.
//!
//! The algorithm works in 2 passes, and goes like this:
//!
//! Outer Pass: we do a top-down, depth-first traversal of the DAG
//! tree, and call the Inner Pass each traversed DAG/frame. We
//! flatten the tree structure by emmiting assembly-like directives,
//! using the register allocation from the Inner Pass.
//!
//! Inner Pass: for each DAG/frame, we do a bottom-up traversal,
//! assigning registers to the labels outputs, matching with their
//! respective break inputs, and detect whether or not there is a
//! conflict, where multiple instructions would write to the same
//! register in the same execution path. In the end, we will have a
//! partial register assignment for some nodes, where conflicts for
//! break inputs are explicitly marked.

mod allocate_registers;
pub mod settings;

use derive_where::derive_where;

use allocate_registers::{Allocation, optimistic_allocation};
use itertools::Itertools;
use std::{
    collections::{BTreeSet, VecDeque},
    marker::PhantomData,
    ops::{Range, RangeFrom},
};
use wasmparser::{Operator as Op, ValType};

use crate::loader::{
    FunctionRef,
    blockless_dag::{BreakTarget, Node, TargetType},
    dag::ValueOrigin,
    flattening::{
        allocate_registers::NotAllocatedError,
        settings::{
            ComparisonFunction, JumpCondition, LoopFrameLayout, ReturnInfosToCopy, Settings,
        },
    },
};

use super::{
    Program,
    blockless_dag::{BlocklessDag, Operation},
};

/// An assembly-like representation for a write-once memory machine.
#[derive(Debug, Clone)]
pub struct WriteOnceASM<D> {
    pub func_idx: u32,
    pub _frame_size: u32,
    pub directives: Vec<D>,
}

pub enum Tree<T> {
    Empty,
    Leaf(T),
    VecLeaf(Vec<T>),
    Node(Vec<Tree<T>>),
}

impl<T> From<T> for Tree<T> {
    fn from(x: T) -> Self {
        Tree::Leaf(x)
    }
}

impl<T> From<Vec<T>> for Tree<T> {
    fn from(vec: Vec<T>) -> Self {
        Tree::VecLeaf(vec)
    }
}

impl<T> From<Vec<Tree<T>>> for Tree<T> {
    fn from(trees: Vec<Tree<T>>) -> Self {
        if trees.is_empty() {
            Tree::Empty
        } else {
            Tree::Node(trees)
        }
    }
}

impl<T> Tree<T> {
    fn flatten(self) -> Vec<T> {
        fn flatten_rec<T>(dnode: Tree<T>, flat: &mut Vec<T>) {
            match dnode {
                Tree::Empty => {}
                Tree::Leaf(x) => {
                    flat.push(x);
                }
                Tree::VecLeaf(vec) => {
                    flat.extend(vec);
                }
                Tree::Node(children) => {
                    for child in children {
                        flatten_rec(child, flat);
                    }
                }
            }
        }

        let mut flat = Vec::new();
        flatten_rec(self, &mut flat);
        flat
    }
}

#[derive(Clone, Debug)]
#[repr(u32)]
pub enum TrapReason {
    UnreachableInstruction,
    /// This trap happens if an instruction that was deemed unreachable
    /// by the register allocator is actually executed. In this case,
    /// there is necessarily a bug in the register allocator.
    RegisterAllocatorBug,
    WrongIndirectCallFunctionType,
}

pub struct Generators<'a, 'b, S: Settings<'a> + ?Sized> {
    label_gen: &'b mut RangeFrom<u32>,
    pub r: RegisterGenerator<'a, S>,
}

impl<'a, S: Settings<'a> + ?Sized> Generators<'a, '_, S> {
    pub fn new_label(&mut self, label_type: LabelType) -> String {
        format_label(self.label_gen.next().unwrap(), label_type)
    }
}

#[derive_where(Default, Debug, Clone, Copy)]
pub struct RegisterGenerator<'a, S: Settings<'a> + ?Sized> {
    next_available: u32,
    settings: PhantomData<(&'a (), S)>,
}

impl<'a, S: Settings<'a>> RegisterGenerator<'a, S> {
    pub fn new() -> Self {
        Self {
            next_available: 0,
            settings: PhantomData,
        }
    }

    fn merge(&mut self, other: Self) {
        if self.next_available < other.next_available {
            self.next_available = other.next_available;
        }
    }

    pub fn allocate_words(&mut self, word_count: u32) -> Range<u32> {
        let start = self.next_available;
        self.next_available = start + word_count;
        start..self.next_available
    }

    pub fn allocate_type(&mut self, ty: ValType) -> Range<u32> {
        self.allocate_words(word_count_type::<S>(ty))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnInfo {
    pub ret_pc: Range<u32>,
    pub ret_fp: Range<u32>,
}

struct CtrlStackEntry {
    entry_type: CtrlStackType,
    allocation: Allocation,
}

enum CtrlStackType {
    TopLevelFunction { output_regs: Vec<Range<u32>> },
    Loop(LoopStackEntry),
}

/// Contains all the information needed to jump into a new loop iteration.
#[derive(Debug)]
struct LoopStackEntry {
    label: String,
    layout: LoopFrameLayout,
    input_regs: Vec<Range<u32>>,
}

pub fn flatten_dag<'a, S: Settings<'a>>(
    ctx: &Program<'a, S>,
    label_gen: &mut RangeFrom<u32>,
    dag: BlocklessDag<'a>,
    func_idx: u32,
) -> (WriteOnceASM<S::Directive>, usize) {
    // Assuming pointer size is 4 bytes, we reserve the space for return PC and return FP.
    let mut reg_gen = RegisterGenerator::<S>::new();

    let ret_pc = reg_gen.allocate_words(S::words_per_ptr());
    let ret_fp = reg_gen.allocate_words(S::words_per_ptr());

    // As per zCray calling convention, after the return PC and FP, we reserve
    // space for the function inputs and outputs. Not only the inputs, but also
    // the outputs are filled by the caller, value preemptively provided by the prover.
    let func_type = &ctx.c.get_func_type(func_idx).ty;
    let input_regs = func_type
        .params()
        .iter()
        .map(|ty| reg_gen.allocate_type(*ty))
        .collect_vec();
    let output_regs = func_type
        .results()
        .iter()
        .map(|ty| reg_gen.allocate_type(*ty))
        .collect_vec();

    let ret_info = ReturnInfo { ret_pc, ret_fp };

    // Perform the register allocation for the function's top-level frame.
    let (mut allocation, mut number_of_saved_copies) =
        optimistic_allocation(&dag, &mut RegisterGenerator::<S>::new());

    // Since this is the top-level frame, the allocation can
    // not be arbitrary. It must conform to the calling convention,
    // so we must permute the allocation we found to match it.
    let reg_gen = allocate_registers::permute_allocation::<S>(
        &mut allocation,
        input_regs,
        reg_gen.next_available,
    );

    let mut gens = Generators {
        label_gen,
        r: reg_gen,
    };

    let mut ctrl_stack = VecDeque::from([CtrlStackEntry {
        entry_type: CtrlStackType::TopLevelFunction { output_regs },
        allocation,
    }]);

    let (flat_result, frame_size) =
        flatten_frame_tree(ctx, &mut gens, dag, &mut ctrl_stack, Some(ret_info));
    number_of_saved_copies += flat_result.saved_copies;

    // Add the function label with the frame size.
    let mut directives_with_labels = vec![
        ctx.s
            .emit_label(
                &mut gens,
                format_label(func_idx, LabelType::Function),
                Some(frame_size),
            )
            .into(),
    ];

    if let Some(name) = ctx.c.get_exported_func(func_idx) {
        // Add an alternative label, using the exported function name.
        directives_with_labels.push(
            ctx.s
                .emit_label(&mut gens, name.to_string(), Some(frame_size))
                .into(),
        );
    }
    directives_with_labels.push(flat_result.tree);

    let directives = Tree::Node(directives_with_labels).flatten();

    (
        WriteOnceASM {
            func_idx,
            _frame_size: frame_size,
            directives,
        },
        number_of_saved_copies,
    )
}

struct FlatteningResult<T> {
    tree: Tree<T>,
    saved_copies: usize,
}

fn flatten_frame_tree<'a, S: Settings<'a>>(
    ctx: &Program<'a, S>,
    gens: &mut Generators<'a, '_, S>,
    dag: BlocklessDag<'a>,
    ctrl_stack: &mut VecDeque<CtrlStackEntry>,
    ret_info: Option<ReturnInfo>,
) -> (FlatteningResult<S::Directive>, u32) {
    let mut directives = Vec::new();
    let mut number_of_saved_copies = 0;

    for (node_idx, node) in dag.nodes.into_iter().enumerate() {
        let result = translate_single_node(ctx, gens, ctrl_stack, &ret_info, node_idx, node);
        match result {
            Ok(flat_result) => {
                directives.push(flat_result.tree);
                number_of_saved_copies += flat_result.saved_copies;
            }
            Err(NotAllocatedError) => {
                // Some required input for this node was not found in the allocation.
                // This means that the node is unreachable, and we should emit a trap.
                directives.push(
                    ctx.s
                        .emit_trap(gens, TrapReason::RegisterAllocatorBug)
                        .into(),
                );
            }
        }
    }

    (
        FlatteningResult {
            tree: directives.into(),
            saved_copies: number_of_saved_copies,
        },
        gens.r.next_available,
    )
}

fn is_single_plain_jump<'a, S: Settings<'a>>(
    tree: Tree<S::Directive>,
) -> Result<String, Tree<S::Directive>> {
    let mut flat = tree.flatten();
    if flat.len() != 1 {
        return Err(flat.into());
    }
    let directive = flat.pop().unwrap();

    S::to_plain_local_jump(directive).map_err(|directive| directive.into())
}

fn translate_single_node<'a, S: Settings<'a>>(
    ctx: &Program<'a, S>,
    gens: &mut Generators<'a, '_, S>,
    ctrl_stack: &mut VecDeque<CtrlStackEntry>,
    ret_info: &Option<ReturnInfo>,
    node_idx: usize,
    node: Node<'a>,
) -> Result<FlatteningResult<S::Directive>, NotAllocatedError> {
    let mut number_of_saved_copies = 0;
    let res = Ok(match node.operation {
        Operation::Inputs => {
            // Inputs does not translate to any assembly directive. It is used on the node tree for its outputs.
            Tree::Empty
        }
        Operation::Label { id } => {
            // This is a local label.
            ctx.s
                .emit_label(gens, format_label(id, LabelType::Local), None)
                .into()
        }
        Operation::Loop {
            sub_dag,
            break_targets,
        } => {
            // If None, this loop does not return from the function nor iterate to any outer loop.
            let shallowest_iter_or_ret = break_targets
                .iter()
                .find(|(_, targets)| targets.first() == Some(&TargetType::FunctionOrLoop))
                .map(|(depth, _)| *depth);

            let mut saved_fps = BTreeSet::new();
            let toplevel_frame_idx = ctrl_stack.len() as u32 - 1;

            // Test if the loop can return from the function. If so, we need to
            // forward the return info.
            let needs_ret_info = ret_info.is_some() && shallowest_iter_or_ret.is_some();

            if needs_ret_info {
                // If the function has outputs, we need to save the toplevel frame pointer, too.
                let CtrlStackType::TopLevelFunction { output_regs } =
                    &ctrl_stack.back().unwrap().entry_type
                else {
                    unreachable!();
                };

                if !output_regs.is_empty() {
                    saved_fps.insert(toplevel_frame_idx + 1);
                }
            }

            // Select the outer frame pointers that are saved in the current frame, and
            // the loop will need in order to start iterations of some outer loop.
            //
            // There seems to be a recursive proof that all the copied frames are necessary,
            // and the set is complete, but I only remember proving it in my head, not the
            // proof itself.
            if let (CtrlStackType::Loop(this_frame), Some(shallowest)) = (
                &ctrl_stack.front().unwrap().entry_type,
                shallowest_iter_or_ret,
            ) {
                let s = &this_frame.layout.saved_fps;
                saved_fps.extend(s.range(shallowest..).map(|(depth, _)| *depth + 1));
            };

            // Select the frame pointers needed to break into outer frames.
            for (depth, targets) in break_targets.iter() {
                for target in targets {
                    if let TargetType::Label(_) = target {
                        saved_fps.insert(*depth + 1);
                        break;
                    }
                }
            }

            let (mut loop_reg_gen, layout) =
                ctx.s.allocate_loop_frame_slots(needs_ret_info, saved_fps);
            let loop_ret_info = layout.ret_info.clone();

            // Finally allocate all the registers for the loop instructions, including the inputs.
            let (loop_allocation, saved_copies) =
                optimistic_allocation(&sub_dag, &mut loop_reg_gen);
            number_of_saved_copies += saved_copies;

            // Sanity check: loops have no outputs:
            assert!(node.output_types.is_empty());

            // This struct contains everything we need to fill in order to jump into the loop.
            let loop_entry = LoopStackEntry {
                label: gens.new_label(LabelType::Loop),
                layout,
                input_regs: loop_allocation
                    .iter()
                    .take_while(|(val_origin, _)| val_origin.node == 0)
                    .map(|(_, reg)| reg.clone())
                    .collect(),
            };

            // Emit all the instructions to enter the loop.
            let enter_loop_directives = jump_into_loop(
                ctx,
                gens,
                &loop_entry,
                -1,
                ret_info.as_ref(),
                ctrl_stack.front().unwrap(),
                &node.inputs,
            )?;

            let mut loop_gens = Generators {
                label_gen: gens.label_gen,
                r: loop_reg_gen,
            };
            // Emit the listing for the loop itself.
            ctrl_stack.push_front(CtrlStackEntry {
                entry_type: CtrlStackType::Loop(loop_entry),
                allocation: loop_allocation,
            });
            let (loop_flat_result, loop_frame_size) =
                flatten_frame_tree(ctx, &mut loop_gens, sub_dag, ctrl_stack, loop_ret_info);
            let CtrlStackType::Loop(loop_entry) = ctrl_stack.pop_front().unwrap().entry_type else {
                unreachable!()
            };
            number_of_saved_copies += loop_flat_result.saved_copies;

            // Assemble the complete listing for this loop.
            Tree::Node(vec![
                enter_loop_directives.into(),
                ctx.s
                    .emit_label(gens, loop_entry.label, Some(loop_frame_size))
                    .into(),
                loop_flat_result.tree,
            ])
        }
        Operation::Br(target) => emit_jump(
            ctx,
            gens,
            ret_info.as_ref(),
            &node.inputs,
            &target,
            ctrl_stack,
        )?
        .into(),
        Operation::BrIf(target) | Operation::BrIfZero(target) => {
            let (cond, inverse_cond) = match node.operation {
                Operation::BrIf(..) => (JumpCondition::IfNotZero, JumpCondition::IfZero),
                Operation::BrIfZero(..) => (JumpCondition::IfZero, JumpCondition::IfNotZero),
                _ => unreachable!(),
            };

            let curr_entry = ctrl_stack.front().unwrap();

            // Get the conditional variable from the inputs.
            let mut inputs = node.inputs;
            let cond_origin = inputs.pop().unwrap();
            let cond_reg = curr_entry.allocation.get(&cond_origin)?;
            assert_reg::<S>(&cond_reg, ValType::I32);

            // Emit the jump to the target label.
            let mut jump_directives =
                emit_jump(ctx, gens, ret_info.as_ref(), &inputs, &target, ctrl_stack)?.into();

            // If the jump is single plain jump to a local label, we can optimize this jump by
            // emitting a single conditional jump. This is the best case.
            let optimized = if S::is_jump_condition_available(cond) {
                match is_single_plain_jump::<S>(std::mem::replace(
                    &mut jump_directives,
                    Tree::Empty,
                )) {
                    Ok(target) => Some(
                        ctx.s
                            .emit_conditional_jump(gens, cond, target, cond_reg.clone())
                            .into(),
                    ),
                    Err(directives) => {
                        jump_directives = directives;
                        None
                    }
                }
            } else {
                None
            };

            if let Some(optimized) = optimized {
                optimized
            } else if S::is_jump_condition_available(inverse_cond) {
                // Uses branch on inverse condition for the general case. This is the second best case.
                let cont_label = gens.new_label(LabelType::Local);
                vec![
                    // Emit the jump to continuation if the condition is non-zero.
                    ctx.s
                        .emit_conditional_jump(gens, inverse_cond, cont_label.clone(), cond_reg)
                        .into(),
                    // Emit the jump to the target label.
                    jump_directives,
                    // Emit the continuation label.
                    ctx.s.emit_label(gens, cont_label, None).into(),
                ]
                .into()
            } else if S::is_jump_condition_available(cond) {
                // Uses conditional branch for the general case. This is the worst case, because it
                // it requires two labels and two jumps.
                let cont_label = gens.new_label(LabelType::Local);
                let jump_label = gens.new_label(LabelType::Local);

                vec![
                    // Emit the jump to the to the jump code
                    ctx.s
                        .emit_conditional_jump(gens, cond, jump_label.clone(), cond_reg)
                        .into(),
                    // Emit the jump to the continuation label.
                    ctx.s.emit_jump(cont_label.clone()).into(),
                    // Emit the jump label.
                    ctx.s.emit_label(gens, jump_label, None).into(),
                    // Emit the jump code.
                    jump_directives,
                    // Emit the continuation label.
                    ctx.s.emit_label(gens, cont_label, None).into(),
                ]
                .into()
            } else {
                panic!(
                    "Neither branch if zero nor branch if not zero is available in the settings."
                );
            }
        }
        Operation::BrTable { targets } => {
            let curr_entry = ctrl_stack.front().unwrap();

            let mut node_inputs = node.inputs;
            let selector = curr_entry.allocation.get(&node_inputs.pop().unwrap())?;

            let mut jump_instructions = targets
                .into_iter()
                .map(|target| {
                    // The inputs for one particular target are a permutation of the inputs
                    // of the BrTable operation.
                    let inputs = target
                        .input_permutation
                        .iter()
                        .map(|&idx| node_inputs[idx as usize])
                        .collect_vec();

                    // Emit the jump to the target label.
                    emit_jump(
                        ctx,
                        gens,
                        ret_info.as_ref(),
                        &inputs,
                        &target.target,
                        ctrl_stack,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;

            // The last target is special, because it is the default target.
            let default_target = jump_instructions.pop().unwrap().into();

            // We need to handle the default target separately first, because it will be
            // the target in case the selector is out of bounds.
            let mut directives = Vec::new();
            match is_single_plain_jump::<S>(default_target) {
                Ok(target) => {
                    // If the default target is a plain jump to a local label.
                    directives.push(
                        ctx.s
                            .emit_conditional_jump_cmp_immediate(
                                gens,
                                ComparisonFunction::GreaterThanOrEqualUnsigned,
                                selector.clone(),
                                jump_instructions.len() as u32,
                                target,
                            )
                            .into(),
                    );
                }
                Err(default_target) => {
                    // If the default target is a complex jump.
                    let table_label = gens.new_label(LabelType::Local);
                    directives.extend([
                        // Jump to the table if the selector is in bounds.
                        ctx.s
                            .emit_conditional_jump_cmp_immediate(
                                gens,
                                ComparisonFunction::LessThanUnsigned,
                                selector.clone(),
                                jump_instructions.len() as u32,
                                table_label.clone(),
                            )
                            .into(),
                        // Otherwise fall through to the default target.
                        default_target,
                        // Emit the label for the jump table that will follow.
                        ctx.s.emit_label(gens, table_label, None).into(),
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
            directives.push(ctx.s.emit_relative_jump(gens, selector).into());

            let jump_instructions = jump_instructions
                .into_iter()
                .filter_map(|jump_directives| {
                    match is_single_plain_jump::<S>(jump_directives.into()) {
                        Ok(target) => {
                            directives.push(ctx.s.emit_jump(target).into());
                            None
                        }
                        Err(jump_directives) => {
                            let jump_label = gens.new_label(LabelType::Local);
                            directives.push(ctx.s.emit_jump(jump_label.clone()).into());
                            Some((jump_label, jump_directives))
                        }
                    }
                })
                // Collecting here is essential, because of side effects of pushing
                // into `directives`.
                .collect_vec();

            // Finally emit the jump directives for each target.
            for (jump_label, jump_directives) in jump_instructions {
                directives.push(ctx.s.emit_label(gens, jump_label, None).into());
                directives.push(jump_directives);
            }
            directives.into()
        }
        Operation::WASMOp(Op::Call { function_index }) => {
            let curr_entry = ctrl_stack.front().unwrap();

            if let Some((module, function)) = ctx.c.get_imported_func(function_index) {
                // Imported functions are kinda like system calls, and we assume
                // the implementation can access the input and output registers directly,
                // so we just have to emit the call directive.
                let inputs = map_input_into_regs(node.inputs, curr_entry)?;
                let outputs = (0..node.output_types.len())
                    .map(|output_idx| {
                        curr_entry.allocation.get(&ValueOrigin {
                            node: node_idx,
                            output_idx: output_idx as u32,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                ctx.s
                    .emit_imported_call(gens, module, function, inputs, outputs)
                    .into()
            } else {
                // Normal function calls requires a frame allocation and copying of the
                // inputs and outputs into the frame (the outputs are provided by the
                // prover "from the future").
                let func_frame_ptr = gens.r.allocate_words(S::words_per_ptr());

                let inputs = node
                    .inputs
                    .into_iter()
                    .map(|origin| curr_entry.allocation.get(&origin))
                    .collect::<Result<Vec<_>, _>>()?;
                let call = prepare_function_call(
                    ctx,
                    gens,
                    inputs,
                    node_idx,
                    node.output_types.len(),
                    curr_entry,
                    func_frame_ptr.clone(),
                )?;

                Tree::Node(vec![
                    ctx.s
                        .emit_allocate_label_frame(
                            gens,
                            format_label(function_index, LabelType::Function),
                            func_frame_ptr.clone(),
                        )
                        .into(),
                    call.copy_directives.into(),
                    ctx.s
                        .emit_function_call(
                            gens,
                            format_label(function_index, LabelType::Function),
                            func_frame_ptr,
                            call.ret_info.ret_pc,
                            call.ret_info.ret_fp,
                        )
                        .into(),
                ])
            }
        }
        Operation::WASMOp(Op::CallIndirect {
            table_index,
            type_index,
        }) => {
            let curr_entry = ctrl_stack.front().unwrap();

            // First, we need to load the function reference from the table, so we allocate
            // the space for it and emit the table.get directive.

            // The last input of the CallIndirect operation is the table entry, the others are the function arguments.
            let mut inputs = map_input_into_regs(node.inputs, curr_entry)?;
            let entry_idx = inputs.pop().unwrap();

            let func_ref_reg = gens.r.allocate_type(ValType::FUNCREF);

            // Split the components of the function reference:
            let func_ref_regs = split_func_ref_regs::<S>(func_ref_reg.clone());

            let ok_label = gens.new_label(LabelType::Local);
            let func_frame_ptr = gens.r.allocate_words(S::words_per_ptr());

            // Perform the function call
            let call = prepare_function_call(
                ctx,
                gens,
                inputs,
                node_idx,
                node.output_types.len(),
                curr_entry,
                func_frame_ptr.clone(),
            )?;

            vec![
                ctx.s
                    .emit_table_get(gens, table_index, entry_idx, func_ref_reg)
                    .into(),
                ctx.s
                    .emit_conditional_jump_cmp_immediate(
                        gens,
                        ComparisonFunction::Equal,
                        func_ref_regs[FunctionRef::<S>::TYPE_ID].clone(),
                        ctx.c.get_type(type_index).unique_id,
                        ok_label.clone(),
                    )
                    .into(),
                ctx.s
                    .emit_trap(gens, TrapReason::WrongIndirectCallFunctionType)
                    .into(),
                ctx.s.emit_label(gens, ok_label, None).into(),
                ctx.s
                    .emit_allocate_value_frame(
                        gens,
                        func_ref_regs[FunctionRef::<S>::FUNC_FRAME_SIZE].clone(),
                        func_frame_ptr.clone(),
                    )
                    .into(),
                call.copy_directives.into(),
                ctx.s
                    .emit_indirect_call(
                        gens,
                        func_ref_regs[FunctionRef::<S>::FUNC_ADDR].clone(),
                        func_frame_ptr,
                        call.ret_info.ret_pc,
                        call.ret_info.ret_fp,
                    )
                    .into(),
            ]
            .into()
        }
        Operation::WASMOp(Op::Unreachable) => ctx
            .s
            .emit_trap(gens, TrapReason::UnreachableInstruction)
            .into(),
        Operation::WASMOp(op) => {
            // Normal WASM operations are handled by the ISA emmiter directly.
            let curr_entry = ctrl_stack.front().unwrap();
            let inputs = map_input_into_regs(node.inputs, curr_entry)?;
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
            ctx.s.emit_wasm_op(gens, op, inputs, output).into()
        }
    });

    res.map(|tree| FlatteningResult {
        tree,
        saved_copies: number_of_saved_copies,
    })
}

fn assert_reg<'a, S: Settings<'a>>(reg: &Range<u32>, ty: ValType) {
    let expected_size = byte_size::<S>(ty);
    assert_eq!(reg.len(), word_count::<S>(expected_size) as usize);
}

fn map_input_into_regs(
    node_inputs: Vec<ValueOrigin>,
    curr_entry: &CtrlStackEntry,
) -> Result<Vec<Range<u32>>, NotAllocatedError> {
    node_inputs
        .into_iter()
        .map(|origin| curr_entry.allocation.get(&origin))
        .collect()
}

fn copy_into_frame<'a, S: Settings<'a>>(
    ctx: &Program<'a, S>,
    gens: &mut Generators<'a, '_, S>,
    src: Range<u32>,
    dest_frame: Range<u32>,
    dest: Range<u32>,
) -> Vec<Tree<S::Directive>> {
    src.zip_eq(dest)
        .map(move |(src_word, dest_word)| {
            ctx.s
                .emit_copy_into_frame(
                    gens,
                    src_word..src_word + 1,
                    dest_frame.clone(),
                    dest_word..dest_word + 1,
                )
                .into()
        })
        .collect()
}

struct FunctionCall<D> {
    copy_directives: Vec<Tree<D>>,
    ret_info: ReturnInfo,
}

fn prepare_function_call<'a, S: Settings<'a>>(
    ctx: &Program<'a, S>,
    gens: &mut Generators<'a, '_, S>,
    inputs: Vec<Range<u32>>,
    node_idx: usize,
    num_outputs: usize,
    curr_entry: &CtrlStackEntry,
    frame_ptr: Range<u32>,
) -> Result<FunctionCall<S::Directive>, NotAllocatedError> {
    let mut copy_directives = Vec::new();

    // Generate the registers in the order expected by the calling convention.
    let mut fn_reg_gen = RegisterGenerator::<S>::new();
    let ret_info = ReturnInfo {
        ret_pc: fn_reg_gen.allocate_words(S::words_per_ptr()),
        ret_fp: fn_reg_gen.allocate_words(S::words_per_ptr()),
    };

    for src_reg in inputs {
        let dest_reg = fn_reg_gen.allocate_words(src_reg.len() as u32);
        copy_directives
            .push(copy_into_frame(ctx, gens, src_reg, frame_ptr.clone(), dest_reg).into());
    }
    for output_idx in 0..num_outputs {
        let src_reg = curr_entry.allocation.get(&ValueOrigin {
            node: node_idx,
            output_idx: output_idx as u32,
        })?;
        let dest_reg = fn_reg_gen.allocate_words(src_reg.len() as u32);
        copy_directives
            .push(copy_into_frame(ctx, gens, src_reg, frame_ptr.clone(), dest_reg).into());
    }

    Ok(FunctionCall {
        copy_directives,
        ret_info,
    })
}

fn emit_jump<'a, S: Settings<'a>>(
    ctx: &Program<'a, S>,
    gens: &mut Generators<'a, '_, S>,
    ret_info: Option<&ReturnInfo>,
    node_inputs: &[ValueOrigin],
    target: &BreakTarget,
    ctrl_stack: &mut VecDeque<CtrlStackEntry>,
) -> Result<Vec<Tree<S::Directive>>, NotAllocatedError> {
    // There are 5 different kinds of jumps, depending on the target:
    //
    // 1. Jump to a label in the current frame. We need to check if the break arguments have
    //    already been filled with the expected values (from the optimistic allocation). If
    //    not, we need to copy from the break inputs.
    //
    // 2. Jump to a label in a previous frame of the same function. I.e. a jump out of a loop.
    //    In this case, we need to copy all the break inputs into the target frame, then
    //    make a frame-switching jump to the label.
    //
    // 3. Jump into a loop iteration.
    //
    // 4. Function return from a loop. We copy the return values to the function output
    //    registers, which are in the toplevel frame, and perform a frame-switching jump. The
    //    jump is to a dynamic label, stored in the return PC register.
    //
    // 5. Function return from the toplevel frame. The difference is that the output registers
    //    we need to fill are in the active frame, so the copy is local, not across frames.
    //
    // We need to identify the case and emit the correct directives.

    // This is a function return.
    let curr_entry = ctrl_stack.front().unwrap();
    match target {
        BreakTarget {
            depth: 0,
            kind: TargetType::Label(label),
        } => local_jump(ctx, gens, *label, &curr_entry.allocation, node_inputs),
        BreakTarget {
            depth,
            kind: TargetType::Label(label),
        } => {
            // This is a jump out of loop, into a previous frame of the same function.
            jump_out_of_loop(ctx, gens, *depth, *label, ctrl_stack, node_inputs)
        }
        BreakTarget {
            depth,
            kind: TargetType::FunctionOrLoop,
        } => {
            let target_stack_entry = &ctrl_stack[*depth as usize];
            match &target_stack_entry.entry_type {
                CtrlStackType::TopLevelFunction { output_regs } => {
                    // This is a function return.
                    match &curr_entry.entry_type {
                        CtrlStackType::TopLevelFunction { output_regs } => {
                            // This is a return from the toplevel frame.
                            top_level_return::<S>(
                                ctx,
                                gens,
                                ret_info.as_ref().unwrap(),
                                &curr_entry.allocation,
                                node_inputs,
                                output_regs,
                            )
                        }
                        CtrlStackType::Loop(loop_entry) => {
                            // This is a return from a loop.
                            assert_eq!(loop_entry.layout.ret_info.as_ref(), ret_info);
                            return_from_loop::<S>(
                                ctx,
                                gens,
                                ctrl_stack.len(),
                                output_regs,
                                node_inputs,
                                &curr_entry.allocation,
                                loop_entry,
                            )
                        }
                    }
                }
                CtrlStackType::Loop(loop_entry) => {
                    // This is a loop iteration.
                    jump_into_loop(
                        ctx,
                        gens,
                        loop_entry,
                        *depth as i64,
                        ret_info,
                        curr_entry,
                        node_inputs,
                    )
                }
            }
        }
    }
}

fn copy_local_jump_args<'a, S: Settings<'a>>(
    ctx: &Program<'a, S>,
    gens: &mut Generators<'a, '_, S>,
    allocation: &Allocation,
    node_inputs: &[ValueOrigin],
    output_regs: &[Range<u32>],
) -> Result<Vec<Tree<S::Directive>>, NotAllocatedError> {
    // Copy the node inputs into the output registers, if they are not already assigned.
    let mut directives = Vec::new();
    for (origin, dest_reg) in node_inputs.iter().zip_eq(output_regs.iter()) {
        let src_reg = &allocation.get(origin)?;
        if src_reg != dest_reg {
            // Explicit rebind to avoid lifetime issues when moving `gens` into the closure.
            let gens = &mut *gens;
            directives.extend(src_reg.clone().zip_eq(dest_reg.clone()).map(
                move |(src_word, dest_word)| {
                    ctx.s
                        .emit_copy(gens, src_word..src_word + 1, dest_word..dest_word + 1)
                        .into()
                },
            ));
        }
    }
    Ok(directives)
}

fn local_jump<'a, S: Settings<'a>>(
    ctx: &Program<'a, S>,
    gens: &mut Generators<'a, '_, S>,
    label_id: u32,
    allocation: &Allocation,
    node_inputs: &[ValueOrigin],
) -> Result<Vec<Tree<S::Directive>>, NotAllocatedError> {
    // Copy the node inputs into the output registers, if they are not already assigned.
    let output_regs = &allocation.labels[&label_id];
    let mut directives = copy_local_jump_args(ctx, gens, allocation, node_inputs, output_regs)?;

    // Emit the jump directive.
    directives.push(
        ctx.s
            .emit_jump(format_label(label_id, LabelType::Local))
            .into(),
    );

    Ok(directives)
}

fn top_level_return<'a, S: Settings<'a>>(
    ctx: &Program<'a, S>,
    gens: &mut Generators<'a, '_, S>,
    ret_info: &ReturnInfo,
    allocation: &Allocation,
    node_inputs: &[ValueOrigin],
    output_regs: &[Range<u32>],
) -> Result<Vec<Tree<S::Directive>>, NotAllocatedError> {
    // Copy the node inputs into the output registers, if they are not already assigned.
    let mut directives = copy_local_jump_args(ctx, gens, allocation, node_inputs, output_regs)?;

    // Emit the return directive.
    assert_ptr_size::<S>(&ret_info.ret_pc);
    assert_ptr_size::<S>(&ret_info.ret_fp);
    directives.push(
        ctx.s
            .emit_return(gens, ret_info.ret_pc.clone(), ret_info.ret_fp.clone())
            .into(),
    );

    Ok(directives)
}

fn return_from_loop<'a, S: Settings<'a>>(
    ctx: &Program<'a, S>,
    gens: &mut Generators<'a, '_, S>,
    ctrl_stack_len: usize,
    output_regs: &[Range<u32>],
    node_inputs: &[ValueOrigin],
    allocation: &Allocation,
    curr_entry: &LoopStackEntry,
) -> Result<Vec<Tree<S::Directive>>, NotAllocatedError> {
    let mut directives = Vec::new();

    if !output_regs.is_empty() {
        let outer_fps = &curr_entry.layout.saved_fps;
        let toplevel_fp = &outer_fps[&((ctrl_stack_len - 1) as u32)];

        // Issue the copy directives.
        for (origin, dest_reg) in node_inputs.iter().zip_eq(output_regs.iter()) {
            let src_reg = allocation.get(origin)?;
            directives.extend(copy_into_frame(
                ctx,
                gens,
                src_reg,
                toplevel_fp.clone(),
                dest_reg.clone(),
            ));
        }
    }

    // Issue the return directive.
    let ret_info = curr_entry.layout.ret_info.as_ref().unwrap();
    assert_ptr_size::<S>(&ret_info.ret_pc);
    assert_ptr_size::<S>(&ret_info.ret_fp);

    directives.push(
        ctx.s
            .emit_return(gens, ret_info.ret_pc.clone(), ret_info.ret_fp.clone())
            .into(),
    );

    Ok(directives)
}

fn jump_out_of_loop<'a, S: Settings<'a>>(
    ctx: &Program<'a, S>,
    gens: &mut Generators<'a, '_, S>,
    depth: u32,
    label_id: u32,
    ctrl_stack: &VecDeque<CtrlStackEntry>,
    node_inputs: &[ValueOrigin],
) -> Result<Vec<Tree<S::Directive>>, NotAllocatedError> {
    let caller_entry = ctrl_stack.front().unwrap();
    let outer_fps = if let CtrlStackType::Loop(curr_entry) = &caller_entry.entry_type {
        &curr_entry.layout.saved_fps
    } else {
        // You can not jump out of a loop from the toplevel frame.
        panic!()
    };
    let dest_fp = outer_fps[&depth].clone();

    let target_entry = &ctrl_stack[depth as usize];
    let target_inputs = &target_entry.allocation.labels[&label_id];

    let mut directives = Vec::new();
    for (origin, dest_reg) in node_inputs.iter().zip_eq(target_inputs.iter()) {
        let src_reg = caller_entry.allocation.get(origin)?;
        directives
            .push(copy_into_frame(ctx, gens, src_reg, dest_fp.clone(), dest_reg.clone()).into());
    }

    directives.push(
        ctx.s
            .emit_jump_out_of_loop(gens, format_label(label_id, LabelType::Local), dest_fp)
            .into(),
    );

    Ok(directives)
}

/// This function is used to generate the directives for frame creation, copy of
/// the loop inputs, and the jump into the loop. Both when iterating the loop
/// and when jumping into the loop for the first time.
///
/// depth_offset is the difference between the caller frame depth and the loop frame depth.
fn jump_into_loop<'a, S: Settings<'a>>(
    ctx: &Program<'a, S>,
    gens: &mut Generators<'a, '_, S>,
    loop_entry: &LoopStackEntry,
    depth_offset: i64,
    ret_info: Option<&ReturnInfo>,
    caller_stack_entry: &CtrlStackEntry,
    node_inputs: &[ValueOrigin],
) -> Result<Vec<Tree<S::Directive>>, NotAllocatedError> {
    let mut directives: Vec<Tree<S::Directive>> = Vec::new();

    // We start by allocating the frame.
    let loop_fp = gens.r.allocate_words(S::words_per_ptr());
    directives.push(
        ctx.s
            .emit_allocate_label_frame(gens, loop_entry.label.clone(), loop_fp.clone())
            .into(),
    );

    // Copy the outer frame pointers.
    // outer_fps must be a superset of loop_entry.saved_fps, except for
    // outer_fps[0], which means the caller's own frame pointer, which might
    // be required if we are entering the loop for the first time.
    let mut depth_adjusted_loop_fps = loop_entry
        .layout
        .saved_fps
        .iter()
        .map(|(depth, fp)| {
            // Adjust the depth to the caller's frame depth.
            ((*depth as i64 + depth_offset) as u32, fp.clone())
        })
        .peekable();

    // Handle the special case where outer_fps[0] is required.
    let saved_caller_fp = if let Some((0, _)) = depth_adjusted_loop_fps.peek() {
        let fp = depth_adjusted_loop_fps.next().unwrap().1;
        assert_ptr_size::<S>(&fp);
        Some(fp)
    } else {
        None
    };

    let outer_fps = if let (CtrlStackType::Loop(curr_entry), Some((first_needed, _))) = (
        &caller_stack_entry.entry_type,
        depth_adjusted_loop_fps.peek(),
    ) {
        curr_entry.layout.saved_fps.range(*first_needed..)
    } else {
        // There are no outer frames to be copied.
        Default::default()
    };

    for outer_fp in depth_adjusted_loop_fps
        .merge_join_by(outer_fps, |(required_depth, _), (available_depth, _)| {
            required_depth.cmp(available_depth)
        })
    {
        use itertools::EitherOrBoth::{Both, Left, Right};
        match outer_fp {
            Both((_, dest_fp), (_, src_fp)) => {
                directives.extend(copy_into_frame(
                    ctx,
                    gens,
                    src_fp.clone(),
                    loop_fp.clone(),
                    dest_fp,
                ));
            }
            Right(_) => {
                // An outer frame pointer is available, but not required. This is fine.
            }
            Left(_) => {
                // An outer frame pointer is required, but not available. Should not be possible.
                panic!();
            }
        }
    }

    // Copy the loop inputs into the loop frame.
    for (origin, input_reg) in node_inputs.iter().zip_eq(loop_entry.input_regs.iter()) {
        let src_reg = caller_stack_entry.allocation.get(origin)?;
        directives.extend(copy_into_frame(
            ctx,
            gens,
            src_reg,
            loop_fp.clone(),
            input_reg.clone(),
        ));
    }

    // Set the return info to be copied, if needed.
    let ret_info_copy = loop_entry.layout.ret_info.as_ref().map(|dest| {
        let src = ret_info.unwrap();
        ReturnInfosToCopy { src, dest }
    });

    // Then we activate the frame.
    //
    // Jumping doesn't really do anything here, because the loop directives are
    // right ahead, but it is not worth to create a new instruction just for that.
    directives.push(
        ctx.s
            .emit_jump_into_loop(
                gens,
                loop_entry.label.clone(),
                loop_fp,
                ret_info_copy,
                saved_caller_fp,
            )
            .into(),
    );

    Ok(directives)
}

pub enum LabelType {
    Function,
    Local,
    Loop,
}

fn format_label(label_id: u32, label_type: LabelType) -> String {
    match label_type {
        LabelType::Function => format!("__func_{label_id}"),
        LabelType::Local => format!("__local_{label_id}"),
        LabelType::Loop => format!("__loop_{label_id}"),
    }
}

pub fn func_idx_to_label(func_idx: u32) -> String {
    format_label(func_idx, LabelType::Function)
}

fn byte_size<'a, S: Settings<'a>>(ty: ValType) -> u32 {
    match ty {
        ValType::I32 | ValType::F32 => 4,
        ValType::I64 | ValType::F64 => 8,
        ValType::V128 => 16,
        ValType::Ref(..) => FunctionRef::<S>::total_byte_size(),
    }
}

fn split_func_ref_regs<'a, S: Settings<'a>>(func_ref_reg: Range<u32>) -> [Range<u32>; 3] {
    let i32_word_count = word_count_type::<S>(ValType::I32);

    let type_index = func_ref_reg.start..func_ref_reg.start + i32_word_count;
    let func_addr = type_index.end..type_index.end + i32_word_count;
    let func_frame_size = func_addr.end..func_addr.end + i32_word_count;

    assert_eq!(func_frame_size.end, func_ref_reg.end);

    [type_index, func_addr, func_frame_size]
}

fn word_count<'a, S: Settings<'a>>(byte_size: u32) -> u32 {
    byte_size.div_ceil(S::bytes_per_word())
}

fn assert_ptr_size<'a, S: Settings<'a>>(ptr: &Range<u32>) {
    assert_eq!(ptr.len(), S::words_per_ptr() as usize);
}

pub fn word_count_type<'a, S: Settings<'a>>(ty: ValType) -> u32 {
    word_count::<S>(byte_size::<S>(ty))
}
