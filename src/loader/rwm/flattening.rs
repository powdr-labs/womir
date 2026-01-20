//! This module flattens the DAG structure, generating an assembly-like representation.
//!
//! The algorithm is straightforward and linear, as most of the complexity was handled
//! in earlier passes (notably register allocation).

use crate::{
    loader::{
        LabelGenerator, Module,
        passes::{
            blockless_dag::{BreakTarget, Operation, TargetType},
            dag::NodeInput,
        },
        rwm::{
            register_allocation::{self, AllocatedDag, Allocation},
            settings::Settings,
        },
        settings::{LabelType, format_label},
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
    todo!()
}

struct StackEntry {
    loop_label: Option<String>,
    allocation: Allocation,
}

fn process_dag<'a, S: Settings<'a>>(
    s: &S,
    ctx: &mut Context<'a, '_>,
    ctrl_stack: &mut VecDeque<StackEntry>,
    nodes: Vec<register_allocation::Node>,
    func_idx: u32,
) -> Tree<S::Directive> {
    for node in nodes {
        let tree = match node.operation {
            Operation::Inputs => {
                // Inputs does not translate to any assembly directive.
                Tree::Empty
            }
            Operation::Label { id } => s.emit_label(ctx, format_label(id, LabelType::Local)).into(),
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
                    ctx,
                    &ctrl_stack[0].allocation,
                    &node.inputs,
                    input_ranges,
                );

                // Emit loop label.
                let loop_label = ctx.new_label(LabelType::Loop);
                loop_directives.push(s.emit_label(ctx, loop_label.clone()).into());

                // Process the loop body.
                ctrl_stack.push_front(StackEntry {
                    loop_label: Some(loop_label),
                    allocation: loop_allocation,
                });
                let loop_tree = process_dag(s, ctx, ctrl_stack, loop_nodes, func_idx);
                ctrl_stack.pop_front();

                loop_directives.push(loop_tree);
                loop_directives.into()
            }
            Operation::Br(break_target) => {
                emit_jump(s, ctx, ctrl_stack, break_target, &node.inputs, func_idx).into()
            }
            Operation::BrIf(break_target) => todo!(),
            Operation::BrIfZero(break_target) => todo!(),
            Operation::BrTable { targets } => todo!(),
            Operation::WASMOp(operator) => todo!(),
        };
    }

    todo!()
}

fn emit_jump<'a, S: Settings<'a>>(
    s: &S,
    ctx: &mut Context,
    ctrl_stack: &VecDeque<StackEntry>,
    target: BreakTarget,
    node_inputs: &[NodeInput],
    func_idx: u32,
) -> Vec<Tree<S::Directive>> {
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
                    (0, loop_label)
                }
                None => {
                    // This is a return from the function.
                    // Calculate the outputs registers from the function type.
                    let func_type = &ctx.prog.get_func_type(func_idx).ty;
                    let ret_types = func_type.results();
                    // They are tightly packed at the top of the stack frame.
                    let mut fn_output_size = 0;
                    let input_ranges = ret_types.iter().scan(&mut fn_output_size, |offset, ty| {
                        let size = word_count_type::<S>(*ty);
                        let start = **offset;
                        **offset += size;
                        Some(start..**offset)
                    });

                    let mut directives =
                        copy_inputs_if_needed(s, ctx, &entry.allocation, node_inputs, input_ranges);

                    // Also calculate the space needed by the function inputs, to calculate where
                    // the return address and caller frame pointer are stored.
                    let fn_input_size = word_count_types::<S>(func_type.params());
                    let ra_ptr = fn_input_size.max(fn_output_size);
                    let caller_fp_ptr = ra_ptr + S::words_per_ptr();

                    let ra = ra_ptr..caller_fp_ptr;
                    let caller_fp = caller_fp_ptr..(caller_fp_ptr + S::words_per_ptr());
                    directives.push(s.emit_return(ctx, ra, caller_fp).into());

                    return directives;
                }
            }
        }
        TargetType::Label(id) => {
            // This is a jump to a label in the current function.
            // The node we want is the target label's node.
            (
                entry.allocation.labels[&id],
                // Appreciate this Rust magic trick: I am returning a reference to
                // a temporary String, and this still compiles...
                &format_label(id, LabelType::Local),
            )
        }
    };

    let input_ranges = entry.allocation.get_for_node(output_node_idx);
    let mut directives =
        copy_inputs_if_needed(s, ctx, &entry.allocation, node_inputs, input_ranges);
    directives.push(s.emit_jump(ctx, target).into());

    directives
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

pub struct Context<'a, 'b> {
    prog: &'b Module<'a>,
    label_gen: &'b AtomicU32,
}

impl<'a, 'b> Context<'a, 'b> {
    pub fn generate_tmp_var(&mut self, size: u32) -> Range<u32> {
        todo!()
    }

    pub fn new_label(&mut self, label_type: LabelType) -> String {
        format_label(self.label_gen.next(), label_type)
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
