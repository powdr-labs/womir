//! This module makes explicit the locals usage inside the blocks.
//!
//! Blocks have explicitly defined inputs and outputs, but since locals
//! can be used inside blocks, they act as alternative ways to pass
//! values into and out of blocks.
//!
//! This module makes explicit what locals are used either as inputs
//! or outputs to blocks.
//!
//! TODO (OPTIMIZATION): track locals permutation. Yf some locals are
//! read into a block, but in the end they are just output unmodified
//! (either on stack or on some local), this can be resolved statically
//! when building the DAG, eliding copies.
//!
//! TODO (OPTIMIZATION): sometimes a loop needs to take locals as inputs
//! just to output them in certain breaks, unmodified. Such locals would
//! have to be copied over through all the iterations, but never actually
//! used inside the loop. In such cases, it is worth to make these breaks
//! indirect, by creating blocks surrounding the loop just to forward the
//! breaks. The passthrough locals will be handled by the outside blocks
//! and breaks, avoiding them to be copied into the loop.

use std::collections::{BTreeSet, VecDeque};

use wasmparser::Operator;

use super::{Block, BlockKind, Element, Instruction as Ins, block_tree::BlockTree};

pub struct LiftedBlockTree<'a> {
    pub elements: Vec<Element<'a>>,
}

pub fn lift_data_flow<'a>(block_tree: BlockTree<'a>) -> wasmparser::Result<LiftedBlockTree<'a>> {
    let mut elements = Vec::new();

    // The top of the control stack is the function itself
    let mut control_stack = VecDeque::from([BlockStackEntry::new()]);

    for elem in block_tree.elements {
        let elem = match elem {
            Element::Block(mut block) =>
            // Iterate repeatedly, until all the inputs and outputs are exposed.
            {
                loop {
                    let (new_block, has_changed) = process_block(&mut control_stack, block);
                    if !has_changed {
                        break Element::Block(new_block);
                    }
                    block = new_block;
                }
            }
            e => e,
        };
        elements.push(elem);
    }

    drop(control_stack);

    Ok(LiftedBlockTree { elements })
}

fn process_block<'a>(
    control_stack: &mut VecDeque<BlockStackEntry>,
    block: Block<'a>,
) -> (Block<'a>, bool) {
    let Block {
        block_kind,
        interface_type,
        elements,
        input_locals: old_input_locals,
        output_locals: old_output_locals,
        carried_locals: old_carried_locals,
    } = block;

    let mut new_input_locals;
    let new_output_locals;
    let new_carried_locals;
    let new_elements;
    let has_changed;

    let (old_input_locals, old_output_locals) = match block_kind {
        BlockKind::Block => {
            // In a Block, breaks to it are outputs.
            control_stack.push_front(BlockStackEntry {
                old_break_locals: old_output_locals,
                new_break_locals: BTreeSet::new(),
            });

            (new_elements, new_input_locals, has_changed) =
                process_elems(control_stack, BTreeSet::new(), elements);

            let this_entry = control_stack.pop_front().unwrap();

            // Since the previous pass guarantees that no block falls through,
            // all the direct outputs are what we get through the breaks.
            new_output_locals = this_entry.new_break_locals;
            let old_output_locals = this_entry.old_break_locals;

            assert!(old_carried_locals.is_empty());
            new_carried_locals = BTreeSet::new();

            (old_input_locals, old_output_locals)
        }
        BlockKind::Loop => {
            // In a Loop, breaks to it are inputs.
            control_stack.push_front(BlockStackEntry {
                old_break_locals: old_input_locals,
                new_break_locals: BTreeSet::new(),
            });

            (new_elements, new_input_locals, has_changed) =
                process_elems(control_stack, old_carried_locals, elements);

            // Due to previous pass transformation, loops never fall through, thus
            // they never have direct outputs.
            new_output_locals = BTreeSet::new();

            let this_entry = control_stack.pop_front().unwrap();
            let old_input_locals = this_entry.old_break_locals;
            new_carried_locals = this_entry.new_break_locals;

            new_input_locals.extend(new_carried_locals.iter());

            (old_input_locals, old_output_locals)
        }
    };

    assert!(old_input_locals.is_subset(&new_input_locals));
    assert!(old_output_locals.is_subset(&new_output_locals));
    let has_changed = has_changed
        || old_input_locals.len() < new_input_locals.len()
        || old_output_locals.len() < new_output_locals.len();

    (
        Block {
            block_kind,
            interface_type,
            input_locals: new_input_locals,
            output_locals: new_output_locals,
            carried_locals: new_carried_locals,
            elements: new_elements,
        },
        has_changed,
    )
}

fn process_elems<'a>(
    control_stack: &mut VecDeque<BlockStackEntry>,
    mut local_outputs: BTreeSet<u32>,
    elements: Vec<Element<'a>>,
) -> (Vec<Element<'a>>, BTreeSet<u32>, bool) {
    let mut local_inputs = BTreeSet::new();

    let mut has_changed = false;

    let elements = elements
        .into_iter()
        .map(|elem| match elem {
            Element::Block(block) => {
                let (block, block_has_changed) = process_block(control_stack, block);

                has_changed = has_changed || block_has_changed;

                local_inputs.extend(block.input_locals.iter());
                local_outputs.extend(block.output_locals.iter());

                Element::Block(block)
            }
            Element::Ins(ins) => {
                match &ins {
                    // Local variables operations
                    Ins::WASMOp(Operator::LocalGet { local_index }) => {
                        local_inputs.insert(*local_index);
                    }
                    Ins::WASMOp(Operator::LocalSet { local_index })
                    | Ins::WASMOp(Operator::LocalTee { local_index }) => {
                        local_outputs.insert(*local_index);
                    }

                    // Break operations
                    Ins::BrTable { targets } => {
                        for relative_depth in targets {
                            process_break_target(
                                control_stack,
                                &mut local_inputs,
                                &local_outputs,
                                *relative_depth,
                            );
                        }
                    }
                    Ins::WASMOp(Operator::Br { relative_depth })
                    | Ins::WASMOp(Operator::BrIf { relative_depth })
                    | Ins::BrIfZero { relative_depth } => {
                        process_break_target(
                            control_stack,
                            &mut local_inputs,
                            &local_outputs,
                            *relative_depth,
                        );
                    }

                    // All other operations
                    Ins::WASMOp(_) => {}
                }

                Element::Ins(ins)
            }
        })
        .collect();

    (elements, local_inputs, has_changed)
}

fn process_break_target(
    control_stack: &mut VecDeque<BlockStackEntry>,
    local_inputs: &mut BTreeSet<u32>,
    local_outputs: &BTreeSet<u32>,
    relative_depth: u32,
) {
    let entry = &mut control_stack[relative_depth as usize];

    // Every local that have been marked as output must be given to this break.
    entry.new_break_locals.extend(local_outputs.iter());

    // Every local this break requires that we don't have marked as output, must
    // be taken as input, so it can be forwarded to the break.
    let diff = entry.old_break_locals.difference(local_outputs);
    local_inputs.extend(diff);
}

struct BlockStackEntry {
    old_break_locals: BTreeSet<u32>,
    new_break_locals: BTreeSet<u32>,
}

impl BlockStackEntry {
    fn new() -> Self {
        Self {
            old_break_locals: BTreeSet::new(),
            new_break_locals: BTreeSet::new(),
        }
    }
}
