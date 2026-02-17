//! This pass takes a DAG and removes unnecessary inputs and outputs from
//! blocks. These spurious inputs and outputs may come from the original Wasm
//! code, but they can also be introduced by the `locals_data_flow` pass, which is
//! conservative in its analysis of local usage.
//!
//! As part of the algorithm, loop inputs that are carried through the loop iterations
//! without modification are detected, so we save this information for later passes,
//! which can use it to optimize register allocation and code generation.

use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet, VecDeque},
};

use wasmparser::Operator as Op;

use crate::loader::{
    BlockKind,
    passes::dag::{BrTableTarget, Dag, Node, NodeInput, Operation, ValueOrigin},
};

/// The set of outputs indexed from the Input node that are redirected
/// as-is to the next iteration of the loop.
///
/// The vector is sorted, and contains no duplicates.
///
/// This is useful to detect outer values that are read by the loop, but
/// not written, so they can be preserved across the entire loop execution,
/// eliding unnecessary copies.
///
/// On the toplevel block (which is not a loop), this is always empty.
struct InputRedirection(Vec<u32>);

pub fn prune_block_io(dag: &mut Dag<'_>) {
    process_block(&mut dag.nodes, &mut VecDeque::new())
}

// Things that need to be computed for each input of a block:
// 1. Is the input used at all? If not, it can be removed from the input list.
// 2. Is an input marked as "redirected" used in anything besides outputs for
//    the same loop, directly or indirectly? If not, it can be removed from the input list.
//
// Things that need to be computed for each target output of a loop block:
// 1. Is a slot of an output target only written with a single input value?
//    If so, then:
//    a. If the target is a plain label, that output slot can be removed from the output list,
//       and the users of that output can be pointed directly to the original value origin.
//    b. If the target is the same loop, and the slot is the same as the input, that input
//       can be marked as "redirected".

#[derive(Debug, Clone)]
enum InputUsage {
    /// This is the most useless input, always safe to remove.
    Unused,
    /// Can be removed if it is not used in any other way.
    /// Used to detect useless circular redirections in loop.
    RedirectedTo {
        /// The maximum depth this input is redirected to.
        max_depth: u32,
        /// The set of output slots this input is redirected to.
        slots: HashSet<u32>,
    },
    /// This input is useful, and cannot be removed.
    Used,
}

impl InputUsage {
    fn depth_down(self) -> Self {
        match self {
            InputUsage::Used | InputUsage::RedirectedTo { max_depth: 0, .. } => InputUsage::Used,
            InputUsage::RedirectedTo { max_depth, slots } => InputUsage::RedirectedTo {
                max_depth: max_depth - 1,
                slots,
            },
            InputUsage::Unused => InputUsage::Unused,
        }
    }

    fn combine(&mut self, other: InputUsage) {
        match (&mut *self, &other) {
            (InputUsage::Used, _) | (_, InputUsage::Used) => {
                *self = InputUsage::Used;
            }
            (
                InputUsage::RedirectedTo {
                    max_depth: d_self,
                    slots: s_self,
                },
                InputUsage::RedirectedTo {
                    max_depth: d_other,
                    slots: s_other,
                },
            ) => match (*d_self).cmp(d_other) {
                Ordering::Less => {
                    *self = other;
                }
                Ordering::Equal => {
                    s_self.extend(s_other);
                }
                Ordering::Greater => (),
            },
            (InputUsage::Unused, InputUsage::Unused)
            | (InputUsage::RedirectedTo { .. }, InputUsage::Unused) => (),
            (InputUsage::Unused, InputUsage::RedirectedTo { .. }) => {
                *self = other;
            }
        }
    }

    fn combine_with_redirection(&mut self, depth: u32, slot: u32) {
        if let InputUsage::Used = self {
            return;
        }

        if let InputUsage::RedirectedTo { max_depth, slots } = self {
            if *max_depth > depth {
                return;
            } else if *max_depth == depth {
                slots.insert(slot);
                return;
            }
        }

        *self = InputUsage::RedirectedTo {
            max_depth: depth,
            slots: HashSet::from([slot]),
        };
    }
}

/// Tells if an output slot of a block is only written with a single input value, and if so, what is that input.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Redirection {
    /// This is a transient state used during the algorithm, which
    /// means we have not yet determined if this output has an input
    /// redirection or not.
    Unknown,
    /// The index of the input that is redirected to this output.
    FromInput(u32),
    /// Marks this output as not being redirected to by any input.
    NotRedirected,
}

struct ControlStackEntry {
    outputs_redirections: Vec<Redirection>,
    /// Input map to previous block
    input_map: HashMap<u32, u32>,
    input_usage: Vec<InputUsage>,
    was_ever_broken_to: bool,
}

fn process_block<'a>(dag: &mut Vec<Node<'a>>, cs: &mut VecDeque<ControlStackEntry>) {
    // Some output slots might be removed from the block outputs in case they are redundant.
    // We track such cases in this map, and also where the users of those outputs should point
    // to instead.
    let mut input_substitutions: HashMap<ValueOrigin, ValueOrigin> = HashMap::new();
    for node_idx in 0..dag.len() {
        let node = &mut dag[node_idx];

        // Apply the input substitutions
        for input in &mut node.inputs {
            if let NodeInput::Reference(origin) = input
                && let Some(subst) = input_substitutions.get(origin)
            {
                *origin = *subst;
            }
        }

        match &mut node.operation {
            Operation::Inputs => {
                // This is the first node of a block, which lists the block inputs.
                // We use its information to initialize the input usage information for this block.
                cs[0]
                    .input_usage
                    .resize(node.output_types.len(), InputUsage::Unused);
            }
            Operation::WASMOp(Op::Br { relative_depth }) => {
                handle_break_target(cs, &node.inputs, *relative_depth);
            }
            Operation::BrIfZero { relative_depth }
            | Operation::WASMOp(Op::BrIf { relative_depth }) => {
                let (condition, break_inputs) = node.inputs.split_last().unwrap();
                // Handle the condition as a normal node input:
                for (_, input_idx) in block_inputs([condition]) {
                    cs[0].input_usage[input_idx as usize] = InputUsage::Used;
                }

                handle_break_target(cs, break_inputs, *relative_depth);
            }
            Operation::BrTable { targets } => {
                let (condition, break_inputs) = node.inputs.split_last().unwrap();
                // Handle the condition as a normal node input:
                for (_, input_idx) in block_inputs([condition]) {
                    cs[0].input_usage[input_idx as usize] = InputUsage::Used;
                }

                for BrTableTarget {
                    relative_depth,
                    input_permutation,
                } in targets
                {
                    let target_inputs = input_permutation
                        .iter()
                        .map(|perm| &break_inputs[*perm as usize]);
                    handle_break_target(cs, target_inputs, *relative_depth);
                }
            }
            Operation::Block { kind, sub_dag } => {
                let num_outputs = if let BlockKind::Loop = kind {
                    // The outputs of a loop block are its own inputs
                    node.inputs.len()
                } else {
                    node.output_types.len()
                };
                let outputs_redirections = vec![Redirection::Unknown; num_outputs];

                // Map from the input inside of the sub-block to the input of the current block.
                let input_map = block_inputs(&node.inputs)
                    .map(|(node_input_idx, block_input_idx)| {
                        (node_input_idx as u32, block_input_idx)
                    })
                    .collect();

                // Call the processing recursively
                cs.push_front(ControlStackEntry {
                    outputs_redirections,
                    input_map,
                    // Let the block initialize the input usage for its inputs...
                    input_usage: Vec::new(),
                    was_ever_broken_to: false,
                });
                process_block(&mut sub_dag.nodes, cs);
                let mut sub_entry = cs.pop_front().unwrap();
                assert_eq!(sub_entry.input_usage.len(), node.inputs.len());

                // Calculate what outputs can be removed
                let mut sub_block_doesnt_return = false;
                let mut outputs_to_remove = Vec::new();
                if !sub_entry.was_ever_broken_to {
                    // Invariant check: there can only be an unknown redirection if the block is
                    // never broken to, in which case, all must be unknown.
                    assert!(
                        sub_entry
                            .outputs_redirections
                            .iter()
                            .all(|redir| *redir == Redirection::Unknown)
                    );

                    // Sub-block is never broken to, so we can do the following transformations:
                    match kind {
                        BlockKind::Block => {
                            // If the sub-block is a plain block, all outputs can be removed,
                            // and the rest of this block is unreachable, and we can stop processing it.
                            outputs_to_remove.extend(0..node.output_types.len() as u32);
                            sub_block_doesnt_return = true;
                        }
                        BlockKind::Loop => {
                            // If the sub-block is a loop, it can be turned into a plain block with no outputs,
                            // because it never iterates.
                            *kind = BlockKind::Block;
                            assert!(node.output_types.is_empty());
                        }
                    }
                } else if let BlockKind::Block = kind {
                    // If sub-block is a plain block, we can remove its output slots that were redirected as-is from its inputs.
                    for (output_idx, redir) in sub_entry.outputs_redirections.iter().enumerate() {
                        assert!(*redir != Redirection::Unknown);
                        if let Redirection::FromInput(input_idx) = redir {
                            // This output is always a redirection of the same input.
                            outputs_to_remove.push(output_idx as u32);
                            let NodeInput::Reference(original_input) =
                                node.inputs[*input_idx as usize]
                            else {
                                unreachable!()
                            };
                            input_substitutions.insert(
                                ValueOrigin {
                                    node: node_idx,
                                    output_idx: output_idx as u32,
                                },
                                original_input,
                            );
                        }
                    }
                }

                // Complete the input_usage: to be redirected, it is not enough that an input is
                // only used in outputs: it also requires that those outputs are only written with that
                // input.
                for (input_idx, usage) in sub_entry.input_usage.iter_mut().enumerate() {
                    if let InputUsage::RedirectedTo {
                        max_depth: 0,
                        slots,
                    } = usage
                        && !slots.iter().all(|slot| {
                            sub_entry.outputs_redirections[*slot as usize]
                                == Redirection::FromInput(input_idx as u32)
                        })
                    {
                        *usage = InputUsage::Used;
                    }
                }

                // Calculate what inputs can be removed.
                #[derive(Debug, Clone, Copy, PartialEq, Eq)]
                enum CanRemoveInput {
                    Unknown,
                    Yes,
                    No,
                }
                let mut can_remove_input = vec![CanRemoveInput::Unknown; node.inputs.len()];
                for (input_idx, usage) in sub_entry.input_usage.iter().enumerate() {
                    let input_idx = input_idx as u32;
                    let removal_status = match usage {
                        // This input is not used at all in the sub-block, so it can be removed from the block inputs.
                        InputUsage::Unused => CanRemoveInput::Yes,
                        InputUsage::RedirectedTo { max_depth: 0, .. } => {
                            match kind {
                                // The input is redirected as-is to some output that we already marked for removal,
                                // so we can remove this input as well.
                                BlockKind::Block => CanRemoveInput::Yes,
                                // The loop case is handled below, because it is more complex.
                                BlockKind::Loop => CanRemoveInput::Unknown,
                            }
                        }
                        // This input is used in some way, or redirected to some outer block, so it cannot be removed.
                        _ => CanRemoveInput::No,
                    };
                    can_remove_input[input_idx as usize] = removal_status;
                }

                if let BlockKind::Loop = kind {
                    // Resolve Unknown inputs in a loop by propagating No backwards.
                    //
                    // Each Unknown input is only used as a redirection to other loop
                    // inputs (its slots). If any of those targets is No, then this
                    // input is also No. We propagate by building reverse edges
                    // (target → source) and BFS-ing from all No inputs.
                    // Whatever remains Unknown afterwards is safely removable (Yes).

                    // Build reverse edges: for each Unknown input, its redirection
                    // slots point forward; we record the reverse (slot → input).
                    let mut reverse_edges: Vec<Vec<u32>> = vec![vec![]; can_remove_input.len()];
                    for (idx, status) in can_remove_input.iter().enumerate() {
                        if *status == CanRemoveInput::Unknown {
                            let InputUsage::RedirectedTo {
                                max_depth: 0,
                                slots,
                            } = &sub_entry.input_usage[idx]
                            else {
                                unreachable!()
                            };
                            for &slot in slots {
                                reverse_edges[slot as usize].push(idx as u32);
                            }
                        }
                    }

                    // Seed the worklist with all No inputs.
                    let mut worklist: VecDeque<u32> = can_remove_input
                        .iter()
                        .enumerate()
                        .filter(|(_, s)| **s == CanRemoveInput::No)
                        .map(|(i, _)| i as u32)
                        .collect();

                    // Propagate No backwards through the reverse edges.
                    while let Some(idx) = worklist.pop_front() {
                        for &source in &reverse_edges[idx as usize] {
                            match can_remove_input[source as usize] {
                                CanRemoveInput::Unknown => {
                                    can_remove_input[source as usize] = CanRemoveInput::No;
                                    worklist.push_back(source);
                                }
                                CanRemoveInput::Yes => {
                                    // This should not happen: a Yes input cannot point to a No input.
                                    unreachable!()
                                }
                                _ => {}
                            }
                        }
                    }

                    // Everything still Unknown is part of a cycle that never
                    // reaches a useful input, so it can be removed.
                    for status in &mut can_remove_input {
                        if *status == CanRemoveInput::Unknown {
                            *status = CanRemoveInput::Yes;
                        }
                    }
                }

                // TODO: actually apply the input and output removals on the sub-block.
                // or maybe leave it for a pass at the end of this function, where further
                // outputs could be removed (in case they are never used).
                todo!();

                // Update this node outputs.
                let mut outputs_to_remove = outputs_to_remove.into_iter().peekable();
                let mut old_idx = 0..;
                let mut new_idx = 0..;
                node.output_types.retain(|_| {
                    let old_idx = old_idx.next().unwrap();
                    if old_idx != *outputs_to_remove.peek().unwrap() {
                        let new_idx = new_idx.next().unwrap();
                        if old_idx != new_idx {
                            input_substitutions.insert(
                                ValueOrigin {
                                    node: node_idx,
                                    output_idx: old_idx,
                                },
                                ValueOrigin {
                                    node: node_idx,
                                    output_idx: new_idx,
                                },
                            );
                        }
                        true
                    } else {
                        outputs_to_remove.next();
                        false
                    }
                });

                // Update this node inputs.
                let mut idx = 0..;
                node.inputs.retain(|_| {
                    let remove = can_remove_input[idx.next().unwrap() as usize];
                    assert_ne!(remove, CanRemoveInput::Unknown);
                    remove == CanRemoveInput::No
                });

                // Update this block input usage based on the sub-block input usage and the removals we have done.
                for (sub_input_idx, usage) in sub_entry.input_usage.iter().enumerate() {
                    if can_remove_input[sub_input_idx] == CanRemoveInput::No
                        && let Some(input_idx) = sub_entry.input_map.get(&(sub_input_idx as u32))
                    {
                        cs[0].input_usage[*input_idx as usize].combine(usage.depth_down());
                    }
                }

                if sub_block_doesnt_return {
                    // The rest of this block is unreachable, so we can stop processing it.
                    dag.truncate(node_idx + 1);
                    break;
                }
            }
            _ => {
                // This is a normal node that might use some block inputs
                for (_, input_idx) in block_inputs(&node.inputs) {
                    // This block input is being used in some way...
                    cs[0].input_usage[input_idx as usize] = InputUsage::Used;
                }
            }
        }
    }

    // TODO: remove unused outputs sub-blocks of this block...
    todo!()
}

fn handle_break_target<'a>(
    cs: &mut VecDeque<ControlStackEntry>,
    node_inputs: impl IntoIterator<Item = &'a NodeInput>,
    relative_depth: u32,
) {
    for (slot_idx, input) in node_inputs.into_iter().enumerate() {
        // Determine if this input is a block input.
        let block_input_idx = if let NodeInput::Reference(ValueOrigin {
            node: 0,
            output_idx: input_idx,
        }) = *input
        {
            // This is a block input. Mark the most restrictive usage given for it inside this block.
            let usage = &mut cs[0].input_usage[input_idx as usize];
            usage.combine_with_redirection(relative_depth, slot_idx as u32);

            Some(input_idx)
        } else {
            None
        };

        // For each block down in the control stack up to the break target
        // we try to find if the inputs are still block inputs.
        let block_input_idx = block_input_idx.and_then(|mut input_idx| {
            for entry in cs.iter().take(relative_depth as usize) {
                if let Some(mapped_input) = entry.input_map.get(&input_idx) {
                    input_idx = *mapped_input;
                } else {
                    // This input is not a block input in this block,
                    return None;
                }
            }

            Some(input_idx)
        });

        let target_entry = &mut cs[relative_depth as usize];
        target_entry.was_ever_broken_to = true;

        // If we have found a block input in the break target block,
        // we must decide if it is a redirection or not.
        let redirection = &mut target_entry.outputs_redirections[slot_idx];
        if let Some(input_idx) = block_input_idx {
            if let Redirection::Unknown = redirection {
                // So far, this could be a redirection.
                *redirection = Redirection::FromInput(input_idx);
            } else if let Redirection::FromInput(existing_input) = redirection
                && *existing_input != input_idx
            {
                // Different inputs are being passed to the same output, so it cannot be a redirection.
                *redirection = Redirection::NotRedirected;
            }
        } else {
            // The value does not come from a block input, so it is certainly not a redirection.
            *redirection = Redirection::NotRedirected;
        }
    }
}

/// Filters inputs that are block inputs, and returns their indices.
fn block_inputs<'a>(
    inputs: impl IntoIterator<Item = &'a NodeInput>,
) -> impl Iterator<Item = (usize, u32)> {
    inputs.into_iter().enumerate().filter_map(|(idx, input)| {
        if let NodeInput::Reference(ValueOrigin {
            node: 0,
            output_idx,
        }) = input
        {
            Some((idx, *output_idx))
        } else {
            None
        }
    })
}
