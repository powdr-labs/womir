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
    vec,
};

use itertools::Itertools;
use wasmparser::Operator as Op;

use crate::{
    loader::{
        BlockKind,
        passes::dag::{BrTableTarget, Dag, Node, NodeInput, Operation, ValueOrigin},
    },
    utils::remove_indices,
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
    let mut input_substitutions: HashMap<ValueOrigin, Option<ValueOrigin>> = HashMap::new();
    for node_idx in 0..dag.len() {
        let node = &mut dag[node_idx];
        apply_substitutions(&mut node.inputs, &input_substitutions);
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
            Operation::Block { .. } => {
                let last_pass = loop {
                    let pass = block_processing_pass(node, node_idx, cs);
                    if !pass.changed {
                        break pass;
                    }
                };

                // Update this block input usage based on the sub-block input usage and the removals we have done.
                for (sub_input_idx, usage) in sub_entry.input_usage.into_iter().enumerate() {
                    if !to_remove_input[sub_input_idx]
                        && let Some(input_idx) = sub_entry.input_map.get(&(sub_input_idx as u32))
                    {
                        cs[0].input_usage[*input_idx as usize].combine(usage.depth_down());
                    }
                }

                if !last_pass.block_returns {
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

struct BlockPassResult {
    /// Did this pass make any changes to the structure of the block?
    changed: bool,

    /// Does this block ever return?
    block_returns: bool,

    /// Was any of the original inputs of this block removed?
    ///
    /// This vector has the same length as the original block
    /// inputs, and is indexed by the original input index.
    was_input_removed: Vec<bool>,

    /// The resulting entry after processing the block.
    entry: ControlStackEntry,
}

fn block_processing_pass(
    node: &mut Node,
    node_idx: usize,
    cs: &mut VecDeque<ControlStackEntry>,
) -> BlockPassResult {
    // TODO: figure the problem of input_substitutions in the context of this being called multiple times until a fixed point is reached.

    let (sub_dag, kind) = if let Operation::Block { sub_dag, kind } = &mut node.operation {
        (sub_dag, kind)
    } else {
        panic!()
    };

    let num_outputs = if let BlockKind::Loop = kind {
        // The outputs of a loop block are its own inputs
        node.inputs.len()
    } else {
        node.output_types.len()
    };
    let outputs_redirections = vec![Redirection::Unknown; num_outputs];

    // Map from the input inside of the sub-block to the input of the current block.
    let input_map = block_inputs(&node.inputs)
        .map(|(node_input_idx, block_input_idx)| (node_input_idx as u32, block_input_idx))
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
                let NodeInput::Reference(original_input) = node.inputs[*input_idx as usize] else {
                    unreachable!()
                };
                input_substitutions.insert(
                    ValueOrigin {
                        node: node_idx,
                        output_idx: output_idx as u32,
                    },
                    Some(original_input),
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

    /// Tells what inputs can be removed.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum CanRemoveInput {
        Yes,
        No,
        Unknown,
    }

    // Calculate what inputs can be removed.
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

    let to_remove_input = can_remove_input
        .into_iter()
        .map(|s| match s {
            CanRemoveInput::Yes => true,
            CanRemoveInput::No => false,
            CanRemoveInput::Unknown => panic!(),
        })
        .collect_vec();

    remove_block_node_io(
        node,
        node_idx,
        &to_remove_input,
        &outputs_to_remove,
        &mut VecDeque::new(),
        &mut input_substitutions,
    );
}

fn apply_substitutions(
    node_inputs: &mut Vec<NodeInput>,
    input_substitutions: &HashMap<ValueOrigin, Option<ValueOrigin>>,
) {
    for input in node_inputs {
        if let NodeInput::Reference(origin) = input
            && let Some(subst) = input_substitutions.get(origin)
        {
            *origin = subst.expect("Input was removed but is still needed");
        }
    }
}

fn apply_input_sub_or_removal(
    node_inputs: &mut Vec<NodeInput>,
    input_substitutions: &HashMap<ValueOrigin, Option<ValueOrigin>>,
    mut removal_callback: impl FnMut(u32),
) {
    let mut slot_idx = 0u32..;
    node_inputs.retain_mut(|input| {
        let slot_idx = slot_idx.next().unwrap();
        if let NodeInput::Reference(origin) = input
            && let Some(subst) = input_substitutions.get(origin)
        {
            if let Some(subst) = subst {
                *origin = *subst;
                true
            } else {
                // This input was removed.
                removal_callback(slot_idx);
                false
            }
        } else {
            true
        }
    });
}

fn remove_block_node_io(
    block_node: &mut Node,
    block_node_idx: usize,
    inputs_to_remove: &[u32],
    outputs_to_remove: &[u32],
    outs_removed: &mut VecDeque<Option<Vec<u32>>>,
    parent_substitutions: &mut HashMap<ValueOrigin, Option<ValueOrigin>>,
) {
    outs_removed.push_front(None);

    let sub_dag = if let Operation::Block { sub_dag, .. } = &mut block_node.operation {
        sub_dag
    } else {
        panic!()
    };

    let mut input_substitutions: HashMap<ValueOrigin, Option<ValueOrigin>> = HashMap::new();
    for (node_idx, node) in sub_dag.nodes.iter_mut().enumerate() {
        match &mut node.operation {
            Operation::Inputs => {
                // This is the first node of the sub-block, which lists the block inputs.
                // We start the removal from here.
                remove_slots(
                    &mut node.output_types,
                    inputs_to_remove,
                    node_idx,
                    &mut input_substitutions,
                );
            }
            Operation::Block { .. } => {
                // Any input set for removal must be propagated to the inner blocks.
                let mut sub_input_to_remove = Vec::new();
                let mut input_changed = false;
                for (slot_idx, input_idx) in block_inputs(&node.inputs) {
                    if inputs_to_remove.binary_search(&input_idx).is_ok() {
                        sub_input_to_remove.push(input_idx);
                        input_changed = true;
                    }
                }

                apply_substitutions(&mut node.inputs, &input_substitutions);

                // If there is anything to remove in the inner block, we need to apply the removals recursively.
                if input_changed || !outputs_to_remove.is_empty() {
                    // TODO: if we knew to what blocks the inner blocks can break to,
                    // we could avoid recursing into blocks that are not affected by
                    // the output removals.

                    remove_block_node_io(
                        node,
                        node_idx,
                        &sub_input_to_remove,
                        outputs_to_remove,
                        outs_removed,
                        &mut input_substitutions,
                    );
                }
            }
            Operation::WASMOp(Op::Br { relative_depth }) => {
                let mut new_inputs = node
                    .inputs
                    .into_iter()
                    .map(|input| {
                        if let NodeInput::Reference(origin) = input {
                            if let Some(subst) = input_substitutions.get(&origin) {
                                *subst
                            } else {
                                Some(origin)
                            }
                        } else {
                            panic!("Break input is not a reference");
                        }
                    })
                    .collect_vec();

                // If the target had some of its outputs explicitly removed, we need to reflect that.
                let extra_remove = if *relative_depth == outs_removed.len() as u32 - 1 {
                    for rem in outputs_to_remove {
                        new_inputs[*rem as usize] = None;
                    }
                };

                // Mark whatever was removed from this target.
                let removed_indices = Vec::new();
                node.inputs = new_inputs
                    .into_iter()
                    .enumerate()
                    .filter_map(|(idx, subst)| {
                        if let Some(subst) = subst {
                            Some(NodeInput::Reference(subst))
                        } else {
                            removed_indices.push(idx as u32);
                            None
                        }
                    })
                    .collect();

                let known_removed = &mut outs_removed[*relative_depth as usize];
                if let Some(known_removed) = known_removed {
                    // Every break to this target must remove the same set of outputs.
                    assert_eq!(known_removed, &removed_indices);
                } else {
                    *known_removed = Some(removed_indices);
                }
            }
            Operation::WASMOp(Op::BrIf { relative_depth })
            | Operation::BrIfZero { relative_depth } => {
                todo!();
            }
            Operation::BrTable { targets } => {
                // BrTable is even more complicated, because we need to update
                // the input permutation inside each of the targets.
                todo!();
                let mut removed_slots = HashSet::new();
                apply_input_sub_or_removal(&mut node.inputs, &input_substitutions, |idx| {
                    removed_slots.insert(idx);
                });

                for BrTableTarget {
                    input_permutation, ..
                } in targets
                {
                    // TODO: check if the break is to the depth we are removing outputs from,
                    // and apply removals as needed...
                    todo!();

                    input_permutation.retain(|perm| !removed_slots.contains(perm));
                }
            }
            _ => {
                // For any other node, we just apply the input substitutions.
                apply_substitutions(&mut node.inputs, &input_substitutions);
            }
        }
    }

    // This is the set of outputs that were removed due to the needed input also being removed.
    let curr_block_outs_removed = outs_removed.pop_front().unwrap();

    // If this is the top-level block, what was actually removed must be identical
    // to was was given from the input.
    let outputs_to_remove = if outs_removed.is_empty() {
        if let Some(removed) = curr_block_outs_removed {
            assert_eq!(removed, outputs_to_remove);
        }
        outputs_to_remove
    } else {
        &curr_block_outs_removed.unwrap_or_default()
    };
    let is_output_removed = bool_from_positions(outputs_to_remove.iter().cloned());

    // Update parent node outputs.
    remove_slots(
        &mut block_node.output_types,
        is_output_removed,
        Some((block_node_idx, parent_substitutions)),
    );

    // Update parent node inputs.
    remove_slots(
        &mut block_node.inputs,
        is_input_removed.iter().cloned(),
        None,
    );
}

fn remove_io_from_break() {
    // If the target had some of its outputs removed, we need to reflect that.
    if *relative_depth == output_removel_depth {
        remove_indices(
            &mut node.inputs,
            outputs_to_remove.iter().map(|r| *r as usize),
        );
    }

    // Input substitutions in breaks are a little different, because
    // we tolerate removals as well.
    apply_input_sub_or_removal(&mut node.inputs, &input_substitutions, |_| {});
}

/// Removes either input or output slots.
///
/// Optionally stores the substitutions to apply for the users of the removed output slots.
fn remove_slots<T>(
    slots: &mut Vec<T>,
    to_remove: &[u32],
    node_idx: usize,
    subs: &mut HashMap<ValueOrigin, Option<ValueOrigin>>,
) {
    remove_indices(
        slots,
        to_remove.iter().map(|&r| r as usize),
        |old_idx, new_idx| {
            subs.insert(
                ValueOrigin {
                    node: node_idx,
                    output_idx: old_idx as u32,
                },
                new_idx.map(|new_idx| ValueOrigin {
                    node: node_idx,
                    output_idx: new_idx as u32,
                }),
            );
        },
    );
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

// Given a sorted iterator of indices, produces an iterator of bools where true means the index is in the input, and false means it is not.
fn bool_from_positions(sorted_iter: impl IntoIterator<Item = u32>) -> impl Iterator<Item = bool> {
    let mut sorted_iter = sorted_iter.into_iter().peekable();
    (0u32..).map(move |idx| {
        if sorted_iter.peek() == Some(&idx) {
            sorted_iter.next();
            true
        } else {
            false
        }
    })
}
