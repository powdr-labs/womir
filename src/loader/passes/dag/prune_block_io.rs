//! This pass takes a DAG and removes unnecessary inputs and outputs from
//! blocks. These spurious inputs and outputs may come from the original Wasm
//! code, but they can also be introduced by the `locals_data_flow` pass, which is
//! conservative in its analysis of local usage.

// TODO: store the redirected inputs in the loop block entry, so that we don't
// have to recompute it in the liveness pass.

use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet, VecDeque},
    iter::Peekable,
    vec,
};

use itertools::Itertools;
use wasmparser::Operator as Op;

use crate::{
    loader::{
        BlockKind,
        passes::dag::{BrTableTarget, Dag, Node, NodeInput, Operation, ValueOrigin},
    },
    utils::{offset_map::OffsetMap, remove_indices},
};

pub fn prune_block_io(dag: &mut Dag<'_>) {
    process_block(&mut dag.nodes, &mut VecDeque::new())
}

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

        // In the function body, we can't change the inputs and outputs of the function,
        // so we can skip a lot of processing.
        let is_func_body = cs.is_empty();

        match (&mut node.operation, is_func_body) {
            (Operation::Inputs, false) => {
                // This is the first node of a block, which lists the block inputs.
                // We use its information to initialize the input usage information for this block.
                cs[0]
                    .input_usage
                    .resize(node.output_types.len(), InputUsage::Unused);
            }
            (Operation::WASMOp(Op::Br { relative_depth }), false) => {
                handle_break_target(cs, &node.inputs, *relative_depth);
            }
            (
                Operation::BrIfZero { relative_depth }
                | Operation::WASMOp(Op::BrIf { relative_depth }),
                false,
            ) => {
                let (condition, break_inputs) = node.inputs.split_last().unwrap();
                // Handle the condition as a normal node input:
                for (_, input_idx) in block_inputs([condition]) {
                    cs[0].input_usage[input_idx as usize] = InputUsage::Used;
                }

                handle_break_target(cs, break_inputs, *relative_depth);
            }
            (Operation::BrTable { targets }, false) => {
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
            (Operation::Block { .. }, is_func_body) => {
                let mut total_outputs_to_remove = Vec::new();

                let last_pass = loop {
                    let mut pass = block_processing_pass(node, cs);

                    // If any output was removed, that might propagate up the block's DAG
                    // causing more inputs to be removable, so we need to repeat until we
                    // reach a fixed point.
                    let done = pass.outputs_to_remove.is_empty();

                    total_outputs_to_remove = combine_removals(
                        total_outputs_to_remove,
                        std::mem::take(&mut pass.outputs_to_remove),
                    );

                    if done {
                        break pass;
                    }
                };

                // Update node outputs.
                remove_indices(
                    &mut node.output_types,
                    total_outputs_to_remove.iter().map(|(r, _)| *r as usize),
                    |old_idx, new_idx| {
                        if let Some(new_idx) = new_idx {
                            // This output was shifted, needs to be mapped to the new index.
                            input_substitutions.insert(
                                ValueOrigin {
                                    node: node_idx,
                                    output_idx: old_idx as u32,
                                },
                                Some(ValueOrigin {
                                    node: node_idx,
                                    output_idx: new_idx as u32,
                                }),
                            );
                        }
                    },
                );

                // The removed outputs needs to be mapped, too.
                for (removed_slot, redir) in total_outputs_to_remove {
                    input_substitutions.insert(
                        ValueOrigin {
                            node: node_idx,
                            output_idx: removed_slot,
                        },
                        redir,
                    );
                }

                // Update this block input usage based on the sub-block input usage and the removals we have done.
                //
                // Both entry.input_usage and entry.input_map are relative to the original block inputs (they are
                // calculated before the input removals), so we need to filter out inputs that were removed.
                if !is_func_body {
                    let mut inputs_removed = last_pass.inputs_removed.into_iter().peekable();
                    for (sub_input_idx, usage) in
                        last_pass.entry.input_usage.into_iter().enumerate()
                    {
                        if !is_in_sorted_iter(&mut inputs_removed, &(sub_input_idx as u32))
                            && let Some(input_idx) =
                                last_pass.entry.input_map.get(&(sub_input_idx as u32))
                        {
                            cs[0].input_usage[*input_idx as usize].combine(usage.depth_down());
                        }
                    }
                }

                if !last_pass.block_returns {
                    // The rest of this block is unreachable, so we can stop processing it.
                    dag.truncate(node_idx + 1);
                    break;
                }
            }
            (_, false) => {
                // This is a normal node that might use some block inputs
                for (_, input_idx) in block_inputs(&node.inputs) {
                    // This block input is being used in some way...
                    cs[0].input_usage[input_idx as usize] = InputUsage::Used;
                }
            }
            _ => {
                // We are processing a non-block node in the function body, we can just skip.
            }
        }
    }
    // TODO: mark and remove unused sub-blocks outputs...
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

        // We can't change the function signature, so if the target is a return,
        // we don't track the redirections.
        if relative_depth >= cs.len() as u32 {
            assert_eq!(relative_depth, cs.len() as u32);
            continue;
        }

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
    /// Does this block ever return?
    block_returns: bool,

    /// List of the indices of inputs removed from the block.
    inputs_removed: Vec<u32>,

    /// List of the indices of outputs to be removed from the block,
    /// together with the redirection users must point to, if any user
    /// is expected.
    outputs_to_remove: Vec<(u32, Option<ValueOrigin>)>,

    /// The resulting entry after processing the block.
    entry: ControlStackEntry,
}

fn block_processing_pass(node: &mut Node, cs: &mut VecDeque<ControlStackEntry>) -> BlockPassResult {
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
    // TODO: MAJOR BUG: you can't just remap the inputs to a loop sub-block,
    // because this only guarantees the mapping on the first iteration. You can only do
    // this if the input is redirected as-is to the next iteration, but we don't have
    // that information at this point.
    //
    // Since this information is also used by the register allocator later,
    // we should have a pass calculating this earlier.
    todo!()
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
    let mut block_returns = true;
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
                outputs_to_remove.extend((0..node.output_types.len() as u32).map(|i| (i, None)));
            }
            BlockKind::Loop => {
                // If the sub-block is a loop, it can be turned into a plain block with no outputs,
                // because it never iterates.
                *kind = BlockKind::Block;
                assert!(node.output_types.is_empty());
            }
        }
        block_returns = false;
    } else if let BlockKind::Block = kind {
        // If sub-block is a plain block, we can remove its output slots that were redirected as-is from its inputs.
        for (output_idx, redir) in sub_entry.outputs_redirections.iter().enumerate() {
            assert!(*redir != Redirection::Unknown);
            if let Redirection::FromInput(input_idx) = redir {
                // This output is always a redirection of the same input.
                let NodeInput::Reference(original_input) = node.inputs[*input_idx as usize] else {
                    unreachable!()
                };
                outputs_to_remove.push((output_idx as u32, Some(original_input)));
            }
        }
    } else {
        // This is a loop, and loops "never" returns. Due to an earlier DAG
        // transformation that made all breaks explicit, when we break out of
        // a loop, it is always an explicit break to an outer block.
        block_returns = false;
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

    let inputs_to_remove = can_remove_input
        .into_iter()
        .enumerate()
        .filter_map(|(idx, s)| match s {
            CanRemoveInput::Yes => Some(idx as u32),
            CanRemoveInput::No => None,
            CanRemoveInput::Unknown => panic!(),
        })
        .collect_vec();

    remove_block_node_io(
        node,
        &inputs_to_remove,
        &mut VecDeque::from(vec![outputs_to_remove.iter().map(|(r, _)| *r).collect()]),
    );

    // Update parent node inputs.
    remove_indices(
        &mut node.inputs,
        inputs_to_remove.iter().map(|&r| r as usize),
        |_, _| {},
    );

    BlockPassResult {
        block_returns,
        inputs_removed: inputs_to_remove,
        outputs_to_remove,
        entry: sub_entry,
    }
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

fn remove_block_node_io(
    block_node: &mut Node,
    inputs_to_remove: &[u32],
    outputs_to_remove: &mut VecDeque<Vec<u32>>,
) {
    let sub_dag = if let Operation::Block { sub_dag, kind } = &mut block_node.operation {
        // For a loop, the block inputs are also its outputs, so we need to mark the corresponding outputs as removed as well.
        if let BlockKind::Loop = kind {
            let outs = &mut outputs_to_remove[0];
            assert!(outs.is_empty());
            *outs = inputs_to_remove.to_vec();
        }

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
                remove_indices(
                    &mut node.output_types,
                    inputs_to_remove.iter().map(|&r| r as usize),
                    |old_idx, new_idx| {
                        input_substitutions.insert(
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
            Operation::Block { .. } => {
                // Any input set for removal must be propagated to the inner blocks.
                let mut sub_input_to_remove = Vec::new();
                let mut input_changed = false;
                let mut inputs_to_remove = inputs_to_remove.iter().cloned().peekable();
                for (_, input_idx) in block_inputs(&node.inputs) {
                    if is_in_sorted_iter(&mut inputs_to_remove, &input_idx) {
                        sub_input_to_remove.push(input_idx);
                        input_changed = true;
                    }
                }

                // If there is anything to remove in the inner block, we need to apply the removals recursively.
                if input_changed || !outputs_to_remove.is_empty() {
                    // TODO: if we knew to what blocks the inner blocks can break to,
                    // we could avoid recursing into blocks that are not affected by
                    // the output removals.

                    outputs_to_remove.push_front(Vec::new());
                    remove_block_node_io(node, &sub_input_to_remove, outputs_to_remove);
                    outputs_to_remove.pop_front();
                }
            }
            Operation::WASMOp(Op::Br { relative_depth }) => {
                remove_break_inputs(&mut node.inputs, *relative_depth, outputs_to_remove);
            }
            Operation::WASMOp(Op::BrIf { relative_depth })
            | Operation::BrIfZero { relative_depth } => {
                // Temporarily take of the selector because it is not part of the break inputs
                let selector = node.inputs.pop().unwrap();
                remove_break_inputs(&mut node.inputs, *relative_depth, outputs_to_remove);
                node.inputs.push(selector);
            }
            Operation::BrTable { targets } => {
                // BrTable is more complicated, because we need to update
                // the input permutation inside each of the targets.

                let selector = node.inputs.pop().unwrap();

                // First do the removals on all the targets.
                let mut slot_still_used = vec![false; node.inputs.len()];
                for t in targets.iter_mut() {
                    let target_outs_to_remove: &[u32] = outputs_to_remove
                        .get(t.relative_depth as usize)
                        .map(|removals| &removals[..])
                        .unwrap_or(&[]);

                    let mut slot_idx = 0..;
                    let mut removal_iter = target_outs_to_remove.iter().cloned().peekable();
                    t.input_permutation.retain(|_| {
                        let slot_idx = slot_idx.next().unwrap();
                        if let Some(removal) = removal_iter.peek()
                            && *removal == slot_idx
                        {
                            // This slot is removed, so we remove it from the permutation.
                            removal_iter.next();
                            false
                        } else {
                            // This slot is not removed, we keep it and mark it as still used.
                            slot_still_used[slot_idx as usize] = true;
                            true
                        }
                    });
                }

                // Now we do the removal on the node inputs.
                let mut idx = 0..;
                let mut offset_map = OffsetMap::new();
                node.inputs.retain(|_| {
                    let idx = idx.next().unwrap();
                    if slot_still_used[idx] {
                        true
                    } else {
                        offset_map.append(idx as u32);
                        false
                    }
                });

                // Apply the map for all the target input permutations.
                for t in targets {
                    for perm in &mut t.input_permutation {
                        *perm -= offset_map.get(perm);
                    }
                }

                // Restore the selector input.
                node.inputs.push(selector);
            }
            _ => {
                // Nothing special to do for other nodes.
            }
        }

        // Apply the input substitutions for this node.
        apply_substitutions(&mut node.inputs, &input_substitutions);
    }
}

fn remove_break_inputs<T>(
    node_inputs: &mut Vec<T>,
    relative_depth: u32,
    outputs_to_remove: &mut VecDeque<Vec<u32>>,
) {
    if let Some(target_outs_to_remove) = &outputs_to_remove.get(relative_depth as usize) {
        // If we have specifyed what outputs to remove, apply them.
        remove_indices(
            node_inputs,
            target_outs_to_remove.iter().cloned().map(|x| x as usize),
            |_, _| {},
        );
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

/// Combines an old list of removed indices with a new list of removed indices,
/// adjusting the new indices by the number of previous removals that come before them.
fn combine_removals(
    previous: Vec<(u32, Option<ValueOrigin>)>,
    new_indices: Vec<(u32, Option<ValueOrigin>)>,
) -> Vec<(u32, Option<ValueOrigin>)> {
    if previous.is_empty() {
        return new_indices;
    }

    let mut result = Vec::new();
    let mut prev = previous.into_iter().peekable();
    let mut offset = 0;

    for (idx, redir) in new_indices {
        while let Some((p, _)) = prev.peek() {
            let original = idx + offset;
            assert_ne!(*p, original);
            if *p < original {
                result.push(prev.next().unwrap());
                offset += 1;
            } else {
                break;
            }
        }
        result.push((idx + offset, redir));
    }
    result.extend(prev);
    result
}

/// Checks if a value is in a sorted iterator, consuming the iterator up to the value.
fn is_in_sorted_iter<T: Ord>(iter: &mut Peekable<impl Iterator<Item = T>>, value: &T) -> bool {
    while let Some(item) = iter.peek() {
        if item > value {
            break;
        }
        let item = iter.next().unwrap();
        if item == *value {
            return true;
        }
    }
    false
}
