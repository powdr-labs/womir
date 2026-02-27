//! This pass takes a DAG and removes unnecessary inputs and outputs from
//! blocks. These spurious inputs and outputs may come from the original Wasm
//! code, but they can also be introduced by the `locals_data_flow` pass, which is
//! conservative in its analysis of local usage, or can be orphans from const
//! dedup/collapse.

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
        passes::{
            calc_input_redirection::{RedirDag, RedirNode, Redirection},
            dag::{BrTableTarget, NodeInput, Operation, ValueOrigin},
        },
    },
    utils::{offset_map::OffsetMap, remove_indices},
};

pub fn prune_block_io(dag: &mut RedirDag<'_>) {
    // If outputs have been removed, we might have created new opportunities for
    // input removals, so we need to repeat until we reach a fixed point.
    while process_block(dag, &mut VecDeque::new()) {}
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

struct ControlStackEntry {
    input_usage: Vec<InputUsage>,
}

fn process_block(dag: &mut RedirDag, cs: &mut VecDeque<ControlStackEntry>) -> bool {
    // Some output slots might be removed from the block outputs in case they are redundant.
    // We track such cases in this map, and also where the users of those outputs should point
    // to instead.
    let mut output_removed = false;
    let mut origin_substitutions: HashMap<ValueOrigin, Option<ValueOrigin>> = HashMap::new();
    for node_idx in 0..dag.nodes.len() {
        let node = &mut dag.nodes[node_idx];
        apply_substitutions(&mut node.inputs, &origin_substitutions);

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
                if let Some((_, input_idx)) = block_inputs([condition]).next() {
                    cs[0].input_usage[input_idx as usize] = InputUsage::Used;
                }

                handle_break_target(cs, break_inputs, *relative_depth);
            }
            (Operation::BrTable { targets }, false) => {
                let (condition, break_inputs) = node.inputs.split_last().unwrap();
                // Handle the condition as a normal node input:
                if let Some((_, input_idx)) = block_inputs([condition]).next() {
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
                let removals = handle_block_node(node_idx, node, cs, &mut origin_substitutions);

                output_removed |= removals.output_removed;

                // Update this block input usage based on the sub-block input usage and the removals we have done.
                if !is_func_body {
                    // Input usage was calculated based on the original block inputs,
                    // so we need to adjust it based on the removals we have done.
                    let mut sub_input_usage = removals.entry.input_usage;
                    remove_indices(
                        &mut sub_input_usage,
                        removals.removed_inputs.iter().map(|r| *r as usize),
                        |_, _| {},
                    );

                    let input_usage = &mut cs[0].input_usage;
                    for (origin, sub_usage) in
                        node.inputs.iter().zip_eq(sub_input_usage.into_iter())
                    {
                        if let NodeInput::Reference(ValueOrigin {
                            node: 0,
                            output_idx,
                        }) = origin
                        {
                            input_usage[*output_idx as usize].combine(sub_usage.depth_down());
                        }
                    }
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

    output_removed
}

fn handle_break_target<'a>(
    cs: &mut VecDeque<ControlStackEntry>,
    node_inputs: impl IntoIterator<Item = &'a NodeInput>,
    relative_depth: u32,
) {
    for (slot_idx, input) in node_inputs.into_iter().enumerate() {
        // Determine if this node input originates at the block input.
        if let NodeInput::Reference(ValueOrigin {
            node: 0,
            output_idx: input_idx,
        }) = *input
        {
            // This is a block input. Mark the most restrictive usage given for it inside this block.
            let usage = &mut cs[0].input_usage[input_idx as usize];
            usage.combine_with_redirection(relative_depth, slot_idx as u32);
        }
    }
}

struct BlockRemovals {
    /// List of the indices of inputs removed from the block.
    removed_inputs: Vec<u32>,

    /// Was any output removed?
    output_removed: bool,

    /// The resulting entry after processing the block.
    entry: ControlStackEntry,
}

fn handle_block_node(
    node_idx: usize,
    node: &mut RedirNode,
    cs: &mut VecDeque<ControlStackEntry>,
    origin_substitutions: &mut HashMap<ValueOrigin, Option<ValueOrigin>>,
) -> BlockRemovals {
    let (sub_dag, kind) = if let Operation::Block { sub_dag, kind } = &mut node.operation {
        (sub_dag, kind)
    } else {
        panic!()
    };

    // Call the processing recursively
    cs.push_front(ControlStackEntry {
        //input_map,
        // Let the block initialize the input usage for its inputs...
        input_usage: Vec::new(),
    });
    process_block(sub_dag, cs);
    let mut sub_entry = cs.pop_front().unwrap();
    assert_eq!(sub_entry.input_usage.len(), node.inputs.len());

    let redirections = &mut sub_dag.block_data;

    // Calculate what outputs can be removed
    // TODO: make the initial set of removals come from the previous pass, because we
    // can only detect if an output was actually used after processing the block.
    let mut outputs_to_remove = Vec::new();
    if let BlockKind::Block = kind {
        // If sub-block is a plain block, we can remove its output slots that were redirected as-is from its inputs.
        for (output_idx, redir) in redirections.iter().enumerate() {
            assert!(*redir != Redirection::Unknown);
            if let Redirection::FromInput(input_idx) = redir {
                // This output is always a redirection of the same input.
                let NodeInput::Reference(original_input) = node.inputs[*input_idx as usize] else {
                    unreachable!()
                };
                origin_substitutions.insert(
                    ValueOrigin {
                        node: node_idx,
                        output_idx: output_idx as u32,
                    },
                    Some(original_input),
                );
                outputs_to_remove.push(output_idx as u32);
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
                redirections[*slot as usize] == Redirection::FromInput(input_idx as u32)
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
        // Resolve Unknown inputs in a loop by propagating CanRemoveInput::No backwards.
        //
        // Each Unknown input is only used as a redirection to other loop
        // inputs (its slots). If any of those targets is No, then this
        // input is also No. We propagate by building reverse edges
        // (target → source) and BFS-ing from all No inputs.
        // Whatever remains Unknown afterwards is safely removable (Yes).

        // Build reverse edges map: target input slot → list of source input slots that are redirected to it.
        let mut reverse_edges: Vec<Vec<u32>> = vec![vec![]; can_remove_input.len()];
        for (source, status) in can_remove_input.iter().enumerate() {
            if *status == CanRemoveInput::Unknown {
                let InputUsage::RedirectedTo {
                    max_depth: 0,
                    slots,
                } = &sub_entry.input_usage[source]
                else {
                    unreachable!()
                };
                for &target in slots {
                    reverse_edges[target as usize].push(source as u32);
                }
            }
        }

        // Seed the worklist with all No inputs.
        let mut worklist = can_remove_input
            .iter()
            .enumerate()
            .filter(|(_, s)| **s == CanRemoveInput::No)
            .map(|(i, _)| i as u32)
            .collect_vec();

        // Propagate No backwards through the reverse edges.
        while let Some(target) = worklist.pop() {
            for &source in &reverse_edges[target as usize] {
                match can_remove_input[source as usize] {
                    CanRemoveInput::Unknown => {
                        can_remove_input[source as usize] = CanRemoveInput::No;
                        worklist.push(source);
                    }
                    CanRemoveInput::Yes => {
                        // This should not happen: an input to be removed can't feed into an input that must be kept.
                        unreachable!()
                    }
                    CanRemoveInput::No => {
                        // Already marked as No, nothing to do.
                    }
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

    let output_removed = !outputs_to_remove.is_empty();

    // Perform the actual removals in the sub-block.
    if !inputs_to_remove.is_empty() || output_removed {
        remove_block_node_io(
            node_idx,
            origin_substitutions,
            node,
            &inputs_to_remove,
            &mut VecDeque::from(vec![outputs_to_remove]),
        );
    }

    BlockRemovals {
        removed_inputs: inputs_to_remove,
        output_removed,
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
    parent_node_idx: usize,
    parend_origin_substitutions: &mut HashMap<ValueOrigin, Option<ValueOrigin>>,
    block_node: &mut RedirNode,
    inputs_to_remove: &[u32],
    outputs_to_remove: &mut VecDeque<Vec<u32>>,
) {
    let (sub_dag, kind) = if let Operation::Block { sub_dag, kind } = &mut block_node.operation {
        (sub_dag, kind)
    } else {
        panic!()
    };

    // Update parent node inputs.
    remove_indices(
        &mut block_node.inputs,
        inputs_to_remove.iter().map(|&r| r as usize),
        |_, _| {},
    );

    // Update parent node outputs.
    remove_indices(
        &mut block_node.output_types,
        outputs_to_remove[0].iter().map(|r| *r as usize),
        |old_idx, new_idx| {
            if let Some(new_idx) = new_idx {
                // This output was shifted, needs to be mapped to the new index.
                parend_origin_substitutions.insert(
                    ValueOrigin {
                        node: parent_node_idx,
                        output_idx: old_idx as u32,
                    },
                    Some(ValueOrigin {
                        node: parent_node_idx,
                        output_idx: new_idx as u32,
                    }),
                );
            }
        },
    );

    // Update node redirections.
    let redirs_to_remove = match kind {
        BlockKind::Loop => inputs_to_remove,
        BlockKind::Block => &outputs_to_remove[0][..],
    };
    let redirections = &mut sub_dag.block_data;
    remove_indices(
        redirections,
        redirs_to_remove.iter().map(|&r| r as usize),
        |_, _| {},
    );

    // For a loop, the block inputs are also its outputs, so we need to mark the corresponding outputs as removed as well.
    if let BlockKind::Loop = kind {
        let outs = &mut outputs_to_remove[0];
        assert!(outs.is_empty());
        // I couldn't avoid cloning here. I tried making `outputs_to_remove: &mut VecDeque<&[u32]>`,
        // but there is no lifetime that allows it to hold external references plus local references.
        *outs = inputs_to_remove.to_vec();
    }

    // Walk the DAG and apply the substitutions and removals.
    let mut origin_substitutions: HashMap<ValueOrigin, Option<ValueOrigin>> = HashMap::new();
    for (node_idx, node) in sub_dag.nodes.iter_mut().enumerate() {
        match &mut node.operation {
            Operation::Inputs => {
                // This is the first node of the sub-block, which lists the block inputs.
                // We start the removal from here.
                remove_indices(
                    &mut node.output_types,
                    inputs_to_remove.iter().map(|&r| r as usize),
                    |old_idx, new_idx| {
                        origin_substitutions.insert(
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
                for (sub_input_idx, parent_input_idx) in block_inputs(&node.inputs) {
                    if inputs_to_remove.binary_search(&parent_input_idx).is_ok() {
                        sub_input_to_remove.push(sub_input_idx as u32);
                        input_changed = true;
                    }
                }

                // If there is anything to remove in the inner block, we need to apply the removals recursively.
                if input_changed || !outputs_to_remove.is_empty() {
                    // TODO: if we knew to what blocks the inner blocks can break to,
                    // we could avoid recursing into blocks that are not affected by
                    // the output removals.

                    outputs_to_remove.push_front(Vec::new());
                    remove_block_node_io(
                        node_idx,
                        &mut origin_substitutions,
                        node,
                        &sub_input_to_remove,
                        outputs_to_remove,
                    );
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
        apply_substitutions(&mut node.inputs, &origin_substitutions);
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
            target_outs_to_remove.iter().map(|x| *x as usize),
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
