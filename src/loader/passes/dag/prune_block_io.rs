//! This pass takes a DAG and removes unnecessary inputs and outputs from
//! blocks. These spurious inputs and outputs may come from the original Wasm
//! code, but they can also be introduced by the `locals_data_flow` pass, which is
//! conservative in its analysis of local usage, or can be orphans from const
//! dedup/collapse.
//!
//! Each pass seems to be quadratic in the number of total (nested included) nodes.

use std::{
    collections::{HashMap, VecDeque},
    fmt::Debug,
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
    utils::{remove_indices, sorted_removals_offset},
};

/// Prunes block inputs and outputs that are not actually used.
///
/// Returns the number of loop inputs removed (normal blocks I/O removal
/// is not tracked, because they do not directly contribute to final
/// cost, they just indirectly contribute to loop input count).
pub fn prune_block_io(dag: &mut RedirDag<'_>) -> usize {
    let mut total_loop_inputs_removed = 0;

    // If outputs have been removed, we might have created new opportunities for
    // input removals, so we need to repeat until we reach a fixed point.
    loop {
        let (output_removed, loop_inputs_removed) = process_dag(dag, &mut VecDeque::new());
        total_loop_inputs_removed += loop_inputs_removed;
        if !output_removed {
            break;
        }
    }

    total_loop_inputs_removed
}

#[derive(Debug)]
enum InputUsage {
    /// This is the most useless input, always safe to remove.
    Unused,
    /// Can be removed if it is not used in any other way.
    /// Used to detect useless circular redirections in loop.
    RedirectedTo {
        /// The set of outputs slots this input is redirected to,
        /// for each depth level. Duplicates slots are possible
        /// while being built, but they are sorted and deduped
        /// before being used.
        slots_per_depth: VecDeque<Vec<u32>>,
    },
    /// This input is useful, and cannot be removed.
    Used,
}

impl InputUsage {
    /// Takes the input usage information from a sub-block,
    /// and adjusts it to be used in the parent block.
    fn depth_down(self) -> Self {
        match self {
            InputUsage::Used => {
                // If an input is used in the sub-block, it is also used in the parent block.
                InputUsage::Used
            }
            InputUsage::RedirectedTo {
                mut slots_per_depth,
            } => {
                // Pop the level 0, corresponding to the sub-block itself, so that the new
                // level 0 corresponds to the parent block, as the parent is not interested
                // in the redirections internal to the sub-block.
                slots_per_depth.pop_front();
                if slots_per_depth.is_empty() {
                    // There is no redirection left after the ones internal to the sub-block,
                    // so this input is just used in the perspective of the parent block.
                    InputUsage::Used
                } else {
                    // Remains a redirection, but now for the perspective of the parent block.
                    InputUsage::RedirectedTo { slots_per_depth }
                }
            }
            InputUsage::Unused => {
                // If an input is unused in the sub-block, it is also unused in the parent block.
                InputUsage::Unused
            }
        }
    }

    fn combine(&mut self, other: InputUsage) {
        match (&mut *self, other) {
            (InputUsage::Used, _) | (_, InputUsage::Used) => {
                *self = InputUsage::Used;
            }
            (
                InputUsage::RedirectedTo {
                    slots_per_depth: self_slots,
                },
                InputUsage::RedirectedTo {
                    slots_per_depth: mut other_slots,
                },
            ) => {
                // Ensures all depth levels in both will be merged.
                if other_slots.len() > self_slots.len() {
                    std::mem::swap(self_slots, &mut other_slots);
                };

                for (self_depth, mut other_depth) in self_slots.iter_mut().zip(other_slots) {
                    // This swap ensures the smaller vec will be extended into the bigger vec.
                    if other_depth.len() > self_depth.len() {
                        std::mem::swap(self_depth, &mut other_depth);
                    }
                    self_depth.extend(other_depth);
                }
            }
            (InputUsage::Unused, InputUsage::Unused)
            | (InputUsage::RedirectedTo { .. }, InputUsage::Unused) => (),
            (InputUsage::Unused, other @ InputUsage::RedirectedTo { .. }) => {
                *self = other;
            }
        }
    }

    fn combine_with_redirection(&mut self, depth: u32, slot: u32) {
        let slots_per_depth = match self {
            InputUsage::Used => return,
            InputUsage::Unused => {
                *self = InputUsage::RedirectedTo {
                    slots_per_depth: VecDeque::new(),
                };
                let InputUsage::RedirectedTo { slots_per_depth } = self else {
                    unreachable!()
                };
                slots_per_depth
            }
            InputUsage::RedirectedTo { slots_per_depth } => slots_per_depth,
        };

        if slots_per_depth.len() <= depth as usize {
            slots_per_depth.resize_with(depth as usize + 1, Vec::new);
        }
        slots_per_depth[depth as usize].push(slot);
    }
}

struct ControlStackEntry {
    input_usage: Vec<InputUsage>,
}

fn process_dag(dag: &mut RedirDag, cs: &mut VecDeque<ControlStackEntry>) -> (bool, usize) {
    // Some output slots might be removed from the block outputs in case they are redundant.
    // We track such cases in this map, and also where the users of those outputs should point
    // to instead.
    let mut output_removed = false;
    let mut origin_substitutions: HashMap<ValueOrigin, Option<ValueOrigin>> = HashMap::new();
    let mut loop_inputs_removed = 0;
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
                    .resize_with(node.output_types.len(), || InputUsage::Unused);
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
                let mut removals = handle_block_node(node_idx, node, cs, &mut origin_substitutions);

                loop_inputs_removed += removals.loop_inputs_removed;

                output_removed |= removals.output_removed;

                // Update this block input usage based on the sub-block input usage and the removals we have done.
                if !is_func_body {
                    // Input usage was calculated based on the original block inputs,
                    // so we need to adjust it based on the removals we have done.
                    remove_indices(
                        &mut removals.inputs_usage,
                        removals.removed_inputs.iter().map(|r| *r as usize),
                        |_, _| {},
                    );

                    let input_usage = &mut cs[0].input_usage;
                    for (origin, sub_usage) in
                        node.inputs.iter().zip_eq(removals.inputs_usage.into_iter())
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

    (output_removed, loop_inputs_removed)
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

    /// Number of loop inputs removed, including indirectly removed ones.
    loop_inputs_removed: usize,

    /// Was any output removed?
    output_removed: bool,

    /// The resulting entry after processing the block.
    inputs_usage: Vec<InputUsage>,
}

fn handle_block_node(
    node_idx: usize,
    node: &mut RedirNode,
    cs: &mut VecDeque<ControlStackEntry>,
    origin_substitutions: &mut HashMap<ValueOrigin, Option<ValueOrigin>>,
) -> BlockRemovals {
    let Operation::Block { sub_dag, kind } = &mut node.operation else {
        panic!()
    };

    // Call the processing recursively
    cs.push_front(ControlStackEntry {
        // Let the block initialize the input usage for its inputs...
        input_usage: Vec::new(),
    });
    let (mut output_removed, mut loop_inputs_removed) = process_dag(sub_dag, cs);
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
        if let InputUsage::RedirectedTo { slots_per_depth } = usage {
            let this_slots = &mut slots_per_depth[0];
            this_slots.sort_unstable();
            this_slots.dedup();
            if this_slots.iter().any(|slot| {
                redirections[*slot as usize] != Redirection::FromInput(input_idx as u32)
            }) {
                *usage = InputUsage::Used;
            }
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
            InputUsage::RedirectedTo { slots_per_depth } if slots_per_depth.len() <= 1 => {
                // This not used as redirection to outside this block, so maybe it can be removed.
                assert_eq!(slots_per_depth.len(), 1);
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
                let InputUsage::RedirectedTo { slots_per_depth } = &sub_entry.input_usage[source]
                else {
                    unreachable!()
                };
                assert_eq!(slots_per_depth.len(), 1);
                assert!(!slots_per_depth[0].is_empty());
                for &target in &slots_per_depth[0] {
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

    // Perform the actual removals in the sub-block.
    if !inputs_to_remove.is_empty() || output_removed {
        let br_inputs_to_remove = (BlockKind::Block == *kind).then_some(outputs_to_remove);
        let (sub_output_removed, sub_loop_inputs_removed) = remove_block_node_io(
            node_idx,
            origin_substitutions,
            node,
            &inputs_to_remove,
            &mut VecDeque::from(vec![br_inputs_to_remove]),
        );
        output_removed |= sub_output_removed;
        loop_inputs_removed += sub_loop_inputs_removed;
    }

    BlockRemovals {
        removed_inputs: inputs_to_remove,
        loop_inputs_removed,
        output_removed,
        inputs_usage: sub_entry.input_usage,
    }
}

fn apply_substitutions(
    node_inputs: &mut [NodeInput],
    input_substitutions: &HashMap<ValueOrigin, Option<ValueOrigin>>,
) {
    for (input_idx, input) in node_inputs.iter_mut().enumerate() {
        if let NodeInput::Reference(origin) = input
            && let Some(subst) = input_substitutions.get(origin)
        {
            *origin = subst.unwrap_or_else(|| {
                panic!("Input {input_idx} was removed but is still needed: {origin:?}")
            });
        }
    }
}

fn remove_block_node_io(
    parent_node_idx: usize,
    parent_origin_substitutions: &mut HashMap<ValueOrigin, Option<ValueOrigin>>,
    block_node: &mut RedirNode,
    inputs_to_remove: &[u32],
    br_inputs_to_remove: &mut VecDeque<Option<Vec<u32>>>,
) -> (bool, usize) {
    let Operation::Block { sub_dag, kind } = &mut block_node.operation else {
        panic!()
    };

    let mut loop_inputs_removed = 0;
    let mut output_removed = false;

    // For a loop, the block inputs are also its break targets, so we need to mark the corresponding outputs as removed as well.
    if let BlockKind::Loop = kind {
        let br_inputs = &mut br_inputs_to_remove[0];
        assert!(br_inputs.is_none());
        // I couldn't avoid cloning here. I tried making `br_inputs_to_remove: &mut VecDeque<&[u32]>`,
        // but there is no lifetime that allows it to hold external references plus local references.
        *br_inputs = Some(inputs_to_remove.to_vec());
        loop_inputs_removed += inputs_to_remove.len();
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

                let mut parent_redir_map = vec![None; node.inputs.len()];
                for (sub_input_idx, parent_input_idx) in block_inputs(&node.inputs) {
                    parent_redir_map[sub_input_idx] = Some(parent_input_idx);
                    if inputs_to_remove.binary_search(&parent_input_idx).is_ok() {
                        sub_input_to_remove.push(sub_input_idx as u32);
                    }
                }

                // TODO: if we knew to what blocks the inner blocks can break to,
                // we could avoid recursing into blocks that are not affected by
                // the output removals.

                br_inputs_to_remove.push_front(None);
                let (sub_output_removed, sub_loop_inputs_removed) = remove_block_node_io(
                    node_idx,
                    &mut origin_substitutions,
                    node,
                    &sub_input_to_remove,
                    br_inputs_to_remove,
                );
                br_inputs_to_remove.pop_front();

                output_removed |= sub_output_removed;
                loop_inputs_removed += sub_loop_inputs_removed;
            }
            Operation::WASMOp(Op::Br { relative_depth }) => {
                rm_plain_br_inputs(
                    &mut node.inputs,
                    *relative_depth,
                    inputs_to_remove,
                    br_inputs_to_remove,
                );
            }
            Operation::WASMOp(Op::BrIf { relative_depth })
            | Operation::BrIfZero { relative_depth } => {
                // Temporarily take of the selector because it is not part of the break inputs
                let selector = node.inputs.pop().unwrap();
                rm_plain_br_inputs(
                    &mut node.inputs,
                    *relative_depth,
                    inputs_to_remove,
                    br_inputs_to_remove,
                );

                node.inputs.push(selector);
            }
            Operation::BrTable { targets } => {
                // BrTable is more complicated, because we need to update
                // the input permutation inside each of the targets.

                let selector = node.inputs.pop().unwrap();

                // First do the removals on all the targets.
                let mut slot_still_used = vec![false; node.inputs.len()];
                for t in targets.iter_mut() {
                    remove_break_inputs(
                        &mut t.input_permutation,
                        t.relative_depth,
                        inputs_to_remove,
                        br_inputs_to_remove,
                        |perm| {
                            let NodeInput::Reference(origin) = &node.inputs[*perm as usize] else {
                                unreachable!()
                            };
                            *origin
                        },
                    );

                    for perm in &t.input_permutation {
                        slot_still_used[*perm as usize] = true;
                    }
                }

                // Now we do the removal on the node inputs.
                let mut idx = 0..;
                let mut removed_indices: Vec<u32> = Vec::new();
                node.inputs.retain(|_| {
                    let idx = idx.next().unwrap();
                    if slot_still_used[idx] {
                        true
                    } else {
                        removed_indices.push(idx as u32);
                        false
                    }
                });

                // Apply the map for all the target input permutations.
                for t in targets {
                    for perm in &mut t.input_permutation {
                        *perm -= sorted_removals_offset(&removed_indices, perm) as u32;
                    }
                }

                // Restore the selector input.
                node.inputs.push(selector);
            }
            _ => {
                // Nothing special to do for other nodes.
            }
        }

        // Apply the substitutions for this node inputs.
        apply_substitutions(&mut node.inputs, &origin_substitutions);
    }

    // Update parent node inputs.
    remove_indices(
        &mut block_node.inputs,
        inputs_to_remove.iter().map(|&r| r as usize),
        |_, _| {},
    );

    // Update parent node outputs.
    if kind == &BlockKind::Block
        // If this block is never broken to, br_inputs_to_remove[0] will be None.
        && let Some(outputs_to_remove) = &br_inputs_to_remove[0]
    {
        output_removed |= !outputs_to_remove.is_empty();

        remove_indices(
            &mut block_node.output_types,
            outputs_to_remove.iter().map(|r| *r as usize),
            |old_idx, new_idx| {
                if let Some(new_idx) = new_idx {
                    // This output was shifted, needs to be mapped to the new index.
                    parent_origin_substitutions.insert(
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
    }

    // Update node redirections.
    let redirections = &mut sub_dag.block_data;
    let redirs_to_remove = match kind {
        BlockKind::Loop => inputs_to_remove,
        BlockKind::Block => br_inputs_to_remove[0].as_ref().map_or(&[][..], |v| &v[..]),
    };
    remove_indices(
        redirections,
        redirs_to_remove.iter().map(|&r| r as usize),
        |_, _| {},
    );
    // Removing is not enough, we also need to update the indices in the remaining redirections.
    for redir in redirections.iter_mut() {
        if let Redirection::FromInput(input_idx) = redir {
            *input_idx -= sorted_removals_offset(redirs_to_remove, input_idx) as u32;
        }
    }

    (output_removed, loop_inputs_removed)
}

fn rm_plain_br_inputs(
    node_inputs: &mut Vec<NodeInput>,
    relative_depth: u32,
    block_ins_to_remove: &[u32],
    br_ins_to_remove: &mut VecDeque<Option<Vec<u32>>>,
) {
    remove_break_inputs(
        node_inputs,
        relative_depth,
        block_ins_to_remove,
        br_ins_to_remove,
        |input| {
            let NodeInput::Reference(origin) = input else {
                unreachable!()
            };
            *origin
        },
    );
}

fn remove_break_inputs<T: Debug>(
    node_inputs: &mut Vec<T>,
    relative_depth: u32,
    block_ins_to_remove: &[u32],
    br_ins_to_remove: &mut VecDeque<Option<Vec<u32>>>,
    to_origin: impl Fn(&T) -> ValueOrigin,
) {
    if let Some(br_ins_to_remove) = br_ins_to_remove.get_mut(relative_depth as usize) {
        if let Some(br_ins_to_remove) = br_ins_to_remove {
            // If we have specified what break inputs to remove, apply them.
            remove_indices(
                node_inputs,
                br_ins_to_remove.iter().map(|x| *x as usize),
                |_, _| {},
            );
        } else {
            // The break inputs to remove are not yet known. We need to calculate them
            // from the removed block inputs.
            let mut slot_idx = 0..;
            let mut to_remove = Vec::new();
            node_inputs.retain(|origin| {
                let slot_idx = slot_idx.next().unwrap();
                if let ValueOrigin {
                    node: 0,
                    output_idx,
                } = to_origin(origin)
                    && block_ins_to_remove.binary_search(&output_idx).is_ok()
                {
                    to_remove.push(slot_idx);
                    false
                } else {
                    true
                }
            });
            *br_ins_to_remove = Some(to_remove);
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

#[cfg(test)]
mod tests {
    use super::prune_block_io;
    use crate::loader::{
        BlockKind,
        passes::{
            calc_input_redirection::{RedirDag, RedirNode, Redirection},
            dag::{BrTableTarget, GenericDag, GenericNode, NodeInput, Operation, ValueOrigin},
        },
    };
    use wasmparser::{Operator as Op, ValType};

    fn input_ref(node: usize, output_idx: u32) -> NodeInput {
        NodeInput::Reference(ValueOrigin::new(node, output_idx))
    }

    /// Assert that `input` is a `Reference` pointing to `(node, output_idx)`.
    fn assert_ref(input: &NodeInput, node: usize, output_idx: u32) {
        match input {
            NodeInput::Reference(origin) => {
                assert_eq!(origin.node, node, "wrong node index");
                assert_eq!(origin.output_idx, output_idx, "wrong output_idx");
            }
            other => panic!("expected Reference({node}, {output_idx}), got {other:?}"),
        }
    }

    fn inputs_node(types: Vec<ValType>) -> RedirNode<'static> {
        GenericNode {
            operation: Operation::Inputs,
            inputs: vec![],
            output_types: types,
        }
    }

    fn br_node(depth: u32, inputs: Vec<NodeInput>) -> RedirNode<'static> {
        GenericNode {
            operation: Operation::WASMOp(Op::Br {
                relative_depth: depth,
            }),
            inputs,
            output_types: vec![],
        }
    }

    fn wasm_op_node(
        op: Op<'static>,
        inputs: Vec<NodeInput>,
        output_types: Vec<ValType>,
    ) -> RedirNode<'static> {
        GenericNode {
            operation: Operation::WASMOp(op),
            inputs,
            output_types,
        }
    }

    fn block_node<'a>(
        inputs: Vec<NodeInput>,
        output_types: Vec<ValType>,
        sub_dag: RedirDag<'a>,
    ) -> RedirNode<'a> {
        GenericNode {
            operation: Operation::Block {
                kind: BlockKind::Block,
                sub_dag,
            },
            inputs,
            output_types,
        }
    }

    fn loop_node<'a>(
        inputs: Vec<NodeInput>,
        output_types: Vec<ValType>,
        sub_dag: RedirDag<'a>,
    ) -> RedirNode<'a> {
        GenericNode {
            operation: Operation::Block {
                kind: BlockKind::Loop,
                sub_dag,
            },
            inputs,
            output_types,
        }
    }

    fn redir_dag(
        nodes: Vec<RedirNode<'static>>,
        block_data: Vec<Redirection>,
    ) -> RedirDag<'static> {
        GenericDag { nodes, block_data }
    }

    fn br_table_node<'a>(
        break_inputs: Vec<NodeInput>,
        selector: NodeInput,
        targets: Vec<BrTableTarget>,
    ) -> RedirNode<'a> {
        let mut inputs = break_inputs;
        inputs.push(selector);
        GenericNode {
            operation: Operation::BrTable { targets },
            inputs,
            output_types: vec![],
        }
    }

    /// An input that is never referenced inside a plain block is removed.
    #[test]
    fn test_unused_block_input_removed() {
        // Function: takes i32, returns nothing.
        // Block: receives the i32 but never uses it; exits immediately.
        let sub_dag = redir_dag(
            vec![inputs_node(vec![ValType::I32]), br_node(0, vec![])],
            vec![],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),
                block_node(vec![input_ref(0, 0)], vec![], sub_dag),
                br_node(0, vec![]),
            ],
            vec![],
        );

        let loop_inputs_removed = prune_block_io(&mut dag);

        assert_eq!(loop_inputs_removed, 0);
        assert!(
            dag.nodes[1].inputs.is_empty(),
            "block input should be removed"
        );
        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        assert!(
            sub_dag.nodes[0].output_types.is_empty(),
            "Inputs node should have no outputs"
        );
        assert!(
            sub_dag.block_data.is_empty(),
            "block_data should remain empty"
        );
    }

    /// A plain-block output that is always equal to an input (FromInput) is
    /// removed, its consumers are redirected to the original source, and the
    /// input that only fed that output is also removed.
    #[test]
    fn test_forwarded_output_removed() {
        // Function: takes i32, returns i32 (via block pass-through).
        // Block output 0 = FromInput(0): always equals block input 0.
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),
                br_node(0, vec![input_ref(0, 0)]), // pass input through
            ],
            vec![Redirection::FromInput(0)],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),
                block_node(vec![input_ref(0, 0)], vec![ValType::I32], sub_dag),
                br_node(0, vec![input_ref(1, 0)]), // function return: consumes block output 0
            ],
            vec![Redirection::NotRedirected],
        );

        prune_block_io(&mut dag);

        assert!(
            dag.nodes[1].inputs.is_empty(),
            "block input should be removed"
        );
        assert!(
            dag.nodes[1].output_types.is_empty(),
            "block output should be removed"
        );
        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        assert!(sub_dag.nodes[0].output_types.is_empty());
        assert!(
            sub_dag.nodes[1].inputs.is_empty(),
            "br inside block should have no inputs"
        );
        assert!(
            sub_dag.block_data.is_empty(),
            "block_data should be trimmed to empty"
        );
        // Consumer (function return) should now reference the function input directly.
        assert_ref(&dag.nodes[2].inputs[0], 0, 0);
    }

    /// In a block with two outputs — one computed, one forwarded from an input —
    /// only the forwarded output and its corresponding input are removed.
    /// The computed output and its input are kept. Consumers of the removed
    /// output are redirected to the original source.
    #[test]
    fn test_mixed_block_partial_removal() {
        // Function: takes i32 X (index 0) and i32 Y (index 1), returns two i32s.
        // Block inputs: X, Y.
        // Block outputs:
        //   slot 0: i32.eqz(X)  — computed, NotRedirected
        //   slot 1: Y           — FromInput(1), will be removed
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]),
                wasm_op_node(Op::I32Eqz, vec![input_ref(0, 0)], vec![ValType::I32]), // uses X only
                br_node(0, vec![input_ref(1, 0), input_ref(0, 1)]), // output 0 = eqz(X), output 1 = Y
            ],
            vec![Redirection::NotRedirected, Redirection::FromInput(1)],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]),
                block_node(
                    vec![input_ref(0, 0), input_ref(0, 1)],
                    vec![ValType::I32, ValType::I32],
                    sub_dag,
                ),
                br_node(0, vec![input_ref(1, 0), input_ref(1, 1)]), // function return: both block outputs
            ],
            vec![Redirection::NotRedirected, Redirection::NotRedirected],
        );

        prune_block_io(&mut dag);

        assert_eq!(
            dag.nodes[1].inputs.len(),
            1,
            "only X should remain as block input"
        );
        assert_ref(&dag.nodes[1].inputs[0], 0, 0); // X is still function input 0
        assert_eq!(
            dag.nodes[1].output_types.len(),
            1,
            "only computed output should remain"
        );
        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        // One NotRedirected entry should remain in block_data (slot 0 = eqz(X)).
        assert_eq!(sub_dag.block_data.len(), 1);
        assert_eq!(sub_dag.block_data[0], Redirection::NotRedirected);
        // Consumer of output 0 (computed): still references block output 0.
        assert_ref(&dag.nodes[2].inputs[0], 1, 0);
        // Consumer of output 1 (forwarded Y): redirected to function input 1.
        assert_ref(&dag.nodes[2].inputs[1], 0, 1);
    }

    /// Loop inputs that only pass values around in a cycle — never used by any
    /// computation and never escaping to the outer scope — are all removed.
    ///
    /// The sub_dag block_data for a loop is indexed by back-edge slot:
    ///   redirections[i] = FromInput(j)  means slot i of the back-edge always
    ///   receives loop input j.
    #[test]
    fn test_loop_dead_cycle_all_removed() {
        // Loop inputs: A (index 0), B (index 1).
        // Back-edge swaps them: slot 0 ← B, slot 1 ← A.
        // Neither is used in any computation. Both are removable.
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]),
                br_node(0, vec![input_ref(0, 1), input_ref(0, 0)]), // slot 0 ← B (input 1), slot 1 ← A (input 0)
            ],
            vec![Redirection::FromInput(1), Redirection::FromInput(0)],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]),
                loop_node(vec![input_ref(0, 0), input_ref(0, 1)], vec![], sub_dag),
            ],
            vec![],
        );

        let loop_inputs_removed = prune_block_io(&mut dag);

        assert_eq!(loop_inputs_removed, 2, "both loop inputs should be removed");
        assert!(
            dag.nodes[1].inputs.is_empty(),
            "loop node should have no remaining inputs"
        );
        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        assert!(
            sub_dag.nodes[0].output_types.is_empty(),
            "Inputs node should have no outputs"
        );
        assert!(
            sub_dag.nodes[1].inputs.is_empty(),
            "back-edge should have no inputs"
        );
        assert!(
            sub_dag.block_data.is_empty(),
            "loop redirections should be empty"
        );
    }

    /// When at least one loop input is genuinely used in a computation, the BFS
    /// propagates that constraint backwards through the cycle and prevents every
    /// input from being removed.
    #[test]
    fn test_loop_cycle_with_used_input_nothing_removed() {
        // Same swapping loop as above, but input A (index 0) is also consumed
        // by i32.eqz. BFS seeds No from A, propagates it to B. Nothing removed.
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]),
                wasm_op_node(Op::I32Eqz, vec![input_ref(0, 0)], vec![ValType::I32]), // uses A
                br_node(0, vec![input_ref(0, 1), input_ref(0, 0)]), // back-edge: slot 0 ← B, slot 1 ← A
            ],
            vec![Redirection::FromInput(1), Redirection::FromInput(0)],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]),
                loop_node(vec![input_ref(0, 0), input_ref(0, 1)], vec![], sub_dag),
            ],
            vec![],
        );

        let loop_inputs_removed = prune_block_io(&mut dag);

        assert_eq!(loop_inputs_removed, 0, "no loop inputs should be removed");
        assert_eq!(
            dag.nodes[1].inputs.len(),
            2,
            "loop should still have 2 inputs"
        );
        assert_ref(&dag.nodes[1].inputs[0], 0, 0); // A
        assert_ref(&dag.nodes[1].inputs[1], 0, 1); // B
        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        assert_eq!(
            sub_dag.nodes[0].output_types.len(),
            2,
            "both Inputs outputs should remain"
        );
        assert_eq!(
            sub_dag.block_data.len(),
            2,
            "loop block_data should be unchanged"
        );
    }

    /// When an inner block's only input is passed straight through as its output
    /// (FromInput), the inner block's I/O is removed. This makes the outer block's
    /// corresponding input entirely unused, so it is also removed — all in a single
    /// outer-loop iteration via cross-level usage propagation.
    #[test]
    fn test_nested_block_input_propagated_removal() {
        // Outer block: inputs A (index 0) and B (index 1).
        //   - A is used by i32.eqz inside the outer block → kept.
        //   - B is only passed to the inner block as its sole input → removable once
        //     the inner block is cleaned.
        // Inner block: sole input = B, sole output = FromInput(0) = B.
        //   The inner block output is not consumed by anything else,
        //   so it is removed along with its input.
        let inner_sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),   // Node 0: B
                br_node(0, vec![input_ref(0, 0)]), // Node 1: pass B as output slot 0
            ],
            vec![Redirection::FromInput(0)], // output 0 = always its input B
        );
        let outer_sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]), // Node 0: A, B
                wasm_op_node(Op::I32Eqz, vec![input_ref(0, 0)], vec![ValType::I32]), // Node 1: eqz(A)
                block_node(
                    // Node 2: inner block
                    vec![input_ref(0, 1)], // input: B
                    vec![ValType::I32],    // output: one i32 (will be removed)
                    inner_sub_dag,
                ),
                br_node(0, vec![input_ref(1, 0)]), // Node 3: break with eqz(A) as outer block's output
            ],
            vec![Redirection::NotRedirected], // outer block's one output is computed, not redirected
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]), // Node 0: function inputs A, B
                block_node(
                    vec![input_ref(0, 0), input_ref(0, 1)], // pass A and B into outer block
                    vec![ValType::I32],                     // outer block produces one i32
                    outer_sub_dag,
                ),
                br_node(0, vec![input_ref(1, 0)]), // Node 2: function return = outer block output 0
            ],
            vec![Redirection::NotRedirected],
        );

        let loop_inputs_removed = prune_block_io(&mut dag);

        assert_eq!(loop_inputs_removed, 0);

        // Outer block: B (index 1) should be removed, only A remains.
        assert_eq!(
            dag.nodes[1].inputs.len(),
            1,
            "only A should remain as outer block input"
        );
        assert_ref(&dag.nodes[1].inputs[0], 0, 0); // still A
        assert_eq!(
            dag.nodes[1].output_types.len(),
            1,
            "outer block output unchanged"
        );

        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };

        // Outer sub_dag Inputs: only A's slot should remain.
        assert_eq!(
            sub_dag.nodes[0].output_types.len(),
            1,
            "only A in Inputs node"
        );

        // Inner block node (sub_dag.nodes[2]): no inputs, no outputs.
        assert!(
            sub_dag.nodes[2].inputs.is_empty(),
            "inner block inputs cleared"
        );
        assert!(
            sub_dag.nodes[2].output_types.is_empty(),
            "inner block outputs cleared"
        );

        // Inner block's own sub_dag should be fully empty.
        let Operation::Block {
            sub_dag: ref inner_sub_dag,
            ..
        } = sub_dag.nodes[2].operation
        else {
            panic!()
        };
        assert!(
            inner_sub_dag.nodes[0].output_types.is_empty(),
            "inner Inputs node is empty"
        );
        assert!(
            inner_sub_dag.nodes[1].inputs.is_empty(),
            "inner Br has no inputs"
        );

        // Function return is unchanged.
        assert_ref(&dag.nodes[2].inputs[0], 1, 0);
    }

    /// Two sequential plain blocks, B1 and B2, each forwarding their sole input as
    /// their sole output (FromInput). B2's input is B1's output. The inline
    /// substitution mechanism applies B1's output removal before B2 is even
    /// analysed, so B2 is cleaned in the same outer-loop iteration. The function
    /// return ends up pointing straight at the original function input.
    #[test]
    fn test_chained_output_substitution() {
        // B1: input=A (function input 0), output=FromInput(0)=A.
        let b1_sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),   // Node 0: A
                br_node(0, vec![input_ref(0, 0)]), // Node 1: pass A to output slot 0
            ],
            vec![Redirection::FromInput(0)],
        );
        // B2: input=B1's output 0, output=FromInput(0)=its input.
        let b2_sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),   // Node 0: B2's input
                br_node(0, vec![input_ref(0, 0)]), // Node 1: pass input to output slot 0
            ],
            vec![Redirection::FromInput(0)],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]), // Node 0: function input A
                block_node(vec![input_ref(0, 0)], vec![ValType::I32], b1_sub_dag), // Node 1: B1
                block_node(vec![input_ref(1, 0)], vec![ValType::I32], b2_sub_dag), // Node 2: B2
                br_node(0, vec![input_ref(2, 0)]), // Node 3: function return = B2 output 0
            ],
            vec![Redirection::NotRedirected],
        );

        let loop_inputs_removed = prune_block_io(&mut dag);

        assert_eq!(loop_inputs_removed, 0);

        // Both blocks should be fully cleaned.
        assert!(dag.nodes[1].inputs.is_empty(), "B1 should have no inputs");
        assert!(
            dag.nodes[1].output_types.is_empty(),
            "B1 should have no outputs"
        );
        assert!(dag.nodes[2].inputs.is_empty(), "B2 should have no inputs");
        assert!(
            dag.nodes[2].output_types.is_empty(),
            "B2 should have no outputs"
        );

        // Inner sub-dags should be fully cleaned too.
        let Operation::Block {
            sub_dag: ref b1_sub,
            ..
        } = dag.nodes[1].operation
        else {
            panic!()
        };
        assert!(b1_sub.nodes[0].output_types.is_empty());
        assert!(b1_sub.nodes[1].inputs.is_empty());
        assert!(b1_sub.block_data.is_empty());
        let Operation::Block {
            sub_dag: ref b2_sub,
            ..
        } = dag.nodes[2].operation
        else {
            panic!()
        };
        assert!(b2_sub.nodes[0].output_types.is_empty());
        assert!(b2_sub.nodes[1].inputs.is_empty());
        assert!(b2_sub.block_data.is_empty());

        // Function return should now reference the original function input directly.
        assert_eq!(dag.nodes[3].inputs.len(), 1);
        assert_ref(&dag.nodes[3].inputs[0], 0, 0);
    }

    /// A BrTable inside a plain block has two targets with permutations [0,1,2] and
    /// [2,1,0]. The block's middle output slot (index 1) is always equal to block
    /// input B (FromInput(1)), so it is shortcircuited. The corresponding permutation
    /// entry (index 1) is removed from every target, and B — no longer referenced by
    /// any target — is pruned from the BrTable's node inputs. Permutation indices are
    /// renumbered after the removal.
    #[test]
    fn test_br_table_partial_target_overlap() {
        // Block: inputs A (0), B (1), C (2); outputs: [NotRedirected, FromInput(1), NotRedirected].
        // BrTable break_inputs = [A, B, C]; selector = A (making A "Used").
        // Target 0: perm [0,1,2] → slot0=A, slot1=B, slot2=C.
        // Target 1: perm [2,1,0] → slot0=C, slot1=B, slot2=A.
        // Both send B to slot 1, confirming FromInput(1).
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32, ValType::I32]), // Node 0: A, B, C
                br_table_node(
                    vec![input_ref(0, 0), input_ref(0, 1), input_ref(0, 2)], // break inputs: A, B, C
                    input_ref(0, 0), // selector = A (marks A as Used)
                    vec![
                        BrTableTarget {
                            relative_depth: 0,
                            input_permutation: vec![0, 1, 2],
                        },
                        BrTableTarget {
                            relative_depth: 0,
                            input_permutation: vec![2, 1, 0],
                        },
                    ],
                ),
            ],
            vec![
                Redirection::NotRedirected,
                Redirection::FromInput(1),
                Redirection::NotRedirected,
            ],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32, ValType::I32]), // Node 0: A, B, C
                block_node(
                    vec![input_ref(0, 0), input_ref(0, 1), input_ref(0, 2)],
                    vec![ValType::I32, ValType::I32, ValType::I32],
                    sub_dag,
                ),
                br_node(0, vec![input_ref(1, 0), input_ref(1, 1), input_ref(1, 2)]), // function return: all 3 block outputs
            ],
            vec![
                Redirection::NotRedirected,
                Redirection::NotRedirected,
                Redirection::NotRedirected,
            ],
        );

        prune_block_io(&mut dag);

        // Block input B (index 1) should be removed; A and C remain.
        assert_eq!(
            dag.nodes[1].inputs.len(),
            2,
            "A and C remain as block inputs"
        );
        assert_ref(&dag.nodes[1].inputs[0], 0, 0); // A
        assert_ref(&dag.nodes[1].inputs[1], 0, 2); // C

        // Block output slot 1 should be removed; 2 outputs remain.
        assert_eq!(dag.nodes[1].output_types.len(), 2);

        // Consumer of old output 1 (B) is redirected to function input B.
        // Consumer of old output 2 (C-or-A) has its index shifted from 2 to 1.
        assert_ref(&dag.nodes[2].inputs[0], 1, 0); // block output 0 unchanged
        assert_ref(&dag.nodes[2].inputs[1], 0, 1); // redirected to function input B
        assert_ref(&dag.nodes[2].inputs[2], 1, 1); // block output 2 shifted to slot 1

        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };

        // Inputs node inside block: B's slot removed, 2 remain.
        assert_eq!(sub_dag.nodes[0].output_types.len(), 2);

        // BrTable node: break_inputs become [A, C_shifted]; selector unchanged.
        assert_eq!(
            sub_dag.nodes[1].inputs.len(),
            3,
            "two break inputs + selector"
        );
        assert_ref(&sub_dag.nodes[1].inputs[0], 0, 0); // A (break input 0)
        assert_ref(&sub_dag.nodes[1].inputs[1], 0, 1); // C (shifted from r(0,2) → r(0,1))
        assert_ref(&sub_dag.nodes[1].inputs[2], 0, 0); // selector = A

        // Permutations after removal of slot 1 and re-indexing.
        let Operation::BrTable { ref targets } = sub_dag.nodes[1].operation else {
            panic!()
        };
        assert_eq!(targets[0].input_permutation, vec![0u32, 1u32]); // was [0,2], C now at index 1
        assert_eq!(targets[1].input_permutation, vec![1u32, 0u32]); // was [2,0], C now at index 1
    }

    /// A BrIf whose break input is removed must keep its selector (condition) intact
    /// as the sole remaining input, at the last position.
    ///
    /// The BrIf node has the form: [...break_inputs, selector] (selector is last).
    /// When the block output the break targets is shortcircuited (FromInput), the
    /// break input feeding it is removed. The selector must survive the removal
    /// unchanged and remain the last (and here, only) input.
    #[test]
    fn test_br_if_selector_preserved_when_break_input_pruned() {
        // Block: inputs A (0) and B (1); one output = A = FromInput(0).
        // BrIf: break input = A (slot 0), selector = B (last input).
        //   → A is removable (only forwarded to the shortcircuited output).
        //   → B is Used (it is the selector, treated as a normal node input).
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]), // Node 0: A, B
                GenericNode {
                    operation: Operation::WASMOp(Op::BrIf { relative_depth: 0 }),
                    inputs: vec![input_ref(0, 0), input_ref(0, 1)], // [break=A, selector=B]
                    output_types: vec![],
                },
            ],
            vec![Redirection::FromInput(0)], // output 0 = A
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]), // Node 0: A, B
                block_node(
                    vec![input_ref(0, 0), input_ref(0, 1)],
                    vec![ValType::I32],
                    sub_dag,
                ),
                br_node(0, vec![input_ref(1, 0)]), // function return = block output 0
            ],
            vec![Redirection::NotRedirected],
        );

        prune_block_io(&mut dag);

        // Block: A removed, only B remains as input; output removed.
        assert_eq!(dag.nodes[1].inputs.len(), 1, "only B should remain");
        assert_ref(&dag.nodes[1].inputs[0], 0, 1); // B
        assert!(dag.nodes[1].output_types.is_empty(), "output removed");

        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        assert!(sub_dag.block_data.is_empty());

        // BrIf: break input A removed; selector B survives as the sole input.
        // After B shifts from index 1 to index 0 in the Inputs node, B is r(0,0).
        assert_eq!(
            sub_dag.nodes[1].inputs.len(),
            1,
            "only the selector should remain"
        );
        assert_ref(&sub_dag.nodes[1].inputs[0], 0, 0); // B (shifted from r(0,1) to r(0,0))

        // Consumer of the removed output is redirected to function input A.
        assert_ref(&dag.nodes[2].inputs[0], 0, 0); // A
    }

    /// A break at relative_depth > 0 that targets an outer block's output slot lives
    /// inside a nested block. When the outer block's output is shortcircuited, the
    /// break input in the *inner* block is removed by the correct VecDeque depth
    /// entry in `br_inputs_to_remove`.
    #[test]
    fn test_nested_relative_depth_break_removal() {
        // Outer block: one input A, one output = A = FromInput(0).
        // Inside outer block: an inner block whose only content is a Br at depth=1
        // (targeting the outer block) that passes A as the single output value.
        // After pruning: output shortcircuited, A removed, Br at depth=1 emptied.
        let inner_sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),   // Node 0: A (inner block's input)
                br_node(1, vec![input_ref(0, 0)]), // Node 1: Br depth=1, passes A to outer output slot 0
            ],
            vec![], // inner block has no outputs of its own
        );
        let outer_sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]), // Node 0: A
                block_node(
                    // Node 1: inner block
                    vec![input_ref(0, 0)], // passes A in
                    vec![],
                    inner_sub_dag,
                ),
            ],
            vec![Redirection::FromInput(0)], // outer block's output 0 = always A
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]), // Node 0: function input A
                block_node(vec![input_ref(0, 0)], vec![ValType::I32], outer_sub_dag),
                br_node(0, vec![input_ref(1, 0)]), // Node 2: function return = outer block output 0
            ],
            vec![Redirection::NotRedirected],
        );

        prune_block_io(&mut dag);

        // Outer block fully cleaned.
        assert!(dag.nodes[1].inputs.is_empty());
        assert!(dag.nodes[1].output_types.is_empty());

        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        assert!(sub_dag.nodes[0].output_types.is_empty()); // Inputs node: A removed
        assert!(sub_dag.nodes[1].inputs.is_empty()); // inner block: no inputs
        assert!(sub_dag.nodes[1].output_types.is_empty()); // inner block: no outputs

        // Inner block's Br at depth=1 should have had its input removed.
        let Operation::Block {
            sub_dag: ref inner_sub,
            ..
        } = sub_dag.nodes[1].operation
        else {
            panic!()
        };
        assert!(inner_sub.nodes[0].output_types.is_empty()); // inner Inputs node: A removed
        assert!(
            inner_sub.nodes[1].inputs.is_empty(),
            "Br at depth=1 should have no inputs"
        );

        // Function return redirected to A directly.
        assert_ref(&dag.nodes[2].inputs[0], 0, 0);
    }

    /// In a loop with three inputs where two form a dead cycle and the third is
    /// genuinely used, only the dead-cycle inputs are removed. BFS from the used
    /// input does not propagate into the independent cycle.
    #[test]
    fn test_loop_partial_cycle_prunes_only_disconnected_component() {
        // Loop inputs: A (0), B (1), C (2).
        // Back-edge: slot 0 ← B (FromInput(1)), slot 1 ← A (FromInput(0)),
        //            slot 2 ← C (FromInput(2)).
        // A and B swap each other each iteration and are never used → removable.
        // C is consumed by i32.eqz → Not removable; BFS from C does not reach A or B.
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32, ValType::I32]),
                wasm_op_node(Op::I32Eqz, vec![input_ref(0, 2)], vec![ValType::I32]), // uses C
                // back-edge: [B, A, C] — slot 0←B, slot 1←A, slot 2←C
                br_node(0, vec![input_ref(0, 1), input_ref(0, 0), input_ref(0, 2)]),
            ],
            vec![
                Redirection::FromInput(1), // slot 0 ← B
                Redirection::FromInput(0), // slot 1 ← A
                Redirection::FromInput(2), // slot 2 ← C
            ],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32, ValType::I32]),
                loop_node(
                    vec![input_ref(0, 0), input_ref(0, 1), input_ref(0, 2)],
                    vec![],
                    sub_dag,
                ),
            ],
            vec![],
        );

        let loop_inputs_removed = prune_block_io(&mut dag);

        assert_eq!(loop_inputs_removed, 2, "A and B should be removed");

        // Loop node: only C remains as input.
        assert_eq!(dag.nodes[1].inputs.len(), 1);
        assert_ref(&dag.nodes[1].inputs[0], 0, 2); // C (still references function input 2)

        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };

        // Inputs node: only C's slot remains.
        assert_eq!(sub_dag.nodes[0].output_types.len(), 1);

        // WASMOp: still references C, now shifted to index 0.
        assert_eq!(sub_dag.nodes[1].inputs.len(), 1);
        assert_ref(&sub_dag.nodes[1].inputs[0], 0, 0); // C shifted to r(0,0)

        // Back-edge: only C remains, shifted to r(0,0).
        assert_eq!(sub_dag.nodes[2].inputs.len(), 1);
        assert_ref(&sub_dag.nodes[2].inputs[0], 0, 0); // C shifted

        // block_data: only C's entry remains, re-indexed to FromInput(0).
        assert_eq!(sub_dag.block_data.len(), 1);
        assert_eq!(sub_dag.block_data[0], Redirection::FromInput(0));
    }
}
