//! This module does the infinite, write-once register allocation.
//!
//! The algorithm requires multiple passes, and goes like this:
//!
//! Pass #1: for each DAG/frame, we do a bottom-up traversal,
//! assigning registers to the labels outputs, matching with their
//! respective break inputs, and detect whether or not there is a
//! conflict, where multiple instructions would write to the same
//! register in the same execution path. In the end, we will have a
//! partial register assignment for some nodes, where conflicts for
//! break inputs are explicitly marked.
//!
//! Pass #2: we will do a top-down traversal of the DAG, completing
//! the register assignment for the node outputs that were not
//! assigned (included the ones that triggered a conflict in the
//! previous pass). When we encounter a break, we copy the correct
//! output to the conflicted register just before the break. Since
//! the conflict was detected per execution path, we can be sure that
//! no register will be written to more than once in the same path.
//! If a break output was not conflicted, we can be sure that the
//! correct value is already in the expected register.
//!
//! TODO: this is still not perfectly optimal, since there might be
//! permutations of register assignments through different execution
//! paths that would avoid the need for some copies.
//!
//! Pass #3: we flatten all the DAGs, loops included, into a single
//! assembly-like representation.

use itertools::Itertools;
use std::{
    collections::{HashMap, HashSet, hash_map::Entry},
    marker::PhantomData,
    ops::RangeFrom,
};
use wasmparser::Operator as Op;

use crate::loader::{
    blockless_dag::{BreakTarget, TargetType},
    dag::ValueOrigin,
};

use super::blockless_dag::{BlocklessDag, Operation};

/// An assembly-like representation for a write-once memory machine.
pub struct WriteOnceASM<'a> {
    _a: PhantomData<&'a ()>,
}

pub fn allocate_registers<'a>(dag: BlocklessDag<'a>) -> WriteOnceASM<'a> {
    println!("dag:\n{:#?}", dag);
    todo!()
}

/// Implementation of pass #1: fixes the expected register assignments
/// for labels outputs, and optimistically tries to assign these same
/// registers to the inputs of the breaks, reverting in case of conflict.
///
/// The allocation is just one unique number per value, not considering
/// the actual size of the value.
fn optimistic_break_allocation<'a>(dag: &BlocklessDag<'a>, free_values: RangeFrom<u32>) {
    struct LabelAllocation {
        node_idx: usize,
        regs: Vec<u32>,
        path_below_it: PerPathData,
    }

    let mut labels: HashMap<u32, LabelAllocation> = HashMap::new();

    #[derive(Clone)]
    struct PerPathData {
        free_values: RangeFrom<u32>,
        writers: HashMap<u32, Vec<ValueOrigin>>,
        conflicted: HashSet<u32>,
    }

    impl PerPathData {
        fn merge(&mut self, other: &Self) {
            if other.free_values.start > self.free_values.start {
                self.free_values = other.free_values.clone();
            }

            self.conflicted.extend(other.conflicted.iter());

            let self_writers = std::mem::take(&mut self.writers);
            for (reg, writers) in self_writers.iter().chain(other.writers.iter()) {
                if self.conflicted.contains(reg) {
                    continue;
                }
                self.writers
                    .entry(*reg)
                    .or_default()
                    .extend_from_slice(writers);
            }
        }
    }

    let new_path = || PerPathData {
        free_values: free_values.clone(),
        writers: HashMap::new(),
        conflicted: HashSet::new(),
    };

    fn merge_path_from_target<'a>(
        active_path: &mut PerPathData,
        target: &BreakTarget,
        labels: &'a mut HashMap<u32, LabelAllocation>,
    ) -> Option<&'a LabelAllocation> {
        let target_label: &LabelAllocation = match target {
            BreakTarget {
                depth: 0,
                kind: TargetType::Label(label),
            } => &labels[label],
            _ => {
                // This is not a local label jump, there is nothing to merge.
                return None;
            }
        };

        active_path.merge(&target_label.path_below_it);

        Some(target_label)
    }

    fn handle_break(
        active_path: &mut PerPathData,
        target: &BreakTarget,
        labels: &mut HashMap<u32, LabelAllocation>,
        inputs: &[ValueOrigin],
    ) {
        // First, we merge the path from the target label
        let Some(target_label) = merge_path_from_target(active_path, target, labels) else {
            return;
        };

        // Now we must assign the expected registers to all
        // the inputs of the break, and undo if there is a conflict.
        for (input_idx, reg) in target_label.regs.iter().enumerate() {
            if active_path.conflicted.contains(reg) {
                continue;
            }
            let writers = active_path.writers.entry(*reg);
            match writers {
                Entry::Occupied(entry) => {
                    let writers = entry.get();
                    assert!(!writers.is_empty());
                    if !writers.contains(&inputs[input_idx]) {
                        // Conflict detected, we must revert the assignment and mark the conflict
                        // for this register.
                        entry.remove_entry();
                        active_path.conflicted.insert(*reg);
                    }
                }
                Entry::Vacant(entry) => {
                    // No conflict, we can assign the register to the input
                    entry.insert(vec![inputs[input_idx]]);
                }
            }
        }
    }

    let mut active_path = new_path();

    for (node_idx, node) in dag.nodes.iter().enumerate().rev() {
        match &node.operation {
            Operation::Label { id } => {
                let regs = active_path
                    .free_values
                    .by_ref()
                    .take(node.output_types.len())
                    .collect();

                labels.insert(
                    *id,
                    LabelAllocation {
                        node_idx,
                        regs,
                        path_below_it: active_path.clone(),
                    },
                );
            }
            Operation::WASMOp(Op::Unreachable) => {
                // Unreachable simply resets the path
                active_path = new_path();
            }
            Operation::Br(target) => {
                // Like unreachable, this instruction can not fall through,
                // so we can reset the path.
                active_path = new_path();
                handle_break(&mut active_path, target, &mut labels, &node.inputs);
            }
            Operation::BrIf(target) | Operation::BrIfZero(target) => {
                // These instructions can fall through, so we must
                // keep the current path.
                handle_break(&mut active_path, target, &mut labels, &node.inputs);
            }
            Operation::BrTable { targets } => {
                // This instruction can not fall through, so we must
                // keep the current path.
                active_path = new_path();
                for target in targets {
                    let inputs = target
                        .input_permutation
                        .iter()
                        .map(|input_idx| node.inputs[*input_idx as usize])
                        .collect_vec();
                    handle_break(&mut active_path, &target.target, &mut labels, &inputs);
                }
            }
            Operation::Loop { break_targets, .. } => {
                // A loop can not fall through, but the source of the break inputs
                // comes from another frame, so we just need reset and merge the paths.
                active_path = new_path();
                for target in break_targets {
                    merge_path_from_target(&mut active_path, target, &mut labels);
                }
            }
            _ => {}
        }
    }
}
