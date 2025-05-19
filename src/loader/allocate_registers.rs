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
    collections::{HashMap, hash_map::Entry},
    marker::PhantomData,
    ops::{Range, RangeFrom},
};
use wasmparser::{Operator as Op, ValType};

use crate::loader::{
    blockless_dag::{BreakTarget, TargetType},
    dag::ValueOrigin,
};

use super::blockless_dag::{BlocklessDag, Operation};

/// An assembly-like representation for a write-once memory machine.
pub struct WriteOnceASM<'a> {
    _a: PhantomData<&'a ()>,
}

pub fn allocate_registers<'a>(dag: BlocklessDag<'a>, bytes_per_word: u32) -> WriteOnceASM<'a> {
    let mut free_values = 0u32..;
    let toplevel_allocations = optimistic_allocation(&dag, free_values, bytes_per_word);
    todo!()
}

#[derive(Default, Clone)]
struct AssignmentSet {
    /// Empty writers Vec means that the register is reserved to be written on demand,
    /// so it can not be used for any more writers.
    reg_to_writers: HashMap<u32, Vec<ValueOrigin>>,
    /// A single writer can write to multiple contiguous registers, depending on its
    /// output types.
    writer_to_regs: HashMap<ValueOrigin, Range<u32>>,
}

impl AssignmentSet {
    fn assign_or_reserve(
        &mut self,
        writer: ValueOrigin,
        reg_range: Range<u32>,
        curr_node_idx: usize,
    ) {
        // First we test if the writer is already assigned to a register range.
        let mut w2r = match self.writer_to_regs.entry(writer) {
            Entry::Occupied(entry) => {
                // Test the very rare special case where the writer
                // is already assigned to the range we need.
                if entry.get() == &reg_range {
                    // Already correctly assigned, nothing to do.
                    return;
                } else {
                    None
                }
            }
            Entry::Vacant(entry) => Some(entry),
        };

        // Second we need to check if the registers are already reserved.
        let mut removed_writers = Vec::new();
        for reg in reg_range.clone() {
            if let Entry::Occupied(entry) = self.reg_to_writers.entry(reg) {
                // Already used or reserved. We have a conflict and can't optimistically
                // set the writer. If the conflict is with a writer node above us, it
                // means it was also optimistically assigned, and we must clear it.
                removed_writers.extend(entry.get().iter().filter(|w| w.node > curr_node_idx));
                w2r = None;
            }
        }

        if let Some(w2r) = w2r {
            // Both are writer and registers are free, so we can assign the register to the writer.
            w2r.insert_entry(reg_range.clone());
            for r in reg_range {
                self.reg_to_writers.entry(r).or_default().push(writer);
            }
        } else {
            // We can't optimistically assign the registers, but we still need to
            // reserve them to be written on demand.
            for reg in reg_range {
                self.reg_to_writers.entry(reg).or_default();
            }

            // We must to clear any conflicting optimistic assignment we found.
            removed_writers.sort_unstable();
            removed_writers.dedup();
            for w in removed_writers {
                let regs = self.writer_to_regs.remove(&w).unwrap();
                for r in regs {
                    self.reg_to_writers
                        .get_mut(&r)
                        .unwrap()
                        .retain(|w2| w2 != &w);
                }
            }
        }
    }

    /// Merge the assignments. This might expose conflicts upper in
    /// execution path, but not in the already traversed nodes.
    /// Traversed nodes are final, and multiple writers to the same
    /// register means they happen in alternative execution paths.
    fn merge(&mut self, other: &Self, curr_node_idx: usize) {
        let old_self = std::mem::take(self);

        // We must first merge the final assignments, and then
        // insert optimistic assignments.

        // Merge the final reg_to_writers.
        for (reg, writers) in old_self
            .reg_to_writers
            .iter()
            .chain(other.reg_to_writers.iter())
        {
            let mut final_writers = writers
                .iter()
                .filter(|w| w.node <= curr_node_idx)
                .peekable();

            if final_writers.peek().is_some() {
                // TODO: I think it is not really necessary to save the writers that are
                // already final, but I am doing it for consistency.
                let writers = self.reg_to_writers.entry(*reg).or_default();
                writers.extend(final_writers);

                // It is very easy to have duplicates, because the path might diverge and
                // then converge again. We need to remove them.
                writers.sort_unstable();
                writers.dedup();
            }
        }

        // Merge the final writer_to_regs.
        let mut optimistic_assignments = Vec::new();
        for (writer, reg_range) in old_self
            .writer_to_regs
            .iter()
            .chain(other.writer_to_regs.iter())
        {
            if writer.node <= curr_node_idx {
                self.writer_to_regs.insert(*writer, reg_range.clone());
            } else {
                optimistic_assignments.push((*writer, reg_range.clone()));
            }
        }

        // Insert the optimistic assignments, possibly detecting conflicts.
        for (writer, reg_range) in optimistic_assignments {
            self.assign_or_reserve(writer, reg_range, curr_node_idx);
        }
    }
}

/// Allocates registers for a given DAG. It is not optimal, but it tries to
/// minimize the number of copies and used registers.
///
/// This is at least O(N^2) in the number of nodes.
///
/// TODO: for performance, keep the final and optimistic assignments in separated
/// structs, and instead of merging them, just store a reference to the earlier
/// labels.
///
/// Does the allocation bottom up, following the execution paths independently,
/// proposing register assignment for future nodes (so to avoid copies), but
/// leaving a final assignment for the traversed nodes.
///
/// The smallest allocation possible is 1 word, and the addresses are given
/// in words, not bytes. E.g. if `bytes_per_word` is 4, then the first 4 bytes
/// register will be 0, the second 4 bytes register will be 1, and so on.
fn optimistic_allocation<'a>(
    dag: &BlocklessDag<'a>,
    free_values: RangeFrom<u32>,
    bytes_per_word: u32,
) -> HashMap<ValueOrigin, Range<u32>> {
    let mut number_of_saved_copies = 0;

    #[derive(Clone)]
    struct PerPathData {
        free_values: RangeFrom<u32>,
        assignments: AssignmentSet,
    }

    struct LabelAllocation {
        node_idx: usize,
        regs: Vec<u32>,
        path_below_it: PerPathData,
    }

    let mut labels: HashMap<u32, LabelAllocation> = HashMap::new();

    impl PerPathData {
        fn merge(&mut self, other: &Self, current_node_idx: usize) {
            // Merge the free values
            if other.free_values.start > self.free_values.start {
                self.free_values = other.free_values.clone();
            }

            self.assignments.merge(&other.assignments, current_node_idx);
        }
    }

    let new_path = || PerPathData {
        free_values: free_values.clone(),
        assignments: AssignmentSet::default(),
    };

    fn merge_path_from_target<'a>(
        active_path: &mut PerPathData,
        target: &BreakTarget,
        labels: &'a mut HashMap<u32, LabelAllocation>,
        current_node_idx: usize,
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

        active_path.merge(&target_label.path_below_it, current_node_idx);

        Some(target_label)
    }

    let handle_break = |active_path: &mut PerPathData,
                        target: &BreakTarget,
                        labels: &mut HashMap<u32, LabelAllocation>,
                        inputs: &[ValueOrigin],
                        current_node_idx: usize| {
        // First, we merge the path from the target label
        let Some(target_label) =
            merge_path_from_target(active_path, target, labels, current_node_idx)
        else {
            return;
        };

        // Now we must optimistically assign the expected registers to all
        // the inputs of the break, or at least leave the registers reserved in case of
        // conflicts.
        for (input_idx, reg) in target_label.regs.iter().enumerate() {
            let origin = inputs[input_idx];
            let word_count =
                (byte_size(dag.nodes[origin.node].output_types[origin.output_idx as usize])
                    + bytes_per_word
                    - 1)
                    / bytes_per_word;

            active_path.assignments.assign_or_reserve(
                origin,
                *reg..(reg + word_count),
                current_node_idx,
            );
        }
    };

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
                handle_break(
                    &mut active_path,
                    target,
                    &mut labels,
                    &node.inputs,
                    node_idx,
                );
            }
            Operation::BrIf(target) | Operation::BrIfZero(target) => {
                // These instructions can fall through, so we must
                // keep the current path.
                handle_break(
                    &mut active_path,
                    target,
                    &mut labels,
                    &node.inputs,
                    node_idx,
                );
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
                    handle_break(
                        &mut active_path,
                        &target.target,
                        &mut labels,
                        &inputs,
                        node_idx,
                    );
                }
            }
            Operation::Loop { break_targets, .. } => {
                // A loop can not fall through, but the source of the break inputs
                // comes from another frame, so we just need reset and merge the paths.
                active_path = new_path();
                for target in break_targets {
                    merge_path_from_target(&mut active_path, target, &mut labels, node_idx);
                }
            }
            _ => {
                // On most nodes, we simply assign the registers to outputs that still
                // don't have them, making it final.
                for (output_idx, output_type) in node.output_types.iter().enumerate() {
                    let origin = ValueOrigin {
                        node: node_idx,
                        output_idx: output_idx as u32,
                    };

                    if let Entry::Vacant(entry) =
                        active_path.assignments.writer_to_regs.entry(origin)
                    {
                        let word_count =
                            (byte_size(*output_type) + bytes_per_word - 1) / bytes_per_word;
                        let past_last_reg = active_path
                            .free_values
                            .nth(word_count as usize - 1)
                            .unwrap()
                            + 1;
                        let reg_range = (past_last_reg - word_count)..past_last_reg;

                        entry.insert(reg_range.clone());

                        // We must also reserve the registers for the writer.
                        for reg in reg_range {
                            active_path
                                .assignments
                                .reg_to_writers
                                .entry(reg)
                                .or_default()
                                .push(origin);
                        }
                    } else {
                        number_of_saved_copies += 1;
                    }
                }
            }
        }
    }

    log::info!(
        "Optimistic allocation: {number_of_saved_copies} copies saved, {} registers used",
        active_path.free_values.start + 1
    );

    active_path.assignments.writer_to_regs
}

fn byte_size(ty: ValType) -> u32 {
    match ty {
        ValType::I32 | ValType::F32 => 4,
        ValType::I64 | ValType::F64 => 8,
        ValType::V128 => 16,
        ValType::Ref(..) => 4,
    }
}
