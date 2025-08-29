use std::{
    collections::{BTreeMap, HashMap, btree_map},
    ops::Range,
};

use derive_where::derive_where;
use itertools::Itertools;
use wasmparser::Operator as Op;

use crate::loader::{
    blockless_dag::{BlocklessDag, BreakTarget, Operation, TargetType},
    dag::ValueOrigin,
    flattening::Settings,
};

use super::RegisterGenerator;

#[derive(Debug, Default, Clone)]
struct AssignmentSet {
    /// Empty writers Vec means that the register is reserved to be written on demand,
    /// so it can not be used for any more writers.
    reg_to_writers: HashMap<u32, Vec<ValueOrigin>>,
    /// A single writer can write to multiple contiguous registers, depending on its
    /// output types.
    writer_to_regs: BTreeMap<ValueOrigin, Range<u32>>,
}

impl AssignmentSet {
    fn assign_or_reserve(
        &mut self,
        writer: Option<ValueOrigin>,
        reg_range: Range<u32>,
        curr_node_idx: usize,
    ) {
        // First we test if the writer is already assigned to a register range.
        let mut w2r = if let Some(writer) = writer {
            match self.writer_to_regs.entry(writer) {
                btree_map::Entry::Occupied(entry) => {
                    // Test the very rare special case where the writer
                    // is already assigned to the range we need.
                    if entry.get() == &reg_range {
                        // Already correctly assigned, nothing to do.
                        return;
                    } else {
                        None
                    }
                }
                btree_map::Entry::Vacant(entry) => Some(entry),
            }
        } else {
            None
        };

        // Second we need to check if the registers are already reserved.
        let mut removed_writers = Vec::new();
        for reg in reg_range.clone() {
            if let Some(writers) = self.reg_to_writers.get(&reg) {
                // Already used or reserved. We have a conflict and can't optimistically
                // set the writer. If the conflict is with a writer node above us, it
                // means it was also optimistically assigned, and we must clear it.
                removed_writers.extend(writers.iter().filter(|w| w.node < curr_node_idx));
                w2r = None;
            }
        }

        if let Some(w2r) = w2r {
            // Both the writer and registers are free, so we can assign the register to the writer.
            for r in reg_range.clone() {
                self.reg_to_writers.entry(r).or_default().push(*w2r.key());
            }
            w2r.insert(reg_range);
        } else {
            // We can't optimistically assign the registers, but we still need to
            // reserve them to be written on demand.
            for reg in reg_range {
                self.reg_to_writers.entry(reg).or_default();
            }

            // We must to clear any conflicting optimistic assignment we found.
            removed_writers.sort_unstable();
            for w in removed_writers.into_iter().dedup() {
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
            let is_final = writers.iter().all(|w| w.node >= curr_node_idx);
            if is_final {
                // TODO: I think it is not really necessary to save the writers that are
                // already final, but I am doing it for consistency.
                let new_writers = self.reg_to_writers.entry(*reg).or_default();
                new_writers.extend(writers);

                // It is very easy to have duplicates, because the path might diverge and
                // then converge again. We need to remove them.
                new_writers.sort_unstable();
                new_writers.dedup();
            } else {
                assert_eq!(writers.len(), 1);
            }
        }

        // Merge the final writer_to_regs.
        let mut optimistic_assignments = Vec::new();
        for (writer, reg_range) in old_self
            .writer_to_regs
            .iter()
            .chain(other.writer_to_regs.iter())
        {
            if writer.node >= curr_node_idx {
                self.writer_to_regs.insert(*writer, reg_range.clone());
            } else {
                optimistic_assignments.push((*writer, reg_range.clone()));
            }
        }

        // Insert the optimistic assignments, possibly detecting conflicts.
        for (writer, reg_range) in optimistic_assignments {
            self.assign_or_reserve(Some(writer), reg_range, curr_node_idx);
        }
    }
}

pub struct NotAllocatedError;

/// One possible register allocation for a given DAG.
pub struct Allocation {
    /// The registers assigned to the nodes outputs.
    nodes_outputs: BTreeMap<ValueOrigin, Range<u32>>,
    /// The registers assigned to the labels. On a break, there is a chance that
    /// the register were already written with the correct value. If not, it must
    /// be written on demand, just before the break.
    pub labels: HashMap<u32, Vec<Range<u32>>>,
}

impl Allocation {
    pub fn get(&self, origin: &ValueOrigin) -> Result<Range<u32>, NotAllocatedError> {
        self.nodes_outputs
            .get(origin)
            .cloned()
            .ok_or(NotAllocatedError)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&ValueOrigin, &Range<u32>)> {
        self.nodes_outputs.iter()
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
/// in words, not bytes. E.g. if `S::bytes_per_word()` is 4, then the first 4 bytes
/// register will be 0, the second 4 bytes register will be 1, and so on.
pub fn optimistic_allocation<'a, S: Settings<'a>>(
    dag: &BlocklessDag<'_>,
    reg_gen: &mut RegisterGenerator<'a, S>,
    top_level_return_regs: Option<&[Range<u32>]>,
) -> (Allocation, usize) {
    let mut number_of_saved_copies = 0;

    #[derive_where(Debug, Clone)]
    struct PerPathData<'a, S: Settings<'a>> {
        reg_gen: RegisterGenerator<'a, S>,
        assignments: AssignmentSet,
    }

    struct LabelAllocation<'a, S: Settings<'a>> {
        node_idx: usize,
        regs: Vec<Range<u32>>,
        path_below_it: PerPathData<'a, S>,
    }

    let mut labels: HashMap<u32, LabelAllocation<S>> = HashMap::new();

    impl<'a, S: Settings<'a>> PerPathData<'a, S> {
        fn merge(&mut self, other: &Self, current_node_idx: usize) {
            self.reg_gen.merge(other.reg_gen);
            self.assignments.merge(&other.assignments, current_node_idx);
        }
    }

    let new_path = || PerPathData {
        reg_gen: *reg_gen,
        assignments: AssignmentSet::default(),
    };

    fn merge_path_from_target<'a, 'b, S: Settings<'a>>(
        active_path: &mut PerPathData<'a, S>,
        target: &BreakTarget,
        labels: &'b mut HashMap<u32, LabelAllocation<'a, S>>,
        current_node_idx: usize,
    ) -> Option<&'b LabelAllocation<'a, S>> {
        let target_label: &LabelAllocation<S> = match target {
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

    let handle_break = |active_path: &mut PerPathData<'a, S>,
                        target: &BreakTarget,
                        labels: &mut HashMap<u32, LabelAllocation<'a, S>>,
                        inputs: Option<&[ValueOrigin]>,
                        current_node_idx: usize| {
        // First, we try to merge the path from the target label
        let regs = if let Some(target_label) =
            merge_path_from_target(active_path, target, labels, current_node_idx)
        {
            // We are breaking to a local label, who has registers in the active frame.
            &target_label.regs
        } else if let Some(regs) = top_level_return_regs {
            // We are breaking out of the function from the top level function, so
            // the return arguments are on the active frame, and we can still optmize.
            regs
        } else {
            // The break inputs must be copied into another frame, so we can't
            // try optimistic allocation.
            return;
        };

        // Now we must optimistically assign the expected registers to all
        // the inputs of the break, or at least leave the registers reserved in case of
        // conflicts.
        for (input_idx, reg) in regs.iter().enumerate() {
            let origin = inputs.and_then(|inputs| {
                let origin = inputs[input_idx];
                if origin.node == 0 && target.kind == TargetType::FunctionOrLoop {
                    // The target is the function output and the origin is the function
                    // input, due to calling convention they must necessarily be different
                    // registers, so we can't do optimistic allocation.
                    None
                } else {
                    Some(origin)
                }
            });

            active_path
                .assignments
                .assign_or_reserve(origin, reg.clone(), current_node_idx);
        }
    };

    let mut active_path = new_path();

    for (node_idx, node) in dag.nodes.iter().enumerate().rev() {
        match &node.operation {
            Operation::Label { id } => {
                let regs = node
                    .output_types
                    .iter()
                    .map(|ty| active_path.reg_gen.allocate_type(*ty))
                    .collect_vec();

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
                    Some(&node.inputs),
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
                    Some(&node.inputs),
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
                        Some(&inputs),
                        node_idx,
                    );
                }
            }
            Operation::Loop { break_targets, .. } => {
                // A loop can not fall through, but the source of the break inputs
                // comes from another frame, so we just need reset and merge the paths.
                active_path = new_path();
                for (depth, targets) in break_targets.iter() {
                    for kind in targets {
                        handle_break(
                            &mut active_path,
                            &BreakTarget {
                                depth: *depth,
                                kind: *kind,
                            },
                            &mut labels,
                            // The inputs to this break comes from the loop's frame,
                            // so it can't be optimistically assigned.
                            None,
                            node_idx,
                        );
                    }
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

                    if let btree_map::Entry::Vacant(entry) =
                        active_path.assignments.writer_to_regs.entry(origin)
                    {
                        let reg_range = active_path.reg_gen.allocate_type(*output_type);

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

    let mut nodes_outputs = active_path.assignments.writer_to_regs;

    let labels = labels
        .into_iter()
        .map(|(label, label_alloc)| {
            // Now that the allocation is done, we can also put in the map the registers
            // for the labels, for access convenience.
            for (output_idx, reg) in label_alloc.regs.iter().enumerate() {
                let origin = ValueOrigin {
                    node: label_alloc.node_idx,
                    output_idx: output_idx as u32,
                };

                nodes_outputs.insert(origin, reg.clone());
            }

            // Simplify the index by label:
            (label, label_alloc.regs)
        })
        .collect();

    *reg_gen = active_path.reg_gen;

    (
        Allocation {
            nodes_outputs,
            labels,
        },
        number_of_saved_copies,
    )
}

/// A permutation of a given allocation, so that the input registers are the given ones, and all the others
/// begin at a given address and are shifted back to fill the holes left by the moved inputs.
///
/// Assumes the original allocation is tightly packed starting at 0.
struct RepackPermutation(Vec<(u32, i64)>);

impl RepackPermutation {
    fn new(
        required_inputs: Vec<Range<u32>>,
        current_inputs: impl Iterator<Item = Range<u32>>,
        first_non_reserved: u32,
    ) -> Self {
        let mut fixed_inputs = current_inputs
            .zip_eq(required_inputs)
            .map(|(cur, req)| {
                assert_eq!(cur.len(), req.len());
                (cur.start, req)
            })
            .collect_vec();

        fixed_inputs.sort_unstable_by_key(|(old_addr, _)| *old_addr);

        let mut next_offset = first_non_reserved as i64;
        let mut next_old = 0u32;
        let mut perm = Vec::new();
        for (old_addr, new_addr) in fixed_inputs {
            if next_old < old_addr {
                perm.push((next_old, next_offset));
            } else {
                assert_eq!(next_old, old_addr);
            }

            // new_addr = old_addr + offset
            let offset = new_addr.start as i64 - old_addr as i64;
            perm.push((old_addr, offset));

            next_old = old_addr + new_addr.len() as u32;
            next_offset -= new_addr.len() as i64;
        }
        perm.push((next_old, next_offset));

        Self(perm)
    }

    fn permute(&self, reg: u32) -> u32 {
        let part = self
            .0
            .partition_point(|(ref_old_addr, _)| *ref_old_addr <= reg)
            - 1;
        (reg as i64 + self.0[part].1) as u32
    }

    fn permute_range(&self, range: &mut Range<u32>) {
        let len = range.len() as u32;
        range.start = self.permute(range.start);
        range.end = range.start + len;
    }
}

/// Reorders the allocation so that the input registers are the given ones,
/// and all the others begin at a given address, and are tightly repacked to
/// fill the holes left by the moved inputs.
pub fn reorder_allocation<'a, S: Settings<'a>>(
    allocation: &mut Allocation,
    inputs: Vec<Range<u32>>,
    first_non_reserved_addr: u32,
) {
    let map = RepackPermutation::new(
        inputs,
        allocation
            .nodes_outputs
            .iter()
            .take_while(|(val_origin, _)| val_origin.node == 0)
            .map(|(_, reg)| reg.clone()),
        first_non_reserved_addr,
    );

    // Permute the nodes outputs
    for reg in allocation.nodes_outputs.values_mut() {
        map.permute_range(reg);
    }

    // Now we need to permute the labels
    for label_regs in allocation.labels.values_mut() {
        for reg in label_regs.iter_mut() {
            map.permute_range(reg);
            // There is no need to update last_used_addr, because
            // all the labels are also represented as nodes.
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_remap() {
        // Setup simple scenario
        let required_inputs = vec![10..20, 30..40];
        let current_inputs = vec![5..15, 25..35].into_iter();
        let first_non_reserved = 50;

        let map = RepackPermutation::new(required_inputs, current_inputs, first_non_reserved);

        // Check offsets are correctly computed
        assert_eq!(map.permute(0), 50);
        assert_eq!(map.permute(4), 54);
        // Address 5 is fixed at 10
        assert_eq!(map.permute(5), 10);
        assert_eq!(map.permute(14), 19);
        // After the first fixed range, should shift again
        assert_eq!(map.permute(15), 55);
        assert_eq!(map.permute(24), 64);
        // Address 25 fixed at 30
        assert_eq!(map.permute(25), 30);
        assert_eq!(map.permute(34), 39);
        // After second fixed range
        assert_eq!(map.permute(35), 65);
    }

    #[test]
    // Clippy is trying to be too smart, ignoring the parameter's type.
    #[allow(clippy::single_range_in_vec_init)]
    fn test_edge_cases() {
        let required_inputs = vec![10..20];
        let current_inputs = vec![0..10].into_iter();
        let first_non_reserved = 20;

        let map = RepackPermutation::new(required_inputs, current_inputs, first_non_reserved);

        assert_eq!(map.permute(0), 10);
        assert_eq!(map.permute(9), 19);
        assert_eq!(map.permute(10), 20);
        assert_eq!(map.permute(15), 25);
    }

    #[test]
    fn test_no_fixed_intervals() {
        let required_inputs = vec![];
        let current_inputs = vec![].into_iter();
        let first_non_reserved = 100;

        let map = RepackPermutation::new(required_inputs, current_inputs, first_non_reserved);

        assert_eq!(map.permute(0), 100);
        assert_eq!(map.permute(10), 110);
    }

    #[test]
    fn test_identity() {
        let required_inputs = vec![];
        let current_inputs = vec![].into_iter();
        let first_non_reserved = 0;

        let map = RepackPermutation::new(required_inputs, current_inputs, first_non_reserved);

        assert_eq!(map.permute(0), 0);
        assert_eq!(map.permute(10), 10);
    }

    #[test]
    fn test_multiple_fixed_intervals() {
        let required_inputs = vec![20..30, 40..50, 60..70];
        let current_inputs = vec![10..20, 30..40, 50..60].into_iter();
        let first_non_reserved = 100;

        let map = RepackPermutation::new(required_inputs, current_inputs, first_non_reserved);

        assert_eq!(map.permute(0), 100);
        assert_eq!(map.permute(9), 109);
        assert_eq!(map.permute(10), 20); // fixed
        assert_eq!(map.permute(19), 29); // end fixed
        assert_eq!(map.permute(20), 110);
        assert_eq!(map.permute(29), 119);
        assert_eq!(map.permute(30), 40); // fixed
        assert_eq!(map.permute(39), 49); // end fixed
        assert_eq!(map.permute(40), 120);
    }

    #[test]
    fn test_inputs_reordered() {
        // 5 maps to 30..40, 25 maps to 10..20
        let required_inputs = vec![10..20, 30..40];
        let current_inputs = vec![25..35, 5..15].into_iter();
        let first_non_reserved = 50;

        let map = RepackPermutation::new(required_inputs, current_inputs, first_non_reserved);

        // "Fixed" addresses
        // 25 -> 10
        assert_eq!(map.permute(25), 10);

        // 5 -> 30
        assert_eq!(map.permute(5), 30);

        // Addresses below any fixed mapping, shifted by first_non_reserved
        assert_eq!(map.permute(0), 50);
        assert_eq!(map.permute(4), 54);

        // Address just after mapped blocks, shifted accordingly
        assert_eq!(map.permute(15), 55);
        assert_eq!(map.permute(20), 60);

        // Address after all mapped blocks
        assert_eq!(map.permute(40), 70);
        assert_eq!(map.permute(45), 75);
    }
}
