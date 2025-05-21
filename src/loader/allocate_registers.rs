//! This module does the infinite, write-once register allocation.
//!
//! The algorithm works in 2 passes, and goes like this:
//!
//! Outer Pass: we do a top-down, depth-first traversal of the DAG
//! tree, and call the Inner Pass each traversed DAG/frame. We
//! flatten the tree structure by emmiting assembly-like directives,
//! using the register allocation from the Inner Pass.
//!
//! Inner Pass: for each DAG/frame, we do a bottom-up traversal,
//! assigning registers to the labels outputs, matching with their
//! respective break inputs, and detect whether or not there is a
//! conflict, where multiple instructions would write to the same
//! register in the same execution path. In the end, we will have a
//! partial register assignment for some nodes, where conflicts for
//! break inputs are explicitly marked.
//!
//! TODO: the register allocation is not perfectly optimal, it
//! just uses a greedy approach to assign registers, and give up
//! when it detects a conflict. It may be possible to model the
//! problem to a SAT solver or something like that.

use itertools::{Itertools, all};
use std::{
    collections::{BTreeMap, HashMap, VecDeque, btree_map, hash_map},
    marker::PhantomData,
    ops::Range,
};
use wasmparser::{FuncType, Operator as Op, ValType};

use crate::loader::{
    blockless_dag::{BreakTarget, TargetType},
    dag::ValueOrigin,
};

use super::{
    ModuleContext,
    blockless_dag::{BlocklessDag, Operation},
};

/// An assembly-like representation for a write-once memory machine.
pub struct WriteOnceASM<'a> {
    _a: PhantomData<&'a ()>,
}

#[derive(Debug, Clone, Copy)]
struct RegisterGenerator {
    next_available: u32,
}

impl RegisterGenerator {
    fn new() -> Self {
        Self { next_available: 0 }
    }

    fn merge(&mut self, other: Self) {
        if self.next_available < other.next_available {
            self.next_available = other.next_available;
        }
    }

    fn allocate_words(&mut self, word_count: u32) -> Range<u32> {
        let start = self.next_available;
        self.next_available = start + word_count;
        start..self.next_available
    }

    fn allocate_bytes(&mut self, bytes_per_word: u32, byte_size: u32) -> Range<u32> {
        self.allocate_words(word_count(byte_size, bytes_per_word))
    }

    fn allocate_type(&mut self, bytes_per_word: u32, ty: ValType) -> Range<u32> {
        self.allocate_bytes(bytes_per_word, byte_size(ty))
    }
}

struct ReturnInfo {
    ret_pc: Range<u32>,
    ret_fp: Range<u32>,
}

enum CtrlStackEntry {
    TopLevelFunction { output_regs: Vec<Range<u32>> },
}

pub fn allocate_registers<'a>(
    module: &ModuleContext,
    func_type: &FuncType,
    dag: BlocklessDag<'a>,
    bytes_per_word: u32,
) -> WriteOnceASM<'a> {
    // Perform the register allocation for the function's top-level frame.
    let mut allocation = optimistic_allocation(&dag, bytes_per_word);

    // Assuming pointer size is 4 bytes, we reserve the space for return PC and return FP.
    let mut reg_gen = RegisterGenerator::new();
    let ret_info = ReturnInfo {
        ret_pc: reg_gen.allocate_bytes(bytes_per_word, 4),
        ret_fp: reg_gen.allocate_bytes(bytes_per_word, 4),
    };

    // As per zCray calling convention, after the return PC and FP, we reserve
    // space for the function inputs and outputs. Not only the inputs, but also
    // the outputs are filled by the caller, value preemptively provided by the prover.
    let input_regs = func_type
        .params()
        .iter()
        .map(|ty| reg_gen.allocate_type(bytes_per_word, *ty))
        .collect_vec();
    let output_regs = func_type
        .results()
        .iter()
        .map(|ty| reg_gen.allocate_type(bytes_per_word, *ty))
        .collect_vec();

    // Since this is the top-level frame, the allocation can
    // not be arbitrary. It must conform to the calling convention,
    // so we must permute the allocation we found to match it.
    permute_allocation(&mut allocation, input_regs, reg_gen);

    let mut ctrl_stack = VecDeque::from([CtrlStackEntry::TopLevelFunction { output_regs }]);

    flatten_frame_tree(
        &dag,
        bytes_per_word,
        allocation,
        &mut ctrl_stack,
        Some(ret_info),
    );

    // TODO...

    WriteOnceASM { _a: PhantomData }
}

fn flatten_frame_tree(
    dag: &BlocklessDag,
    bytes_per_word: u32,
    allocation: Allocation,
    ctrl_stack: &mut VecDeque<CtrlStackEntry>,
    ret_info: Option<ReturnInfo>,
) {
    // TODO: do the proper tree flattening...
    for node in dag.nodes.iter() {
        if let Operation::Loop { sub_dag, .. } = &node.operation {
            let loop_allocation = optimistic_allocation(sub_dag, bytes_per_word);

            ctrl_stack.push_front(todo!());
            let loop_ret_info = todo!();
            flatten_frame_tree(
                sub_dag,
                bytes_per_word,
                loop_allocation,
                &mut ctrl_stack,
                loop_ret_info,
            );
            ctrl_stack.pop_front();
        }
    }
}

#[derive(Default, Clone)]
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
        writer: ValueOrigin,
        reg_range: Range<u32>,
        curr_node_idx: usize,
    ) {
        // First we test if the writer is already assigned to a register range.
        let mut w2r = match self.writer_to_regs.entry(writer) {
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
        };

        // Second we need to check if the registers are already reserved.
        let mut removed_writers = Vec::new();
        for reg in reg_range.clone() {
            if let hash_map::Entry::Occupied(entry) = self.reg_to_writers.entry(reg) {
                // Already used or reserved. We have a conflict and can't optimistically
                // set the writer. If the conflict is with a writer node above us, it
                // means it was also optimistically assigned, and we must clear it.
                removed_writers.extend(entry.get().iter().filter(|w| w.node > curr_node_idx));
                w2r = None;
            }
        }

        if let Some(w2r) = w2r {
            // Both are writer and registers are free, so we can assign the register to the writer.
            w2r.insert(reg_range.clone());
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

/// One possible register allocation for a given DAG.
struct Allocation {
    /// The registers assigned to the nodes outputs.
    nodes_outputs: BTreeMap<ValueOrigin, Range<u32>>,
    /// The registers assigned to the labels. On a break, there is a chance that
    /// the register were already written with the correct value. If not, it must
    /// be written on demand, just before the break.
    labels: HashMap<u32, Vec<Range<u32>>>,
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
fn optimistic_allocation<'a>(dag: &BlocklessDag<'a>, bytes_per_word: u32) -> Allocation {
    let mut number_of_saved_copies = 0;
    let reg_gen = RegisterGenerator::new();

    #[derive(Clone)]
    struct PerPathData {
        reg_gen: RegisterGenerator,
        assignments: AssignmentSet,
    }

    struct LabelAllocation {
        regs: Vec<Range<u32>>,
        path_below_it: PerPathData,
    }

    let mut labels: HashMap<u32, LabelAllocation> = HashMap::new();

    impl PerPathData {
        fn merge(&mut self, other: &Self, current_node_idx: usize) {
            self.reg_gen.merge(other.reg_gen);
            self.assignments.merge(&other.assignments, current_node_idx);
        }
    }

    let new_path = || PerPathData {
        reg_gen,
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
                    .map(|ty| active_path.reg_gen.allocate_type(bytes_per_word, *ty))
                    .collect_vec();

                labels.insert(
                    *id,
                    LabelAllocation {
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
                for target in break_targets.iter().filter_map(|&t| {
                    t.depth
                        .checked_sub(1)
                        .map(|depth| BreakTarget { depth, ..t })
                }) {
                    merge_path_from_target(&mut active_path, &target, &mut labels, node_idx);
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
                        let reg_range = active_path
                            .reg_gen
                            .allocate_type(bytes_per_word, *output_type);

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
        active_path.reg_gen.next_available
    );

    let labels = labels
        .into_iter()
        .map(|(label, label_alloc)| (label, label_alloc.regs))
        .collect();

    Allocation {
        nodes_outputs: active_path.assignments.writer_to_regs,
        labels,
    }
}

/// Permutes a given allocation, so that the input registers are the given ones.
/// Assumes the input node is 0.
///
/// The inputs registers must not overlap with the output of the RegisterGenerator!
fn permute_allocation(
    allocation: &mut Allocation,
    inputs: Vec<Range<u32>>,
    mut reg_gen: RegisterGenerator,
) {
    // Create a mapping from old register ranges to new register ranges
    let mut reg_map = HashMap::new();

    // Map the input registers to the given ones
    let mut old_allocs = std::mem::take(&mut allocation.nodes_outputs).into_iter();
    for (new_reg, (val_origin, old_reg)) in inputs.into_iter().zip_eq(
        old_allocs
            .by_ref()
            .take_while(|(val_origin, _)| val_origin.node == 0),
    ) {
        assert_eq!(new_reg.len(), old_reg.len());
        reg_map.insert(old_reg, new_reg.clone());
        allocation.nodes_outputs.insert(val_origin, new_reg);
    }

    for (val_origin, old_reg) in old_allocs {
        let len = old_reg.len();
        // A node might use the same register as another node, even if they
        // are write-once. This is because the nodes might be in different,
        // independent execution paths. The original allocation should
        // have guaranteed that.
        let new_reg = reg_map
            .entry(old_reg)
            .and_modify(|new_reg| assert_eq!(new_reg.len(), len))
            .or_insert_with(|| reg_gen.allocate_words(len as u32));

        allocation.nodes_outputs.insert(val_origin, new_reg.clone());
    }

    // Now we need to permute the labels
    for label_regs in allocation.labels.values_mut() {
        for old_reg in label_regs.iter_mut() {
            let len = old_reg.len();
            let new_reg = reg_map
                .entry(old_reg.clone())
                .and_modify(|new_reg| assert_eq!(new_reg.len(), len))
                .or_insert_with(|| {
                    let new_reg = reg_gen.allocate_words(len as u32);
                    new_reg
                })
                .clone();

            *old_reg = new_reg;
        }
    }
}

fn byte_size(ty: ValType) -> u32 {
    match ty {
        ValType::I32 | ValType::F32 => 4,
        ValType::I64 | ValType::F64 => 8,
        ValType::V128 => 16,
        ValType::Ref(..) => 4,
    }
}

fn word_count(byte_size: u32, bytes_per_word: u32) -> u32 {
    (byte_size + bytes_per_word - 1) / bytes_per_word
}
