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

use itertools::Itertools;
use std::{
    collections::{BTreeMap, HashMap, VecDeque, btree_map, hash_map},
    marker::PhantomData,
    ops::{Range, RangeFrom},
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

/// Just to make it explicit that the directive argument is not an immediate, but a register location inside the frame.
/// If the value is multi-word, the first word is at the given address, and the rest are at the next addresses.
type Register = u32;

pub enum Directive {
    Label {
        id: String,
    },
    /// Allocates a new frame.
    AllocateFrame {
        word_count: u32,
        result_ptr: Register, // i32
    },
    /// Copies a word from the active frame to a given place in the given frame.
    CopyIntoFrame {
        src_word: Register,   // word
        dest_frame: Register, // i32
        dest_word: Register,  // word
    },
    /// Jump and activate a frame.
    JumpAndActivateFrame {
        target: String,
        frame_ptr: Register, // i32
    },
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
    output_regs: Vec<Range<u32>>,
}

enum CtrlStackEntry {
    TopLevelFunction,
    Loop { label: String },
}

pub fn allocate_registers<'a>(
    module: &ModuleContext,
    func_type: &FuncType,
    dag: BlocklessDag<'a>,
    bytes_per_word: u32,
) -> WriteOnceASM<'a> {
    // Assuming pointer size is 4 bytes, we reserve the space for return PC and return FP.
    let mut reg_gen = RegisterGenerator::new();

    let ret_pc = reg_gen.allocate_bytes(bytes_per_word, 4);
    let ret_fp = reg_gen.allocate_bytes(bytes_per_word, 4);

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

    let ret_info = ReturnInfo {
        ret_pc,
        ret_fp,
        output_regs,
    };

    // Perform the register allocation for the function's top-level frame.
    let mut allocation = optimistic_allocation(&dag, bytes_per_word, &mut RegisterGenerator::new());

    // Since this is the top-level frame, the allocation can
    // not be arbitrary. It must conform to the calling convention,
    // so we must permute the allocation we found to match it.
    let reg_gen = permute_allocation(&mut allocation, input_regs, reg_gen.next_available);

    let mut ctrl_stack = VecDeque::from([CtrlStackEntry::TopLevelFunction]);

    flatten_frame_tree(
        dag,
        bytes_per_word,
        allocation,
        reg_gen,
        // TODO: share the label generator among all the functions.
        &mut (0..),
        &mut ctrl_stack,
        HashMap::new(),
        Some(ret_info),
    );

    // TODO...

    WriteOnceASM { _a: PhantomData }
}

fn flatten_frame_tree(
    dag: BlocklessDag,
    bytes_per_word: u32,
    allocation: Allocation,
    mut reg_gen: RegisterGenerator,
    loop_label_gen: &mut RangeFrom<u32>,
    ctrl_stack: &mut VecDeque<CtrlStackEntry>,
    outer_fps: HashMap<u32, Range<u32>>,
    ret_info: Option<ReturnInfo>,
) -> (u32, Vec<Directive>) {
    let mut directives = Vec::new();
    for node in dag.nodes {
        match node.operation {
            Operation::Loop {
                sub_dag,
                break_targets,
            } => {
                let loop_fp = reg_gen.allocate_bytes(bytes_per_word, 4);

                let mut loop_reg_gen = RegisterGenerator::new();

                let mut copy_instructions = Vec::new();

                // Test if the loop can return from the function. If so, we need to
                // forward the return info.
                let mut loop_ret_info = None;
                if let Some(ret_info) = &ret_info {
                    let func_frame_depth = ctrl_stack.len() as u32 - 1;
                    if let Some(&(depth, ref targets)) = break_targets.last() {
                        if depth == func_frame_depth
                            && targets.get(0) == Some(&TargetType::FunctionOrLoop)
                        {
                            let ret_pc = loop_reg_gen.allocate_bytes(bytes_per_word, 4);
                            let ret_fp = loop_reg_gen.allocate_bytes(bytes_per_word, 4);
                            let output_regs = ret_info
                                .output_regs
                                .iter()
                                .map(|reg| loop_reg_gen.allocate_words(reg.len() as u32))
                                .collect_vec();

                            // Issue the copy instructions into the loop frame.
                            copy_instructions.extend(copy_into_frame(
                                ret_info.ret_pc.clone(),
                                loop_fp.start,
                                ret_pc.clone(),
                            ));
                            copy_instructions.extend(copy_into_frame(
                                ret_info.ret_fp.clone(),
                                loop_fp.start,
                                ret_fp.clone(),
                            ));
                            copy_instructions.extend(
                                output_regs
                                    .iter()
                                    .zip_eq(ret_info.output_regs.iter())
                                    .flat_map(|(dst, src)| {
                                        copy_into_frame(src.clone(), loop_fp.start, dst.clone())
                                    }),
                            );

                            loop_ret_info = Some(ReturnInfo {
                                ret_pc,
                                ret_fp,
                                output_regs,
                            });
                        }
                    }
                };

                let mut loop_outer_fps = HashMap::new();
                // For each of the frames this loop can return to, we need to save the frame pointer.
                for (depth, targets) in break_targets.iter() {
                    for target in targets {
                        if let TargetType::Label(_) = target {
                            // This is a jump to a label in another frame, we must save the frame pointer.
                            let outer_fp = loop_reg_gen.allocate_bytes(bytes_per_word, 4);

                            copy_instructions.extend(copy_into_frame(
                                outer_fp.clone(),
                                loop_fp.start,
                                outer_fps[depth].clone(),
                            ));

                            loop_outer_fps.insert(*depth + 1, outer_fp);

                            break;
                        }
                    }
                }

                let loop_allocation =
                    optimistic_allocation(&sub_dag, bytes_per_word, &mut loop_reg_gen);

                // Finaly, we copy the inputs from the outer frame to the inner frame.
                let src_inputs = node
                    .inputs
                    .iter()
                    .map(|input| allocation.nodes_outputs[input].clone());

                let dest_inputs = loop_allocation
                    .nodes_outputs
                    .iter()
                    .take_while(|(val_origin, _)| val_origin.node == 0)
                    .map(|(_, reg)| reg.clone());

                for (src, dest) in src_inputs.zip_eq(dest_inputs) {
                    copy_instructions.extend(copy_into_frame(src, loop_fp.start, dest));
                }

                // Sanity check: loops have no outputs:
                assert!(node.output_types.is_empty());

                ctrl_stack.push_front(CtrlStackEntry::Loop {
                    label: format!("L{}", loop_label_gen.next().unwrap()),
                });

                let (loop_frame_size, loop_directives) = flatten_frame_tree(
                    sub_dag,
                    bytes_per_word,
                    loop_allocation,
                    loop_reg_gen,
                    loop_label_gen,
                    ctrl_stack,
                    loop_outer_fps,
                    loop_ret_info,
                );

                let CtrlStackEntry::Loop { label } = ctrl_stack.pop_front().unwrap() else {
                    unreachable!();
                };

                // Now we can actually emit the listing for the loop.
                // We start by allocating the frame.
                directives.push(Directive::AllocateFrame {
                    word_count: loop_frame_size,
                    result_ptr: loop_fp.start,
                });

                // Then we emit the copy instructions.
                directives.extend(copy_instructions);

                // Then we activate the frame.
                //
                // Jumping doesn't really do anything here, because the loop directives are
                // right ahead, but it is not worth to create a new instruction just for that.
                directives.push(Directive::JumpAndActivateFrame {
                    target: label.clone(),
                    frame_ptr: loop_fp.start,
                });

                // Then the loop label.
                directives.push(Directive::Label { id: label });

                // Finally, we emit the directives for the inner frame.
                directives.extend(loop_directives);
            }
            Operation::Br(target) => {
                // There are 4 different kinds of jumps, depending on the target:
                //
                // 1. Jump to a label in the current frame. We need to check if the break arguments have
                //    already been filled with the expected values (from the optimistic allocation). If
                //    not, we need to copy from the break inputs.
                //
                // 2. Jump to a label in a previous frame of the same function. I.e. a jump out of a loop.
                //    In this case, we need to copy all the break inputs into the target frame, then
                //    make a frame-switching jump to the label.
                //
                // 3. Jump into a loop iteration. This is very similar to emiting a loop, we need to
                //    see if the loop can return from the function, allocate the frame, and copy over
                //    the loop inputs, all possible target frames and po and return values before making the frame-switching jump.
                //
                // 4. Function return. This is similar to the previous case, we copy the return values to
                //    the function output registers, and perform a frame-switching jump. The difference is
                //    that the jump is to a dynamic label, stored in the return PC register.
                //
                // We need to identify the case and emit the correct directives.
                directives.extend(emit_jump(&target));
            }
            _ => todo!(),
        }
    }

    (reg_gen.next_available, directives)
}

fn copy_into_frame(
    src: Range<u32>,
    dest_frame: u32,
    dest: Range<u32>,
) -> impl Iterator<Item = Directive> {
    src.zip_eq(dest)
        .map(move |(src_word, dest_word)| Directive::CopyIntoFrame {
            src_word,
            dest_frame,
            dest_word,
        })
}

fn emit_jump(target: &BreakTarget) -> impl Iterator<Item = Directive> {
    [].into_iter() // TODO: implement this
}

fn jump_into_loop() {
    todo!()
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
fn optimistic_allocation<'a>(
    dag: &BlocklessDag<'a>,
    bytes_per_word: u32,
    reg_gen: &mut RegisterGenerator,
) -> Allocation {
    let mut number_of_saved_copies = 0;

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
        reg_gen: reg_gen.clone(),
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
                for (depth, targets) in break_targets.iter() {
                    for kind in targets {
                        merge_path_from_target(
                            &mut active_path,
                            &BreakTarget {
                                depth: *depth,
                                kind: *kind,
                            },
                            &mut labels,
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

    *reg_gen = active_path.reg_gen;

    Allocation {
        nodes_outputs: active_path.assignments.writer_to_regs,
        labels,
    }
}

/// A permutation of a given allocation, so that the input registers are the given ones, and all the others
/// begin at a given address.
///
/// Assumes the original allocation is tightly packed starting at 0.
struct InputPermutation(Vec<(u32, i64)>);

impl InputPermutation {
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

/// Permutes the allocation so that the input registers are the given ones,
/// and all the others begin at a given address.
fn permute_allocation(
    allocation: &mut Allocation,
    inputs: Vec<Range<u32>>,
    first_non_reserved_addr: u32,
) -> RegisterGenerator {
    let mut last_used_addr = 0;

    let map = InputPermutation::new(
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
        if reg.end > last_used_addr {
            last_used_addr = reg.end;
        }
    }

    // Now we need to permute the labels
    for label_regs in allocation.labels.values_mut() {
        for reg in label_regs.iter_mut() {
            map.permute_range(reg);
            // There is no need to update last_used_addr, because
            // all the labels are also represented as nodes.
        }
    }

    RegisterGenerator {
        next_available: last_used_addr,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_remap() {
        // Setup simple scenario
        let required_inputs = vec![10..20, 30..40];
        let current_inputs = vec![5..15, 25..35].into_iter();
        let first_non_reserved = 50;

        let map = InputPermutation::new(required_inputs, current_inputs, first_non_reserved);

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
    fn test_edge_cases() {
        let required_inputs = vec![10..20];
        let current_inputs = vec![0..10].into_iter();
        let first_non_reserved = 20;

        let map = InputPermutation::new(required_inputs, current_inputs, first_non_reserved);

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

        let map = InputPermutation::new(required_inputs, current_inputs, first_non_reserved);

        assert_eq!(map.permute(0), 100);
        assert_eq!(map.permute(10), 110);
    }

    #[test]
    fn test_identity() {
        let required_inputs = vec![];
        let current_inputs = vec![].into_iter();
        let first_non_reserved = 0;

        let map = InputPermutation::new(required_inputs, current_inputs, first_non_reserved);

        assert_eq!(map.permute(0), 0);
        assert_eq!(map.permute(10), 10);
    }

    #[test]
    fn test_multiple_fixed_intervals() {
        let required_inputs = vec![20..30, 40..50, 60..70];
        let current_inputs = vec![10..20, 30..40, 50..60].into_iter();
        let first_non_reserved = 100;

        let map = InputPermutation::new(required_inputs, current_inputs, first_non_reserved);

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

        let map = InputPermutation::new(required_inputs, current_inputs, first_non_reserved);

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
