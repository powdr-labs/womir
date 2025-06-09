//! This module generates an assembly-like representation, flattening
//! the DAG structure and allocating registers for the operations.
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

mod allocate_registers;

use allocate_registers::{Allocation, optimistic_allocation};
use itertools::Itertools;
use std::{
    collections::{BTreeSet, VecDeque},
    fmt::Display,
    ops::{Range, RangeFrom},
};
use wasmparser::{Operator as Op, ValType};

use crate::loader::{
    FunctionRef,
    blockless_dag::{BreakTarget, Node, TargetType},
    dag::ValueOrigin,
};

use super::{
    Program,
    blockless_dag::{BlocklessDag, Operation},
};

/// Size, in bytes, used both to frame pointers and return addresses.
const PTR_BYTE_SIZE: u32 = 4;

/// An assembly-like representation for a write-once memory machine.
#[derive(Debug, Clone)]
pub struct WriteOnceASM<'a> {
    pub func_idx: u32,
    pub frame_size: u32,
    pub directives: Vec<Directive<'a>>,
}

/// Just to make it explicit that the directive argument is not an immediate, but a register location inside the frame.
/// If the value is multi-word, the first word is at the given address, and the rest are at the next addresses.
type Register = u32;

#[derive(Clone, Debug)]
pub enum Directive<'a> {
    Label {
        id: String,
        /// If this label is the start of a frame, this is the size of the frame in words.
        frame_size: Option<u32>,
    },
    /// Allocates a new frame from an immediate size.
    AllocateFrameI {
        /// The same identifier as the label, which has the frame size.
        target_frame: String,
        result_ptr: Register, // size: PTR_BYTE_SIZE
    },
    /// Allocates a new frame from a dynamic size
    AllocateFrameV {
        frame_size: Register, // size: I32
        result_ptr: Register, // size: PTR_BYTE_SIZE
    },
    /// Copies a word inside the active frame.
    Copy {
        /// The source word, in the active frame.
        src_word: Register, // size: 1 word
        /// The destination word, in the active frame.
        dest_word: Register, // size: 1 word
    },
    /// Copies a word from the active frame to a given place in the given frame.
    CopyIntoFrame {
        src_word: Register,   // size: 1 word
        dest_frame: Register, // size: PTR_BYTE_SIZE
        dest_word: Register,  // size: 1 word
    },
    /// Local jump to a label local to the current frame.
    Jump { target: String },
    /// Local jump over the next offset instructions.
    /// This is used to implement the `br_table` instruction.
    /// This instruction can be a little brittle, because it relies on the
    /// following instructions to map 1-to-1 in the final ISA.
    JumpOffset {
        /// The number of instructions to jump over.
        ///
        /// To be strictly compliant to how `br_table` works, this should be
        /// interpreted as unsigned, but assuming a 32-bit ROM address space,
        /// and wrapping arithmetics, it makes no difference whether one considers
        /// this as signed or unsigned.
        offset: Register, // size: i32
    },
    /// Jump to a local label if the condition is non-zero.
    JumpIf {
        target: String,
        condition: Register, // size: i32
    },
    /// Jump and activate a frame.
    JumpAndActivateFrame {
        target: String,
        new_frame_ptr: Register, // size: PTR_BYTE_SIZE
        /// Where, in the new frame, to save the frame pointer of the frame Wwe just left.
        /// May be None if the frame pointer is not needed.
        saved_caller_fp: Option<Register>, // size: PTR_BYTE_SIZE
    },
    /// Returns from the function.
    ///
    /// Similar to `JumpAndActivateFrame`, but the target is a dynamic address taken
    /// from a register, and it can't save the caller frame pointer.
    Return {
        ret_pc: Register, // size: PTR_BYTE_SIZE
        ret_fp: Register, // size: PTR_BYTE_SIZE
    },
    /// Calls a normal function.
    /// Use `JumpAndActivateFrame` for a tail call.
    Call {
        target: String,
        new_frame_ptr: Register, // size: PTR_BYTE_SIZE
        /// Where, in the new frame, to save the return PC at the call site.
        saved_ret_pc: Register, // size: PTR_BYTE_SIZE
        /// Where, in the new frame, to save the frame pointer of the frame we just left.
        saved_caller_fp: Register, // size: PTR_BYTE_SIZE
    },
    /// Calls a normal function indirectly, using a function reference.
    CallIndirect {
        target_pc: Register,       // size: PTR_BYTE_SIZE
        new_frame_ptr: Register,   // size: PTR_BYTE_SIZE
        saved_ret_pc: Register,    // size: PTR_BYTE_SIZE
        saved_caller_fp: Register, // size: PTR_BYTE_SIZE
    },
    /// Calls an imported function.
    ImportedCall {
        module: &'a str,
        function: &'a str,
        inputs: Vec<Range<u32>>,
        outputs: Vec<Range<u32>>,
    },
    /// General trap, which includes an unreachable instruction.
    Trap { reason: TrapReason },
    /// A forwarded operation from WebAssembly, only with the inputs and output registers specified.
    WASMOp {
        op: Op<'a>,
        inputs: Vec<Range<u32>>,
        output: Option<Range<u32>>,
    },
}

enum DirectiveTree<'a> {
    Empty,
    Leaf(Directive<'a>),
    VecLeaf(Vec<Directive<'a>>),
    Node(Vec<DirectiveTree<'a>>),
}

impl<'a> From<Directive<'a>> for DirectiveTree<'a> {
    fn from(directive: Directive<'a>) -> Self {
        DirectiveTree::Leaf(directive)
    }
}

impl<'a> From<Vec<Directive<'a>>> for DirectiveTree<'a> {
    fn from(directives: Vec<Directive<'a>>) -> Self {
        DirectiveTree::VecLeaf(directives)
    }
}

impl<'a> From<Vec<DirectiveTree<'a>>> for DirectiveTree<'a> {
    fn from(directives: Vec<DirectiveTree<'a>>) -> Self {
        if directives.is_empty() {
            DirectiveTree::Empty
        } else {
            DirectiveTree::Node(directives)
        }
    }
}

impl<'a> DirectiveTree<'a> {
    fn flatten(self) -> Vec<Directive<'a>> {
        fn flatten_rec<'b>(dnode: DirectiveTree<'b>, directives: &mut Vec<Directive<'b>>) {
            match dnode {
                DirectiveTree::Empty => {}
                DirectiveTree::Leaf(directive) => {
                    directives.push(directive);
                }
                DirectiveTree::VecLeaf(directives_vec) => {
                    directives.extend(directives_vec);
                }
                DirectiveTree::Node(children) => {
                    for child in children {
                        flatten_rec(child, directives);
                    }
                }
            }
        }

        let mut directives = Vec::new();
        flatten_rec(self, &mut directives);
        directives
    }
}

#[derive(Clone, Debug)]
pub enum TrapReason {
    UnreachableInstruction,
    /// This trap happens if an instruction that was deemed unreachable
    /// by the register allocator is actually executed. In this case,
    /// there is necessarily a bug in the register allocator.
    RegisterAllocatorBug,
    WrongIndirectCallFunctionType,
}

impl Display for Directive<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Directive::Label { id, frame_size } => {
                write!(f, "{id}")?;
                if let Some(size) = frame_size {
                    write!(f, " [{size}]")?;
                };
                write!(f, ":")?;
            }
            Directive::AllocateFrameI {
                target_frame,
                result_ptr,
            } => {
                write!(f, "    AllocateFrameI {target_frame} -> ${result_ptr}")?;
            }
            Directive::AllocateFrameV {
                frame_size,
                result_ptr,
            } => {
                write!(f, "    AllocateFrameV ${frame_size} -> ${result_ptr}")?;
            }
            Directive::Copy {
                src_word,
                dest_word,
            } => {
                write!(f, "    Copy ${src_word} -> ${dest_word}")?;
            }
            Directive::CopyIntoFrame {
                src_word,
                dest_frame,
                dest_word,
            } => {
                write!(
                    f,
                    "    CopyIntoFrame ${src_word} ${dest_frame} -> ${dest_frame}[{dest_word}]"
                )?;
            }
            Directive::Jump { target } => {
                write!(f, "    Jump {target}")?;
            }
            Directive::JumpOffset { offset } => {
                write!(f, "    JumpOffset ${offset}")?;
            }
            Directive::JumpIf { target, condition } => {
                write!(f, "    JumpIf {target} ${condition}")?;
            }
            Directive::JumpAndActivateFrame {
                target,
                new_frame_ptr,
                saved_caller_fp,
            } => {
                write!(f, "    JumpAndActivateFrame {target} ${new_frame_ptr}")?;
                if let Some(fp) = saved_caller_fp {
                    write!(f, " -> ${new_frame_ptr}[{fp}]")?;
                }
            }
            Directive::Return { ret_pc, ret_fp } => {
                write!(f, "    Return ${ret_pc} ${ret_fp}")?;
            }
            Directive::Call {
                target,
                new_frame_ptr,
                saved_ret_pc,
                saved_caller_fp,
            } => {
                write!(
                    f,
                    "    Call {target} ${new_frame_ptr} -> ${new_frame_ptr}[{saved_ret_pc}] ${new_frame_ptr}[{saved_caller_fp}]"
                )?;
            }
            Directive::CallIndirect {
                target_pc,
                new_frame_ptr,
                saved_ret_pc,
                saved_caller_fp,
            } => {
                write!(
                    f,
                    "    CallIndirect ${target_pc} ${new_frame_ptr} -> ${new_frame_ptr}[{saved_ret_pc}] ${new_frame_ptr}[{saved_caller_fp}]"
                )?;
            }
            Directive::ImportedCall {
                module,
                function,
                inputs,
                outputs,
            } => {
                let escaped_module = module.replace('"', "\\\"");
                let escaped_function = function.replace('"', "\\\"");
                write!(
                    f,
                    "    ImportedCall \"{}\" \"{}\"",
                    escaped_module, escaped_function
                )?;
                for input in inputs.iter() {
                    if input.len() == 1 {
                        write!(f, " ${}", input.start)?;
                    } else {
                        write!(f, " ${}..=${}", input.start, input.end - 1)?;
                    }
                }
                if !outputs.is_empty() {
                    write!(f, " ->")?;
                    for output in outputs.iter() {
                        if output.len() == 1 {
                            write!(f, " ${}", output.start)?;
                        } else {
                            write!(f, " ${}..=${}", output.start, output.end - 1)?;
                        }
                    }
                }
            }
            Directive::Trap { reason } => {
                write!(f, "    Trap")?;
                match reason {
                    TrapReason::UnreachableInstruction => write!(f, " (unreachable instruction)")?,
                    TrapReason::RegisterAllocatorBug => write!(f, " (register allocator bug)")?,
                    TrapReason::WrongIndirectCallFunctionType => {
                        write!(f, " (wrong indirect call function type)")?
                    }
                }
            }
            Directive::WASMOp { op, inputs, output } => {
                write!(f, "    ")?;
                format_op(op, f)?;
                for input in inputs.iter() {
                    if input.len() == 1 {
                        write!(f, " ${}", input.start)?;
                    } else {
                        write!(f, " ${}..=${}", input.start, input.end - 1)?;
                    }
                }
                if let Some(output) = output {
                    if output.len() == 1 {
                        write!(f, " -> ${}", output.start)?;
                    } else {
                        write!(f, " -> ${}..=${}", output.start, output.end - 1)?;
                    }
                }
            }
        }

        Ok(())
    }
}

fn format_op(op: &Op<'_>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    // A little hack to get the string representation of the operation.
    // Debug format and get the string up to the first space.
    let op_name = format!("{op:?}");
    write!(f, "{}", op_name.split_whitespace().next().unwrap())?;

    match op {
        // ======== Constants (all have `{ value }`) ========
        Op::I32Const { value } => write!(f, " {value}"),
        Op::I64Const { value } => write!(f, " {value}"),
        Op::F32Const { value } => write!(f, " {}", value.bits()),
        Op::F64Const { value } => write!(f, " {}", value.bits()),

        // ======== Loads & Stores (all have `{ memarg }`) ========
        Op::I32Load { memarg }
        | Op::I64Load { memarg }
        | Op::F32Load { memarg }
        | Op::F64Load { memarg }
        | Op::I32Load8S { memarg }
        | Op::I32Load8U { memarg }
        | Op::I32Load16S { memarg }
        | Op::I32Load16U { memarg }
        | Op::I64Load8S { memarg }
        | Op::I64Load8U { memarg }
        | Op::I64Load16S { memarg }
        | Op::I64Load16U { memarg }
        | Op::I64Load32S { memarg }
        | Op::I64Load32U { memarg }
        | Op::V128Load { memarg }
        | Op::I32Store { memarg }
        | Op::I64Store { memarg }
        | Op::F32Store { memarg }
        | Op::F64Store { memarg }
        | Op::I32Store8 { memarg }
        | Op::I32Store16 { memarg }
        | Op::I64Store8 { memarg }
        | Op::I64Store16 { memarg }
        | Op::I64Store32 { memarg }
        | Op::V128Store { memarg } => {
            write!(f, " {}", memarg.offset)
        }

        // ======== MemoryInit & DataDrop ========
        Op::MemoryInit { data_index, .. } | Op::DataDrop { data_index } => {
            write!(f, " {data_index}")
        }

        // ======== Table Ops (all have `{ table }`) ========
        Op::TableGet { table }
        | Op::TableSet { table }
        | Op::TableSize { table }
        | Op::TableGrow { table }
        | Op::TableFill { table } => {
            write!(f, " {table}")
        }

        // ======== TableCopy (has `{ dst_table, src_table }`) ========
        Op::TableCopy {
            dst_table,
            src_table,
        } => {
            write!(f, " {dst_table} {src_table}")
        }

        // ======== TableInit & ElemDrop ========
        Op::TableInit { elem_index, table } => {
            write!(f, " {elem_index} {table}")
        }
        Op::ElemDrop { elem_index } => {
            write!(f, " {elem_index}")
        }

        // ======== Anything else ========
        _ => Ok(()),
    }
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
        self.allocate_words(word_count_type(ty, bytes_per_word))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ReturnInfo {
    ret_pc: Range<u32>,
    ret_fp: Range<u32>,
}

struct CtrlStackEntry {
    entry_type: CtrlStackType,
    allocation: Allocation,
}

enum CtrlStackType {
    TopLevelFunction { output_regs: Vec<Range<u32>> },
    Loop(LoopStackEntry),
}

/// Contains all the information needed to jump into a new loop iteration.
#[derive(Debug)]
struct LoopStackEntry {
    label: String,
    /// ret_info is only present if the loop can return from the function.
    ret_info: Option<ReturnInfo>,
    /// The intermediate frame pointers in the frame stack that this loop
    /// might need to restore.
    ///
    /// (depth, fp_range), sorted by depth
    saved_fps: Vec<(u32, Range<u32>)>,
    input_regs: Vec<Range<u32>>,
}

pub fn flatten_dag<'a>(
    module: &Program<'a>,
    bytes_per_word: u32,
    label_gen: &mut RangeFrom<u32>,
    dag: BlocklessDag<'a>,
    func_idx: u32,
) -> WriteOnceASM<'a> {
    // Assuming pointer size is 4 bytes, we reserve the space for return PC and return FP.
    let mut reg_gen = RegisterGenerator::new();

    let ret_pc = reg_gen.allocate_bytes(bytes_per_word, PTR_BYTE_SIZE);
    let ret_fp = reg_gen.allocate_bytes(bytes_per_word, PTR_BYTE_SIZE);

    // As per zCray calling convention, after the return PC and FP, we reserve
    // space for the function inputs and outputs. Not only the inputs, but also
    // the outputs are filled by the caller, value preemptively provided by the prover.
    let func_type = module.get_func_type(func_idx);
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

    let ret_info = ReturnInfo { ret_pc, ret_fp };

    // Perform the register allocation for the function's top-level frame.
    let mut allocation = optimistic_allocation(&dag, bytes_per_word, &mut RegisterGenerator::new());

    // Since this is the top-level frame, the allocation can
    // not be arbitrary. It must conform to the calling convention,
    // so we must permute the allocation we found to match it.
    let reg_gen =
        allocate_registers::permute_allocation(&mut allocation, input_regs, reg_gen.next_available);

    let mut ctrl_stack = VecDeque::from([CtrlStackEntry {
        entry_type: CtrlStackType::TopLevelFunction { output_regs },
        allocation,
    }]);

    let (directives, frame_size) = flatten_frame_tree(
        module,
        dag,
        bytes_per_word,
        reg_gen,
        label_gen,
        &mut ctrl_stack,
        Some(ret_info),
    );

    // Now we can fill the function label with the actual frame size.
    let mut directives_with_labels = vec![
        Directive::Label {
            id: format_label(func_idx, LabelType::Function),
            frame_size: Some(frame_size),
        }
        .into(),
    ];

    if let Some(name) = module.get_exported_func(func_idx) {
        // Fill the exported function label with the name.
        directives_with_labels.push(
            Directive::Label {
                id: name.to_string(),
                frame_size: Some(frame_size),
            }
            .into(),
        );
    }
    directives_with_labels.push(DirectiveTree::Node(directives));

    let directives = DirectiveTree::Node(directives_with_labels).flatten();

    WriteOnceASM {
        func_idx,
        frame_size,
        directives,
    }
}

fn flatten_frame_tree<'a>(
    ctx: &Program<'a>,
    dag: BlocklessDag<'a>,
    bytes_per_word: u32,
    mut reg_gen: RegisterGenerator,
    label_gen: &mut RangeFrom<u32>,
    ctrl_stack: &mut VecDeque<CtrlStackEntry>,
    ret_info: Option<ReturnInfo>,
) -> (Vec<DirectiveTree<'a>>, u32) {
    let mut directives = Vec::new();

    for (node_idx, node) in dag.nodes.into_iter().enumerate() {
        let node_directives = translate_single_node(
            ctx,
            bytes_per_word,
            &mut reg_gen,
            label_gen,
            ctrl_stack,
            &ret_info,
            node_idx,
            node,
        );
        directives.push(node_directives);
    }

    (directives, reg_gen.next_available)
}

fn translate_single_node<'a>(
    ctx: &Program<'a>,
    bytes_per_word: u32,
    mut reg_gen: &mut RegisterGenerator,
    label_gen: &mut RangeFrom<u32>,
    ctrl_stack: &mut VecDeque<CtrlStackEntry>,
    ret_info: &Option<ReturnInfo>,
    node_idx: usize,
    node: Node<'a>,
) -> DirectiveTree<'a> {
    match node.operation {
        Operation::Inputs => {
            // Inputs does not translate to any assembly directive. It is used on the node tree for its outputs.
            DirectiveTree::Empty
        }
        Operation::Label { id } => {
            // This is a local label.
            Directive::Label {
                id: format_label(id, LabelType::Local),
                frame_size: None,
            }
            .into()
        }
        Operation::Loop {
            sub_dag,
            break_targets,
        } => {
            let mut loop_reg_gen = RegisterGenerator::new();

            // If None, this loop does not return from the function nor iterate to any outer loop.
            let shallowest_iter_or_ret = break_targets
                .iter()
                .find(|(_, targets)| targets.first() == Some(&TargetType::FunctionOrLoop))
                .map(|(depth, _)| *depth);

            let mut saved_fps = BTreeSet::new();
            let toplevel_frame_idx = ctrl_stack.len() as u32 - 1;

            // Test if the loop can return from the function. If so, we need to
            // forward the return info.
            let loop_ret_info = if ret_info.is_some() && shallowest_iter_or_ret.is_some() {
                let ret_pc = loop_reg_gen.allocate_bytes(bytes_per_word, PTR_BYTE_SIZE);
                let ret_fp = loop_reg_gen.allocate_bytes(bytes_per_word, PTR_BYTE_SIZE);

                // If the function has outputs, we need to save the toplevel frame pointer, too.
                if let CtrlStackType::TopLevelFunction { output_regs } =
                    &ctrl_stack.back().unwrap().entry_type
                {
                    if !output_regs.is_empty() {
                        saved_fps.insert(toplevel_frame_idx);
                    }
                }

                Some(ReturnInfo { ret_pc, ret_fp })
            } else {
                None
            };

            // Select the outer frame pointers that are saved in the current frame, and
            // the loop will need in order to start iterations of some outer loop.
            //
            // There seems to be a recursive proof that all the copied frames are necessary,
            // and the set is complete, but I only remember proving it in my head, not the
            // proof itself.
            if let (CtrlStackType::Loop(this_frame), Some(shallowest)) = (
                &ctrl_stack.front().unwrap().entry_type,
                shallowest_iter_or_ret,
            ) {
                let s = &this_frame.saved_fps;
                let start_i = s.partition_point(|(depth, _)| *depth < shallowest);
                saved_fps.extend(s[start_i..].iter().map(|(depth, _)| *depth));
            };

            // Select the frame pointers needed to break into outer frames.
            for (depth, targets) in break_targets.iter() {
                for target in targets {
                    if let TargetType::Label(_) = target {
                        saved_fps.insert(*depth);
                        break;
                    }
                }
            }

            // Actually allocate the slots for the saved frame pointers.
            let loop_outer_fps = saved_fps
                .into_iter()
                .map(|depth| {
                    let outer_fp = loop_reg_gen.allocate_bytes(bytes_per_word, PTR_BYTE_SIZE);
                    (depth + 1, outer_fp)
                })
                .collect();

            // Finally allocate all the registers for the loop instructions, including the inputs.
            let loop_allocation =
                optimistic_allocation(&sub_dag, bytes_per_word, &mut loop_reg_gen);

            // Sanity check: loops have no outputs:
            assert!(node.output_types.is_empty());

            // This struct contains everything we need to fill in order to jump into the loop.
            let loop_entry = LoopStackEntry {
                label: format_label(label_gen.next().unwrap(), LabelType::Loop),
                ret_info: loop_ret_info.clone(),
                saved_fps: loop_outer_fps,
                input_regs: loop_allocation
                    .nodes_outputs
                    .iter()
                    .take_while(|(val_origin, _)| val_origin.node == 0)
                    .map(|(_, reg)| reg.clone())
                    .collect(),
            };

            // Emit all the instructions to enter the loop.
            let enter_loop_directives = jump_into_loop(
                bytes_per_word,
                &loop_entry,
                &mut reg_gen,
                -1,
                ret_info.as_ref(),
                ctrl_stack.front().unwrap(),
                &node.inputs,
            );

            // Emit the listing for the loop itself.
            ctrl_stack.push_front(CtrlStackEntry {
                entry_type: CtrlStackType::Loop(loop_entry),
                allocation: loop_allocation,
            });
            let (loop_directives, loop_frame_size) = flatten_frame_tree(
                ctx,
                sub_dag,
                bytes_per_word,
                loop_reg_gen,
                label_gen,
                ctrl_stack,
                loop_ret_info,
            );
            let CtrlStackType::Loop(loop_entry) = ctrl_stack.pop_front().unwrap().entry_type else {
                unreachable!()
            };

            // Assemble the complete listing for this loop.
            DirectiveTree::Node(vec![
                enter_loop_directives.into(),
                Directive::Label {
                    id: loop_entry.label,
                    frame_size: Some(loop_frame_size),
                }
                .into(),
                loop_directives.into(),
            ])
        }
        Operation::Br(target) => emit_jump(
            bytes_per_word,
            &mut reg_gen,
            ret_info.as_ref(),
            &node.inputs,
            &target,
            ctrl_stack,
        )
        .into(),
        Operation::BrIfZero(target) => {
            let curr_entry = ctrl_stack.front().unwrap();

            // Get the conditional variable from the inputs.
            let mut inputs = node.inputs;
            let cond_origin = inputs.pop().unwrap();
            let cond_reg = curr_entry.allocation.nodes_outputs[&cond_origin].clone();
            assert_reg(&cond_reg, bytes_per_word, ValType::I32);

            let cont_label = format_label(label_gen.next().unwrap(), LabelType::Local);

            DirectiveTree::Node(vec![
                // Emit the jump if the condition is non-zero.
                Directive::JumpIf {
                    target: cont_label.clone(),
                    condition: cond_reg.start,
                }
                .into(),
                // Emit the jump to the target label.
                emit_jump(
                    bytes_per_word,
                    &mut reg_gen,
                    ret_info.as_ref(),
                    &inputs,
                    &target,
                    ctrl_stack,
                )
                .into(),
                // Emit the continuation label.
                Directive::Label {
                    id: cont_label,
                    frame_size: None,
                }
                .into(),
            ])
        }
        Operation::BrIf(target) => {
            let curr_entry = ctrl_stack.front().unwrap();

            // Get the conditional variable from the inputs.
            let mut inputs = node.inputs;
            let cond_origin = inputs.pop().unwrap();
            let cond_reg = curr_entry.allocation.nodes_outputs[&cond_origin].clone();
            assert_reg(&cond_reg, bytes_per_word, ValType::I32);

            // Generate the jump instructions
            let jump_directives = DirectiveTree::Node(emit_jump(
                bytes_per_word,
                &mut reg_gen,
                ret_info.as_ref(),
                &inputs,
                &target,
                ctrl_stack,
            ))
            .flatten();

            // If the jump_directives is one plain jump to a local label, we can
            // optimize this jump by emitting a single JumpIf.
            if let [Directive::Jump { .. }] = jump_directives.as_slice() {
                let Directive::Jump { target } = jump_directives.into_iter().next().unwrap() else {
                    unreachable!()
                };
                Directive::JumpIf {
                    target: target.clone(),
                    condition: cond_reg.start,
                }
                .into()
            } else {
                // The general case requires two helper labels to implement.
                let zero_label = format_label(label_gen.next().unwrap(), LabelType::Local);
                let cont_label = format_label(label_gen.next().unwrap(), LabelType::Local);

                // Either jump to the zero label if the condition is zero,
                // or the next instruction is a jump to the continuation label.
                DirectiveTree::Node(vec![
                    Directive::JumpIf {
                        target: zero_label.clone(),
                        condition: cond_reg.start,
                    }
                    .into(),
                    Directive::Jump {
                        target: cont_label.clone(),
                    }
                    .into(),
                    // The zero label contains the jump directives.
                    Directive::Label {
                        id: zero_label,
                        frame_size: None,
                    }
                    .into(),
                    jump_directives.into(),
                    // The continuation label is the next one.
                    Directive::Label {
                        id: cont_label,
                        frame_size: None,
                    }
                    .into(),
                ])
            }
        }
        Operation::BrTable { targets } => {
            let curr_entry = ctrl_stack.front().unwrap();

            let mut node_inputs = node.inputs;
            let selector = curr_entry.allocation.nodes_outputs[&node_inputs.pop().unwrap()].clone();

            let mut jump_instructions = targets
                .into_iter()
                .map(|target| {
                    // The inputs for one particular target are a permutation of the inputs
                    // of the BrTable operation.
                    let inputs = target
                        .input_permutation
                        .iter()
                        .map(|&idx| node_inputs[idx as usize].clone())
                        .collect_vec();

                    // Emit the jump to the target label.
                    emit_jump(
                        bytes_per_word,
                        &mut reg_gen,
                        ret_info.as_ref(),
                        &inputs,
                        &target.target,
                        ctrl_stack,
                    )
                })
                .collect_vec();

            // The last target is special, because it is the default target.
            let default_target = DirectiveTree::Node(jump_instructions.pop().unwrap()).flatten();

            // We need to handle the default target separately first, because it will be
            // the target in case the selector is out of bounds.

            let num_choices = reg_gen.allocate_type(bytes_per_word, ValType::I32);
            let mut directives: Vec<DirectiveTree<'a>> = vec![
                Directive::WASMOp {
                    op: Op::I32Const {
                        value: jump_instructions.len() as i32,
                    },
                    inputs: vec![],
                    output: Some(num_choices.clone()),
                }
                .into(),
            ];

            if let [Directive::Jump { .. }] = default_target.as_slice() {
                // If the default target is a plain jump to a local label, the JumpIf
                // targets it, and the fallthrough is the table itself.
                let Directive::Jump { target } = default_target.into_iter().next().unwrap() else {
                    unreachable!()
                };

                let is_default_taken = reg_gen.allocate_type(bytes_per_word, ValType::I32);
                directives.push(
                    Directive::WASMOp {
                        op: Op::I32GeU,
                        inputs: vec![selector.clone(), num_choices],
                        output: Some(is_default_taken.clone()),
                    }
                    .into(),
                );

                // Jump to the default target if the selector is out of bounds.
                directives.push(
                    Directive::JumpIf {
                        target,
                        condition: is_default_taken.start,
                    }
                    .into(),
                );
            } else {
                // The default target is a complicated jump, so it is the fallthrough,
                // and the JumpIf will target the table.
                let is_default_not_taken = reg_gen.allocate_type(bytes_per_word, ValType::I32);
                directives.push(
                    Directive::WASMOp {
                        op: Op::I32LtU,
                        inputs: vec![selector.clone(), num_choices],
                        output: Some(is_default_not_taken.clone()),
                    }
                    .into(),
                );

                let table_label = format_label(label_gen.next().unwrap(), LabelType::Local);
                directives.push(
                    Directive::JumpIf {
                        target: table_label.clone(),
                        condition: is_default_not_taken.start,
                    }
                    .into(),
                );

                directives.push(default_target.into());

                directives.push(
                    Directive::Label {
                        id: table_label,
                        frame_size: None,
                    }
                    .into(),
                );
            }

            // For robustness, the jump table has two indirections:
            // - jump_offset $selector
            // - jump jump_to_target_0
            // - jump jump_to_target_1
            // - ...
            // - jump jump_to_target_n
            // - jump_to_target_0:
            // - <actual instructions to jump to target 0>
            // - jump_to_target_1:
            // - <actual instructions to jump to target 1>
            // - ...
            // - jump_to_target_n:
            // - <actual instructions to jump to target n>
            //
            // The exception is if the target jump contains one single local jump instruction,
            // which can be embedded in the jump table directly.
            //
            // TODO: theoretically, any single instruction can be embedded in the jump table,
            // but it would require the guarantee that further translations wouldn't implement
            // any of them as multiple ISA instructions. It is safer to assume just Jump will
            // remain a single instruction. Maybe also Return?
            //
            // TODO: if jump_offset can jump $selector * N, where N is some immediate, this
            // can be implemented with a single indirection, but that would also require
            // 1-to-1 mapping in all the instructions belonging to the jump table.
            directives.push(
                Directive::JumpOffset {
                    offset: selector.start,
                }
                .into(),
            );

            let jump_instructions = jump_instructions
                .into_iter()
                .filter_map(|jump_directives| {
                    let jump_directives = DirectiveTree::Node(jump_directives).flatten();

                    if let [Directive::Jump { .. }] = jump_directives.as_slice() {
                        let Directive::Jump { target } =
                            jump_directives.into_iter().next().unwrap()
                        else {
                            unreachable!()
                        };
                        directives.push(Directive::Jump { target }.into());
                        None
                    } else {
                        let jump_label = format_label(label_gen.next().unwrap(), LabelType::Local);
                        directives.push(
                            Directive::Jump {
                                target: jump_label.clone(),
                            }
                            .into(),
                        );
                        Some((jump_label, jump_directives))
                    }
                })
                // Collecting here is essential, because of side effects of pushing
                // into `directives`.
                .collect_vec();

            // Finally emit the jump directives for each target.
            for (jump_label, jump_directives) in jump_instructions {
                directives.push(
                    Directive::Label {
                        id: jump_label,
                        frame_size: None,
                    }
                    .into(),
                );
                directives.push(jump_directives.into());
            }
            directives.into()
        }
        Operation::WASMOp(Op::Call { function_index }) => {
            let curr_entry = ctrl_stack.front().unwrap();

            if let Some((module, function)) = ctx.get_imported_func(function_index) {
                // Imported functions are kinda like system calls, and we assume
                // the implementation can access the input and output registers directly,
                // so we just have to emit the call directive.
                let inputs = map_input_into_regs(node.inputs, curr_entry);
                let outputs = (0..node.output_types.len())
                    .map(|output_idx| {
                        curr_entry.allocation.nodes_outputs[&ValueOrigin {
                            node: node_idx,
                            output_idx: output_idx as u32,
                        }]
                            .clone()
                    })
                    .collect();

                Directive::ImportedCall {
                    module,
                    function,
                    inputs,
                    outputs,
                }
                .into()
            } else {
                // Normal function calls requires a frame allocation and copying of the
                // inputs and outputs into the frame (the outputs are provided by the
                // prover "from the future").
                let func_frame_ptr = reg_gen.allocate_bytes(bytes_per_word, PTR_BYTE_SIZE);

                let inputs = node
                    .inputs
                    .into_iter()
                    .map(|origin| curr_entry.allocation.nodes_outputs[&origin].clone())
                    .collect();
                let (call_directives, this_ret_info) = prepare_function_call(
                    bytes_per_word,
                    inputs,
                    node_idx,
                    node.output_types.len(),
                    curr_entry,
                    func_frame_ptr.start,
                );

                DirectiveTree::Node(vec![
                    Directive::AllocateFrameI {
                        target_frame: format_label(function_index, LabelType::Function),
                        result_ptr: func_frame_ptr.start,
                    }
                    .into(),
                    call_directives.into(),
                    Directive::Call {
                        target: format_label(function_index, LabelType::Function),
                        new_frame_ptr: func_frame_ptr.start,
                        saved_caller_fp: this_ret_info.ret_fp.start,
                        saved_ret_pc: this_ret_info.ret_pc.start,
                    }
                    .into(),
                ])
            }
        }
        Operation::WASMOp(Op::CallIndirect {
            table_index,
            type_index,
        }) => {
            let curr_entry = ctrl_stack.front().unwrap();

            // First, we need to load the function reference from the table, so we allocate
            // the space for it and emit the table.get directive.

            // The last input of the CallIndirect operation is the table entry, the others are the function arguments.
            let mut inputs = map_input_into_regs(node.inputs, curr_entry);
            let table_get_inputs = vec![inputs.pop().unwrap()];

            let func_ref_reg = reg_gen.allocate_type(bytes_per_word, ValType::FUNCREF);

            // Split the components of the function reference:
            let func_ref_regs = split_func_ref_regs(bytes_per_word, func_ref_reg.clone());

            // We need two new registers to compare the expected function type with the loaded one.
            let expected_func_type = reg_gen.allocate_type(bytes_per_word, ValType::I32);
            let eq_result = reg_gen.allocate_type(bytes_per_word, ValType::I32);

            let ok_label = format_label(label_gen.next().unwrap(), LabelType::Local);
            let func_frame_ptr = reg_gen.allocate_bytes(bytes_per_word, PTR_BYTE_SIZE);

            // Perform the function call
            let (call_directives, this_ret_info) = prepare_function_call(
                bytes_per_word,
                inputs,
                node_idx,
                node.output_types.len(),
                curr_entry,
                func_frame_ptr.start,
            );

            DirectiveTree::Node(vec![
                Directive::WASMOp {
                    op: Op::TableGet { table: table_index },
                    inputs: table_get_inputs,
                    output: Some(func_ref_reg),
                }
                .into(),
                Directive::WASMOp {
                    op: Op::I32Const {
                        value: type_index as i32,
                    },
                    inputs: vec![],
                    output: Some(expected_func_type.clone()),
                }
                .into(),
                Directive::WASMOp {
                    op: Op::I32Eq,
                    inputs: vec![
                        expected_func_type.clone(),
                        func_ref_regs[FunctionRef::TYPE_INDEX].clone(),
                    ],
                    output: Some(eq_result.clone()),
                }
                .into(),
                // Now we need to jump to the actual function call if the types match.
                // Otherwise trap.
                Directive::JumpIf {
                    target: ok_label.clone(),
                    condition: eq_result.start,
                }
                .into(),
                Directive::Trap {
                    reason: TrapReason::WrongIndirectCallFunctionType,
                }
                .into(),
                Directive::Label {
                    id: ok_label,
                    frame_size: None,
                }
                .into(),
                // Allocate the new function frame
                Directive::AllocateFrameV {
                    frame_size: func_ref_regs[FunctionRef::FUNC_FRAME_SIZE].start,
                    result_ptr: func_frame_ptr.start,
                }
                .into(),
                call_directives.into(),
                Directive::CallIndirect {
                    target_pc: func_ref_regs[FunctionRef::FUNC_ADDR].start,
                    new_frame_ptr: func_frame_ptr.start,
                    saved_ret_pc: this_ret_info.ret_pc.start,
                    saved_caller_fp: this_ret_info.ret_fp.start,
                }
                .into(),
            ])
        }
        Operation::WASMOp(Op::Unreachable) => Directive::Trap {
            reason: TrapReason::UnreachableInstruction,
        }
        .into(),
        Operation::WASMOp(op) => {
            // Everything else is a normal operation, which will be forwarded almost as is.
            // Only that the registers inputs and output are explicit.
            let curr_entry = ctrl_stack.front().unwrap();
            let inputs = map_input_into_regs(node.inputs, curr_entry);
            let output = match node.output_types.len() {
                0 => None,
                1 => Some(
                    curr_entry.allocation.nodes_outputs[&ValueOrigin {
                        node: node_idx,
                        output_idx: 0,
                    }]
                        .clone(),
                ),
                _ => {
                    // WASM instructions have at most one output, so this is a bug.
                    panic!()
                }
            };
            Directive::WASMOp { op, inputs, output }.into()
        }
    }
}

fn assert_reg(reg: &Range<u32>, bytes_per_word: u32, ty: ValType) {
    let expected_size = byte_size(bytes_per_word, ty);
    assert_eq!(
        reg.len(),
        word_count(expected_size, bytes_per_word) as usize
    );
}

fn map_input_into_regs(
    node_inputs: Vec<ValueOrigin>,
    curr_entry: &CtrlStackEntry,
) -> Vec<Range<u32>> {
    node_inputs
        .into_iter()
        .map(|origin| curr_entry.allocation.nodes_outputs[&origin].clone())
        .collect()
}

fn copy_into_frame<'a>(
    src: Range<u32>,
    dest_frame: u32,
    dest: Range<u32>,
) -> Vec<DirectiveTree<'a>> {
    src.zip_eq(dest)
        .map(move |(src_word, dest_word)| {
            Directive::CopyIntoFrame {
                src_word,
                dest_frame,
                dest_word,
            }
            .into()
        })
        .collect()
}

fn prepare_function_call<'a>(
    bytes_per_word: u32,
    inputs: Vec<Range<u32>>,
    node_idx: usize,
    num_outputs: usize,
    curr_entry: &CtrlStackEntry,
    frame_ptr: u32,
) -> (Vec<DirectiveTree<'a>>, ReturnInfo) {
    let mut directives = Vec::new();

    // Generate the registers in the order expected by the calling convention.
    let mut fn_reg_gen = RegisterGenerator::new();
    let ret_info = ReturnInfo {
        ret_pc: fn_reg_gen.allocate_bytes(bytes_per_word, PTR_BYTE_SIZE),
        ret_fp: fn_reg_gen.allocate_bytes(bytes_per_word, PTR_BYTE_SIZE),
    };

    for src_reg in inputs {
        let dest_reg = fn_reg_gen.allocate_words(src_reg.len() as u32);
        directives.push(copy_into_frame(src_reg, frame_ptr, dest_reg).into());
    }
    for output_idx in 0..num_outputs {
        let src_reg = curr_entry.allocation.nodes_outputs[&ValueOrigin {
            node: node_idx,
            output_idx: output_idx as u32,
        }]
            .clone();
        let dest_reg = fn_reg_gen.allocate_words(src_reg.len() as u32);
        directives.push(copy_into_frame(src_reg, frame_ptr, dest_reg).into());
    }

    (directives, ret_info)
}

fn emit_jump<'a>(
    bytes_per_word: u32,
    reg_gen: &mut RegisterGenerator,
    ret_info: Option<&ReturnInfo>,
    node_inputs: &[ValueOrigin],
    target: &BreakTarget,
    ctrl_stack: &mut VecDeque<CtrlStackEntry>,
) -> Vec<DirectiveTree<'a>> {
    // There are 5 different kinds of jumps, depending on the target:
    //
    // 1. Jump to a label in the current frame. We need to check if the break arguments have
    //    already been filled with the expected values (from the optimistic allocation). If
    //    not, we need to copy from the break inputs.
    //
    // 2. Jump to a label in a previous frame of the same function. I.e. a jump out of a loop.
    //    In this case, we need to copy all the break inputs into the target frame, then
    //    make a frame-switching jump to the label.
    //
    // 3. Jump into a loop iteration.
    //
    // 4. Function return from a loop. We copy the return values to the function output
    //    registers, which are in the toplevel frame, and perform a frame-switching jump. The
    //    jump is to a dynamic label, stored in the return PC register.
    //
    // 5. Function return from the toplevel frame. The difference is that the output registers
    //    we need to fill are in the active frame, so the copy is local, not across frames.
    //
    // We need to identify the case and emit the correct directives.

    // This is a function return.
    let curr_entry = ctrl_stack.front().unwrap();
    match target {
        BreakTarget {
            depth: 0,
            kind: TargetType::Label(label),
        } => local_jump(*label, &curr_entry.allocation, node_inputs),
        BreakTarget {
            depth,
            kind: TargetType::Label(label),
        } => {
            // This is a jump out of loop, into a previous frame of the same function.
            jump_out_of_loop(bytes_per_word, *depth, *label, ctrl_stack, node_inputs)
        }
        BreakTarget {
            depth,
            kind: TargetType::FunctionOrLoop,
        } => {
            let target_stack_entry = &ctrl_stack[*depth as usize];
            match &target_stack_entry.entry_type {
                CtrlStackType::TopLevelFunction { output_regs } => {
                    // This is a function return.
                    match &curr_entry.entry_type {
                        CtrlStackType::TopLevelFunction { output_regs } => {
                            // This is a return from the toplevel frame.
                            top_level_return(
                                bytes_per_word,
                                ret_info.as_ref().unwrap(),
                                &curr_entry.allocation,
                                node_inputs,
                                output_regs,
                            )
                        }
                        CtrlStackType::Loop(loop_entry) => {
                            // This is a return from a loop.
                            assert_eq!(loop_entry.ret_info.as_ref(), ret_info);
                            return_from_loop(
                                bytes_per_word,
                                ctrl_stack.len(),
                                output_regs,
                                node_inputs,
                                &curr_entry.allocation,
                                loop_entry,
                            )
                        }
                    }
                }
                CtrlStackType::Loop(loop_entry) => {
                    // This is a loop iteration.
                    jump_into_loop(
                        bytes_per_word,
                        loop_entry,
                        reg_gen,
                        *depth as i64,
                        ret_info,
                        curr_entry,
                        node_inputs,
                    )
                }
            }
        }
    }
}

fn copy_local_jump_args<'a>(
    allocation: &Allocation,
    node_inputs: &[ValueOrigin],
    output_regs: &[Range<u32>],
) -> Vec<DirectiveTree<'a>> {
    // Copy the node inputs into the output registers, if they are not already assigned.
    let mut directives = Vec::new();
    for (origin, dest_reg) in node_inputs.iter().zip_eq(output_regs.iter()) {
        let src_reg = &allocation.nodes_outputs[origin];
        if src_reg != dest_reg {
            directives.extend(src_reg.clone().zip_eq(dest_reg.clone()).map(
                move |(src_word, dest_word)| {
                    Directive::Copy {
                        src_word,
                        dest_word,
                    }
                    .into()
                },
            ));
        }
    }
    directives
}

fn local_jump<'a>(
    label_id: u32,
    allocation: &Allocation,
    node_inputs: &[ValueOrigin],
) -> Vec<DirectiveTree<'a>> {
    // Copy the node inputs into the output registers, if they are not already assigned.
    let output_regs = &allocation.labels[&label_id];
    let mut directives = copy_local_jump_args(allocation, node_inputs, output_regs);

    // Emit the jump directive.
    directives.push(
        Directive::Jump {
            target: format_label(label_id, LabelType::Local),
        }
        .into(),
    );

    directives
}

fn top_level_return<'a>(
    bytes_per_word: u32,
    ret_info: &ReturnInfo,
    allocation: &Allocation,
    node_inputs: &[ValueOrigin],
    output_regs: &[Range<u32>],
) -> Vec<DirectiveTree<'a>> {
    // Copy the node inputs into the output registers, if they are not already assigned.
    let mut directives = copy_local_jump_args(allocation, node_inputs, output_regs);

    // Emit the return directive.
    assert_ptr_size(bytes_per_word, &ret_info.ret_pc);
    assert_ptr_size(bytes_per_word, &ret_info.ret_fp);
    directives.push(
        Directive::Return {
            ret_pc: ret_info.ret_pc.start,
            ret_fp: ret_info.ret_fp.start,
        }
        .into(),
    );

    directives
}

fn return_from_loop<'a>(
    bytes_per_word: u32,
    ctrl_stack_len: usize,
    output_regs: &[Range<u32>],
    node_inputs: &[ValueOrigin],
    allocation: &Allocation,
    curr_entry: &LoopStackEntry,
) -> Vec<DirectiveTree<'a>> {
    let mut directives = Vec::new();

    if !output_regs.is_empty() {
        let outer_fps = &curr_entry.saved_fps[..];
        let toplevel_depth = ctrl_stack_len - 1;
        let toplevel_idx = outer_fps.len() - 1;
        let toplevel_fp = get_fp_from_sorted(
            bytes_per_word,
            outer_fps,
            toplevel_depth as u32,
            toplevel_idx,
        );

        // Issue the copy directives.
        for (origin, dest_reg) in node_inputs.iter().zip_eq(output_regs.iter()) {
            let src_reg = allocation.nodes_outputs[origin].clone();
            directives.extend(copy_into_frame(src_reg, toplevel_fp, dest_reg.clone()));
        }
    }

    // Issue the return directive.
    let ret_info = curr_entry.ret_info.as_ref().unwrap();
    assert_ptr_size(bytes_per_word, &ret_info.ret_pc);
    assert_ptr_size(bytes_per_word, &ret_info.ret_fp);

    directives.push(
        Directive::Return {
            ret_pc: ret_info.ret_pc.start,
            ret_fp: ret_info.ret_fp.start,
        }
        .into(),
    );

    directives
}

fn jump_out_of_loop<'a>(
    bytes_per_word: u32,
    depth: u32,
    label_id: u32,
    ctrl_stack: &VecDeque<CtrlStackEntry>,
    node_inputs: &[ValueOrigin],
) -> Vec<DirectiveTree<'a>> {
    let caller_entry = ctrl_stack.front().unwrap();
    let outer_fps = if let CtrlStackType::Loop(curr_entry) = &caller_entry.entry_type {
        &curr_entry.saved_fps[..]
    } else {
        // You can not jump out of a loop from the toplevel frame.
        panic!()
    };
    let dest_fp_idx = outer_fps.partition_point(|(d, _)| *d < depth);
    let dest_fp = get_fp_from_sorted(bytes_per_word, outer_fps, depth, dest_fp_idx);

    let target_entry = &ctrl_stack[depth as usize];
    let target_inputs = &target_entry.allocation.labels[&label_id];

    let mut directives = Vec::new();
    for (origin, dest_reg) in node_inputs.iter().zip_eq(target_inputs.iter()) {
        let src_reg = caller_entry.allocation.nodes_outputs[origin].clone();
        directives.push(copy_into_frame(src_reg, dest_fp, dest_reg.clone()).into());
    }

    directives.push(
        Directive::JumpAndActivateFrame {
            target: format_label(label_id, LabelType::Local),
            new_frame_ptr: dest_fp,
            // This iteration's frame will not be needed again.
            saved_caller_fp: None,
        }
        .into(),
    );

    directives
}

fn get_fp_from_sorted(
    bytes_per_word: u32,
    sorted_fps: &[(u32, Range<u32>)],
    expected_depth: u32,
    idx: usize,
) -> u32 {
    let dest_fp = &sorted_fps[idx];
    assert_eq!(dest_fp.0, expected_depth);
    assert_ptr_size(bytes_per_word, &dest_fp.1);
    dest_fp.1.start
}

/// This function is used to generate the directives for frame creation, copy of
/// the loop inputs, and the jump into the loop. Both when iterating the loop
/// and when jumping into the loop for the first time.
///
/// depth_offset is the difference between the caller frame depth and the loop frame depth.
fn jump_into_loop<'a>(
    bytes_per_word: u32,
    loop_entry: &LoopStackEntry,
    reg_gen: &mut RegisterGenerator,
    depth_offset: i64,
    ret_info: Option<&ReturnInfo>,
    caller_stack_entry: &CtrlStackEntry,
    node_inputs: &[ValueOrigin],
) -> Vec<DirectiveTree<'a>> {
    let mut directives: Vec<DirectiveTree<'a>> = Vec::new();

    // We start by allocating the frame.
    let loop_fp = reg_gen.allocate_bytes(bytes_per_word, PTR_BYTE_SIZE);
    directives.push(
        Directive::AllocateFrameI {
            target_frame: loop_entry.label.clone(),
            result_ptr: loop_fp.start,
        }
        .into(),
    );

    // Copy the return info, if needed.
    if let Some(loop_ret_info) = &loop_entry.ret_info {
        // If the loop needs a return info, then the caller must have it, too.
        let ret_info = ret_info.unwrap();
        directives.push(
            copy_into_frame(
                ret_info.ret_pc.clone(),
                loop_fp.start,
                loop_ret_info.ret_pc.clone(),
            )
            .into(),
        );
        directives.push(
            copy_into_frame(
                ret_info.ret_fp.clone(),
                loop_fp.start,
                loop_ret_info.ret_fp.clone(),
            )
            .into(),
        );
    }

    // Copy the outer frame pointers.
    // outer_fps must be a superset of loop_entry.saved_fps, except for
    // outer_fps[0], which means the caller's own frame pointer, which might
    // be required if we are entering the loop for the first time.
    let mut depth_adjusted_loop_fps = loop_entry
        .saved_fps
        .iter()
        .map(|(depth, fp)| {
            // Adjust the depth to the caller's frame depth.
            ((*depth as i64 + depth_offset) as u32, fp.clone())
        })
        .peekable();

    // Handle the special case where outer_fps[0] is required.
    let saved_caller_fp = if let Some((0, _)) = depth_adjusted_loop_fps.peek() {
        let fp = depth_adjusted_loop_fps.next().unwrap().1;
        assert_ptr_size(bytes_per_word, &fp);
        Some(fp.start)
    } else {
        None
    };

    let outer_fps = if let CtrlStackType::Loop(curr_entry) = &caller_stack_entry.entry_type {
        // I resisted the devil's temptation to search the first needed element
        // with partition_point, which would probably do more harm than good.
        &curr_entry.saved_fps[..]
    } else {
        // The toplevel frame has no outer frames.
        &[]
    };

    for outer_fp in depth_adjusted_loop_fps.merge_join_by(
        outer_fps.iter().cloned(),
        |(required_depth, _), (available_depth, _)| required_depth.cmp(available_depth),
    ) {
        use itertools::EitherOrBoth::{Both, Left, Right};
        match outer_fp {
            Both((_, dest_fp), (_, src_fp)) => {
                directives.extend(copy_into_frame(src_fp, loop_fp.start, dest_fp));
            }
            Right(_) => {
                // An outer frame pointer is available, but not required. This is fine.
            }
            Left(_) => {
                // An outer frame pointer is required, but not available. Should not be possible.
                panic!();
            }
        }
    }

    // Copy the loop inputs into the loop frame.
    for (origin, input_reg) in node_inputs.iter().zip_eq(loop_entry.input_regs.iter()) {
        let src_reg = caller_stack_entry.allocation.nodes_outputs[origin].clone();
        directives.extend(copy_into_frame(src_reg, loop_fp.start, input_reg.clone()));
    }

    // Then we activate the frame.
    //
    // Jumping doesn't really do anything here, because the loop directives are
    // right ahead, but it is not worth to create a new instruction just for that.
    directives.push(
        Directive::JumpAndActivateFrame {
            target: loop_entry.label.clone(),
            new_frame_ptr: loop_fp.start,
            saved_caller_fp,
        }
        .into(),
    );

    directives
}

enum LabelType {
    Function,
    Local,
    Loop,
}

fn format_label(label_id: u32, label_type: LabelType) -> String {
    match label_type {
        LabelType::Function => format!("__func_{label_id}"),
        LabelType::Local => format!("__local_{label_id}"),
        LabelType::Loop => format!("__loop_{label_id}"),
    }
}

pub fn func_idx_to_label(func_idx: u32) -> String {
    format_label(func_idx, LabelType::Function)
}

fn byte_size(bytes_per_word: u32, ty: ValType) -> u32 {
    match ty {
        ValType::I32 | ValType::F32 => 4,
        ValType::I64 | ValType::F64 => 8,
        ValType::V128 => 16,
        ValType::Ref(..) => {
            // Since this is a struct of multiple memory words (u32) that we will need to
            // unpack into registers, so we need to provision enough registers for each memory
            // word independently.
            FunctionRef::NUM_WORDS * word_count(4, bytes_per_word) * bytes_per_word
        }
    }
}

fn split_func_ref_regs(bytes_per_word: u32, func_ref_reg: Range<u32>) -> Vec<Range<u32>> {
    let comp_size = func_ref_reg.len() as u32 / FunctionRef::NUM_WORDS;
    // Each component must have the same word-size as a I32,
    assert_eq!(comp_size, word_count_type(ValType::I32, bytes_per_word));
    let func_ref_regs = (0..FunctionRef::NUM_WORDS)
        .map(|i| func_ref_reg.start + i * comp_size..func_ref_reg.start + (i + 1) * comp_size)
        .collect_vec();
    assert_eq!(func_ref_reg.start, func_ref_regs[0].start);
    assert_eq!(func_ref_reg.end, func_ref_regs.last().unwrap().end);
    func_ref_regs
}

fn word_count(byte_size: u32, bytes_per_word: u32) -> u32 {
    (byte_size + bytes_per_word - 1) / bytes_per_word
}

fn assert_ptr_size(bytes_per_word: u32, ptr: &Range<u32>) {
    assert_eq!(
        ptr.len(),
        word_count(PTR_BYTE_SIZE, bytes_per_word) as usize
    );
}

pub fn word_count_type(ty: ValType, bytes_per_word: u32) -> u32 {
    word_count(byte_size(bytes_per_word, ty), bytes_per_word)
}
