use crate::{
    linker,
    loader::flattening::{
        Generators, RegisterGenerator, ReturnInfo, TrapReason,
        settings::{
            ComparisonFunction, JumpCondition, LoopFrameLayout, ReturnInfosToCopy, Settings,
        },
    },
};
use std::{collections::BTreeSet, fmt::Display, ops::Range};
use wasmparser::{Operator as Op, ValType};

type Gen<'a, 'b> = Generators<'a, 'b, GenericIrSetting>;

pub struct GenericIrSetting;

#[allow(refining_impl_trait)]
impl<'a> Settings<'a> for GenericIrSetting {
    type Directive = Directive<'a>;

    fn bytes_per_word() -> u32 {
        4
    }

    fn words_per_ptr() -> u32 {
        1
    }

    fn is_jump_condition_available(cond: JumpCondition) -> bool {
        match cond {
            JumpCondition::IfZero => false,
            JumpCondition::IfNotZero => true,
        }
    }

    fn is_relative_jump_available() -> bool {
        true
    }

    fn allocate_loop_frame_slots(
        &self,
        need_ret_info: bool,
        saved_fps: BTreeSet<u32>,
    ) -> (RegisterGenerator<'a, Self>, LoopFrameLayout) {
        let mut rgen = RegisterGenerator::new();

        let ret_info = need_ret_info.then(|| {
            // Allocate the return PC and frame pointer for the loop.
            let ret_pc = rgen.allocate_words(Self::words_per_ptr());
            let ret_fp = rgen.allocate_words(Self::words_per_ptr());
            ReturnInfo { ret_pc, ret_fp }
        });

        // Allocate the slots for the saved frame pointers.
        let saved_fps = saved_fps
            .into_iter()
            .map(|depth| {
                let outer_fp = rgen.allocate_words(Self::words_per_ptr());
                (depth, outer_fp)
            })
            .collect();

        (
            rgen,
            LoopFrameLayout {
                saved_fps,
                ret_info,
            },
        )
    }

    fn emit_label(&self, _g: &mut Gen, name: String, frame_size: Option<u32>) -> Directive<'a> {
        Directive::Label {
            id: name,
            frame_size,
        }
    }

    fn emit_trap(&self, _g: &mut Gen, trap: TrapReason) -> Directive<'a> {
        Directive::Trap { reason: trap }
    }

    fn emit_allocate_label_frame(
        &self,
        _g: &mut Gen,
        label: String,
        result_ptr: Range<u32>,
    ) -> Directive<'a> {
        Directive::AllocateFrameI {
            target_frame: label,
            result_ptr: result_ptr.start,
        }
    }

    fn emit_allocate_value_frame(
        &self,
        _g: &mut Gen,
        frame_size_ptr: Range<u32>,
        result_ptr: Range<u32>,
    ) -> Directive<'a> {
        Directive::AllocateFrameV {
            frame_size: frame_size_ptr.start,
            result_ptr: result_ptr.start,
        }
    }

    fn emit_copy(&self, _g: &mut Gen, src_ptr: Range<u32>, dest_ptr: Range<u32>) -> Directive<'a> {
        Directive::Copy {
            src_word: src_ptr.start,
            dest_word: dest_ptr.start,
        }
    }

    fn emit_copy_into_frame(
        &self,
        _g: &mut Gen,
        src_ptr: Range<u32>,
        dest_frame_ptr: Range<u32>,
        dest_offset: Range<u32>,
    ) -> Directive<'a> {
        Directive::CopyIntoFrame {
            src_word: src_ptr.start,
            dest_frame: dest_frame_ptr.start,
            dest_word: dest_offset.start,
        }
    }

    fn emit_jump_into_loop(
        &self,
        _g: &mut Gen,
        loop_label: String,
        loop_frame_ptr: Range<u32>,
        ret_info_to_copy: Option<ReturnInfosToCopy>,
        saved_curr_fp_ptr: Option<Range<u32>>,
    ) -> Vec<Directive<'a>> {
        let mut directives = if let Some(to_copy) = ret_info_to_copy {
            assert_eq!(Self::words_per_ptr(), 1);
            vec![
                Directive::CopyIntoFrame {
                    src_word: to_copy.src.ret_pc.start,
                    dest_frame: loop_frame_ptr.start,
                    dest_word: to_copy.dest.ret_pc.start,
                },
                Directive::CopyIntoFrame {
                    src_word: to_copy.src.ret_fp.start,
                    dest_frame: loop_frame_ptr.start,
                    dest_word: to_copy.dest.ret_fp.start,
                },
            ]
        } else {
            Vec::new()
        };

        directives.push(Directive::JumpAndActivateFrame {
            target: loop_label,
            new_frame_ptr: loop_frame_ptr.start,
            saved_caller_fp: saved_curr_fp_ptr.map(|r| r.start),
        });

        directives
    }

    fn to_plain_local_jump(directive: Directive) -> Result<String, Directive> {
        if let Directive::Jump { target } = directive {
            Ok(target)
        } else {
            Err(directive)
        }
    }

    fn emit_jump(&self, label: String) -> Directive<'a> {
        Directive::Jump { target: label }
    }

    fn emit_conditional_jump(
        &self,
        _g: &mut Gen,
        condition_type: JumpCondition,
        label: String,
        condition_ptr: Range<u32>,
    ) -> Directive<'a> {
        assert_eq!(condition_type, JumpCondition::IfNotZero);
        Directive::JumpIf {
            target: label,
            condition: condition_ptr.start,
        }
    }

    fn emit_conditional_jump_cmp_immediate(
        &self,
        g: &mut Gen,
        cmp: ComparisonFunction,
        value_ptr: Range<u32>,
        immediate: u32,
        label: String,
    ) -> Vec<Directive<'a>> {
        let cmp_op = match cmp {
            ComparisonFunction::Equal => Op::I32Eq,
            ComparisonFunction::GreaterThanOrEqualUnsigned => Op::I32GeU,
            ComparisonFunction::LessThanUnsigned => Op::I32LtU,
        };

        let const_value = g.r.allocate_type(ValType::I32);
        let comparison = g.r.allocate_type(ValType::I32);
        vec![
            Directive::WASMOp {
                op: Op::I32Const {
                    value: immediate as i32,
                },
                inputs: Vec::new(),
                output: Some(const_value.clone()),
            },
            Directive::WASMOp {
                op: cmp_op,
                inputs: vec![value_ptr.clone(), const_value],
                output: Some(comparison.clone()),
            },
            Directive::JumpIf {
                target: label,
                condition: comparison.start,
            },
        ]
    }

    fn emit_relative_jump(&self, _g: &mut Gen, offset_ptr: Range<u32>) -> Directive<'a> {
        Directive::JumpOffset {
            offset: offset_ptr.start,
        }
    }

    fn emit_jump_out_of_loop(
        &self,
        _g: &mut Gen,
        target_label: String,
        target_frame_ptr: Range<u32>,
    ) -> Directive<'a> {
        Directive::JumpAndActivateFrame {
            target: target_label,
            new_frame_ptr: target_frame_ptr.start,
            // This iteration's frame will not be needed again.
            saved_caller_fp: None,
        }
    }

    fn emit_return(
        &self,
        _g: &mut Gen,
        ret_pc_ptr: Range<u32>,
        caller_fp_ptr: Range<u32>,
    ) -> Directive<'a> {
        Directive::Return {
            ret_pc: ret_pc_ptr.start,
            ret_fp: caller_fp_ptr.start,
        }
    }

    fn emit_imported_call(
        &self,
        _g: &mut Gen,
        module: &'a str,
        function: &'a str,
        inputs: Vec<Range<u32>>,
        outputs: Vec<Range<u32>>,
    ) -> Directive<'a> {
        Directive::ImportedCall {
            module,
            function,
            inputs,
            outputs,
        }
    }

    fn emit_function_call(
        &self,
        _g: &mut Gen,
        function_label: String,
        function_frame_ptr: Range<u32>,
        saved_ret_pc_ptr: Range<u32>,
        saved_caller_fp_ptr: Range<u32>,
    ) -> Directive<'a> {
        Directive::Call {
            target: function_label,
            new_frame_ptr: function_frame_ptr.start,
            saved_ret_pc: saved_ret_pc_ptr.start,
            saved_caller_fp: saved_caller_fp_ptr.start,
        }
    }

    fn emit_indirect_call(
        &self,
        _g: &mut Gen,
        target_pc_ptr: Range<u32>,
        function_frame_ptr: Range<u32>,
        saved_ret_pc_ptr: Range<u32>,
        saved_caller_fp_ptr: Range<u32>,
    ) -> Directive<'a> {
        Directive::CallIndirect {
            target_pc: target_pc_ptr.start,
            new_frame_ptr: function_frame_ptr.start,
            saved_ret_pc: saved_ret_pc_ptr.start,
            saved_caller_fp: saved_caller_fp_ptr.start,
        }
    }

    fn emit_table_get(
        &self,
        _g: &mut Gen,
        table_idx: u32,
        entry_idx_ptr: Range<u32>,
        dest_ptr: Range<u32>,
    ) -> Directive<'a> {
        Directive::WASMOp {
            op: Op::TableGet { table: table_idx },
            inputs: vec![entry_idx_ptr],
            output: Some(dest_ptr),
        }
    }

    fn emit_wasm_op(
        &self,
        _g: &mut Gen,
        op: Op<'a>,
        inputs: Vec<Range<u32>>,
        output: Option<Range<u32>>,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        Directive::WASMOp { op, inputs, output }
    }
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
        result_ptr: Register, // size: PTR
    },
    /// Allocates a new frame from a dynamic size
    AllocateFrameV {
        frame_size: Register, // size: i32
        result_ptr: Register, // size: PTR
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
        dest_frame: Register, // size: PTR
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
        new_frame_ptr: Register, // size: PTR
        /// Where, in the new frame, to save the frame pointer of the frame Wwe just left.
        /// May be None if the frame pointer is not needed.
        saved_caller_fp: Option<Register>, // size: PTR
    },
    /// Returns from the function.
    ///
    /// Similar to `JumpAndActivateFrame`, but the target is a dynamic address taken
    /// from a register, and it can't save the caller frame pointer.
    Return {
        ret_pc: Register, // size: PTR
        ret_fp: Register, // size: PTR
    },
    /// Calls a normal function.
    /// Use `JumpAndActivateFrame` for a tail call.
    Call {
        target: String,
        new_frame_ptr: Register, // size: PTR
        /// Where, in the new frame, to save the return PC at the call site.
        saved_ret_pc: Register, // size: PTR
        /// Where, in the new frame, to save the frame pointer of the frame we just left.
        saved_caller_fp: Register, // size: PTR
    },
    /// Calls a normal function indirectly, using a function reference.
    CallIndirect {
        // Notice the target_pc is an i32, not a PTR. This is because
        // the value is taken from the memory, and for now, code pointers are fixed to
        // 32 bits there.
        target_pc: Register,       // size: i32
        new_frame_ptr: Register,   // size: PTR
        saved_ret_pc: Register,    // size: PTR
        saved_caller_fp: Register, // size: PTR
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

impl linker::Directive for Directive<'_> {
    fn nop() -> Self {
        Directive::WASMOp {
            op: Op::Nop,
            inputs: Vec::new(),
            output: None,
        }
    }

    fn as_label(&self) -> Option<linker::Label> {
        if let Directive::Label { id, frame_size } = self {
            Some(linker::Label {
                id,
                frame_size: *frame_size,
            })
        } else {
            None
        }
    }
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
