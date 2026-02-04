use crate::loader::passes::dag::WasmValue;
use std::{cell::Cell, ops::Range};
use wasmparser::Operator as Op;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JumpCondition {
    IfZero,
    IfNotZero,
}

#[derive(Debug, Clone)]
pub enum WasmOpInput {
    Register(Range<u32>),
    Constant(WasmValue),
}

impl WasmOpInput {
    pub fn as_register(&self) -> Option<&Range<u32>> {
        match self {
            WasmOpInput::Register(r) => Some(r),
            WasmOpInput::Constant(_) => None,
        }
    }

    pub fn as_constant(&self) -> Option<&WasmValue> {
        match self {
            WasmOpInput::Register(_) => None,
            WasmOpInput::Constant(c) => Some(c),
        }
    }
}

#[derive(Clone, Debug)]
#[repr(u32)]
pub enum TrapReason {
    UnreachableInstruction,
    /// This trap happens if an instruction that was deemed unreachable
    /// by the register allocator is actually executed. In this case,
    /// there is necessarily a bug in the register allocator.
    RegisterAllocatorBug,
    WrongIndirectCallFunctionType,
}

/// Indicates whether the input for a Wasm node is a constant, and if so, its value.
///
/// This is part of the interface for constant collapsing optimization.
pub enum MaybeConstant {
    /// The corresponding input is a reference to a non-constant node,
    /// and we don't know the value at compile time.
    NonConstant,
    /// The corresponding input is a constant already set to be collapsed into the instruction.
    /// Can not happen in the default Womir pipeline, as the constant collapsing optimization
    /// pass is executed only once. This is defined for completeness.
    CollapsedConstant(WasmValue),
    /// The corresponding input is a reference to a constant node,
    /// and we know its value at compile time. The user may choose to collapse
    /// the value into the node, severing the dependency on the constant node.
    ReferenceConstant {
        value: WasmValue,
        /// This Cell value can be mutated to true indicate that the constant
        /// should be collapsed into the instruction, and the ISA supports it.
        /// Initially false.
        must_collapse: Cell<bool>,
    },
}

/// Trait providing settings for WOMIR loader passes.
pub trait Settings {
    type Directive;

    fn bytes_per_word() -> u32;

    /// The size, in words, of a pointer to an executable ROM address,
    /// and a pointer to a frame.
    fn words_per_ptr() -> u32;

    fn is_jump_condition_available(cond: JumpCondition) -> bool;
    fn is_relative_jump_available() -> bool;

    /// Tells whether constant collapsing optimization is enabled.
    ///
    /// The returned function will be called on every Wasm node with
    /// at least one provably constant input, and is responsible for
    /// deciding which of them, if any, should be part of the node itself.
    ///
    /// This can be used for ISAs that support immediate operands on
    /// certain instructions.
    ///
    /// Default implementation returns None, meaning no constant collapsing
    /// is performed.
    fn get_const_collapse_processor() -> Option<impl Fn(&Op, &[MaybeConstant])> {
        None::<fn(&Op, &[MaybeConstant])>
    }

    /// Test if a directive is a plain jump to a local frame label.
    fn to_plain_local_jump(directive: Self::Directive) -> Result<String, Self::Directive>;

    /// Test if a directive is a label.
    fn is_label(directive: &Self::Directive) -> Option<&str>;

    /// Emits an unconditional jump to a label.
    ///
    /// This must be exactly one instruction, otherwise jump tables will
    /// not work correctly.
    fn emit_jump(&self, target: String) -> Self::Directive;
}

pub enum LabelType {
    Function,
    Local,
    Loop,
}

pub fn format_label(label_id: u32, label_type: LabelType) -> String {
    match label_type {
        LabelType::Function => format!("__func_{label_id}"),
        LabelType::Local => format!("__local_{label_id}"),
        LabelType::Loop => format!("__loop_{label_id}"),
    }
}

pub fn func_idx_to_label(func_idx: u32) -> String {
    format_label(func_idx, LabelType::Function)
}

pub enum ComparisonFunction {
    Equal,
    GreaterThanOrEqualUnsigned,
    LessThanUnsigned,
}
