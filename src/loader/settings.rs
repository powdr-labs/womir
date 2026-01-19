use crate::loader::passes::dag::WasmValue;
use std::cell::Cell;
use wasmparser::Operator as Op;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JumpCondition {
    IfZero,
    IfNotZero,
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
}
