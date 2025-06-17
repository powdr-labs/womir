use wasmparser::Operator as Op;

use crate::loader::flattening::{Generators, TrapReason, Tree};
use std::{fmt::Debug, ops::Range};

#[derive(Debug, PartialEq, Eq)]
pub enum JumpCondition {
    IfZero,
    IfNotZero,
}

pub enum ComparisonFunction {
    Equal,
    GreaterThanOrEqualUnsigned,
    LessThanUnsigned,
}

/// Trait controlling the behavior of the flattening process.
///
/// TODO: find a way to make calling conventions and interface registers allocation
/// part of this trait.
pub trait Settings<'a> {
    type Directive: Debug + Clone;

    fn bytes_per_word() -> u32;

    /// The size, in words, of a pointer to an executable ROM address,
    /// and a pointer to a frame.
    fn words_per_ptr() -> u32;

    fn is_jump_condition_available(cond: JumpCondition) -> bool;
    fn is_relative_jump_available() -> bool;

    /// Test if a directive is a plain jump to a local frame label.
    fn to_plain_local_jump(directive: Self::Directive) -> Result<String, Self::Directive>;

    /// Emits a directive to mark a code position, and possibly a frame size.
    fn emit_label(
        &self,
        g: &mut Generators<'a, '_, Self>,
        name: String,
        frame_size: Option<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a trap instruction with the given reason.
    fn emit_trap(
        &self,
        g: &mut Generators<'a, '_, Self>,
        trap: TrapReason,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits the instructions to allocate a new frame for a given immediate label.
    fn emit_allocate_label_frame(
        &self,
        g: &mut Generators<'a, '_, Self>,
        label: String,
        result_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits the instructions to allocate a new frame for a given a dynamic frame size.
    fn emit_allocate_value_frame(
        &self,
        g: &mut Generators<'a, '_, Self>,
        frame_size_ptr: Range<u32>,
        result_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Copies a single word within the active frame.
    fn emit_copy(
        &self,
        g: &mut Generators<'a, '_, Self>,
        src_ptr: Range<u32>,
        dest_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Copies a single word from the active frame to the given frame pointer.
    fn emit_copy_into_frame(
        &self,
        g: &mut Generators<'a, '_, Self>,
        src_ptr: Range<u32>,
        dest_frame_ptr: Range<u32>,
        dest_offset: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a plain jump to a label in the same frame.
    ///
    /// This must be exactly one instruction, as counted by the
    /// `emit_relative_jump()` method, otherwise jump tables will
    /// not work correctly.
    fn emit_jump(&self, label: String) -> Self::Directive;

    /// Emits the instructions to jump into a new loop iteration in a new frame,
    /// possibly saving the current frame pointer into the new frame.
    fn emit_jump_into_loop(
        &self,
        g: &mut Generators<'a, '_, Self>,
        loop_label: String,
        loop_frame_ptr: Range<u32>,
        saved_curr_fp_ptr: Option<Range<u32>>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits conditional jump to label in the same frame.
    ///
    /// The condition type will be one of the available, as per
    /// `is_branch_if_zero_available()` and `is_branch_if_not_zero_available()`.
    fn emit_conditional_jump(
        &self,
        g: &mut Generators<'a, '_, Self>,
        condition_type: JumpCondition,
        label: String,
        condition_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a jump to a label in the same frame conditioned on cmp(value, immediate).
    fn emit_conditional_jump_cmp_immediate(
        &self,
        g: &mut Generators<'a, '_, Self>,
        cmp: ComparisonFunction,
        value_ptr: Range<u32>,
        immediate: u32,
        label: String,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a jump relative to the next instruction (i.e. to PC+1+offset, where offset is unsigned).
    ///
    /// If offset is 0, it is equivalent to a NOP. Otherwise, it skips as many instructions as the offset.
    fn emit_relative_jump(
        &self,
        g: &mut Generators<'a, '_, Self>,
        offset_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a jump out of a loop, to label in a parent frame.
    fn emit_jump_out_of_loop(
        &self,
        g: &mut Generators<'a, '_, Self>,
        target_label: String,
        target_frame_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a function return instruction.
    fn emit_return(
        &self,
        g: &mut Generators<'a, '_, Self>,
        ret_pc_ptr: Range<u32>,
        caller_fp_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a call to an imported function.
    fn emit_imported_call(
        &self,
        g: &mut Generators<'a, '_, Self>,
        module: &'a str,
        function: &'a str,
        inputs: Vec<Range<u32>>,
        outputs: Vec<Range<u32>>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a call to a local function.
    fn emit_function_call(
        &self,
        g: &mut Generators<'a, '_, Self>,
        function_label: String,
        function_frame_ptr: Range<u32>,
        saved_ret_pc_ptr: Range<u32>,
        saved_caller_fp_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a call to a local function via a function pointer.
    fn emit_indirect_call(
        &self,
        g: &mut Generators<'a, '_, Self>,
        target_pc_ptr: Range<u32>,
        function_frame_ptr: Range<u32>,
        saved_ret_pc_ptr: Range<u32>,
        saved_caller_fp_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits the instructions to retrieve a function pointer from a table entry.
    fn emit_table_get(
        &self,
        g: &mut Generators<'a, '_, Self>,
        table_idx: u32,
        entry_idx_ptr: Range<u32>,
        dest_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits the equivalent set of instructions to a WASM operation.
    fn emit_wasm_op(
        &self,
        g: &mut Generators<'a, '_, Self>,
        op: Op<'a>,
        inputs: Vec<Range<u32>>,
        output: Option<Range<u32>>,
    ) -> impl Into<Tree<Self::Directive>>;
}
