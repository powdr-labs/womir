use std::ops::Range;
use wasmparser::Operator;

use crate::{
    loader::{
        self,
        rwm::flattening::Context,
        settings::{ComparisonFunction, JumpCondition, TrapReason, WasmOpInput},
    },
    utils::tree::Tree,
};

/// Trait controlling the behavior of the flattening process.
pub trait Settings<'a>: loader::Settings {
    type Directive;

    /// Emits a directive to mark a code position.
    fn emit_label(&self, c: &mut Context, name: String) -> impl Into<Tree<Self::Directive>>;

    /// Emits a trap instruction with the given reason.
    fn emit_trap(&self, c: &mut Context, trap: TrapReason) -> impl Into<Tree<Self::Directive>>;

    /// Copies a single word between two registers.
    fn emit_copy(
        &self,
        g: &mut Context,
        src_reg: u32,
        dest_reg: u32,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits an unconditional jump to a label.
    ///
    /// This must be exactly one instruction, as counted by the
    /// `emit_relative_jump()` method, otherwise jump tables will
    /// not work correctly.
    fn emit_jump(&self, target: String) -> impl Into<Tree<Self::Directive>>;

    /// Emits conditional jump to a label.
    ///
    /// The condition type will be one of the available, as per
    /// `is_branch_if_zero_available()` and `is_branch_if_not_zero_available()`.
    fn emit_conditional_jump(
        &self,
        c: &mut Context,
        condition_type: JumpCondition,
        label: String,
        condition_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a jump to a label conditioned on cmp(value, immediate).
    fn emit_conditional_jump_cmp_immediate(
        &self,
        c: &mut Context,
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
        g: &mut Context,
        offset_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a function return instruction.
    fn emit_return(
        &self,
        c: &mut Context,
        ret_pc_ptr: Range<u32>,
        caller_fp_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a call to an imported function.
    fn emit_imported_call(
        &self,
        c: &mut Context,
        module: &'a str,
        function: &'a str,
        inputs: Vec<Range<u32>>,
        outputs: Vec<Range<u32>>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a call to a local function.
    ///
    /// `saved_ret_pc_ptr` and `saved_caller_fp_ptr` are given in callee's frame space.
    fn emit_function_call(
        &self,
        c: &mut Context,
        function_label: String,
        function_frame_offset: u32,
        saved_ret_pc_ptr: Range<u32>,
        saved_caller_fp_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a call to a local function via a function pointer.
    ///
    /// `saved_ret_pc_ptr` and `saved_caller_fp_ptr` are given in callee's frame space.
    fn emit_indirect_call(
        &self,
        c: &mut Context,
        target_pc_ptr: Range<u32>,
        function_frame_offset: u32,
        saved_ret_pc_ptr: Range<u32>,
        saved_caller_fp_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits the equivalent set of instructions to a WASM operation.
    fn emit_wasm_op(
        &self,
        c: &mut Context,
        op: Operator<'a>,
        inputs: Vec<WasmOpInput>,
        output: Option<Range<u32>>,
    ) -> impl Into<Tree<Self::Directive>>;
}
