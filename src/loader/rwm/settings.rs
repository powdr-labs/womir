use std::ops::Range;
use wasmparser::Operator;

use crate::{
    loader::{self, rwm::flattening::Context, settings::WasmOpInput},
    utils::tree::Tree,
};

/// Trait controlling the behavior of the flattening process.
pub trait Settings<'a>: loader::Settings {
    type Directive;

    /// Emits a directive to mark a code position.
    fn emit_label(&self, c: &mut Context, name: String) -> impl Into<Tree<Self::Directive>>;

    /// Copies a single word between two registers.
    fn emit_copy(
        &self,
        g: &mut Context,
        src_reg: u32,
        dest_reg: u32,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits an unconditional jump to a label.
    fn emit_jump(&self, c: &mut Context, target: &str) -> impl Into<Tree<Self::Directive>>;

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
    fn emit_function_call(
        &self,
        c: &mut Context,
        function_label: String,
        function_frame_ptr: Range<u32>,
        saved_ret_pc_ptr: Range<u32>,
        saved_caller_fp_ptr: Range<u32>,
    ) -> impl Into<Tree<Self::Directive>>;

    /// Emits a call to a local function via a function pointer.
    fn emit_indirect_call(
        &self,
        c: &mut Context,
        target_pc_ptr: Range<u32>,
        function_frame_ptr: Range<u32>,
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
