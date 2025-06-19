use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Display,
    ops::Range,
};

use crate::loader::flattening::{
    Generators, RegisterGenerator, ReturnInfo, TrapReason,
    settings::{JumpCondition, LoopFrameLayout, Settings},
};

pub struct PetraVmSetting;

#[allow(refining_impl_trait)]
impl<'a> Settings<'a> for PetraVmSetting {
    type Directive = Directive;

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
        mut saved_fps: BTreeSet<u32>,
    ) -> (RegisterGenerator<'a, Self>, LoopFrameLayout) {
        let mut rgen = RegisterGenerator::new();
        let mut fp_map = BTreeMap::new();

        // The only way to save the current frame pointer is with the
        // CALL instruction, which also saves the return PC, using slots
        // #0 (PC) and #1 (FP). So, if this loop requires the current FP,
        // we must allocate both as the first thing.
        if Some(&0) == saved_fps.first() {
            saved_fps.pop_first();
            let _pc_slot = rgen.allocate_words(Self::words_per_ptr());
            let fp_slot = rgen.allocate_words(Self::words_per_ptr());
            fp_map.insert(0, fp_slot);
        }

        let ret_info = need_ret_info.then(|| {
            // Allocate the return PC and frame pointer for the loop.
            let ret_pc = rgen.allocate_words(Self::words_per_ptr());
            let ret_fp = rgen.allocate_words(Self::words_per_ptr());
            ReturnInfo { ret_pc, ret_fp }
        });

        // Allocate the slots for the saved frame pointers.
        for depth in saved_fps {
            let outer_fp = rgen.allocate_words(Self::words_per_ptr());
            fp_map.insert(depth, outer_fp);
        }

        (
            rgen,
            LoopFrameLayout {
                saved_fps: fp_map,
                ret_info,
            },
        )
    }

    fn to_plain_local_jump(directive: Directive) -> Result<String, Directive> {
        if let Directive::JumpI {
            target: Immediate::LabelAddress(label),
        } = directive
        {
            Ok(label)
        } else {
            Err(directive)
        }
    }

    fn emit_label(
        &self,
        _g: &mut Generators<'a, '_, Self>,
        name: String,
        frame_size: Option<u32>,
    ) -> Directive {
        Directive::Label { name, frame_size }
    }

    fn emit_trap(&self, g: &mut Generators<'a, '_, Self>, trap: TrapReason) -> Vec<Directive> {
        // Assemble a trap frame according to https://petraprover.github.io/PetraVM/specification.html#36-exceptions
        // and return to address 0.

        let this_fp = g.r.allocate_words(Self::words_per_ptr());

        let trap_pc = g.r.allocate_words(Self::words_per_ptr());
        let trap_fp = g.r.allocate_words(Self::words_per_ptr());

        vec![
            Directive::AllocI {
                word_count: Immediate::Value(3),
                dest: trap_fp.clone(),
            },
            Directive::MvIW {
                value: Immediate::CurrentPC,
                dest_fp: trap_fp.clone(),
                dest_offset: 0..1,
            },
            Directive::FP {
                dest_ptr: this_fp.clone(),
            },
            Directive::MvVW {
                src_ptr: this_fp.clone(),
                dest_fp: trap_fp.clone(),
                dest_offset: 1..2,
            },
            Directive::MvIW {
                value: Immediate::Value(trap as u16),
                dest_fp: trap_fp.clone(),
                dest_offset: 2..3,
            },
            Directive::Ret {
                target_pc: trap_pc,
                target_fp: trap_fp,
            },
        ]
    }

    fn emit_allocate_label_frame(
        &self,
        _g: &mut Generators<'a, '_, Self>,
        label: String,
        result_ptr: Range<u32>,
    ) -> Directive {
        Directive::AllocI {
            word_count: FrameSize::Label(label),
            dest: result_ptr,
        }
    }

    fn emit_allocate_value_frame(
        &self,
        _g: &mut Generators<'a, '_, Self>,
        frame_size_ptr: Range<u32>,
        result_ptr: Range<u32>,
    ) -> Directive {
        Directive::AllocV {
            word_count_ptr: frame_size_ptr,
            frame_ptr: result_ptr,
        }
    }

    fn emit_copy(
        &self,
        g: &mut Generators<'a, '_, Self>,
        src_ptr: Range<u32>,
        dest_ptr: Range<u32>,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        todo!()
    }

    fn emit_copy_into_frame(
        &self,
        g: &mut Generators<'a, '_, Self>,
        src_ptr: Range<u32>,
        dest_frame_ptr: Range<u32>,
        dest_offset: Range<u32>,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        todo!()
    }

    fn emit_jump(&self, label: String) -> Self::Directive {
        todo!()
    }

    fn emit_jump_into_loop(
        &self,
        g: &mut Generators<'a, '_, Self>,
        loop_label: String,
        loop_frame_ptr: Range<u32>,
        ret_info_to_copy: Option<crate::loader::flattening::settings::ReturnInfosToCopy>,
        saved_curr_fp_ptr: Option<Range<u32>>,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        todo!()
    }

    fn emit_conditional_jump(
        &self,
        g: &mut Generators<'a, '_, Self>,
        condition_type: JumpCondition,
        label: String,
        condition_ptr: Range<u32>,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        todo!()
    }

    fn emit_conditional_jump_cmp_immediate(
        &self,
        g: &mut Generators<'a, '_, Self>,
        cmp: crate::loader::flattening::settings::ComparisonFunction,
        value_ptr: Range<u32>,
        immediate: u32,
        label: String,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        todo!()
    }

    fn emit_relative_jump(
        &self,
        g: &mut Generators<'a, '_, Self>,
        offset_ptr: Range<u32>,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        todo!()
    }

    fn emit_jump_out_of_loop(
        &self,
        g: &mut Generators<'a, '_, Self>,
        target_label: String,
        target_frame_ptr: Range<u32>,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        todo!()
    }

    fn emit_return(
        &self,
        g: &mut Generators<'a, '_, Self>,
        ret_pc_ptr: Range<u32>,
        caller_fp_ptr: Range<u32>,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        todo!()
    }

    fn emit_imported_call(
        &self,
        g: &mut Generators<'a, '_, Self>,
        module: &'a str,
        function: &'a str,
        inputs: Vec<Range<u32>>,
        outputs: Vec<Range<u32>>,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        todo!()
    }

    fn emit_function_call(
        &self,
        g: &mut Generators<'a, '_, Self>,
        function_label: String,
        function_frame_ptr: Range<u32>,
        saved_ret_pc_ptr: Range<u32>,
        saved_caller_fp_ptr: Range<u32>,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        todo!()
    }

    fn emit_indirect_call(
        &self,
        g: &mut Generators<'a, '_, Self>,
        target_pc_ptr: Range<u32>,
        function_frame_ptr: Range<u32>,
        saved_ret_pc_ptr: Range<u32>,
        saved_caller_fp_ptr: Range<u32>,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        todo!()
    }

    fn emit_table_get(
        &self,
        g: &mut Generators<'a, '_, Self>,
        table_idx: u32,
        entry_idx_ptr: Range<u32>,
        dest_ptr: Range<u32>,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        todo!()
    }

    fn emit_wasm_op(
        &self,
        g: &mut Generators<'a, '_, Self>,
        op: wasmparser::Operator<'a>,
        inputs: Vec<Range<u32>>,
        output: Option<Range<u32>>,
    ) -> impl Into<crate::loader::flattening::Tree<Self::Directive>> {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub enum Immediate16 {
    Value(u16),
    LabelFrameSize(String),
}

#[derive(Debug, Clone)]
pub enum Immediate32 {
    Value(u32),
    LabelAddress(String),
}

type Ptr = u16;

#[derive(Debug, Clone)]
pub enum Directive {
    Label {
        name: String,
        frame_size: Option<u16>,
    },

    AllocI {
        word_count: Immediate16,
        dest: Ptr,
    },

    AllocV {
        word_count: Ptr,
        dest: Ptr,
    },

    JumpI {
        target: Immediate32,
    },

    CallI {
        target: Immediate32,
        next_fp: Ptr,
    },

    Ret {
        target_pc: Ptr,
        target_fp: Ptr,
    },

    MvVW {
        src_ptr: Ptr,
        dest_fp: Ptr,
        dest_offset: Ptr,
    },

    MvIH {
        value: Immediate16,
        dest_fp: Ptr,
        dest_offset: Ptr,
    },

    FP {
        dest: Ptr,
        offset: Immediate16,
    },
}

impl Display for Directive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
