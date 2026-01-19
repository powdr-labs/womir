//! This module contains passes and interfaces specific to write-once memory execution model.

use std::sync::atomic::AtomicU32;

use crate::loader::{
    CommonFunctionProcessingStage, FunctionProcessingStage, Module, Statistics,
    wom::{flattening::WriteOnceAsm, settings::Settings},
};

pub mod dumb_jump_removal;
pub mod flattening;
pub mod settings;

/// The Wom-specific stages of function processing.
#[derive(Debug)]
pub enum WomFunctionProcessingStage<'a, S: Settings<'a>> {
    CommonStages(CommonFunctionProcessingStage<'a>),
    PlainFlatAsm(WriteOnceAsm<S::Directive>),
    DumbJumpOptFlatAsm(WriteOnceAsm<S::Directive>),
}

impl<'a, S: Settings<'a>> FunctionProcessingStage<'a, S> for WomFunctionProcessingStage<'a, S> {
    type LastStage = WriteOnceAsm<S::Directive>;

    fn advance_stage(
        self,
        settings: &S,
        ctx: &Module<'a>,
        func_idx: u32,
        label_gen: &AtomicU32,
        mut stats: Option<&mut Statistics>,
    ) -> wasmparser::Result<Self> {
        Ok(match self {
            Self::CommonStages(stage) => {
                if let CommonFunctionProcessingStage::BlocklessDag(blockless_dag) = stage {
                    // Flatten the blockless DAG into assembly-like representation.
                    let (flat_asm, copies_saved) =
                        flattening::flatten_dag(settings, ctx, label_gen, blockless_dag, func_idx);
                    if let Some(stats) = stats {
                        stats.register_copies_saved += copies_saved;
                    }
                    Self::PlainFlatAsm(flat_asm)
                } else {
                    // Advance the common stage first.
                    Self::CommonStages(stage.advance_stage(
                        settings,
                        ctx,
                        func_idx,
                        label_gen,
                        stats.as_deref_mut(),
                    )?)
                }
            }
            Self::PlainFlatAsm(mut flat_asm) => {
                // Optimization pass: remove useless jumps.
                let jumps_removed = dumb_jump_removal::remove_dumb_jumps(settings, &mut flat_asm);
                if let Some(stats) = stats {
                    stats.useless_jumps_removed += jumps_removed;
                }
                Self::DumbJumpOptFlatAsm(flat_asm)
            }
            Self::DumbJumpOptFlatAsm(flat_asm) => {
                // Processing is complete. Just return itself.
                Self::DumbJumpOptFlatAsm(flat_asm)
            }
        })
    }

    fn consume_last_stage(self) -> Result<Self::LastStage, Self> {
        if let Self::DumbJumpOptFlatAsm(flat_asm) = self {
            Ok(flat_asm)
        } else {
            Err(self)
        }
    }
}

impl<'a, S: Settings<'a>> From<CommonFunctionProcessingStage<'a>>
    for WomFunctionProcessingStage<'a, S>
{
    fn from(stage: CommonFunctionProcessingStage<'a>) -> Self {
        Self::CommonStages(stage)
    }
}
