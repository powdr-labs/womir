//! This module contains passes and interfaces specific to the read-write memory execution model.

use std::sync::atomic::AtomicU32;

use crate::loader::{
    CommonStages, FunctionAsm, FunctionProcessingStage, Module, Statistics,
    rwm::{liveness_dag::LivenessDag, register_allocation::AllocatedDag, settings::Settings},
    wom::dumb_jump_removal,
};

pub mod flattening;
pub mod liveness_dag;
pub mod register_allocation;
pub mod settings;

/// The RWM-specific stages of function processing.
#[derive(Debug)]
pub enum RWMStages<'a, S: Settings<'a>> {
    CommonStages(CommonStages<'a>),
    LivenessDag(LivenessDag<'a>),
    RegisterAllocatedDag(AllocatedDag<'a>),
    PlainFlatAsm(FunctionAsm<S::Directive>),
    DumbJumpOptFlatAsm(FunctionAsm<S::Directive>),
}

impl<'a, S: Settings<'a>> FunctionProcessingStage<'a, S> for RWMStages<'a, S> {
    type LastStage = FunctionAsm<S::Directive>;

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
                if let CommonStages::BlocklessDag(blockless_dag) = stage {
                    // Convert the blockless DAG to a liveness DAG representation.
                    let liveness_dag = LivenessDag::new(blockless_dag);
                    Self::LivenessDag(liveness_dag)
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
            Self::LivenessDag(liveness_dag) => {
                // Allocate read-write registers using the liveness information.
                let (allocated_dag, copies_saved) =
                    register_allocation::optimistic_allocation::<S>(ctx, func_idx, liveness_dag);
                if let Some(stats) = stats {
                    stats.register_copies_saved += copies_saved;
                }
                Self::RegisterAllocatedDag(allocated_dag)
            }
            Self::RegisterAllocatedDag(allocated_dag) => {
                // Flatten the DAG into assembly-like representation.
                Self::PlainFlatAsm(flattening::flatten_dag(
                    settings,
                    ctx,
                    label_gen,
                    func_idx,
                    allocated_dag,
                ))
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

impl<'a, S: Settings<'a>> From<CommonStages<'a>> for RWMStages<'a, S> {
    fn from(stage: CommonStages<'a>) -> Self {
        Self::CommonStages(stage)
    }
}
