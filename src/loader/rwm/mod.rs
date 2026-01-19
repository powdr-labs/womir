//! This module contains passes and interfaces specific to the read-write memory execution model.

use std::sync::atomic::AtomicU32;

use crate::loader::{
    CommonStages, FunctionProcessingStage, Module, Statistics,
    rwm::{liveness_dag::LivenessDag, register_allocation::AllocatedDag},
    settings::Settings,
};

pub mod flattening;
pub mod liveness_dag;
pub mod register_allocation;
pub mod settings;

/// The RWM-specific stages of function processing.
#[derive(Debug)]
pub enum RWMStages<'a> {
    CommonStages(CommonStages<'a>),
    LivenessDag(LivenessDag<'a>),
    RegisterAllocatedDag(AllocatedDag<'a>),
}

impl<'a, S: Settings> FunctionProcessingStage<'a, S> for RWMStages<'a> {
    type LastStage = AllocatedDag<'a>;

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
                    register_allocation::optimistic_allocation::<S>(func_idx, liveness_dag);
                if let Some(stats) = stats {
                    stats.register_copies_saved += copies_saved;
                }
                Self::RegisterAllocatedDag(allocated_dag)
            }
            Self::RegisterAllocatedDag(allocated_dag) => {
                // TODO: There are more steps to come, but for now, just return itself.
                Self::RegisterAllocatedDag(allocated_dag)
            }
        })
    }

    fn consume_last_stage(self) -> Result<Self::LastStage, Self> {
        if let Self::RegisterAllocatedDag(allocated_dag) = self {
            Ok(allocated_dag)
        } else {
            Err(self)
        }
    }
}

impl<'a> From<CommonStages<'a>> for RWMStages<'a> {
    fn from(stage: CommonStages<'a>) -> Self {
        Self::CommonStages(stage)
    }
}
