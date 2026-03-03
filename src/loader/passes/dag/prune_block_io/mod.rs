//! This pass takes a DAG and removes unnecessary inputs and outputs from
//! blocks. These spurious inputs and outputs may come from the original Wasm
//! code, but they can also be introduced by the `locals_data_flow` pass, which is
//! conservative in its analysis of local usage, or can be orphans from const
//! dedup/collapse.

use crate::loader::passes::calc_input_redirection::RedirDag;

mod bottom_up;
mod top_down;

#[derive(Default, Debug)]
pub struct Statistics {
    pub removed_nodes: usize,
    pub removed_block_outputs: usize,
    pub removed_loop_inputs: usize,
    // We don't track removed block inputs because they have no visible effect
    // on the generated code. They may, however, help remove more nodes and block
    // inputs, which is already counted.
}

/// Prunes block inputs and outputs that are not actually used.
///
/// Returns the statistics of the pruning process.
pub fn prune_block_io(dag: &mut RedirDag<'_>) -> Statistics {
    let mut stats = Statistics::default();

    // If outputs are removed, we might have created new opportunities for
    // input removals, and vice-versa, so we need to repeat until we reach
    // a fixed point.
    let mut must_run_bottom_up = true;
    let mut must_run_top_down = true;
    loop {
        // The sub-pass that removes unused block outputs and pure nodes with no users.
        if must_run_bottom_up {
            let result = bottom_up::remove_useless_outputs(dag);
            stats.removed_nodes += result.removed_nodes;
            stats.removed_block_outputs += result.removed_block_outputs;

            // Either removal of outputs or nodes might leave loop inputs unused,
            // which can be removed by the next top-down sub-pass.
            must_run_top_down |= result.removed_nodes > 0 || result.removed_block_outputs > 0;
            must_run_bottom_up = false;
        }

        if !must_run_bottom_up && !must_run_top_down {
            break;
        }

        // The sub-pass that removes unecessary block inputs. It is more complex because
        // it handles loops, and it alone needs to iterate to reach a fixed point.
        // But we are already in a fixed-point loop, so we just run it once.
        if must_run_top_down {
            let result = top_down::remove_useless_inputs(dag);
            stats.removed_loop_inputs += result.removed_loop_inputs;
            stats.removed_block_outputs += result.removed_block_outputs;

            // If any loop input was removed, we might have left nodes or blocks dangling,
            // that can be removed by the bottom-up sub-pass.
            must_run_bottom_up = result.removed_loop_inputs > 0;

            // If any block output was removed, we might have uncovered new unused loop inputs,
            // that can be removed by the next iteration of the top-down sub-pass.
            must_run_top_down = result.removed_block_outputs > 0;

            // We probably don't have to concern with plain block inputs removed, because
            // any case that doesn't involve a loop input removal would also be covered
            // by the bottom-up sub-pass.
        }

        if !must_run_bottom_up && !must_run_top_down {
            break;
        }
    }

    stats
}
