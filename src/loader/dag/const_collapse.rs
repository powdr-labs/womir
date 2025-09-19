use wasmparser::Operator;

use crate::loader::{
    dag::{self, Dag},
    settings::{MaybeConstant, Settings},
};

/// This is an optional optimization pass that collapses constants into
/// the node that uses them, if the ISA supports it.
///
/// For example, an `i32.add` instruction that takes a constant
/// `5` as input could be collapsed into an `i32.add_imm` instruction
/// that takes `5` as an immediate operand.
///
/// This pass only happens if `Settings::get_const_collapse_processor()` is
/// implemented by the user.
///
/// Returns the number of constants collapsed.
pub fn constant_collapse<'a, S: Settings<'a>>(settings: &S, dag: &mut Dag) -> usize {
    if let Some(processor) = settings.get_const_collapse_processor() {
        recursive_constant_collapse(&processor, &mut dag.nodes)
    } else {
        0
    }
}

fn recursive_constant_collapse(
    processor: &impl Fn(&Operator, &[MaybeConstant]),
    nodes: &mut [dag::Node],
) -> usize {
    let mut num_collapsed = 0;

    for node in nodes.iter_mut() {
        match &mut node.operation {
            dag::Operation::WASMOp(operator) => {
                todo!()
            }
            dag::Operation::Block { sub_dag, .. } => {
                // Constant collapse of the block node itself is not supported,
                // but we can recurse into the block's sub-DAG.
                num_collapsed += recursive_constant_collapse(processor, &mut sub_dag.nodes);
            }
            _ => {
                // Constant collapse is not supported for other node types.
            }
        }
    }

    num_collapsed
}
