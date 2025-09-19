use std::{cell::Cell, collections::HashMap};

use itertools::Itertools;
use wasmparser::Operator;

use crate::loader::{
    BlockKind,
    dag::{self, Dag, NodeInput, Operation, WasmValue},
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
        recursive_constant_collapse(&processor, &mut dag.nodes, HashMap::new())
    } else {
        0
    }
}

fn recursive_constant_collapse(
    processor: &impl Fn(&Operator, &[MaybeConstant]),
    nodes: &mut [dag::Node],
    const_block_inputs: HashMap<u32, WasmValue>,
) -> usize {
    let mut num_collapsed = 0;

    for i in 0..nodes.len() {
        // We split the nodes so that previous nodes can be borrowed (immutably) independently
        // from the currently processed node (mutably borrowed).
        let (prev_nodes, node) = nodes.split_at_mut(i);
        let node = &mut node[0];

        match &mut node.operation {
            dag::Operation::WASMOp(operator) => {
                let (has_constant, input_constants) =
                    find_constant_inputs(&node.inputs, prev_nodes, const_block_inputs.clone());
                if has_constant {
                    // Call the user-provided processor to potentially modify the input constants.
                    processor(operator, &input_constants);

                    // Collapse any inputs that were marked for collapsing.
                    for (input, maybe_const) in
                        node.inputs.iter_mut().zip(input_constants.into_iter())
                    {
                        if let MaybeConstant::ReferenceConstant {
                            value,
                            must_collapse,
                        } = maybe_const
                            && must_collapse.get()
                        {
                            *input = NodeInput::Constant(value);
                            num_collapsed += 1;
                        }
                    }
                }
            }
            dag::Operation::Block { sub_dag, kind } => {
                // Constant input collapse to the block node itself is not supported,
                // but we can recurse into the block's sub-DAG.

                // In order to collapse constants that come from the block inputs,
                // we need to know which block inputs are constants.
                let const_inputs = if matches!(kind, BlockKind::Block) {
                    find_constant_inputs(&node.inputs, prev_nodes, const_block_inputs.clone())
                        .1
                        .into_iter()
                        .enumerate()
                        .filter_map(|(idx, maybe_const)| match maybe_const {
                            MaybeConstant::ReferenceConstant { value, .. } => {
                                Some((idx as u32, value))
                            }
                            MaybeConstant::CollapsedConstant(value) => Some((idx as u32, value)),
                            MaybeConstant::NonConstant => None,
                        })
                        .collect()
                } else {
                    // Loops have multiple entry points, so we can't be sure a constant input
                    // is always constant. Besides, an optimized WASM wouldn't have constant
                    // inputs to loops anyway.
                    HashMap::new()
                };

                num_collapsed +=
                    recursive_constant_collapse(processor, &mut sub_dag.nodes, const_inputs);
            }
            _ => {
                // Constant collapse is not supported for other node types.
            }
        }
    }

    num_collapsed
}

fn find_constant_inputs(
    inputs: &[NodeInput],
    nodes: &mut [dag::Node],
    const_block_inputs: HashMap<u32, WasmValue>,
) -> (bool, Vec<MaybeConstant>) {
    let mut has_constant = false;

    // Check if any of the inputs are constants.
    let input_constants = inputs
        .iter()
        .map(|input| {
            let origin = match input {
                NodeInput::Reference(value_origin) => value_origin,
                NodeInput::Constant(wasm_value) => {
                    // Weird... there shouldn't be any collapsed constants before this pass.
                    // But we can handle it anyway.
                    return MaybeConstant::CollapsedConstant(wasm_value.clone());
                }
            };

            match &nodes[origin.node].operation {
                Operation::Inputs => {
                    // This refers to the input of the block, we need to check if it's a constant.
                    const_block_inputs.get(&origin.output_idx).cloned()
                }
                Operation::WASMOp(op) => op.try_into().ok(),
                _ => None,
            }
            .map_or(MaybeConstant::NonConstant, |value| {
                has_constant = true;
                MaybeConstant::ReferenceConstant {
                    value,
                    must_collapse: Cell::new(false),
                }
            })
        })
        .collect_vec();

    (has_constant, input_constants)
}
