use std::{cell::Cell, collections::HashMap};

use wasmparser::Operator;

use crate::loader::{
    BlockKind,
    dag::{self, Dag, NodeInput, Operation, WasmValue},
    settings::{MaybeConstant, Settings},
};

/// This is an optional optimization pass that collapses constants into
/// the node that uses them, if the ISA supports it.
///
/// For example, if the output ISA is RISC-V, in an `i32.add` instruction that
/// has a constant node `5` as input, the value `5` could be collapsed into an
/// immediate for `addi` instruction.
///
/// This pass only happens if `Settings::get_const_collapse_processor()` is
/// implemented by the user.
///
/// Returns the number of constants collapsed.
pub fn constant_collapse<S: Settings>(dag: &mut Dag) -> usize {
    if let Some(processor) = S::get_const_collapse_processor() {
        let mut finder = ConstantInputFinder::new();
        recursive_constant_collapse(&mut finder, &processor, &mut dag.nodes, HashMap::new())
    } else {
        0
    }
}

fn recursive_constant_collapse(
    finder: &mut ConstantInputFinder,
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
                let (has_constant, input_constants) = finder.find_constant_inputs(
                    &node.inputs,
                    prev_nodes,
                    const_block_inputs.clone(),
                );
                if has_constant {
                    // Call the user-provided processor to potentially mark constants to be collapsed.
                    processor(operator, input_constants);

                    // Collapse any inputs that were marked.
                    for (input, maybe_const) in node.inputs.iter_mut().zip(input_constants) {
                        if let MaybeConstant::ReferenceConstant {
                            value,
                            must_collapse,
                        } = maybe_const
                            && must_collapse.get()
                        {
                            *input = NodeInput::Constant(value.clone());
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
                    finder
                        .find_constant_inputs(&node.inputs, prev_nodes, const_block_inputs.clone())
                        .1
                        .iter()
                        .enumerate()
                        .filter_map(|(idx, maybe_const)| match maybe_const {
                            MaybeConstant::ReferenceConstant { value, .. } => {
                                Some((idx as u32, value.clone()))
                            }
                            MaybeConstant::CollapsedConstant(value) => {
                                Some((idx as u32, value.clone()))
                            }
                            MaybeConstant::NonConstant => None,
                        })
                        .collect()
                } else {
                    // Loops have multiple entry points, so we can't be sure a constant input
                    // at entry will be always constant. Besides, an optimized WASM wouldn't
                    // have constant inputs to loops anyway.
                    HashMap::new()
                };

                num_collapsed += recursive_constant_collapse(
                    finder,
                    processor,
                    &mut sub_dag.nodes,
                    const_inputs,
                );
            }
            _ => {
                // Constant collapse is not supported for other node types.
            }
        }
    }

    num_collapsed
}

struct ConstantInputFinder {
    /// This buffer will be reused to avoid allocations on each node.
    buffer: Vec<MaybeConstant>,
}

impl ConstantInputFinder {
    fn new() -> Self {
        Self { buffer: Vec::new() }
    }

    /// Finds which of the given inputs are constants.
    fn find_constant_inputs<'a>(
        &'a mut self,
        inputs: &[NodeInput],
        nodes: &mut [dag::Node],
        const_block_inputs: HashMap<u32, WasmValue>,
    ) -> (bool, &'a [MaybeConstant]) {
        let mut has_constant = false;

        // Check if any of the inputs are constants.
        self.buffer.clear();
        self.buffer.extend(inputs.iter().map(|input| {
            let origin = match input {
                NodeInput::Reference(value_origin) => value_origin,
                NodeInput::Constant(wasm_value) => {
                    // In default Womir pipeline, there shouldn't be any constant
                    // before this pass. But we handle it anyway, in case this pass
                    // is used in a different context by the user.
                    return MaybeConstant::CollapsedConstant(wasm_value.clone());
                }
            };

            match &nodes[origin.node].operation {
                Operation::Inputs => {
                    // This refers to the input of the block, we need to check if it's a constant.
                    const_block_inputs.get(&origin.output_idx).cloned()
                }
                Operation::WASMOp(op) => WasmValue::try_from(op).ok(),
                _ => None,
            }
            .map_or(MaybeConstant::NonConstant, |value| {
                has_constant = true;
                MaybeConstant::ReferenceConstant {
                    value,
                    must_collapse: Cell::new(false),
                }
            })
        }));

        (has_constant, &self.buffer)
    }
}
