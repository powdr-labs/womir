//! Pass that takes a blockless dag and calculates liveness information for each node.

use std::collections::{HashMap, VecDeque};

use crate::loader::{
    blockless_dag::{
        BlocklessDag, BreakTarget, GenericBlocklessDag, GenericNode, Node as BDNode, TargetType,
    },
    dag::{NodeInput, ValueOrigin},
};

#[derive(Debug)]
pub struct Liveness {
    /// Last usage of a value produced by a node.
    ///
    /// Maps (node index, output index) to the index of the last node that uses it.
    last_usage: HashMap<(usize, u32), usize>,

    /// The set of outputs indexed from the Input node that are redirected
    /// as-is to the next iteration of the loop.
    ///
    /// The vector is sorted, and contains no duplicates.
    ///
    /// This is useful to detect outer values that are read by the loop, but
    /// not written, so they can be preserved across the entire loop execution,
    /// eliding unnecessary copies.
    ///
    /// On the toplevel block (which is not a loop), this is always empty.
    redirected_inputs: Vec<u32>,
}

impl Liveness {
    /// Query the liveness information for a given node output.
    ///
    /// Returns the index of the last node that uses the output.
    ///
    /// TODO: calculate the liveness for all possible control flow paths,
    /// and use the _curr_node_idx parameter to fine grain the query
    /// based on what path is being taken.
    pub fn query_liveness(&self, _curr_node_idx: usize, node_idx: usize, output_idx: u32) -> usize {
        self.last_usage[&(node_idx, output_idx)]
    }

    pub fn query_if_input_is_redirected(&self, input_idx: u32) -> bool {
        self.redirected_inputs.binary_search(&input_idx).is_ok()
    }
}

pub type LivenessDag<'a> = GenericBlocklessDag<'a, Liveness>;

pub type Node<'a> = GenericNode<'a, Liveness>;

impl<'a> LivenessDag<'a> {
    pub fn new(dag: BlocklessDag<'a>) -> Self {
        // The top-level block does not have a stack entry,
        // because it is not a loop.
        process_block(dag, &mut VecDeque::new())
    }
}

/// Entry tracking the input redirection for a loop block.
struct ControlStackEntry {
    is_input_redirected: Vec<bool>,
    /// Input map to previous block
    input_map: HashMap<u32, u32>,
}

fn process_block<'a>(
    dag: BlocklessDag<'a>,
    control_stack: &mut VecDeque<ControlStackEntry>,
) -> LivenessDag<'a> {
    use super::blockless_dag::Operation::*;

    /// Tests if the iteration inputs are being redirected as-is.
    fn handle_iteration_inputs<'b>(
        control_stack: &mut VecDeque<ControlStackEntry>,
        break_target: &BreakTarget,
        inputs: impl Iterator<Item = &'b NodeInput>,
    ) {
        if break_target.kind == TargetType::FunctionOrLoop
            // If the target depth is not in the control stack, it means
            // this is not a loop (it is a function return).
            && control_stack.len() > break_target.depth as usize
        {
            for (input_idx, input) in inputs.enumerate() {
                // There is no point in checking further if this input is already
                // marked as not redirected.
                if !control_stack[break_target.depth as usize].is_input_redirected[input_idx] {
                    continue;
                }

                if let NodeInput::Reference(ValueOrigin {
                    node: 0,
                    output_idx,
                }) = input
                {
                    let mut output_idx = Some(*output_idx);
                    let mut depth = 0;

                    // Map the output index through the stack of loops.
                    while let Some(output_idx_val) = output_idx
                        && depth < break_target.depth
                    {
                        output_idx = control_stack[depth as usize]
                            .input_map
                            .get(&output_idx_val)
                            .copied();
                        depth += 1;
                    }

                    // The value is being carried over as-is only if the mapped
                    // output index matches the input index. If not, we mark it
                    // as not redirected.
                    if output_idx != Some(input_idx as u32) {
                        control_stack[break_target.depth as usize].is_input_redirected[input_idx] =
                            false;
                    }
                } else {
                    // Some arbitrary value is being used, so it is not a redirected input.
                    control_stack[break_target.depth as usize].is_input_redirected[input_idx] =
                        false;
                }
            }
        }
    }

    let nodes = dag.nodes;
    let mut last_usage = HashMap::new();
    let mut liveness_nodes: Vec<Node<'a>> = Vec::with_capacity(nodes.len());
    for (
        index,
        BDNode {
            operation,
            inputs,
            output_types,
        },
    ) in nodes.into_iter().enumerate()
    {
        // For each input, we mark its last used node as the current node index.
        for input in &inputs {
            if let NodeInput::Reference(ValueOrigin { node, output_idx }) = input {
                last_usage.insert((*node, *output_idx), index);
            }
        }

        // Initialize last used node to the current node index
        for output_idx in 0..(output_types.len() as u32) {
            last_usage.insert((index, output_idx), index);
        }

        // Process subnodes recursively
        let operation = {
            match operation {
                Loop {
                    sub_dag,
                    break_targets,
                } => {
                    // If current block is a loop, for each input to this node that is
                    // carried directly from this block input, we create an entry in the
                    // input map.
                    let mut input_map = HashMap::new();
                    if !control_stack.is_empty() {
                        for (input_idx, input) in inputs.iter().enumerate() {
                            if let NodeInput::Reference(ValueOrigin {
                                node: 0,
                                output_idx,
                            }) = input
                            {
                                input_map.insert(input_idx as u32, *output_idx);
                            }
                        }
                    }
                    let old_control_stack_len = control_stack.len();
                    control_stack.push_front(ControlStackEntry {
                        is_input_redirected: vec![true; inputs.len()],
                        input_map,
                    });
                    let sub_dag = process_block(sub_dag, control_stack);

                    // There is no need to pop_front here, because it is done by the process_block.
                    assert_eq!(control_stack.len(), old_control_stack_len);

                    Loop {
                        sub_dag,
                        break_targets,
                    }
                }

                // Other operations remain unchanged, but we have to spell them out
                // because the types are different.
                Inputs => Inputs,
                WASMOp(operator) => WASMOp(operator),
                Label { id } => Label { id },
                Br(break_target) => Br(break_target),
                BrIf(break_target) => BrIf(break_target),
                BrIfZero(break_target) => BrIfZero(break_target),
                BrTable { targets } => BrTable { targets },
            }
        };

        // Update input redirection tracking based on breaks to the loop
        if !control_stack.is_empty() {
            match &operation {
                Br(break_target) => {
                    handle_iteration_inputs(control_stack, break_target, inputs.iter());
                }
                BrIf(break_target) | BrIfZero(break_target) => {
                    handle_iteration_inputs(
                        control_stack,
                        break_target,
                        inputs[0..inputs.len() - 1].iter(),
                    );
                }
                BrTable { targets } => {
                    for target in targets {
                        handle_iteration_inputs(
                            control_stack,
                            &target.target,
                            target
                                .input_permutation
                                .iter()
                                .map(|perm| &inputs[*perm as usize]),
                        );
                    }
                }
                _ => {}
            }
        }

        liveness_nodes.push(Node {
            operation,
            inputs,
            output_types,
        });
    }

    let mut redirected_inputs = Vec::new();
    if let Some(entry) = control_stack.pop_front() {
        for (input_idx, is_redirected) in entry.is_input_redirected.into_iter().enumerate() {
            if is_redirected {
                redirected_inputs.push(input_idx as u32);
            }
        }
    }

    LivenessDag {
        nodes: liveness_nodes,
        block_data: Liveness {
            last_usage,
            redirected_inputs,
        },
    }
}
