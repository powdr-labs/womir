//! Pass that takes a blockless dag and calculates liveness information for each node.
//!
//! TODO: I think there is a way to merge this pass with register allocation, by using
//! the same bottom-up algorithm used in wom::flattening::allocate_registers, keeping
//! track of the state independently for each execution path.

use std::collections::HashMap;

use crate::loader::{
    blockless_dag::{GenericBlocklessDag, GenericNode, GenericNode as BDNode},
    dag::{NodeInput, ValueOrigin},
    passes::{blockless_dag::BlocklessDag, calc_input_redirection::Redirection},
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
    pub fn from_blockless_dag(dag: BlocklessDag<'a>) -> Self {
        use crate::loader::passes::blockless_dag::Operation::*;

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
                        let sub_dag = LivenessDag::from_blockless_dag(sub_dag);

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

            liveness_nodes.push(Node {
                operation,
                inputs,
                output_types,
            });
        }

        let redirections = dag.block_data;
        let redirected_inputs = redirections
            .into_iter()
            .enumerate()
            .filter_map(|(idx, redir)| {
                (redir == Redirection::FromInput(idx as u32)).then_some(idx as u32)
            })
            .collect();

        LivenessDag {
            nodes: liveness_nodes,
            block_data: Liveness {
                last_usage,
                redirected_inputs,
            },
        }
    }
}
