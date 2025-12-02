//! Pass that takes a blockless dag and calculates liveness information for each node.

use std::collections::HashMap;

use crate::loader::{
    blockless_dag::{BlocklessDag, GenericBlocklessDag, GenericNode, Node as BDNode},
    dag::{NodeInput, ValueOrigin},
};

#[derive(Debug)]
pub struct Liveness(HashMap<(usize, u32), u32>);

impl Liveness {
    /// Query the liveness information for a given node output.
    ///
    /// Returns the index of the last node that uses the output.
    ///
    /// TODO: calculate the liveness for all possible control flow paths,
    /// and use the _curr_node_idx parameter to fine grain the query
    /// based on what path is being taken.
    pub fn query_liveness(&self, _curr_node_idx: usize, node_idx: usize, output_idx: u32) -> u32 {
        self.0[&(node_idx, output_idx)]
    }
}

pub type LivenessDag<'a> = GenericBlocklessDag<'a, Liveness>;

pub type Node<'a> = GenericNode<'a, Liveness>;

impl<'a> LivenessDag<'a> {
    pub fn new(dag: BlocklessDag<'a>) -> Self {
        let nodes = dag.nodes;
        let mut liveness_map = HashMap::new();
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
                    liveness_map.insert((*node, *output_idx), index as u32);
                }
            }

            // Initialize last used node to the current node index
            for output_idx in 0..(output_types.len() as u32) {
                liveness_map.insert((index, output_idx), index as u32);
            }

            // Process subnodes recursively
            let operation = {
                use super::blockless_dag::Operation::*;
                match operation {
                    Loop {
                        sub_dag,
                        break_targets,
                    } => Loop {
                        sub_dag: LivenessDag::new(sub_dag),
                        break_targets,
                    },

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

        LivenessDag {
            nodes: liveness_nodes,
            block_data: Liveness(liveness_map),
        }
    }
}
