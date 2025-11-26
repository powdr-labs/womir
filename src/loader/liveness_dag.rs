//! Pass that takes a blockless dag and calculates liveness information for each node.

use itertools::Itertools;
use wasmparser::ValType;

use crate::loader::{
    blockless_dag::{BlocklessDag, GenericBlocklessDag, GenericNode, Node as BDNode},
    dag::{NodeInput, ValueOrigin},
};

#[derive(Debug)]
pub struct Output {
    pub ty: ValType,
    pub last_used_at: u32,
}

pub type LivenessDag<'a> = GenericBlocklessDag<'a, Output>;

pub type Node<'a> = GenericNode<'a, Output>;

impl<'a> LivenessDag<'a> {
    pub fn new(dag: BlocklessDag<'a>) -> Self {
        // Process nodes to set up last_used_at
        let nodes = process_nodes(dag.nodes);

        LivenessDag { nodes }
    }
}

fn process_nodes<'a>(nodes: Vec<BDNode<'a>>) -> Vec<Node<'a>> {
    let mut liveness_nodes: Vec<Node<'a>> = Vec::with_capacity(nodes.len());
    for (
        index,
        BDNode {
            operation,
            inputs,
            outputs,
        },
    ) in nodes.into_iter().enumerate()
    {
        // For each input, we mark its last_used_at to the current node index.
        for input in &inputs {
            if let NodeInput::Reference(ValueOrigin { node, output_idx }) = input {
                liveness_nodes[*node].outputs[*output_idx as usize].last_used_at = index as u32;
            }
        }

        // Initialize last_used_at to the current node index
        let outputs = outputs
            .into_iter()
            .map(|output| Output {
                ty: output,
                last_used_at: index as u32,
            })
            .collect_vec();

        // Process subnodes recursively
        let operation = {
            use super::blockless_dag::Operation::*;
            match operation {
                Loop {
                    sub_dag,
                    break_targets,
                } => Loop {
                    sub_dag: GenericBlocklessDag {
                        nodes: process_nodes(sub_dag.nodes),
                    },
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
            outputs,
        });
    }

    liveness_nodes
}
