use std::collections::HashSet;

use itertools::Itertools;
use wasmparser::Operator as Op;

use crate::loader::{
    BlockKind,
    dag::{Dag, Node, Operation, ValueOrigin},
};

/// This optimization pass removes nodes that have no side effects, and whose outputs are never used.
///
/// Returns the new DAG and the number of removed nodes.
pub fn remove_dangling_nodes(dag: &mut Dag) -> usize {
    // This is the top-level function, so we can't change its inputs.
    let (removed_count, _) = recursive_removal(&mut dag.nodes, false);
    log::info!("Removed {} dangling nodes from the DAG", removed_count);

    removed_count
}

fn recursive_removal<'a>(nodes: &mut Vec<Node<'a>>, remove_inputs: bool) -> (usize, Vec<u32>) {
    let mut removed_count = 0;

    // The first pass happens bottom up, and just detects which nodes can be removed.
    let mut used_outputs = HashSet::new();
    let mut to_be_removed = nodes
        .iter_mut()
        .enumerate()
        .rev()
        .filter_map(|(node_idx, node)| {
            removed_count += recurse_into_block(node);

            let to_be_removed = is_pure(node)
                && (0..node.output_types.len()).all(|output_idx| {
                    !used_outputs.contains(&ValueOrigin::new(node_idx, output_idx as u32))
                });

            if !to_be_removed {
                // If the node is not to be removed, mark its inputs as used.
                for node in node.inputs.iter() {
                    used_outputs.insert(node.clone());
                }
                None
            } else {
                Some(node_idx)
            }
        })
        .collect_vec();
    removed_count += to_be_removed.len();

    // If requested, use the used_outputs to remove inputs that are no longer needed.
    let inputs = &mut nodes[0];
    assert!(matches!(inputs.operation, Operation::Inputs { .. }));
    let mut removed_inputs = Vec::new();
    let input_map = if remove_inputs {
        let mut input_map = vec![u32::MAX; inputs.output_types.len()];
        let mut new_idx = 0;
        for output_idx in 0..inputs.output_types.len() as u32 {
            let origin = ValueOrigin::new(0, output_idx);
            if used_outputs.contains(&origin) {
                input_map[output_idx as usize] = new_idx;
                new_idx += 1;
            } else {
                removed_inputs.push(output_idx);
            }
        }
        input_map
    } else {
        (0..inputs.output_types.len() as u32).collect_vec()
    };

    // The second pass happens top down, and actually removes the nodes.
    let mut offset = 0;
    let mut offset_map = Vec::new();
    *nodes = std::mem::take(nodes)
        .into_iter()
        .enumerate()
        .filter_map(|(node_idx, mut node)| {
            let res = if to_be_removed.last() == Some(&node_idx) {
                // Remove the node if it is in the to-be-removed list.
                to_be_removed.pop();
                offset += 1;
                None
            } else {
                // Fix the node index for all the inputs of a node that is not being removed.
                for input in node.inputs.iter_mut() {
                    input.node -= offset_map[input.node as usize];

                    // If this refers to the inputs node, we need to remap it.
                    if input.node == 0 {
                        input.output_idx = input_map[input.output_idx as usize];
                    }
                }
                Some(node)
            };

            offset_map.push(offset);
            res
        })
        .collect_vec();

    (removed_count, removed_inputs)
}

/// Checks if a node is pure
fn is_pure(node: &Node) -> bool {
    match &node.operation {
        Operation::WASMOp(Op::I32Const { .. })
        | Operation::WASMOp(Op::I64Const { .. })
        | Operation::WASMOp(Op::F32Const { .. })
        | Operation::WASMOp(Op::F64Const { .. })
        | Operation::WASMOp(Op::V128Const { .. }) => true,
        // TODO: there are many more operations that are pure in WASM that could be added here.
        // But only consts are really important for optimized WASM input.
        _ => false,
    }
}

/// Apply the dangling removal recursivelly to a block node.
fn recurse_into_block(node: &mut Node) -> usize {
    if let Operation::Block { kind, sub_dag } = &mut node.operation {
        // It is too complicated to mess with loops inputs, so we keep them as is.
        // TODO: handle loop inputs properly. Probably useless if the WASM is already optimized.
        let remove_inputs = match kind {
            BlockKind::Loop => false,
            BlockKind::Block => true,
        };

        let (count, removed_inputs) = recursive_removal(&mut sub_dag.nodes, remove_inputs);

        let mut removed_inputs = removed_inputs.into_iter().peekable();
        node.inputs = std::mem::take(&mut node.inputs)
            .into_iter()
            .enumerate()
            .filter_map(|(input_idx, input)| {
                if removed_inputs.peek() == Some(&(input_idx as u32)) {
                    removed_inputs.next();
                    None
                } else {
                    Some(input)
                }
            })
            .collect();

        count
    } else {
        0
    }
}
