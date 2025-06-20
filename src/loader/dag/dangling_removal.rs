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

    removed_count
}

fn recursive_removal<'a>(nodes: &mut Vec<Node<'a>>, remove_inputs: bool) -> (usize, Vec<u32>) {
    let mut removed_count = 0;

    // The first pass happens bottom up, and just detects which nodes can be removed.
    let mut used_outputs = HashSet::new();
    let to_be_removed = nodes
        .iter_mut()
        .enumerate()
        .rev()
        .filter_map(|(node_idx, node)| {
            removed_count += recurse_into_block(node);

            let to_be_removed = !may_have_side_effect(node)
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

    remove_indices_from_vec(&mut inputs.output_types, &removed_inputs);

    // The second pass happens top down, and actually removes the nodes.
    let mut offset = 0;
    let mut offset_map = Vec::new();
    let mut to_be_removed = to_be_removed.into_iter().rev().peekable();
    let mut node_idx = 0usize..;
    nodes.retain_mut(|node| {
        let node_idx = node_idx.next();
        let res = if to_be_removed.peek() == node_idx.as_ref() {
            // Remove the node if it is in the to-be-removed list.
            to_be_removed.next();
            offset += 1;
            false
        } else {
            // Fix the node index for all the inputs of a node that is not being removed.
            for input in node.inputs.iter_mut() {
                input.node -= offset_map[input.node as usize];

                // If this refers to the inputs node, we need to remap it.
                if input.node == 0 {
                    input.output_idx = input_map[input.output_idx as usize];
                }
            }
            true
        };

        offset_map.push(offset);
        res
    });

    (removed_count, removed_inputs)
}

/// Checks if a node has side effects
fn may_have_side_effect(node: &Node) -> bool {
    if let Operation::WASMOp(op) = &node.operation {
        match op {
            // Constants are pure.
            Op::I32Const { .. }
            | Op::I64Const { .. }
            | Op::F32Const { .. }
            | Op::F64Const { .. }
            | Op::V128Const { .. }

            // Numeric operations are pure.
            | Op::I32Eqz
            | Op::I32Eq
            | Op::I32Ne
            | Op::I32LtS
            | Op::I32LtU
            | Op::I32GtS
            | Op::I32GtU
            | Op::I32LeS
            | Op::I32LeU
            | Op::I32GeS
            | Op::I32GeU
            | Op::I64Eqz
            | Op::I64Eq
            | Op::I64Ne
            | Op::I64LtS
            | Op::I64LtU
            | Op::I64GtS
            | Op::I64GtU
            | Op::I64LeS
            | Op::I64LeU
            | Op::I64GeS
            | Op::I64GeU
            | Op::F32Eq
            | Op::F32Ne
            | Op::F32Lt
            | Op::F32Gt
            | Op::F32Le
            | Op::F32Ge
            | Op::F64Eq
            | Op::F64Ne
            | Op::F64Lt
            | Op::F64Gt
            | Op::F64Le
            | Op::F64Ge
            | Op::I32Clz
            | Op::I32Ctz
            | Op::I32Popcnt
            | Op::I32Add
            | Op::I32Sub
            | Op::I32Mul
            | Op::I32DivS
            | Op::I32DivU
            | Op::I32RemS
            | Op::I32RemU
            | Op::I32And
            | Op::I32Or
            | Op::I32Xor
            | Op::I32Shl
            | Op::I32ShrS
            | Op::I32ShrU
            | Op::I32Rotl
            | Op::I32Rotr
            | Op::I64Clz
            | Op::I64Ctz
            | Op::I64Popcnt
            | Op::I64Add
            | Op::I64Sub
            | Op::I64Mul
            | Op::I64DivS
            | Op::I64DivU
            | Op::I64RemS
            | Op::I64RemU
            | Op::I64And
            | Op::I64Or
            | Op::I64Xor
            | Op::I64Shl
            | Op::I64ShrS
            | Op::I64ShrU
            | Op::I64Rotl
            | Op::I64Rotr
            | Op::F32Abs
            | Op::F32Neg
            | Op::F32Ceil
            | Op::F32Floor
            | Op::F32Trunc
            | Op::F32Nearest
            | Op::F32Sqrt
            | Op::F32Add
            | Op::F32Sub
            | Op::F32Mul
            | Op::F32Div
            | Op::F32Min
            | Op::F32Max
            | Op::F32Copysign
            | Op::F64Abs
            | Op::F64Neg
            | Op::F64Ceil
            | Op::F64Floor
            | Op::F64Trunc
            | Op::F64Nearest
            | Op::F64Sqrt
            | Op::F64Add
            | Op::F64Sub
            | Op::F64Mul
            | Op::F64Div
            | Op::F64Min
            | Op::F64Max
            | Op::F64Copysign
            | Op::I32WrapI64
            | Op::I32TruncF32S
            | Op::I32TruncF32U
            | Op::I32TruncF64S
            | Op::I32TruncF64U
            | Op::I64ExtendI32S
            | Op::I64ExtendI32U
            | Op::I64TruncF32S
            | Op::I64TruncF32U
            | Op::I64TruncF64S
            | Op::I64TruncF64U
            | Op::F32ConvertI32S
            | Op::F32ConvertI32U
            | Op::F32ConvertI64S
            | Op::F32ConvertI64U
            | Op::F32DemoteF64
            | Op::F64ConvertI32S
            | Op::F64ConvertI32U
            | Op::F64ConvertI64S
            | Op::F64ConvertI64U
            | Op::F64PromoteF32
            | Op::I32ReinterpretF32
            | Op::I64ReinterpretF64
            | Op::F32ReinterpretI32
            | Op::F64ReinterpretI64
            | Op::I32Extend8S
            | Op::I32Extend16S
            | Op::I64Extend8S
            | Op::I64Extend16S
            | Op::I64Extend32S
            // Ref operations are pure.
            | Op::RefNull { .. }
            | Op::RefIsNull
            | Op::RefFunc { .. }
            // Select is pure.
            | Op::Select { .. }
            // Global get is pure.
            | Op::GlobalGet { .. }
            // Memory and table reads have no side-effects, although I am not sure they are strictly "pure".
            | Op::TableGet { .. }
            | Op::TableSize { .. }
            | Op::I32Load { .. }
            | Op::I64Load { .. }
            | Op::F32Load { .. }
            | Op::F64Load { .. }
            | Op::I32Load8S { .. }
            | Op::I32Load8U { .. }
            | Op::I32Load16S { .. }
            | Op::I32Load16U { .. }
            | Op::I64Load8S { .. }
            | Op::I64Load8U { .. }
            | Op::I64Load16S { .. }
            | Op::I64Load16U { .. }
            | Op::I64Load32S { .. }
            | Op::I64Load32U { .. }
            | Op::V128Load { .. }
            | Op::MemorySize { .. }
            // TODO: there are more WebAssembly 2.0 operations that are missing here...
            => false,
            _ => true,
        }
    } else {
        // For now, we consider all non-WASM operations as having side effects.
        true
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
        remove_indices_from_vec(&mut node.inputs, &removed_inputs);

        count
    } else {
        0
    }
}

fn remove_indices_from_vec<T>(vec: &mut Vec<T>, sorted_ids: &[u32]) {
    let mut sorted_ids = sorted_ids.iter().cloned().peekable();
    let mut curr_idx = 0u32..;
    vec.retain(|_| {
        let curr_idx = curr_idx.next().unwrap();
        if sorted_ids.peek() == Some(&curr_idx) {
            sorted_ids.next();
            false
        } else {
            true
        }
    });
}
