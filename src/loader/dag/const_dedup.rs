use std::{
    collections::{HashMap, hash_map::Entry},
    hash::Hash,
};

use wasmparser::{Operator as Op, ValType};

use crate::loader::{
    BlockKind,
    dag::{Dag, Node, Operation, ValueOrigin},
};

/// This is an optimization pass that, if a constant has been defined
/// previously, it will be used in place of a newly created one.
///
/// To be complete, this pass requires a follow-up to remove orphaned
/// constants that are no longer referenced in the DAG.
pub fn deduplicate_constants(dag: &mut Dag) {
    let (num_removed_consts, requested_inputs) =
        recursive_deduplication(&mut dag.nodes, HashMap::new(), HashMap::new());
    assert!(requested_inputs.is_empty());

    log::info!("Deduplicated {} constants in the DAG", num_removed_consts);
}

#[derive(Clone, PartialEq, Eq)]
struct HashableConst<'a>(Op<'a>);

impl HashableConst<'_> {
    fn value_type(&self) -> ValType {
        match self.0 {
            Op::I32Const { .. } => ValType::I32,
            Op::I64Const { .. } => ValType::I64,
            Op::F32Const { .. } => ValType::F32,
            Op::F64Const { .. } => ValType::F64,
            Op::V128Const { .. } => ValType::V128,
            _ => panic!("Unsupported constant type for hashing"),
        }
    }
}

impl<'a> Hash for HashableConst<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(&self.0).hash(state);
        match self.0 {
            Op::I32Const { value } => value.hash(state),
            Op::I64Const { value } => value.hash(state),
            Op::F32Const { value } => value.bits().hash(state),
            Op::F64Const { value } => value.bits().hash(state),
            Op::V128Const { value } => value.hash(state),
            _ => panic!("Unsupported constant type for hashing"),
        }
    }
}

fn recursive_deduplication<'a>(
    nodes: &mut Vec<Node<'a>>,
    mut const_to_origin: HashMap<HashableConst<'a>, Option<ValueOrigin>>,
    mut origin_to_const: HashMap<ValueOrigin, HashableConst<'a>>,
) -> (usize, Vec<HashableConst<'a>>) {
    let mut num_consts_removed = 0;

    let (input_node, nodes) = nodes.as_mut_slice().split_first_mut().unwrap();
    assert!(matches!(input_node.operation, Operation::Inputs));

    let mut missing_from_inputs = Vec::new();

    // Find the best origin of a constant, possibly requiring it as input if not available.
    let mut get_origin = |const_to_origin: &mut HashMap<HashableConst<'a>, Option<ValueOrigin>>,
                          ct: &HashableConst<'a>|
     -> ValueOrigin {
        let origin = const_to_origin.get_mut(ct).unwrap();
        if let Some(origin) = origin {
            // The constant is defined at the current depth, and we can use it directly.
            *origin
        } else {
            // The constant is defined at an outer depth, we need to include it in the inputs.
            missing_from_inputs.push(ct.clone());

            let new_input_idx = input_node.output_types.len() as u32;
            input_node.output_types.push(ct.value_type());

            let new_origin = ValueOrigin::new(0, new_input_idx);
            *origin = Some(new_origin);
            new_origin
        }
    };

    for (node_index, node) in (1usize..).zip(nodes.iter_mut()) {
        // For each input of this node, remap it if needed.
        for input in node.inputs.iter_mut() {
            if let Some(ct) = origin_to_const.get(input) {
                *input = get_origin(&mut const_to_origin, ct);
            }
        }

        match &mut node.operation {
            Operation::Inputs => unreachable!(),
            Operation::WASMOp(op @ Op::I32Const { .. })
            | Operation::WASMOp(op @ Op::I64Const { .. })
            | Operation::WASMOp(op @ Op::F32Const { .. })
            | Operation::WASMOp(op @ Op::F64Const { .. })
            | Operation::WASMOp(op @ Op::V128Const { .. }) => {
                // Every constant creates an entry in the `origin_to_const` map.
                origin_to_const.insert(ValueOrigin::new(node_index, 0), HashableConst(op.clone()));

                // If there is no previous definition of this constant, it also
                // creates an entry in the `const_to_origin` map.
                match const_to_origin.entry(HashableConst(op.clone())) {
                    Entry::Occupied(..) => {
                        num_consts_removed += 1;
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(Some(ValueOrigin::new(node_index, 0)));
                    }
                };
            }
            Operation::Block {
                kind: BlockKind::Loop,
                sub_dag,
            } => {
                // For loop, we just recurse into the sub-DAG. We don't need to
                // pass the known constants, as it is cheaper to redefine them
                // than to copy them inside the iteration.
                let (loop_removed, requested_inputs) =
                    recursive_deduplication(&mut sub_dag.nodes, HashMap::new(), HashMap::new());
                assert!(requested_inputs.is_empty());

                num_consts_removed += loop_removed;
            }
            Operation::Block {
                kind: BlockKind::Block,
                sub_dag,
            } => {
                // For blocks, we need to assemble the input hash maps based on which of the block
                // inputs are constants.
                let mut block_const_to_origin = const_to_origin
                    .iter()
                    .map(|(k, _)| (k.clone(), None))
                    .collect::<HashMap<_, _>>();

                let block_origin_to_const = node
                    .inputs
                    .iter()
                    .enumerate()
                    .filter_map(|(input_idx, input)| {
                        origin_to_const.get(input).map(|constant| {
                            // Inside the block, its inputs became the outputs of the Inputs node (node 0).
                            let origin = ValueOrigin::new(0, input_idx as u32);
                            *block_const_to_origin.get_mut(constant).unwrap() = Some(origin);

                            (origin, constant.clone())
                        })
                    })
                    .collect();

                let (block_removed, requested_inputs) = recursive_deduplication(
                    &mut sub_dag.nodes,
                    block_const_to_origin,
                    block_origin_to_const,
                );

                num_consts_removed += block_removed;

                node.inputs.extend(
                    requested_inputs
                        .iter()
                        .map(|ct| get_origin(&mut const_to_origin, ct)),
                );
            }
            _ => (),
        }
    }

    (num_consts_removed, missing_from_inputs)
}
