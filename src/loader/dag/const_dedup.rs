use std::collections::{HashMap, hash_map::Entry};

use crate::loader::{
    BlockKind,
    dag::{Dag, Node, NodeInput, Operation, ValueOrigin, WasmValue},
};

/// This is an optimization pass that, if a constant has been defined
/// previously, it will be used in place of a newly created one.
///
/// To be complete, this pass requires a follow-up to remove orphaned
/// constants that are no longer referenced in the DAG.
pub fn deduplicate_constants(dag: &mut Dag) -> usize {
    let (num_removed_consts, requested_inputs) =
        recursive_deduplication(&mut dag.nodes, HashMap::new(), HashMap::new());
    assert!(requested_inputs.is_empty());

    num_removed_consts
}

fn recursive_deduplication<'a>(
    nodes: &mut Vec<Node<'a>>,
    mut const_to_origin: HashMap<WasmValue, Option<ValueOrigin>>,
    mut origin_to_const: HashMap<ValueOrigin, WasmValue>,
) -> (usize, Vec<WasmValue>) {
    let mut num_consts_removed = 0;

    let (input_node, nodes) = nodes.as_mut_slice().split_first_mut().unwrap();
    assert!(matches!(input_node.operation, Operation::Inputs));

    let mut missing_from_inputs = Vec::new();

    // Find the best origin of a constant, possibly requiring it as input if not available.
    let mut get_origin = |const_to_origin: &mut HashMap<WasmValue, Option<ValueOrigin>>,
                          ct: &WasmValue|
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
            if let NodeInput::Reference(origin) = input
                && let Some(ct) = origin_to_const.get(origin)
            {
                *origin = get_origin(&mut const_to_origin, ct);
            }
            // Constants pass through unchanged
        }

        match &mut node.operation {
            Operation::Inputs => unreachable!(),
            Operation::WASMOp(op) => {
                if let Ok(const_val) = WasmValue::try_from(&*op) {
                    // Every constant creates an entry in the `origin_to_const` map.
                    origin_to_const.insert(ValueOrigin::new(node_index, 0), const_val.clone());

                    // If there is no previous definition of this constant, it also
                    // creates an entry in the `const_to_origin` map.
                    match const_to_origin.entry(const_val) {
                        Entry::Occupied(..) => {
                            num_consts_removed += 1;
                        }
                        Entry::Vacant(entry) => {
                            entry.insert(Some(ValueOrigin::new(node_index, 0)));
                        }
                    };
                }
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
                    .keys()
                    .map(|k| (k.clone(), None))
                    .collect::<HashMap<_, _>>();

                let block_origin_to_const = node
                    .inputs
                    .iter()
                    .enumerate()
                    .filter_map(|(input_idx, input)| {
                        match input {
                            NodeInput::Reference(origin) => {
                                origin_to_const.get(origin).map(|constant| {
                                    // Inside the block, its inputs became the outputs of the Inputs node (node 0).
                                    let origin = ValueOrigin::new(0, input_idx as u32);
                                    *block_const_to_origin.get_mut(constant).unwrap() =
                                        Some(origin);

                                    (origin, constant.clone())
                                })
                            }
                            NodeInput::Constant(_) => None, // Constants don't need deduplication
                        }
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
                        .map(|ct| NodeInput::Reference(get_origin(&mut const_to_origin, ct))),
                );
            }
            _ => (),
        }
    }

    (num_consts_removed, missing_from_inputs)
}
