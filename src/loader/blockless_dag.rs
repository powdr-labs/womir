//! In this pass we will flatten the blocks that belong in a single
//! frame, so that just loops will have independent DAGs.
//! Non-loop blocks will be merged into a single DAG, with labels
//! delimiting the jump points. One important property of this
//! structure is that jumps are never backwards.

use itertools::Itertools;
use std::{
    collections::{HashMap, VecDeque},
    marker::PhantomData,
    ops::RangeFrom,
};
use wasmparser::{Operator as Op, ValType};

use crate::loader::BlockKind;

use super::dag::{self, Dag, ValueOrigin};

#[derive(Debug)]
enum BreakTarget {
    Label(LabelTarget),
    ReturnOrInterate { depth: u32 },
}

#[derive(Debug)]
struct LabelTarget {
    /// The depth of the frame stack when this label belongs.
    depth: u32,
    /// The label id.
    id: u32,
}

#[derive(Debug)]
pub enum Operation<'a> {
    Inputs,
    WASMOp(Op<'a>),

    Label {
        /// This label is unique to this block/frame. A complete jump target
        /// will also include the depth of the frame stack.
        id: u32,
    },

    Loop {
        sub_dag: BlocklessDag<'a>,
        /// The possible break targets for this block, relative to the itself
        /// (i.e. 0 is itself, 1 is the parent block, 2 is the block above it, etc).
        break_targets: Vec<u32>,
    },

    // All the Br variations below are only used for jumps out of the current
    // block/frame.
    Br(BreakTarget),
    BrIf(BreakTarget),
    BrIfZero(BreakTarget),
    BrTable {
        targets: Vec<BrTableTarget>,
    },
}

#[derive(Debug)]
pub struct BrTableTarget {
    pub target: BreakTarget,
    /// For each of the nodes inputs, this is the permutation of the inputs that
    /// each break target will receive.
    pub input_permutation: Vec<u32>,
}

#[derive(Debug)]
pub struct Node<'a> {
    pub operation: Operation<'a>,
    pub inputs: Vec<ValueOrigin>,
    pub output_types: Vec<ValType>,
}

#[derive(Debug)]
pub struct BlocklessDag<'a> {
    pub nodes: Vec<Node<'a>>,
}

impl<'a> BlocklessDag<'a> {
    pub fn new(dag: Dag) -> Self {
        //process_nodes(dag.nodes);
        todo!()
    }
}

enum TargetType {
    FunctionOrLoop,
    Label(u32),
}

struct BlockStack {
    target_type: TargetType,
    /// Starts at 0, and every stack level that creates a new frame
    /// increments it. The outermost function frame is 0.
    frame_level: u32,
}

fn process_nodes<'a>(
    orig_nodes: Vec<dag::Node<'a>>,
    label_generator: &mut RangeFrom<u32>,
    new_nodes: &mut Vec<Node<'a>>,
    ctrl_stack: &mut VecDeque<BlockStack>,
    input_mapping: Option<Vec<ValueOrigin>>,
) {
    let mut outputs_map = HashMap::new();

    for (node_idx, mut node) in orig_nodes.into_iter().enumerate() {
        let new_op = match node.operation {
            dag::Operation::Inputs => {
                if let Some(input_mapping) = &input_mapping {
                    // This node is suppressed, and references to its outputs
                    // points to the nodes of the outer block.
                    assert!(node.inputs.is_empty());
                    assert_eq!(node.output_types.len(), input_mapping.len());

                    for (output_idx, origin) in input_mapping.iter().enumerate() {
                        outputs_map.insert(ValueOrigin::new(node_idx, output_idx as u32), *origin);
                    }

                    None
                } else {
                    // This node is preserved as the first node of the frame.
                    assert!(node.inputs.is_empty());

                    Some(Operation::Inputs)
                }
            }
            dag::Operation::BrIfZero { relative_depth } => Some(Operation::BrIfZero(
                calculate_break_target(ctrl_stack, relative_depth),
            )),
            dag::Operation::BrTable { targets } => {
                let targets = targets
                    .into_iter()
                    .map(|target| {
                        let input_permutation = target.input_permutation;
                        let target = calculate_break_target(ctrl_stack, target.relative_depth);

                        BrTableTarget {
                            target,
                            input_permutation,
                        }
                    })
                    .collect_vec();

                Some(Operation::BrTable { targets })
            }
            dag::Operation::WASMOp(operator) => match operator {
                Op::Br { relative_depth } => Some(Operation::Br(calculate_break_target(
                    ctrl_stack,
                    relative_depth,
                ))),
                Op::BrIf { relative_depth } => Some(Operation::BrIf(calculate_break_target(
                    ctrl_stack,
                    relative_depth,
                ))),
                _ => Some(Operation::WASMOp(operator)),
            },
            dag::Operation::Block {
                kind,
                sub_dag,
                break_targets,
            } => match kind {
                BlockKind::Loop => {
                    // Loops are not merged, they create a new frame.

                    let mut loop_nodes = Vec::new();

                    ctrl_stack.push_front(BlockStack {
                        target_type: TargetType::FunctionOrLoop,
                        frame_level: ctrl_stack[0].frame_level + 1,
                    });

                    // Loops don't have input mapping, because its internal variables lives in another frame's address space.
                    process_nodes(
                        sub_dag.nodes,
                        &mut (0u32..),
                        &mut loop_nodes,
                        ctrl_stack,
                        None,
                    );

                    ctrl_stack.pop_front().unwrap();

                    Some(Operation::Loop {
                        sub_dag: BlocklessDag { nodes: loop_nodes },
                        break_targets: todo!(),
                    })
                }
                BlockKind::Block => {
                    // Blocks are merged into the current frame.

                    let label = label_generator.next().unwrap();
                    ctrl_stack.push_front(BlockStack {
                        target_type: TargetType::Label(label),
                        frame_level: ctrl_stack[0].frame_level,
                    });

                    let input_mapping = Some(
                        // We mem::take the inputs from the node, because the node
                        // replacing this block will be a label, which has only outputs.
                        // The inputs are resolved statically during the traversal.
                        std::mem::take(&mut node.inputs)
                            .into_iter()
                            .map(|input| outputs_map[&input])
                            .collect(),
                    );

                    process_nodes(
                        sub_dag.nodes,
                        label_generator,
                        new_nodes,
                        ctrl_stack,
                        input_mapping,
                    );

                    ctrl_stack.pop_front().unwrap();

                    Some(Operation::Label { id: label })
                }
            },
        };

        if let Some(operation) = new_op {
            let new_node_idx = new_nodes.len();

            for output_idx in 0..node.output_types.len() {
                outputs_map.insert(
                    ValueOrigin::new(node_idx, output_idx as u32),
                    ValueOrigin::new(new_node_idx, output_idx as u32),
                );
            }

            let mut inputs = node.inputs;
            for input in inputs.iter_mut() {
                *input = outputs_map[input];
            }

            new_nodes.push(Node {
                operation,
                inputs,
                output_types: node.output_types,
            });
        }
    }

    todo!()
}

fn calculate_break_target(
    ctrl_stack: &mut VecDeque<BlockStack>,
    relative_depth: u32,
) -> BreakTarget {
    let target_frame = &ctrl_stack[relative_depth as usize];

    let depth = ctrl_stack[0].frame_level - target_frame.frame_level;

    match ctrl_stack[relative_depth as usize].target_type {
        TargetType::FunctionOrLoop => BreakTarget::ReturnOrInterate { depth },
        TargetType::Label(id) => BreakTarget::Label(LabelTarget { depth, id }),
    }
}
