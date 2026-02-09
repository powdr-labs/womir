//! In this pass we will flatten the blocks that belong in a single
//! frame, so that just loops will have independent DAGs.
//! Non-loop blocks will be merged into a single DAG, with labels
//! delimiting the jump points. One important property of this
//! structure is that jumps are never backwards.

use itertools::Itertools;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    sync::atomic::AtomicU32,
};
use wasmparser::{Operator as Op, ValType};

use crate::loader::{BlockKind, LabelGenerator};

pub use super::dag::NodeInput;
use super::dag::{self, Dag, ValueOrigin};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct BreakTarget {
    pub depth: u32,
    pub kind: TargetType,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TargetType {
    /// The target is the function or loop itself.
    FunctionOrLoop,
    /// The target is a label within the loop or function body.
    Label(u32),
}

#[derive(Debug, Clone)]
pub enum Operation<'a, T> {
    Inputs,
    WASMOp(Op<'a>),

    Label {
        /// This label is unique. A complete jump target
        /// will also include the depth of the frame stack.
        id: u32,
    },

    Loop {
        sub_dag: GenericBlocklessDag<'a, T>,
        /// The possible break targets for this loop, relative to the parent frame.
        /// (i.e. depth 0 is the frame before entering the loop, 1 is the frame above it, etc).
        ///
        /// The two vector levels are sorted for easy searching.
        break_targets: Vec<(u32, Vec<TargetType>)>,
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

#[derive(Debug, Clone)]
pub struct BrTableTarget {
    pub target: BreakTarget,
    /// For each of the nodes inputs, this is the permutation of the inputs that
    /// each break target will receive.
    pub input_permutation: Vec<u32>,
}

#[derive(Debug, Clone)]
pub struct GenericNode<'a, T> {
    pub operation: Operation<'a, T>,
    pub inputs: Vec<NodeInput>,
    pub output_types: Vec<ValType>,
}

pub type Node<'a> = GenericNode<'a, ()>;

#[derive(Debug, Clone)]
pub struct GenericBlocklessDag<'a, T> {
    pub nodes: Vec<GenericNode<'a, T>>,
    pub block_data: T,
}

pub type BlocklessDag<'a> = GenericBlocklessDag<'a, ()>;

impl<'a> BlocklessDag<'a> {
    pub fn new(dag: Dag<'a>, label_generator: &AtomicU32) -> Self {
        let mut new_nodes = Vec::new();

        let mut ctrl_stack = VecDeque::from([BlockStack {
            target_type: TargetType::FunctionOrLoop,
            frame_level: 0,
        }]);

        process_nodes(
            dag.nodes,
            label_generator,
            &mut new_nodes,
            &mut ctrl_stack,
            &mut HashSet::new(),
            None,
        );

        BlocklessDag {
            nodes: new_nodes,
            block_data: (),
        }
    }
}

struct BlockStack {
    target_type: TargetType,
    /// Starts at 0, and every stack level that creates a new frame
    /// increments it. The outermost function frame is 0.
    frame_level: u32,
}

fn process_nodes<'a>(
    orig_nodes: Vec<dag::Node<'a>>,
    label_generator: &AtomicU32,
    new_nodes: &mut Vec<Node<'a>>,
    ctrl_stack: &mut VecDeque<BlockStack>,
    break_targets: &mut HashSet<BreakTarget>,
    input_mapping: Option<Vec<ValueOrigin>>,
) {
    let mut outputs_map = HashMap::new();

    for (node_idx, mut node) in orig_nodes.into_iter().enumerate() {
        let operation = match node.operation {
            dag::Operation::Inputs => {
                if let Some(input_mapping) = &input_mapping {
                    // This node is suppressed, and references to its outputs
                    // points to the nodes of the outer block.
                    assert!(node.inputs.is_empty());
                    assert_eq!(node.output_types.len(), input_mapping.len());

                    for (output_idx, origin) in input_mapping.iter().enumerate() {
                        outputs_map.insert(ValueOrigin::new(node_idx, output_idx as u32), *origin);
                    }

                    continue;
                } else {
                    // This node is preserved as the first node of the frame.
                    assert!(node.inputs.is_empty());

                    Operation::Inputs
                }
            }
            dag::Operation::BrIfZero { relative_depth } => Operation::BrIfZero(
                calculate_break_target(ctrl_stack, break_targets, relative_depth),
            ),
            dag::Operation::BrTable { targets } => {
                let targets = targets
                    .into_iter()
                    .map(|target| {
                        let input_permutation = target.input_permutation;
                        let target = calculate_break_target(
                            ctrl_stack,
                            break_targets,
                            target.relative_depth,
                        );

                        BrTableTarget {
                            target,
                            input_permutation,
                        }
                    })
                    .collect_vec();

                Operation::BrTable { targets }
            }
            dag::Operation::WASMOp(operator) => match operator {
                Op::Br { relative_depth } => Operation::Br(calculate_break_target(
                    ctrl_stack,
                    break_targets,
                    relative_depth,
                )),
                Op::BrIf { relative_depth } => Operation::BrIf(calculate_break_target(
                    ctrl_stack,
                    break_targets,
                    relative_depth,
                )),
                _ => Operation::WASMOp(operator),
            },
            dag::Operation::Block { kind, sub_dag } => match kind {
                BlockKind::Loop => {
                    // Loops are not merged, they create a new frame.

                    let mut loop_nodes = Vec::new();

                    ctrl_stack.push_front(BlockStack {
                        target_type: TargetType::FunctionOrLoop,
                        frame_level: ctrl_stack[0].frame_level + 1,
                    });

                    let mut loop_break_targets = HashSet::new();

                    // Loops don't have input mapping, because its internal variables lives in another frame's address space.
                    process_nodes(
                        sub_dag.nodes,
                        // The label space is shared across all the frames, to facilitate assembly generation.
                        // TODO: maybe should be shared across all the functions...
                        label_generator,
                        &mut loop_nodes,
                        ctrl_stack,
                        &mut loop_break_targets,
                        None,
                    );

                    ctrl_stack.pop_front().unwrap();

                    // Make the loop break targets relative to the current frame.
                    let mut loop_break_targets = loop_break_targets
                        .iter()
                        .filter_map(|target| {
                            target.depth.checked_sub(1).map(|depth| BreakTarget {
                                depth,
                                kind: target.kind,
                            })
                        })
                        .collect_vec();

                    // Merge the loop break targets with the current frame break targets.
                    // We must subtract 1 from the depth to make it relative to the current frame.
                    break_targets.extend(loop_break_targets.iter());

                    // Reorganize the break targets as a vector of vectors.
                    loop_break_targets.sort_unstable();
                    let loop_break_targets = loop_break_targets
                        .into_iter()
                        .chunk_by(|BreakTarget { depth, .. }| *depth)
                        .into_iter()
                        .map(|(depth, group)| {
                            let kinds = group.map(|BreakTarget { kind, .. }| kind).collect();
                            (depth, kinds)
                        })
                        .collect_vec();

                    Operation::Loop {
                        sub_dag: BlocklessDag {
                            nodes: loop_nodes,
                            block_data: (),
                        },
                        break_targets: loop_break_targets,
                    }
                }
                BlockKind::Block => {
                    // Blocks are merged into the current frame.

                    let label = label_generator.next();
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
                            .map(|input| match input {
                                NodeInput::Reference(origin) => outputs_map[&origin],
                                NodeInput::Constant(_) => {
                                    panic!("Constants not expected in block inputs")
                                }
                            })
                            .collect(),
                    );

                    process_nodes(
                        sub_dag.nodes,
                        label_generator,
                        new_nodes,
                        ctrl_stack,
                        break_targets,
                        input_mapping,
                    );

                    ctrl_stack.pop_front().unwrap();

                    Operation::Label { id: label }
                }
            },
        };

        // Translate the old node into the new node.
        let new_node_idx = new_nodes.len();

        let mut inputs = node.inputs;
        for input in inputs.iter_mut() {
            if let NodeInput::Reference(origin) = input {
                *origin = outputs_map[origin];
            }
            // Constants pass through unchanged
        }

        for output_idx in 0..node.output_types.len() {
            outputs_map.insert(
                ValueOrigin::new(node_idx, output_idx as u32),
                ValueOrigin::new(new_node_idx, output_idx as u32),
            );
        }

        new_nodes.push(Node {
            operation,
            inputs,
            output_types: node.output_types,
        });
    }
}

fn calculate_break_target(
    ctrl_stack: &VecDeque<BlockStack>,
    break_targets: &mut HashSet<BreakTarget>,
    relative_depth: u32,
) -> BreakTarget {
    let target_frame = &ctrl_stack[relative_depth as usize];

    let depth = ctrl_stack[0].frame_level - target_frame.frame_level;

    let target = BreakTarget {
        depth,
        kind: ctrl_stack[relative_depth as usize].target_type,
    };

    break_targets.insert(target);
    target
}
