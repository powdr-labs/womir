//! This pass detects block inputs that are redirected as-is to block outputs.

use std::{
    collections::{HashMap, VecDeque},
    vec,
};

use wasmparser::Operator as Op;

use crate::loader::{
    BlockKind, Module,
    passes::dag::{
        BrTableTarget, Dag, GenericDag, GenericNode, Node, NodeInput, Operation, ValueOrigin,
    },
};

/// Tells if an output slot of a block is only written with a single input value, and if so, what is that input.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Redirection {
    /// This is a transient state used during the algorithm, which
    /// means we have not yet determined if this output has an input
    /// redirection or not.
    Unknown,
    /// The index of the input that is redirected to this output.
    FromInput(u32),
    /// Marks this output as not being redirected to by any input.
    NotRedirected,
}

pub type RedirDag<'a> = GenericDag<'a, Vec<Redirection>>;
pub type RedirNode<'a> = GenericNode<'a, Vec<Redirection>>;

pub fn calculate_input_redirection<'a>(
    dag: Dag<'a>,
    module: &Module<'a>,
    func_idx: u32,
) -> RedirDag<'a> {
    let output_size = module.get_func_type(func_idx).ty.results().len();

    let entry = ControlStackEntry {
        redirections: vec![Redirection::Unknown; output_size],
        input_map: HashMap::new(),
        was_ever_broken_to: false,
    };

    let cs = &mut VecDeque::from(vec![entry]);
    let (mut nodes, mut at_fixed_point) = process_block(dag.nodes, cs);
    while !at_fixed_point {
        let result = process_block(nodes, cs);
        nodes = result.0;
        at_fixed_point = result.1;
    }

    let mut redirections = cs.pop_front().unwrap().redirections;
    if redirections.contains(&Redirection::Unknown) {
        assert!(
            redirections
                .iter()
                .all(|redir| *redir == Redirection::Unknown)
        );

        // The function never returns, so it can't be a redirection.
        redirections
            .iter_mut()
            .for_each(|redir| *redir = Redirection::NotRedirected);
    }

    RedirDag {
        nodes,
        block_data: redirections,
    }
}

/// This is a helper trait so that process_block is written only once,
/// but works with both the original Dag and the RedirectionDag.
trait RedirDecompose<'a, T> {
    fn decompose(self, num_redirs: usize) -> (Vec<GenericNode<'a, T>>, Vec<Redirection>);
}

impl<'a> RedirDecompose<'a, ()> for Dag<'a> {
    fn decompose(self, num_redirs: usize) -> (Vec<Node<'a>>, Vec<Redirection>) {
        (self.nodes, vec![Redirection::Unknown; num_redirs])
    }
}

impl<'a> RedirDecompose<'a, Vec<Redirection>> for RedirDag<'a> {
    fn decompose(self, num_redirs: usize) -> (Vec<RedirNode<'a>>, Vec<Redirection>) {
        let redirections = self.block_data;
        assert_eq!(redirections.len(), num_redirs);
        (self.nodes, redirections)
    }
}

/// Helper trait to convert an operation with generic
/// block data to an operation with redirection block data.
trait MapToRedir<'a, T> {
    fn map_to_redir(self) -> Operation<'a, Vec<Redirection>>;
}

impl<'a> MapToRedir<'a, ()> for Operation<'a, ()> {
    fn map_to_redir(self) -> Operation<'a, Vec<Redirection>> {
        match self {
            Operation::Inputs => Operation::Inputs,
            Operation::WASMOp(operator) => Operation::WASMOp(operator),
            Operation::BrIfZero { relative_depth } => Operation::BrIfZero { relative_depth },
            Operation::BrTable { targets } => Operation::BrTable { targets },
            Operation::Block { .. } => {
                // Block should be handled separately in handle_sub_block, so we should never encounter it here.
                panic!()
            }
        }
    }
}

impl<'a> MapToRedir<'a, Vec<Redirection>> for Operation<'a, Vec<Redirection>> {
    fn map_to_redir(self) -> Operation<'a, Vec<Redirection>> {
        self
    }
}

struct ControlStackEntry {
    redirections: Vec<Redirection>,
    /// Input map to previous block
    input_map: HashMap<u32, u32>,
    was_ever_broken_to: bool,
}

fn process_block<'a, T>(
    nodes: Vec<GenericNode<'a, T>>,
    cs: &mut VecDeque<ControlStackEntry>,
) -> (Vec<RedirNode<'a>>, bool)
where
    GenericDag<'a, T>: RedirDecompose<'a, T>,
    Operation<'a, T>: MapToRedir<'a, T>,
{
    let mut new_nodes = Vec::with_capacity(nodes.len());
    let mut fixed_point = true;
    for node in nodes {
        let op = match node.operation {
            Operation::WASMOp(Op::Br { relative_depth }) => {
                fixed_point &= handle_break_target(cs, &node.inputs, relative_depth);
                node.operation
            }
            Operation::BrIfZero { relative_depth }
            | Operation::WASMOp(Op::BrIf { relative_depth }) => {
                let break_inputs = &node.inputs[..node.inputs.len() - 1];
                fixed_point &= handle_break_target(cs, break_inputs, relative_depth);
                node.operation
            }
            Operation::BrTable { ref targets } => {
                for BrTableTarget {
                    relative_depth,
                    input_permutation,
                } in targets
                {
                    let target_inputs = input_permutation
                        .iter()
                        .map(|perm| &node.inputs[*perm as usize]);
                    fixed_point &= handle_break_target(cs, target_inputs, *relative_depth);
                }
                node.operation
            }
            Operation::Block { .. } => {
                let SubBlockResult {
                    block_returns,
                    at_fixed_point,
                    node,
                } = handle_sub_block(node, cs);

                fixed_point &= at_fixed_point;

                new_nodes.push(node);

                if block_returns {
                    continue;
                } else {
                    // The rest of this block is unreachable, so we can stop processing it.
                    //
                    // Other dead code cases (namely, after Loop blocks, Br, BrTable and
                    // Unreachable) were handled in a previous pass, so we don't need to
                    // worry about them here.
                    //
                    // Only this dead code removal, when after a Block never broken to,
                    // is new to this pass.
                    break;
                }
            }
            _ => {
                // Nothing special to do for other nodes.
                node.operation
            }
        };

        let new_op = op.map_to_redir();
        let new_node = RedirNode {
            operation: new_op,
            inputs: node.inputs,
            output_types: node.output_types,
        };

        new_nodes.push(new_node);
    }

    (new_nodes, fixed_point)
}

#[must_use]
fn handle_break_target<'a>(
    cs: &mut VecDeque<ControlStackEntry>,
    node_inputs: impl IntoIterator<Item = &'a NodeInput>,
    relative_depth: u32,
) -> bool {
    let mut fixed_point = true;
    for (slot_idx, input) in node_inputs.into_iter().enumerate() {
        // Determine if this input is a block input.
        let block_input_idx = if let NodeInput::Reference(ValueOrigin {
            node: 0,
            output_idx: input_idx,
        }) = *input
        {
            Some(input_idx)
        } else {
            None
        };

        // For each block down in the control stack up to the break target
        // we try to find if the inputs are still block inputs.
        let block_input_idx = block_input_idx.and_then(|mut input_idx| {
            for entry in cs.iter().take(relative_depth as usize) {
                if let Some(mapped_input) = entry.input_map.get(&input_idx) {
                    input_idx = *mapped_input;
                } else {
                    // This input is not a block input in this block,
                    return None;
                }
            }

            Some(input_idx)
        });

        let target_entry = &mut cs[relative_depth as usize];
        target_entry.was_ever_broken_to = true;

        // If we have found a block input in the break target block,
        // we must decide if it is a redirection or not.
        let redirection = &mut target_entry.redirections[slot_idx];
        let old_redirection = *redirection;
        if let Some(input_idx) = block_input_idx {
            if let Redirection::Unknown = redirection {
                // So far, this could be a redirection.
                *redirection = Redirection::FromInput(input_idx);
            } else if let Redirection::FromInput(existing_input) = redirection
                && *existing_input != input_idx
            {
                // Different inputs are being passed to the same output, so it cannot be a redirection.
                *redirection = Redirection::NotRedirected;
            }
        } else {
            // The value does not come from a block input, so it is certainly not a redirection.
            *redirection = Redirection::NotRedirected;
        }

        if *redirection != old_redirection {
            // If the redirection status of this output has changed, we need another pass.
            fixed_point = false;
        }
    }

    fixed_point
}

struct SubBlockResult<'a> {
    /// Does this block ever return?
    block_returns: bool,

    /// Fixed point reached?
    at_fixed_point: bool,

    /// New processed block node.
    node: RedirNode<'a>,
}

fn handle_sub_block<'a, T>(
    mut node: GenericNode<'a, T>,
    cs: &mut VecDeque<ControlStackEntry>,
) -> SubBlockResult<'a>
where
    GenericDag<'a, T>: RedirDecompose<'a, T>,
    Operation<'a, T>: MapToRedir<'a, T>,
{
    let (sub_dag, mut kind) = if let Operation::Block { sub_dag, kind } = node.operation {
        (sub_dag, kind)
    } else {
        panic!()
    };

    let num_outputs = if let BlockKind::Loop = kind {
        // The outputs of a loop block are its own inputs
        node.inputs.len()
    } else {
        node.output_types.len()
    };
    let (sub_nodes, redirections) = sub_dag.decompose(num_outputs);

    // Map from the input inside of the sub-block to the input of the current block.
    //
    // This is optimistic in the inner passes: we assume inputs to loops will be redirected
    // if it can happen according to the current redirections. Wrong choices will be fixed
    // in the following passes.
    let input_map: HashMap<u32, u32> = if let BlockKind::Loop = kind {
        // For loops, only include inputs whose corresponding output
        // is (optimistically) redirected to the same parent input.
        block_inputs(&node.inputs)
            .filter_map(|(node_input_idx, block_input_idx)| {
                let redir = &redirections[node_input_idx];
                (*redir == Redirection::Unknown
                    || *redir == Redirection::FromInput(block_input_idx))
                .then_some((node_input_idx as u32, block_input_idx))
            })
            .collect()
    } else {
        // For non-loop blocks, inputs never change,
        // so all parent-sourced inputs are always valid mappings.
        block_inputs(&node.inputs)
            .map(|(node_input_idx, block_input_idx)| (node_input_idx as u32, block_input_idx))
            .collect()
    };

    // Call the processing recursively
    cs.push_front(ControlStackEntry {
        input_map,
        redirections,
        was_ever_broken_to: false,
    });
    let (sub_nodes, at_fixed_point) = process_block(sub_nodes, cs);
    let mut sub_entry = cs.pop_front().unwrap();

    // Detect dead code.
    let mut block_returns = true;
    if !sub_entry.was_ever_broken_to {
        // Invariant check: there can only be an unknown redirection if the block is
        // never broken to, in which case, all must be unknown.
        assert!(
            sub_entry
                .redirections
                .iter()
                .all(|redir| *redir == Redirection::Unknown)
        );

        // Sub-block is never broken to, so we can do the following transformations:
        match kind {
            BlockKind::Block => {
                // If the sub-block is a plain block, all outputs can be removed,
                // and the rest of this block is unreachable, and we can stop processing it.
                node.output_types.clear();
                sub_entry.redirections.clear();
            }
            BlockKind::Loop => {
                // If the sub-block is a loop, it can be turned into a plain block with no outputs,
                // because it never iterates.
                kind = BlockKind::Block;
                assert!(node.output_types.is_empty());
            }
        }
        block_returns = false;
    } else if let BlockKind::Loop = kind {
        // This is a loop, and loops "never" returns. When we break out of
        // a loop, it is always an explicit break to an outer block.
        block_returns = false;
    }

    let node = RedirNode {
        operation: Operation::Block {
            sub_dag: GenericDag {
                nodes: sub_nodes,
                block_data: sub_entry.redirections,
            },
            kind,
        },
        inputs: node.inputs,
        output_types: node.output_types,
    };

    SubBlockResult {
        block_returns,
        at_fixed_point,
        node,
    }
}

/// Filters inputs that are block inputs, and returns tuples of
/// (input index in the node, output index they point to in the input node).
fn block_inputs<'a>(
    inputs: impl IntoIterator<Item = &'a NodeInput>,
) -> impl Iterator<Item = (usize, u32)> {
    inputs.into_iter().enumerate().filter_map(|(idx, input)| {
        if let NodeInput::Reference(ValueOrigin {
            node: 0,
            output_idx,
        }) = input
        {
            Some((idx, *output_idx))
        } else {
            None
        }
    })
}
