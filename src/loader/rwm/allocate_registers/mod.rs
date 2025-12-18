mod occupation_tracker;

use std::{
    collections::{BTreeMap, HashMap, VecDeque},
    num::NonZeroU32,
    ops::Range,
};

use wasmparser::{Operator as Op, ValType};

use crate::{
    loader::{
        blockless_dag::{
            BreakTarget, GenericBlocklessDag, GenericNode, NodeInput, Operation, TargetType,
        },
        dag::ValueOrigin,
        rwm::{
            allocate_registers::occupation_tracker::OccupationTracker,
            liveness_dag::{self, LivenessDag},
        },
        settings::Settings,
        wom::flattening::word_count_type,
    },
    utils::rev_vec_filler::RevVecFiller,
};

pub enum Error {
    NotAllocated,
    NotARegister,
}

/// One possible register allocation for a given DAG.
#[derive(Debug)]
pub struct Allocation {
    /// The registers assigned to the nodes outputs.
    nodes_outputs: BTreeMap<ValueOrigin, Range<u32>>,
    /// The map of label id to its node index, for quick lookup on a break.
    pub labels: HashMap<u32, usize>,
}

impl Allocation {
    pub fn get(&self, origin: &ValueOrigin) -> Result<Range<u32>, Error> {
        self.nodes_outputs
            .get(origin)
            .cloned()
            .ok_or(Error::NotAllocated)
    }

    pub fn get_as_reg(&self, input: &NodeInput) -> Result<Range<u32>, Error> {
        match input {
            NodeInput::Reference(origin) => self.get(origin),
            NodeInput::Constant(_) => {
                // Constants don't need register allocation
                Err(Error::NotARegister)
            }
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&ValueOrigin, &Range<u32>)> {
        self.nodes_outputs.iter()
    }
}

pub type AllocatedDag<'a> = GenericBlocklessDag<'a, Allocation>;

pub type Node<'a> = GenericNode<'a, Allocation>;

struct OptimisticAllocator {
    occupation_tracker: OccupationTracker,
    labels: HashMap<u32, usize>,
}

impl OptimisticAllocator {
    /// Allocates the inputs of a node that have not been allocated yet.
    fn allocate_inputs<'a, S: Settings<'a>>(
        &mut self,
        inputs: &[NodeInput],
        nodes: &[liveness_dag::Node<'a>],
    ) {
        for input in inputs {
            if let NodeInput::Reference(origin) = input {
                self.occupation_tracker
                    .try_allocate(*origin, assert_non_zero(word_count::<S>(nodes, *origin)));
            }
        }
    }

    /// Allocates the outputs of a node that have not been allocated yet.
    fn allocate_outputs<'a, S: Settings<'a>>(
        &mut self,
        node_index: usize,
        output_types: &[ValType],
    ) {
        for (output_idx, output_type) in output_types.iter().enumerate() {
            let origin = ValueOrigin {
                node: node_index,
                output_idx: output_idx as u32,
            };
            let num_words = assert_non_zero(word_count_type::<S>(*output_type));
            self.occupation_tracker.try_allocate(origin, num_words);
        }
    }
}

/// Allocates the inputs for a break node.
fn handle_break<'a, S: Settings<'a>>(
    nodes: &[liveness_dag::Node<'a>],
    oa: &mut VecDeque<OptimisticAllocator>,
    inputs: &[NodeInput],
    break_target: &BreakTarget,
) -> usize {
    let mut number_of_saved_copies = 0;

    let curr_depth = oa.len() as u32 - 1;
    match break_target.kind {
        TargetType::FunctionOrLoop if break_target.depth >= curr_depth => {
            // This is a function return. We must try to place the outputs in the expected registers
            // for function return.
            assert!(break_target.depth == curr_depth);
            let mut next_reg = 0u32;
            for input in inputs {
                let origin = unwrap_ref(input, "break inputs must be references");
                let num_words = word_count::<S>(nodes, *origin);
                if oa[0]
                    .occupation_tracker
                    .try_allocate_with_hint(*origin, next_reg..next_reg + num_words)
                {
                    number_of_saved_copies += num_words as usize;
                }
                next_reg += num_words;
            }
        }
        TargetType::FunctionOrLoop => {
            // This is a break to a loop iteration.

            // For each input, we try to mirror the allocation expected by the loop input.
            let target_idx = break_target.depth as usize;
            for (input_index, break_input) in inputs.iter().enumerate() {
                let loop_input_origin = ValueOrigin {
                    node: 0,
                    output_idx: input_index as u32,
                };
                let loop_input_allocation = oa[target_idx]
                    .occupation_tracker
                    .get_allocation(loop_input_origin)
                    .expect("loop input must be allocated");
                let num_words = loop_input_allocation.len();
                let break_origin = unwrap_ref(break_input, "break inputs must be references");
                if oa[0]
                    .occupation_tracker
                    .try_allocate_with_hint(*break_origin, loop_input_allocation)
                {
                    number_of_saved_copies += num_words;
                }
            }
        }
        TargetType::Label(label) => {
            // Try to allocate the break input at the same registers as the label output.

            // We are dealing with potentially two different levels of depth here,
            // target_idx is the level that contains the label with the outputs we
            // want to match. 0 is the current level we must set the allocations for.
            //
            // They might be the same, but not necessarily.
            let target_idx = break_target.depth as usize;

            // Node index at the target level
            let label_index = *oa[target_idx]
                .labels
                .get(&label)
                .expect("label must be defined");

            for (index, break_input) in inputs.iter().enumerate() {
                let label_origin = ValueOrigin {
                    node: label_index,
                    output_idx: index as u32,
                };
                let label_allocation = oa[target_idx]
                    .occupation_tracker
                    .get_allocation(label_origin)
                    .unwrap();
                let num_words = label_allocation.len();

                // Value origin at the current level we are setting the allocation for.
                let break_origin = unwrap_ref(break_input, "break inputs must be references");
                if oa[0]
                    .occupation_tracker
                    .try_allocate_with_hint(*break_origin, label_allocation)
                {
                    number_of_saved_copies += num_words;
                }
            }
        }
    }

    number_of_saved_copies
}

fn recursive_block_allocation<'a, S: Settings<'a>>(
    mut nodes: Vec<liveness_dag::Node<'a>>,
    oa: &mut VecDeque<OptimisticAllocator>,
) -> (Vec<Node<'a>>, usize) {
    let mut number_of_saved_copies = 0;

    let mut new_nodes = RevVecFiller::new(nodes.len());

    for index in (0..nodes.len()).rev() {
        let node = nodes.pop().unwrap();

        let operation = match node.operation {
            Operation::Inputs => {
                assert_eq!(index, 0);

                // Allocate whatever output was not allocated yet.
                // (can happen for loop inputs that are not used inside the body)
                oa[0].allocate_outputs::<S>(index, &node.output_types);

                Operation::Inputs
            }
            Operation::WASMOp(operator) => {
                match &operator {
                    Op::Call { .. } | Op::CallIndirect { .. } => {
                        // TODO: implement a simple heuristic to try to avoid having to
                        // copy the function outputs to the slots allocated for them by
                        // the nodes who uses them as inputs.
                        //
                        // The idea goes like this: we first check if an output slot
                        // was specifically requested by the user node with a hint.
                        // If it was, then we most likely have to do copy it anyway, so
                        // we stop. If it wasn't, we check if between this call and the last
                        // user of the output there are no other function calls (and we
                        // must check inside the loop blocks as well). If there are not,
                        // then we can set the output slots to the ones that naturally
                        // follow from the function call, avoiding a register copy. In this
                        // case, it is also possible that we can shift the call frame
                        // itself some slots up, as the removal of the original output slots
                        // might have freed up some space.
                        //
                        // The search can follow uncoditional breaks, skipping code that
                        // will not be executed in this path.
                        //
                        // Since the search only happens in between function calls, this
                        // heuristic is still linear in the number of nodes.
                        //
                        // It might leave holes in the register allocation, but the
                        // optimization problem is NP-hard, so we must stop somewhere.

                        // On a given node index, the one after the last used slot is the
                        // start of the called function frame. From there, two slots are
                        // reserved for return address and frame pointer, and then come
                        // the arguments.
                        let output_sizes =
                            node.output_types.iter().map(|ty| word_count_type::<S>(*ty));
                        let arg_start = oa[0]
                            .occupation_tracker
                            .allocate_fn_call(index, output_sizes);

                        for input in &node.inputs {
                            let origin =
                                unwrap_ref(input, "function call inputs must be references");
                            let num_words = word_count::<S>(&nodes, *origin);
                            if oa[0]
                                .occupation_tracker
                                .try_allocate_with_hint(*origin, arg_start..arg_start + num_words)
                            {
                                number_of_saved_copies += num_words as usize;
                            }
                        }
                    }
                    _ => {
                        // This is the general case. Allocates inputs and outputs that have not been allocated yet.
                        oa[0].allocate_inputs::<S>(&node.inputs, &nodes);
                        oa[0].allocate_outputs::<S>(index, &node.output_types);
                    }
                };

                Operation::WASMOp(operator)
            }
            Operation::Label { id } => {
                // Record the current allocation for this label
                oa[0].labels.insert(id, index);

                // Allocate any remaining output that was not allocated yet.
                oa[0].allocate_outputs::<S>(index, &node.output_types);

                Operation::Label { id }
            }
            Operation::Loop {
                sub_dag,
                break_targets,
            } => {
                // As with the general case, we allocate the inputs of the loop node.
                // It has no outputs that would require allocation.
                oa[0].allocate_inputs::<S>(&node.inputs, &nodes);

                // We need a new allocation tracker for the loop body.
                // It is derived from the current one, completely blocking the
                // slots that are occupied for the duration of the loop.
                let LivenessDag {
                    nodes: loop_nodes,
                    block_data: loop_liveness,
                } = sub_dag;
                let mut occupation_tracker = oa[0]
                    .occupation_tracker
                    .make_sub_tracker(index, loop_liveness);

                // There is an heuristic we can do here to minimize copies: for each loop input, if this
                // is the last usage of the value, or if the loop body does not change the input and just
                // forwards it unchanged to the next iteration, we can fix the allocation of the input to
                // the current one, saving a copy.
                for (input_idx, input) in node.inputs.iter().enumerate() {
                    let origin = unwrap_ref(input, "loop inputs must be references");

                    // Check if we can fix this allocation for the loop input.
                    let last_usage = oa[0].occupation_tracker.liveness().query_liveness(
                        index,
                        origin.node,
                        origin.output_idx,
                    );
                    if (last_usage <= index && {
                        assert_eq!(
                            last_usage, index,
                            "liveness bug: last usage is before a node that uses the value"
                        );
                        true
                    }) || occupation_tracker
                        .liveness()
                        .query_if_input_is_redirected(input_idx as u32)
                    {
                        // We can fix the allocation of this input to the current one,
                        // because either we don't care if it is rewritten by the loop,
                        // or we have the guarantee that it won't be changed.
                        let allocation = oa[0].occupation_tracker.get_allocation(*origin).unwrap();
                        number_of_saved_copies += allocation.len();
                        occupation_tracker
                            .set_allocation(
                                ValueOrigin {
                                    node: 0,
                                    output_idx: input_idx as u32,
                                },
                                allocation,
                            )
                            .unwrap();
                    }
                }

                let loop_oa = OptimisticAllocator {
                    occupation_tracker,
                    labels: HashMap::new(),
                };
                oa.push_front(loop_oa);

                let (loop_nodes, loop_saved_copies) =
                    recursive_block_allocation::<S>(loop_nodes, oa);

                // Pop the loop allocation tracker.
                let OptimisticAllocator {
                    occupation_tracker,
                    labels,
                } = oa.pop_front().unwrap();

                // Project the allocations back to the outer level. This will prevent
                // the outer level from placing allocations that should survive across
                // this loop block on registers that could be overwritten here.
                oa[0]
                    .occupation_tracker
                    .project_from_sub_tracker(index, &occupation_tracker);

                let allocation = Allocation {
                    nodes_outputs: occupation_tracker.into_allocations(),
                    labels,
                };

                // Collect the new nodes
                let loop_dag = AllocatedDag {
                    nodes: loop_nodes,
                    block_data: allocation,
                };

                number_of_saved_copies += loop_saved_copies;

                // We have to set the allocations for the inputs of the loop node, mirroring
                // the allocations set in the loop body.
                for (input_idx, input) in node.inputs.iter().enumerate() {
                    // Get the allocation assigned to the loop input inside the body.
                    let preferred_alloc = loop_dag
                        .block_data
                        .nodes_outputs
                        .get(&ValueOrigin {
                            node: 0,
                            output_idx: input_idx as u32,
                        })
                        .unwrap()
                        .clone();
                    let alloc_len = preferred_alloc.len();

                    let origin = unwrap_ref(input, "loop inputs must be references");
                    if oa[0]
                        .occupation_tracker
                        .try_allocate_with_hint(*origin, preferred_alloc)
                    {
                        number_of_saved_copies += alloc_len;
                    }
                }

                Operation::Loop {
                    sub_dag: loop_dag,
                    break_targets,
                }
            }
            Operation::Br(break_target) => {
                number_of_saved_copies +=
                    handle_break::<S>(&nodes, oa, &node.inputs, &break_target);
                Operation::Br(break_target)
            }
            Operation::BrIf(break_target) => {
                number_of_saved_copies +=
                    handle_break::<S>(&nodes, oa, &node.inputs, &break_target);
                Operation::BrIf(break_target)
            }
            Operation::BrIfZero(break_target) => {
                number_of_saved_copies +=
                    handle_break::<S>(&nodes, oa, &node.inputs, &break_target);
                Operation::BrIfZero(break_target)
            }
            Operation::BrTable { targets } => {
                let mut inputs = Vec::new();
                for target in &targets {
                    inputs.clear();
                    inputs.extend(
                        target
                            .input_permutation
                            .iter()
                            .map(|&idx| node.inputs[idx as usize].clone()),
                    );
                    number_of_saved_copies +=
                        handle_break::<S>(&nodes, oa, &inputs, &target.target);
                }
                Operation::BrTable { targets }
            }
        };

        let new_node = Node {
            operation,
            inputs: node.inputs,
            output_types: node.output_types,
        };

        new_nodes.try_push_front(new_node).unwrap();
    }

    (new_nodes.try_into_vec().unwrap(), number_of_saved_copies)
}

/// Allocates registers for a given function DAG. It is not optimal, but it tries
/// to minimize the number of copies and used registers.
///
/// Does the allocation bottom up, following the execution paths independently,
/// proposing register assignment for future nodes (so to avoid copies), but
/// leaving a final assignment for the traversed nodes.
pub fn optimistic_allocation<'a, S: Settings<'a>>(
    dag: LivenessDag<'a>,
) -> (AllocatedDag<'a>, usize) {
    let LivenessDag {
        nodes,
        block_data: liveness,
    } = dag;

    let mut oa = OptimisticAllocator {
        occupation_tracker: OccupationTracker::new(liveness),
        labels: HashMap::new(),
    };

    // Fix the allocation of the function inputs first
    let inputs = &nodes[0];
    let Operation::Inputs = &inputs.operation else {
        panic!("First node must be Inputs");
    };
    let mut next_reg = 0u32;
    for (output_idx, input) in inputs.output_types.iter().enumerate() {
        let origin = ValueOrigin {
            node: 0,
            output_idx: output_idx as u32,
        };
        let num_words = word_count_type::<S>(*input);
        oa.occupation_tracker
            .set_allocation(origin, next_reg..next_reg + num_words)
            .unwrap();
        next_reg += num_words;
    }

    // Do the allocation for the rest of the nodes, bottom up.
    let mut oa_stack = VecDeque::from([oa]);
    let (nodes, number_of_saved_copies) = recursive_block_allocation::<S>(nodes, &mut oa_stack);

    // Generate the final allocation for this block
    let OptimisticAllocator {
        occupation_tracker,
        labels,
    } = oa_stack.pop_front().unwrap();

    let allocation = Allocation {
        nodes_outputs: occupation_tracker.into_allocations(),
        labels,
    };

    (
        AllocatedDag {
            nodes,
            block_data: allocation,
        },
        number_of_saved_copies,
    )
}

/// Helper to extract ValueOrigin from NodeInput
fn unwrap_ref<'a>(input: &'a NodeInput, msg: &'static str) -> &'a ValueOrigin {
    match input {
        NodeInput::Reference(origin) => origin,
        NodeInput::Constant(_) => panic!("{}", msg),
    }
}

/// Gets the type of a value origin
fn type_of<'a>(nodes: &[liveness_dag::Node<'a>], origin: ValueOrigin) -> ValType {
    let node = &nodes[origin.node];
    node.output_types[origin.output_idx as usize]
}

fn assert_non_zero(value: u32) -> NonZeroU32 {
    NonZeroU32::new(value).expect("word count is non-zero")
}

/// Gets the word count of a value origin
fn word_count<'a, S: Settings<'a>>(nodes: &[liveness_dag::Node<'a>], origin: ValueOrigin) -> u32 {
    word_count_type::<S>(type_of(nodes, origin))
}
