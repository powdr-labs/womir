use std::{
    collections::{BTreeMap, HashMap, VecDeque},
    ops::Range,
};

use wasmparser::{Operator as Op, ValType};

use crate::{
    loader::{
        blockless_dag::{
            BreakTarget, GenericBlocklessDag, GenericNode, NodeInput, Operation, TargetType,
        },
        dag::ValueOrigin,
        liveness_dag::{self, LivenessDag},
        rw_flattening::Settings,
        word_count_type,
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

/// Tracks what registers are currently occupied by what values.
struct OccupationTracker {
    // TODO
}

impl OccupationTracker {
    fn new() -> Self {
        todo!()
    }

    fn make_sub_tracker(&self, sub_block_index: usize) -> Self {
        todo!()
    }

    /// Allocates the value exactly at the given register range.
    fn set_allocation(&mut self, origin: ValueOrigin, reg_range: Range<u32>) -> Result<(), ()> {
        todo!()
    }

    /// Tries to allocate the value at the given register range, if not already allocated.
    /// Returns false if the value was already allocated.
    /// If not possible to allocate on hint, allocates elsewhere and returns false.
    /// Returns true if allocation happened at hint.
    fn try_allocate_with_hint(&mut self, origin: ValueOrigin, hint: Range<u32>) -> bool {
        todo!()
    }

    /// Allocates a value wherever there is space, if not already allocated.
    fn allocate(&mut self, origin: ValueOrigin, size: u32) {
        todo!()
    }

    /// Gets the current allocation of a value.
    fn get_allocation(&self, origin: ValueOrigin) -> Option<Range<u32>> {
        todo!()
    }

    /// The first free register after the last allocated one.
    fn allocation_end(&self) -> u32 {
        todo!()
    }

    /// Generates the final allocations map.
    fn into_allocations(self) -> BTreeMap<ValueOrigin, Range<u32>> {
        todo!()
    }
}

struct OptimisticAllocator {
    occupation_tracker: OccupationTracker,
    labels: HashMap<u32, usize>,
}

impl OptimisticAllocator {
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
            let num_words = word_count_type::<S>(*output_type);
            self.occupation_tracker.allocate(origin, num_words);
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
                let num_words = word_count::<S>(&nodes, *origin);
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
            // TODO
            todo!()
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
    dag: LivenessDag<'a>,
    oa: &mut VecDeque<OptimisticAllocator>,
) -> (AllocatedDag<'a>, usize) {
    let mut number_of_saved_copies = 0;

    let LivenessDag {
        mut nodes,
        block_data: liveness,
    } = dag;

    let mut new_nodes = RevVecFiller::new(nodes.len());

    for index in (0..nodes.len()).rev() {
        let node = nodes.pop().unwrap();

        let operation = match node.operation {
            Operation::Inputs => {
                assert_eq!(index, 0);
                // TODO: handle the inputs that might not have been allocated yet.
                // (a pathological case for loop inputs, but still possible)
                todo!();

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
                        let arg_start = oa[0].occupation_tracker.allocation_end() + 2;

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
                        // This is the general case: for each input, allocate it.
                        for input in &node.inputs {
                            if let NodeInput::Reference(origin) = input {
                                oa[0]
                                    .occupation_tracker
                                    .allocate(*origin, word_count::<S>(&nodes, *origin));
                            }
                        }

                        // Also allocate any remaining output that was not allocated yet.
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
                // We need a new allocation tracker for the loop body.
                // It is derived from the current one, completely blocking the
                // slots that are occupied for the duration of the loop.
                let occupation_tracker = oa[0].occupation_tracker.make_sub_tracker(index);

                // There are some heuristics we can do here to minimize copies.

                // For each loop input, if it is already allocated, and this is the
                // last usage of the value (can happen if the value comes from the
                // input node), or if the loop body does not change the input,
                // just forwards it unchanged to the next iteration, we can fix
                // the allocation of the input to the current one, saving copies.
                todo!();

                let loop_oa = OptimisticAllocator {
                    occupation_tracker,
                    labels: HashMap::new(),
                };
                oa.push_front(loop_oa);

                let (loop_allocation, loop_saved_copies) =
                    recursive_block_allocation::<S>(sub_dag, oa);

                number_of_saved_copies += loop_saved_copies;

                // TODO: somehow save the loop allocation to the loop node...
                todo!()
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

    // Generate the final allocation for this block
    let OptimisticAllocator {
        occupation_tracker,
        labels,
    } = oa.pop_front().unwrap();

    let allocation = Allocation {
        nodes_outputs: occupation_tracker.into_allocations(),
        labels,
    };

    // Collect the new nodes
    let nodes = new_nodes.try_into_vec().unwrap();
    (
        AllocatedDag {
            nodes,
            block_data: allocation,
        },
        number_of_saved_copies,
    )
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
    let mut oa = OptimisticAllocator {
        occupation_tracker: OccupationTracker::new(),
        labels: HashMap::new(),
    };

    // Fix the allocation of the function inputs first
    let inputs = &dag.nodes[0];
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
    recursive_block_allocation::<S>(dag, &mut VecDeque::from([oa]))
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

/// Gets the word count of a value origin
fn word_count<'a, S: Settings<'a>>(nodes: &[liveness_dag::Node<'a>], origin: ValueOrigin) -> u32 {
    word_count_type::<S>(type_of(nodes, origin))
}
