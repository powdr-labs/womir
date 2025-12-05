use std::{
    collections::{BTreeMap, HashMap},
    ops::Range,
};

use itertools::Itertools;
use wasmparser::{Operator as Op, ValType};

use crate::loader::{
    blockless_dag::{BreakTarget, NodeInput, Operation, TargetType},
    dag::ValueOrigin,
    liveness_dag::LivenessDag,
    rw_flattening::Settings,
    word_count_type,
};

pub enum Error {
    NotAllocated,
    NotARegister,
}

/// One possible register allocation for a given DAG.
pub struct Allocation {
    /// The registers assigned to the nodes outputs.
    nodes_outputs: BTreeMap<ValueOrigin, Range<u32>>,
    /// The registers assigned to the labels. On a break, there is a chance that
    /// the register were already written with the correct value. If not, it must
    /// be written on demand, just before the break.
    pub labels: HashMap<u32, Vec<Range<u32>>>,
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

/// Tracks what registers are currently occupied by what values.
struct OccupationTracker {
    // TODO
}

impl OccupationTracker {
    fn new() -> Self {
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
}

struct OptimisticAllocator {
    curr_depth: u32,
    occupation_tracker: OccupationTracker,
    labels: HashMap<u32, usize>,
    number_of_saved_copies: usize,
}

impl OptimisticAllocator {
    /// Allocates the inputs for a break node.
    fn handle_break<'a, S: Settings<'a>>(
        &mut self,
        dag: &LivenessDag<'_>,
        inputs: &[NodeInput],
        break_target: &BreakTarget,
    ) {
        match break_target.kind {
            TargetType::FunctionOrLoop if break_target.depth >= self.curr_depth => {
                // This is a function return. We must try to place the outputs in the expected registers.
                assert!(break_target.depth == self.curr_depth);
                let mut next_reg = 0u32;
                for input in inputs {
                    let origin = unwrap_ref(input, "break inputs must be references");
                    let num_words = word_count::<S>(&dag, *origin);
                    if self
                        .occupation_tracker
                        .try_allocate_with_hint(*origin, next_reg..next_reg + num_words)
                    {
                        self.number_of_saved_copies += num_words as usize;
                    }
                    next_reg += num_words;
                }
            }
            TargetType::FunctionOrLoop => {
                // This is a break out of a loop...
                // TODO
                todo!()
            }
            TargetType::Label(label) => {
                // This is a break to a label. We should try to match the break inputs
                // to the label's outputs, to avoid a copy.
                let label_index = self.labels.get(&label).expect("label must be defined");
                let label_node = &dag.nodes[*label_index];
                for (index, (break_input, label_output)) in inputs
                    .iter()
                    .zip_eq(label_node.output_types.iter())
                    .enumerate()
                {
                    let break_origin = unwrap_ref(break_input, "break inputs must be references");

                    // Sanitity check: label output and break input must match.
                    assert_eq!(type_of(&dag, *break_origin), *label_output);

                    // Try to allocate the break input at the same registers as the label output
                    let label_origin = ValueOrigin {
                        node: *label_index,
                        output_idx: index as u32,
                    };
                    let label_allocation = self
                        .occupation_tracker
                        .get_allocation(label_origin)
                        .unwrap();
                    if self
                        .occupation_tracker
                        .try_allocate_with_hint(*break_origin, label_allocation)
                    {
                        self.number_of_saved_copies += word_count_type::<S>(*label_output) as usize;
                    }
                }
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
            let num_words = word_count_type::<S>(*output_type);
            self.occupation_tracker.allocate(origin, num_words);
        }
    }
}

/// Allocates registers for a given DAG. It is not optimal, but it tries to
/// minimize the number of copies and used registers.
///
/// Does the allocation bottom up, following the execution paths independently,
/// proposing register assignment for future nodes (so to avoid copies), but
/// leaving a final assignment for the traversed nodes.
pub fn optimistic_allocation<'a, S: Settings<'a>>(dag: &LivenessDag<'_>) -> (Allocation, usize) {
    let mut oa = OptimisticAllocator {
        curr_depth: 0, // TODO: this must be passed recursively
        occupation_tracker: OccupationTracker::new(),
        labels: HashMap::new(),
        number_of_saved_copies: 0,
    };

    // Fix the allocation of the inputs first
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

    for (index, node) in dag.nodes.iter().enumerate().rev() {
        match &node.operation {
            Operation::Inputs => {
                assert_eq!(index, 0);
                // Already handled
            }
            Operation::WASMOp(operator) => match operator {
                Op::Call { .. } | Op::CallIndirect { .. } => {
                    // TODO: implement a simple heuristic to try to avoid having to
                    // copy the function outputs to the slots allocated for them by
                    // the nodes who uses them as inputs.
                    //
                    // The idea goes like this: we first check if an output slot
                    // was specifically requested by the user node, with a hint.
                    // If it was, then we most likely have to do copy it anyway, so
                    // we stop. If it wasn't, we check if between this call and the last
                    // user of the output there are no other function calls (and we
                    // must check inside the loop blocks as well). If there are not,
                    // then we can set the output slots to the ones that naturally
                    // follow from the function callm avoiding a register copy. In this
                    // case, it is also possible that we can shift the call frame
                    // itself some slots up, as the removal of the original output slots
                    // might have freed up some space.
                    //
                    // The search can follow uncoditional breaks, skipping code that
                    // will not be executed in this path.
                    //
                    // Since the search stops at the next function call, this heuristic
                    // is still linear in the number of nodes.
                    //
                    // It might leave holes in the register allocation, but the
                    // optimization problem is NP-hard, so we must stop somewhere.

                    // On a given node index, the one after the last used slot is the
                    // start of the called function frame. From there, two slots are
                    // reserved for return address and frame pointer, and then come
                    // the arguments.
                    let arg_start = oa.occupation_tracker.allocation_end() + 2;

                    for input in &node.inputs {
                        let origin = unwrap_ref(input, "function call inputs must be references");
                        let num_words = word_count::<S>(&dag, *origin);
                        if oa
                            .occupation_tracker
                            .try_allocate_with_hint(*origin, arg_start..arg_start + num_words)
                        {
                            oa.number_of_saved_copies += num_words as usize;
                        }
                    }
                }
                _ => {
                    // This is the general case: for each input, allocate it.
                    for input in &node.inputs {
                        if let NodeInput::Reference(origin) = input {
                            oa.occupation_tracker
                                .allocate(*origin, word_count::<S>(&dag, *origin));
                        }
                    }

                    oa.allocate_outputs::<S>(index, &node.output_types);
                }
            },
            Operation::Label { id } => {
                // Record the current allocation for this label
                oa.labels.insert(*id, index);

                oa.allocate_outputs::<S>(index, &node.output_types);
            }
            Operation::Loop {
                sub_dag,
                break_targets,
            } => todo!(),
            Operation::Br(break_target)
            | Operation::BrIf(break_target)
            | Operation::BrIfZero(break_target) => {
                oa.handle_break::<S>(dag, &node.inputs, break_target);
            }
            Operation::BrTable { targets } => {
                let mut inputs = Vec::new();
                for target in targets {
                    inputs.clear();
                    inputs.extend(
                        target
                            .input_permutation
                            .iter()
                            .map(|&idx| node.inputs[idx as usize].clone()),
                    );
                    oa.handle_break::<S>(dag, &inputs, &target.target);
                }
            }
        }
    }

    todo!()
}

/// Helper to extract ValueOrigin from NodeInput
fn unwrap_ref<'a>(input: &'a NodeInput, msg: &'static str) -> &'a ValueOrigin {
    match input {
        NodeInput::Reference(origin) => origin,
        NodeInput::Constant(_) => panic!("{}", msg),
    }
}

/// Gets the type of a value origin
fn type_of<'a>(dag: &LivenessDag<'_>, origin: ValueOrigin) -> ValType {
    let node = &dag.nodes[origin.node];
    node.output_types[origin.output_idx as usize]
}

/// Gets the word count of a value origin
fn word_count<'a, S: Settings<'a>>(dag: &LivenessDag<'_>, origin: ValueOrigin) -> u32 {
    word_count_type::<S>(type_of(dag, origin))
}
