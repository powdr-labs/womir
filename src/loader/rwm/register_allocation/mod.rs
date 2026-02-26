mod occupation_tracker;

use std::{
    collections::{BTreeMap, HashMap, VecDeque},
    num::NonZeroU32,
    ops::Range,
};

use wasmparser::{Operator as Op, ValType};

use crate::{
    loader::{
        Module,
        blockless_dag::{BreakTarget, GenericBlocklessDag, NodeInput, Operation, TargetType},
        dag::ValueOrigin,
        passes::blockless_dag::GenericNode,
        rwm::{
            liveness_dag::{self, LivenessDag},
            register_allocation::occupation_tracker::{Occupation, OccupationTracker},
        },
        settings::Settings,
        word_count_type, word_count_types,
    },
    utils::rev_vec_filler::RevVecFiller,
};

#[derive(Debug)]
pub enum Error {
    NotAllocated,
    NotARegister,
}

/// One possible register allocation for a given DAG.
#[derive(Debug)]
pub struct Allocation {
    /// The registers assigned to the nodes outputs.
    nodes_outputs: BTreeMap<ValueOrigin, Range<u32>>,
    /// The full register occupation map.
    occupation: Occupation,
    /// The map of label id to its node index, for quick lookup on a break.
    pub labels: HashMap<u32, usize>,
    /// The call frame start register for each call node index.
    pub call_frames: HashMap<usize, u32>,
}

impl Allocation {
    pub fn get_for_node(&self, node_index: usize) -> impl Iterator<Item = Range<u32>> {
        let start = ValueOrigin {
            node: node_index,
            output_idx: 0,
        };
        let end = ValueOrigin {
            node: node_index + 1,
            output_idx: 0,
        };
        self.nodes_outputs.range(start..end).map(|(_, r)| r.clone())
    }

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

    pub fn occupation_for_node(&self, node_index: usize) -> Vec<Range<u32>> {
        self.occupation.reg_occupation(node_index..node_index + 1)
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
    fn allocate_inputs<'a, S: Settings>(
        &mut self,
        node_index: usize,
        inputs: &[NodeInput],
        nodes: &[liveness_dag::Node<'a>],
    ) {
        for input in inputs {
            if let NodeInput::Reference(origin) = input {
                let end_of_liveness = self
                    .occupation_tracker
                    .try_allocate(*origin, assert_non_zero(word_count::<S>(nodes, *origin)));

                // If the input was just allocated, it must end its life at this node.
                // Otherwise, it should already have been allocated.
                if let Some(end_of_liveness) = end_of_liveness {
                    assert_eq!(
                        end_of_liveness, node_index,
                        "liveness bug: value allocated after its last usage"
                    );
                }
            }
        }
    }

    /// Allocates the outputs of a node that have not been allocated yet.
    fn allocate_outputs<S: Settings>(
        &mut self,
        node_index: usize,
        output_types: &[ValType],
        outputs_may_live: bool,
    ) {
        for (output_idx, output_type) in output_types.iter().enumerate() {
            let origin = ValueOrigin {
                node: node_index,
                output_idx: output_idx as u32,
            };
            let num_words = assert_non_zero(word_count_type::<S>(*output_type));
            let end_of_liveness = self.occupation_tracker.try_allocate(origin, num_words);

            // If the output was just allocated, usually it has no users and ends its life
            // at this node. However, in some cases (like loop inputs), the output may live
            // beyond this node.
            if !outputs_may_live && let Some(end_of_liveness) = end_of_liveness {
                assert_eq!(
                    end_of_liveness,
                    node_index + 1,
                    "liveness bug: value allocated after its last usage"
                );
            }
        }
    }
}

/// Allocates the inputs for a break node.
fn handle_break<'a, S: Settings>(
    node_index: usize,
    nodes: &[liveness_dag::Node<'a>],
    oa: &mut VecDeque<OptimisticAllocator>,
    inputs: &[NodeInput],
    break_target: &BreakTarget,
    is_conditional: bool,
) -> usize {
    // For conditional breaks, the last input is the condition,
    // which is not tied to the break target.
    let inputs = if is_conditional {
        let (break_inputs, condition) = inputs.split_at(inputs.len() - 1);
        oa[0].allocate_inputs::<S>(node_index, condition, nodes);
        break_inputs
    } else {
        inputs
    };

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
                if try_allocate_with_hint(oa, node_index, *origin, next_reg..next_reg + num_words) {
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
                    // Node 0 is always the input node of a block.
                    node: 0,
                    output_idx: input_index as u32,
                };
                let loop_input_allocation = oa[target_idx]
                    .occupation_tracker
                    .get_allocation(loop_input_origin)
                    .expect("loop input must be allocated");
                let num_words = loop_input_allocation.len();
                let break_origin = unwrap_ref(break_input, "break inputs must be references");

                if try_allocate_with_hint(oa, node_index, *break_origin, loop_input_allocation) {
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

                if try_allocate_with_hint(oa, node_index, *break_origin, label_allocation) {
                    number_of_saved_copies += num_words;
                }
            }
        }
    }

    number_of_saved_copies
}

fn recursive_block_allocation<'a, S: Settings>(
    prog: &Module<'a>,
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
                // All node outputs must have been allocated already.
                Operation::Inputs
            }
            Operation::WASMOp(operator) => {
                match &operator {
                    Op::Call { .. } | Op::CallIndirect { .. } => 'call_match: {
                        let inputs = if let Op::Call { function_index } = &operator {
                            // If this is an imported function, treat it as a generic operation.
                            // We assume imported functions are kinda like system calls, and can
                            // read and write to any register we choose here.
                            if prog.get_imported_func(*function_index).is_some() {
                                oa[0].allocate_inputs::<S>(index, &node.inputs, &nodes);
                                oa[0].allocate_outputs::<S>(index, &node.output_types, false);
                                break 'call_match;
                            }
                            &node.inputs
                        } else {
                            // This is an indirect call, we need allocate the last input separately.
                            let (fn_inputs, fn_index) = node.inputs.split_at(node.inputs.len() - 1);
                            oa[0].allocate_inputs::<S>(index, fn_index, &nodes);
                            fn_inputs
                        };

                        // TODO: implement a simple heuristic to try to avoid having to
                        // copy the function outputs to the slots allocated for them by
                        // the nodes who uses them as inputs. The details are in
                        // TODO-optimizations.txt.

                        // On a given node index, the one after the last used slot is the
                        // start of the called function frame. From there, two slots are
                        // reserved for return address and frame pointer, and then come
                        // the arguments.
                        let output_sizes =
                            node.output_types.iter().map(|ty| word_count_type::<S>(*ty));
                        let mut next_arg = oa[0]
                            .occupation_tracker
                            .allocate_fn_call(index, output_sizes);

                        // Try to place the function inputs at the expected argument slots.
                        for input in inputs {
                            let origin =
                                unwrap_ref(input, "function call inputs must be references");
                            let num_words = word_count::<S>(&nodes, *origin);
                            if try_allocate_with_hint(
                                oa,
                                index,
                                *origin,
                                next_arg..next_arg + num_words,
                            ) {
                                number_of_saved_copies += num_words as usize;
                            }
                            next_arg += num_words;
                        }
                    }
                    _ => {
                        // This is the general case. Allocates inputs and outputs that have not been allocated yet.
                        oa[0].allocate_inputs::<S>(index, &node.inputs, &nodes);
                        oa[0].allocate_outputs::<S>(index, &node.output_types, false);
                    }
                };

                Operation::WASMOp(operator)
            }
            Operation::Label { id } => {
                // Record the current allocation for this label
                oa[0].labels.insert(id, index);

                // Allocate any remaining output that was not allocated yet.
                oa[0].allocate_outputs::<S>(index, &node.output_types, false);

                Operation::Label { id }
            }
            Operation::Loop {
                sub_dag,
                break_targets,
            } => {
                // As with the general case, we allocate the inputs of the loop node.
                // It has no outputs that would require allocation.
                oa[0].allocate_inputs::<S>(index, &node.inputs, &nodes);

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

                // There is an heuristic we do here to minimize copies: for each loop input, if this
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
                    if last_usage <= index && {
                        assert_eq!(
                            last_usage, index,
                            "liveness bug: last usage is before a node that uses the value"
                        );
                        true
                    } {
                        // This is the last usage of the value before the loop,
                        // so we should try to reuse the same allocation for the loop input.
                        // Doesn't always work, because the same input value could be used
                        // by multiple loop inputs. Only one will be able to reuse the allocation.
                        let allocation = oa[0].occupation_tracker.get_allocation(*origin).unwrap();
                        let alloc_len = allocation.len();
                        let hint_used = occupation_tracker
                            .try_allocate_with_hint(
                                ValueOrigin {
                                    node: 0,
                                    output_idx: input_idx as u32,
                                },
                                allocation,
                            )
                            .0;

                        if hint_used {
                            number_of_saved_copies += alloc_len;
                        }
                    } else if occupation_tracker
                        .liveness()
                        .query_if_input_is_redirected(input_idx as u32)
                    {
                        // This input outlives the loop body, but inside the loop
                        // it is just forwarded unchanged to the next iteration.
                        // We can always reuse the allocation from the outer level.
                        let allocation = oa[0].occupation_tracker.get_allocation(*origin).unwrap();
                        number_of_saved_copies += allocation.len();

                        occupation_tracker.set_allocation(
                            ValueOrigin {
                                node: 0,
                                output_idx: input_idx as u32,
                            },
                            allocation,
                        )
                    }
                }

                let mut loop_oa = OptimisticAllocator {
                    occupation_tracker,
                    labels: HashMap::new(),
                };

                // Allocate the rest of the input node values (inside the loop body).
                loop_oa.allocate_outputs::<S>(0, &loop_nodes[0].output_types, true);
                oa.push_front(loop_oa);

                let (loop_nodes, loop_saved_copies) =
                    recursive_block_allocation::<S>(prog, loop_nodes, oa);

                // Pop the loop allocation tracker.
                let OptimisticAllocator {
                    occupation_tracker,
                    labels,
                    ..
                } = oa.pop_front().unwrap();

                // Project the allocations back to the outer level. This will prevent
                // the outer level from placing allocations that should survive across
                // this loop block on registers that could be overwritten here.
                oa[0]
                    .occupation_tracker
                    .project_from_sub_tracker(index, &occupation_tracker);

                let allocation = occupation_tracker.into_allocations(labels);

                // Collect the new nodes
                let loop_dag = AllocatedDag {
                    nodes: loop_nodes,
                    block_data: allocation,
                };

                number_of_saved_copies += loop_saved_copies;

                Operation::Loop {
                    sub_dag: loop_dag,
                    break_targets,
                }
            }
            Operation::Br(break_target) => {
                number_of_saved_copies +=
                    handle_break::<S>(index, &nodes, oa, &node.inputs, &break_target, false);
                Operation::Br(break_target)
            }
            Operation::BrIf(break_target) => {
                number_of_saved_copies +=
                    handle_break::<S>(index, &nodes, oa, &node.inputs, &break_target, true);
                Operation::BrIf(break_target)
            }
            Operation::BrIfZero(break_target) => {
                number_of_saved_copies +=
                    handle_break::<S>(index, &nodes, oa, &node.inputs, &break_target, true);
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
                        handle_break::<S>(index, &nodes, oa, &inputs, &target.target, false);
                }
                // Allocate the selector input
                let selector_input = &node.inputs[node.inputs.len() - 1..];
                oa[0].allocate_inputs::<S>(index, selector_input, &nodes);

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

fn try_allocate_with_hint(
    oa: &mut VecDeque<OptimisticAllocator>,
    node_index: usize,
    origin: ValueOrigin,
    hint: Range<u32>,
) -> bool {
    let (at_hint, end_of_liveness) = oa[0]
        .occupation_tracker
        .try_allocate_with_hint(origin, hint);

    if let Some(end_of_liveness) = end_of_liveness {
        assert_eq!(
            end_of_liveness, node_index,
            "liveness bug: value allocated after its last usage"
        );
    }

    at_hint
}

/// Allocates registers for a given function DAG. It is not optimal, but it tries
/// to minimize the number of copies and used registers.
///
/// Does the allocation bottom up, following the execution paths independently,
/// proposing register assignment for future nodes (so to avoid copies), but
/// leaving a final assignment for the traversed nodes.
pub fn optimistic_allocation<'a, S: Settings>(
    prog: &Module<'a>,
    func_idx: u32,
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
    let mut next_in_reg = 0u32;
    for (output_idx, input) in inputs.output_types.iter().enumerate() {
        let origin = ValueOrigin {
            node: 0,
            output_idx: output_idx as u32,
        };
        let num_words = word_count_type::<S>(*input);
        oa.occupation_tracker
            .set_allocation(origin, next_in_reg..next_in_reg + num_words);
        next_in_reg += num_words;
    }

    // Calculate the space needed for the return values.
    let outputs = prog.get_func_type(func_idx).ty.results();
    let out_words = word_count_types::<S>(outputs);

    // Reserve the space for the return address and frame pointer after the maximum
    // between the inputs and outputs.
    let ra_fp_regs = next_in_reg.max(out_words);
    oa.occupation_tracker
        .reserve_range(ra_fp_regs..ra_fp_regs + 2 * S::words_per_ptr());

    // Do the allocation for the rest of the nodes, bottom up.
    let mut oa_stack = VecDeque::from([oa]);
    let (nodes, number_of_saved_copies) =
        recursive_block_allocation::<S>(prog, nodes, &mut oa_stack);

    // Generate the final allocation for this block
    let OptimisticAllocator {
        occupation_tracker,
        labels,
        ..
    } = oa_stack.pop_front().unwrap();

    let allocation = occupation_tracker.into_allocations(labels);

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
fn word_count<'a, S: Settings>(nodes: &[liveness_dag::Node<'a>], origin: ValueOrigin) -> u32 {
    word_count_type::<S>(type_of(nodes, origin))
}
