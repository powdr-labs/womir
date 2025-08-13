pub mod const_dedup;
pub mod dangling_removal;

use std::{
    collections::{BTreeSet, HashMap, VecDeque},
    mem::MaybeUninit,
};

use itertools::Itertools;
use wasmparser::{FuncType, Operator as Op, RefType, ValType};

use crate::loader::Global;

use super::{
    Block, BlockKind, CommonProgram, Element, Instruction as Ins, locals_data_flow::LiftedBlockTree,
};

#[derive(Debug)]
pub enum Operation<'a> {
    Inputs,
    WASMOp(Op<'a>),
    BrIfZero { relative_depth: u32 },
    BrTable { targets: Vec<BrTableTarget> },
    Block { kind: BlockKind, sub_dag: Dag<'a> },
}

#[derive(Debug)]
pub struct BrTableTarget {
    pub relative_depth: u32,
    /// For each of the nodes inputs, this is the permutation of the inputs that
    /// each break target will receive.
    pub input_permutation: Vec<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ValueOrigin {
    pub node: usize,
    pub output_idx: u32,
}

impl ValueOrigin {
    pub fn new(node: usize, output_idx: u32) -> Self {
        Self { node, output_idx }
    }
}

#[derive(Debug)]
pub struct Node<'a> {
    pub operation: Operation<'a>,
    pub inputs: Vec<ValueOrigin>,
    pub output_types: Vec<ValType>,
}

#[derive(Debug)]
pub struct Dag<'a> {
    pub nodes: Vec<Node<'a>>,
}

impl<'a> Dag<'a> {
    pub fn new(
        module: &CommonProgram<'a>,
        func_type: &FuncType,
        locals_types: &[ValType],
        block_tree: LiftedBlockTree<'a>,
    ) -> wasmparser::Result<Self> {
        // Lets assemble a kind of directed graph, where the nodes are the operations that
        // can input and output values, and the edges are the values. It is directed in a
        // sense that variables have one origin and multiple destinations.

        // Sanity check: the first locals are the function arguments.
        assert_eq!(
            func_type.params(),
            &locals_types[..func_type.params().len()]
        );

        let mut locals = Vec::with_capacity(locals_types.len());

        // For the function body, the inputs are given as locals:
        locals.extend((0..func_type.params().len() as u32).map(|output_idx| {
            Value::Defined(ValueOrigin {
                node: 0,
                output_idx,
            })
        }));

        // The rest of the locals starts as unused.
        locals.extend(
            locals_types[func_type.params().len()..]
                .iter()
                .copied()
                .map(|val_type| Value::UnusedLocal { val_type }),
        );

        let mut block_stack = VecDeque::from([BreakArgs {
            stack: func_type.results().to_vec(),
            locals: BTreeSet::new(),
        }]);

        let nodes = build_dag(
            module,
            locals_types,
            func_type.params().to_vec(),
            &mut block_stack,
            Vec::new(),
            locals,
            block_tree.elements,
            &get_local_or_default,
        )?;

        Ok(Dag { nodes })
    }
}

struct BreakArgs {
    stack: Vec<ValType>,
    locals: BTreeSet<u32>,
}

/// Follows the instructions sequence of a block to build the DAG.
///
/// For that we need to keep track of the stack and of which of our hypergraph edges is
/// currently each local variable. When a local is assigned, it becames a new edge.
// TODO: refactor "too many arguments"
#[allow(clippy::too_many_arguments)]
// TODO: refactor
#[allow(clippy::type_complexity)]
fn build_dag<'a>(
    module: &CommonProgram<'a>,
    locals_types: &[ValType],
    input_types: Vec<ValType>,
    block_stack: &mut VecDeque<BreakArgs>,
    stack: Vec<ValueOrigin>,
    mut locals: Vec<Value>,
    block_elements: Vec<Element<'a>>,
    local_getter: &dyn Fn(&mut Vec<Node>, &mut [Value], u32) -> ValueOrigin,
) -> wasmparser::Result<Vec<Node<'a>>> {
    let mut t = StackTracker {
        module,
        // The first node in a block are the inputs
        nodes: vec![Node {
            operation: Operation::Inputs,
            inputs: Vec::new(),
            output_types: input_types.clone(),
        }],
        stack,
    };

    for elem in block_elements {
        log::trace!("Stack: {:#?}", t.stack);
        log::trace!("Processing element: {elem:#?}");
        match elem {
            // Most instructions creates a new node that consumes some inputs and produces
            // some outputs. We will have special handlers for cases that are no so simple.
            Element::Ins(inst) => match inst {
                // First we handle the special stack and local manipulation instructions
                // that don't create nodes. Instructions local.* and drop simply move
                // around the references between the stack and the locals, and most of the
                // time can be resolved statically.
                Ins::WASMOp(Op::LocalGet { local_index }) => {
                    // LocalGet simply pushes a local value to the stack, and it can be
                    // resolved immediatelly without creating a new node.

                    // We may need to mark the local as an input, if it is not already.
                    let value = local_getter(&mut t.nodes, &mut locals, local_index);
                    t.stack.push(value);
                }
                Ins::WASMOp(Op::LocalSet { local_index }) => {
                    // LocalSet pops a value from the stack and sets it to a local.
                    locals[local_index as usize] = Value::Defined(t.stack.pop().unwrap());
                }
                Ins::WASMOp(Op::LocalTee { local_index }) => {
                    // LocalTee copies the value from the stack to a local.
                    locals[local_index as usize] = Value::Defined(*t.stack.last().unwrap());
                }
                Ins::WASMOp(Op::Drop) => {
                    // Drop could be a node that consumes a value and produces nothing,
                    // but since it has no side effects, we can just resolve it statically.
                    t.stack.pop().unwrap();
                }

                // We now handle the break instructions. They are special because they
                // take inputs both from the stack and from the locals, and to know
                // which locals are inputs we need to look up at the block stack.
                Ins::WASMOp(op @ Op::Br { relative_depth }) => {
                    let target = &block_stack[relative_depth as usize];

                    // The stack part of the input
                    let mut inputs = t.stack.split_off(t.stack.len() - target.stack.len());
                    assert!(types_matches(&t.nodes, &target.stack, &inputs));

                    // The locals part of the input
                    for local_index in target.locals.iter() {
                        let value = local_getter(&mut t.nodes, &mut locals, *local_index);
                        inputs.push(value);
                    }

                    t.nodes.push(Node {
                        operation: Operation::WASMOp(op),
                        inputs,
                        output_types: Vec::new(),
                    });
                }
                Ins::WASMOp(Op::BrIf { relative_depth }) | Ins::BrIfZero { relative_depth } => {
                    let operation = match inst {
                        Ins::WASMOp(Op::BrIf { .. }) => {
                            Operation::WASMOp(Op::BrIf { relative_depth })
                        }
                        Ins::BrIfZero { .. } => Operation::BrIfZero { relative_depth },
                        _ => unreachable!(),
                    };

                    let target = &block_stack[relative_depth as usize];

                    // Pop the condition to reinsert it after the locals:
                    let cond = t.stack.pop().unwrap();
                    // Assert the condition type is I32.
                    assert_eq!(
                        t.nodes[cond.node].output_types[cond.output_idx as usize],
                        ValType::I32
                    );

                    // The stack part of the input
                    // BrIf[Not] does not consume the stack.
                    let mut inputs = t.stack[t.stack.len() - target.stack.len()..].to_vec();
                    assert!(types_matches(&t.nodes, &target.stack, &inputs));

                    // The locals part of the input
                    for local_index in target.locals.iter() {
                        let value = local_getter(&mut t.nodes, &mut locals, *local_index);
                        inputs.push(value);
                    }

                    // Push the condition back to the inputs
                    inputs.push(cond);

                    t.nodes.push(Node {
                        operation,
                        inputs,
                        output_types: Vec::new(),
                    });
                }
                Ins::BrTable { targets } => {
                    // The stack input for the br_table is the choice value, plus the
                    // stack inputs for the largest target.

                    // Take the choice to insert it back later.
                    let choice = t.stack.pop().unwrap();
                    // Assert the choice type is I32.
                    assert_eq!(
                        t.nodes[choice.node].output_types[choice.output_idx as usize],
                        ValType::I32
                    );

                    // Calculate how much of the stack to take
                    let largest_stack = targets
                        .iter()
                        .map(|target| &block_stack[*target as usize].stack)
                        .max_by_key(|t| t.len())
                        .unwrap();

                    // The stack part of the input
                    let mut inputs = t.stack.split_off(t.stack.len() - largest_stack.len());
                    assert!(types_matches(&t.nodes, largest_stack, &inputs));

                    // The locals part of the input is the union of the locals inputs
                    // for all the targets.
                    let mut locals_inputs = BTreeSet::new();
                    for target in targets.iter() {
                        let target = &block_stack[*target as usize];
                        locals_inputs.extend(target.locals.iter().copied());
                    }

                    // The locals part of the input
                    let mut locals_inputs_map = HashMap::new();
                    for local_index in locals_inputs.iter() {
                        locals_inputs_map.insert(*local_index, inputs.len() as u32);

                        let value = local_getter(&mut t.nodes, &mut locals, *local_index);
                        inputs.push(value);
                    }

                    // Push the choice back to the inputs
                    inputs.push(choice);

                    // Only a subset of the inputs are passed to each target.
                    // We need to calculate the permutation of the inputs for each target.
                    let targets = targets
                        .into_iter()
                        .map(|relative_depth| {
                            let target = &block_stack[relative_depth as usize];
                            let mut input_permutation = Vec::new();

                            // The stack part of the input
                            for i in 0..target.stack.len() {
                                let input_idx = largest_stack.len() - target.stack.len() + i;
                                input_permutation.push(input_idx as u32);
                            }

                            // The locals part of the input
                            for local_index in target.locals.iter() {
                                let input_idx = locals_inputs_map[local_index];
                                input_permutation.push(input_idx);
                            }

                            BrTableTarget {
                                relative_depth,
                                input_permutation,
                            }
                        })
                        .collect_vec();

                    t.nodes.push(Node {
                        operation: Operation::BrTable { targets },
                        inputs,
                        output_types: Vec::new(),
                    });
                }
                // The rest of the instructions are normal operations that creates a new node
                // that consumes some inputs and produces some outputs.
                Ins::WASMOp(op) => {
                    let (inputs_types, output_types) = t.get_operator_type(&op).unwrap();
                    let inputs = t.stack.split_off(t.stack.len() - inputs_types.len());
                    assert!(types_matches(&t.nodes, &inputs_types, &inputs));

                    let node_idx = t.nodes.len();
                    t.stack.extend(
                        (0..output_types.len() as u32).map(|output_idx| ValueOrigin {
                            node: node_idx,
                            output_idx,
                        }),
                    );

                    t.nodes.push(Node {
                        operation: Operation::WASMOp(op),
                        inputs,
                        output_types,
                    });
                }
            },
            Element::Block(block) => {
                // Blocks are not much different from a normal instruction. But instead of
                // taking and returning values just from the stack, they take and return
                // values from the locals and the stack.

                // Block inputs are the concatenation of the stack inputs and the locals inputs.
                let mut inputs = t
                    .stack
                    .split_off(t.stack.len() - block.interface_type.ty.params().len());

                // Sanity check the types
                assert!(types_matches(
                    &t.nodes,
                    block.interface_type.ty.params(),
                    &inputs
                ));

                inputs.extend(
                    block
                        .input_locals
                        .iter()
                        .map(|local_idx| local_getter(&mut t.nodes, &mut locals, *local_idx)),
                );

                // Of the outputs, the first ones goes to the stack.
                let node_idx = t.nodes.len();
                let stack_results_len = block.interface_type.ty.results().len() as u32;
                t.stack
                    .extend((0..stack_results_len).map(|output_idx| ValueOrigin {
                        node: node_idx,
                        output_idx,
                    }));

                // The rest of the outputs goes to the locals.
                for (i, output_local) in block.output_locals.iter().enumerate() {
                    locals[*output_local as usize] = Value::Defined(ValueOrigin {
                        node: node_idx,
                        output_idx: (i as u32 + stack_results_len),
                    });
                }

                // Build the DAG for the block and push it
                let node = build_dag_for_block(module, locals_types, inputs, block_stack, block)?;

                t.nodes.push(node);
            }
        }
    }

    let nodes = t.nodes;

    Ok(nodes)
}

fn build_dag_for_block<'a>(
    module: &CommonProgram<'a>,
    locals_types: &[ValType],
    inputs: Vec<ValueOrigin>,
    block_stack: &mut VecDeque<BreakArgs>,
    block: Block<'a>,
) -> wasmparser::Result<Node<'a>> {
    let Block {
        block_kind,
        interface_type,
        elements,

        input_locals,
        output_locals,
        ..
    } = block;

    // For a block, the inputs are given in a mix between the stack and the locals.
    // We place the stack inputs first on the new node:
    let mut input_types = interface_type.ty.params().to_vec();

    // We place the locals inputs last:
    let mut local_idx_to_input = HashMap::new();
    for local_idx in input_locals.iter() {
        local_idx_to_input.insert(*local_idx, input_types.len() as u32);
        input_types.push(locals_types[*local_idx as usize]);
    }

    // The stack inputs are the first elements in the stack.
    let stack = interface_type
        .ty
        .params()
        .iter()
        .enumerate()
        .map(|(i, _)| ValueOrigin {
            node: 0,
            output_idx: i as u32,
        })
        .collect_vec();

    // Locals that are inputs points to the first node in the block.
    let locals = locals_types
        .iter()
        .enumerate()
        .map(|(local_idx, val_type)| {
            if input_locals.contains(&(local_idx as u32)) {
                Value::Defined(ValueOrigin {
                    node: 0,
                    output_idx: local_idx_to_input[&(local_idx as u32)],
                })
            } else {
                let val_type = *val_type;
                Value::UnusedLocal { val_type }
            }
        })
        .collect_vec();

    // Output types are the concatenation of the stack outputs and the locals outputs.
    let mut output_types = interface_type.ty.results().to_vec();
    output_types.extend(
        output_locals
            .iter()
            .map(|local_idx| locals_types[*local_idx as usize]),
    );

    // What types are expected at a break depends wether this is a block or a loop.
    block_stack.push_front(match block_kind {
        BlockKind::Block => BreakArgs {
            stack: interface_type.ty.results().to_vec(),
            locals: output_locals,
        },
        BlockKind::Loop => BreakArgs {
            stack: interface_type.ty.params().to_vec(),
            locals: input_locals,
        },
    });

    let nodes = build_dag(
        module,
        locals_types,
        input_types,
        block_stack,
        stack,
        locals,
        elements,
        &get_local_or_panic,
    )?;

    block_stack.pop_front();

    Ok(Node {
        operation: Operation::Block {
            kind: block_kind,
            sub_dag: Dag { nodes },
        },
        inputs,
        output_types,
    })
}

// This function is passed as a function pointer argument where the signature needs a &mut Vec<Node>
// because sometimes the passed function pointer will modify the nodes, even though this is not the
// case here.
// TODO: could be refactored.
#[allow(clippy::ptr_arg)]
fn get_local_or_panic(
    _nodes: &mut Vec<Node>,
    locals: &mut [Value],
    local_index: u32,
) -> ValueOrigin {
    let local = &mut locals[local_index as usize];
    match local {
        Value::UnusedLocal { .. } => panic!("Local {local_index} should be defined"),
        Value::Defined(value) => *value,
    }
}

fn get_local_or_default(
    nodes: &mut Vec<Node>,
    locals: &mut [Value],
    local_index: u32,
) -> ValueOrigin {
    let local = &mut locals[local_index as usize];
    match local {
        Value::UnusedLocal { val_type } => {
            let node_idx = nodes.len();

            nodes.push(Node {
                operation: default_const_for_type(*val_type),
                inputs: Vec::new(),
                output_types: vec![*val_type],
            });

            let value = ValueOrigin {
                node: node_idx,
                output_idx: 0,
            };

            *local = Value::Defined(value);
            value
        }
        Value::Defined(value) => *value,
    }
}

fn types_matches(nodes: &[Node], expected_types: &[ValType], inputs: &[ValueOrigin]) -> bool {
    if inputs.len() != expected_types.len() {
        return false;
    }
    for (input, expected_type) in inputs.iter().zip(expected_types.iter()) {
        let node = &nodes[input.node];
        if node.output_types[input.output_idx as usize] != *expected_type {
            return false;
        }
    }
    true
}

#[derive(Clone, Copy)]
enum Value {
    UnusedLocal { val_type: ValType },
    Defined(ValueOrigin),
}

/// Returns a constant with the default value for the given type.
/// This is used to materialize the locals that are read before being written.
fn default_const_for_type(value_type: ValType) -> Operation<'static> {
    match value_type {
        ValType::I32 => Operation::WASMOp(Op::I32Const { value: 0 }),
        ValType::I64 => Operation::WASMOp(Op::I64Const { value: 0 }),
        ValType::F32 => Operation::WASMOp(Op::F32Const { value: 0.0.into() }),
        ValType::F64 => Operation::WASMOp(Op::F64Const { value: 0.0.into() }),
        ValType::V128 => Operation::WASMOp(Op::V128Const {
            // Apparently there is no way to instantiate a V128 value.
            // TODO: Fix this when issue is resolved: https://github.com/bytecodealliance/wasm-tools/issues/2101
            value: unsafe { MaybeUninit::zeroed().assume_init() },
        }),
        ValType::Ref(ref_type) => Operation::WASMOp(Op::RefNull {
            hty: ref_type.heap_type(),
        }),
    }
}

struct StackTracker<'a, 'b> {
    module: &'b CommonProgram<'a>,
    nodes: Vec<Node<'a>>,
    stack: Vec<ValueOrigin>,
}

impl StackTracker<'_, '_> {
    fn stack_type(&self, idx: usize) -> ValType {
        let val_type = &self.stack[idx];
        let node = &self.nodes[val_type.node];
        node.output_types[val_type.output_idx as usize]
    }

    /// Returns the list of input types and output types of an operator.
    fn get_operator_type(&self, op: &Op) -> Option<(Vec<ValType>, Vec<ValType>)> {
        let ty = match op {
            // # Numeric instructions
            // ## const
            Op::I32Const { .. } => (vec![], vec![ValType::I32]),
            Op::I64Const { .. } => (vec![], vec![ValType::I64]),
            Op::F32Const { .. } => (vec![], vec![ValType::F32]),
            Op::F64Const { .. } => (vec![], vec![ValType::F64]),
            // ## unop
            Op::I32Clz | Op::I32Ctz | Op::I32Popcnt | Op::I32Extend8S | Op::I32Extend16S => {
                (vec![ValType::I32], vec![ValType::I32])
            }
            Op::I64Clz
            | Op::I64Ctz
            | Op::I64Popcnt
            | Op::I64Extend8S
            | Op::I64Extend16S
            | Op::I64Extend32S => (vec![ValType::I64], vec![ValType::I64]),
            Op::F32Abs
            | Op::F32Neg
            | Op::F32Sqrt
            | Op::F32Ceil
            | Op::F32Floor
            | Op::F32Trunc
            | Op::F32Nearest => (vec![ValType::F32], vec![ValType::F32]),
            Op::F64Abs
            | Op::F64Neg
            | Op::F64Sqrt
            | Op::F64Ceil
            | Op::F64Floor
            | Op::F64Trunc
            | Op::F64Nearest => (vec![ValType::F64], vec![ValType::F64]),
            // ## binop
            Op::I32Add
            | Op::I32Sub
            | Op::I32Mul
            | Op::I32DivU
            | Op::I32DivS
            | Op::I32RemU
            | Op::I32RemS
            | Op::I32And
            | Op::I32Or
            | Op::I32Xor
            | Op::I32Shl
            | Op::I32ShrU
            | Op::I32ShrS
            | Op::I32Rotl
            | Op::I32Rotr => (vec![ValType::I32, ValType::I32], vec![ValType::I32]),
            Op::I64Add
            | Op::I64Sub
            | Op::I64Mul
            | Op::I64DivU
            | Op::I64DivS
            | Op::I64RemU
            | Op::I64RemS
            | Op::I64And
            | Op::I64Or
            | Op::I64Xor
            | Op::I64Shl
            | Op::I64ShrU
            | Op::I64ShrS
            | Op::I64Rotl
            | Op::I64Rotr => (vec![ValType::I64, ValType::I64], vec![ValType::I64]),
            Op::F32Add
            | Op::F32Sub
            | Op::F32Mul
            | Op::F32Div
            | Op::F32Min
            | Op::F32Max
            | Op::F32Copysign => (vec![ValType::F32, ValType::F32], vec![ValType::F32]),
            Op::F64Add
            | Op::F64Sub
            | Op::F64Mul
            | Op::F64Div
            | Op::F64Min
            | Op::F64Max
            | Op::F64Copysign => (vec![ValType::F64, ValType::F64], vec![ValType::F64]),
            // ## testop
            Op::I32Eqz => (vec![ValType::I32], vec![ValType::I32]),
            Op::I64Eqz => (vec![ValType::I64], vec![ValType::I32]),
            // ## relop
            Op::I32Eq
            | Op::I32Ne
            | Op::I32LtU
            | Op::I32LtS
            | Op::I32GtU
            | Op::I32GtS
            | Op::I32LeU
            | Op::I32LeS
            | Op::I32GeU
            | Op::I32GeS => (vec![ValType::I32, ValType::I32], vec![ValType::I32]),
            Op::I64Eq
            | Op::I64Ne
            | Op::I64LtU
            | Op::I64LtS
            | Op::I64GtU
            | Op::I64GtS
            | Op::I64LeU
            | Op::I64LeS
            | Op::I64GeU
            | Op::I64GeS => (vec![ValType::I64, ValType::I64], vec![ValType::I32]),
            Op::F32Eq | Op::F32Ne | Op::F32Lt | Op::F32Gt | Op::F32Le | Op::F32Ge => {
                (vec![ValType::F32, ValType::F32], vec![ValType::I32])
            }
            Op::F64Eq | Op::F64Ne | Op::F64Lt | Op::F64Gt | Op::F64Le | Op::F64Ge => {
                (vec![ValType::F64, ValType::F64], vec![ValType::I32])
            }
            // ## cvtop
            Op::I32WrapI64 => (vec![ValType::I64], vec![ValType::I32]),
            Op::I64ExtendI32U | Op::I64ExtendI32S => (vec![ValType::I32], vec![ValType::I64]),
            Op::I32TruncF32U
            | Op::I32TruncF32S
            | Op::I32TruncSatF32U
            | Op::I32TruncSatF32S
            | Op::I32ReinterpretF32 => (vec![ValType::F32], vec![ValType::I32]),
            Op::I64TruncF32U | Op::I64TruncF32S | Op::I64TruncSatF32U | Op::I64TruncSatF32S => {
                (vec![ValType::F32], vec![ValType::I64])
            }
            Op::I32TruncF64U | Op::I32TruncF64S | Op::I32TruncSatF64U | Op::I32TruncSatF64S => {
                (vec![ValType::F64], vec![ValType::I32])
            }
            Op::I64TruncF64U
            | Op::I64TruncF64S
            | Op::I64TruncSatF64U
            | Op::I64TruncSatF64S
            | Op::I64ReinterpretF64 => (vec![ValType::F64], vec![ValType::I64]),
            Op::F32DemoteF64 => (vec![ValType::F64], vec![ValType::F32]),
            Op::F64PromoteF32 => (vec![ValType::F32], vec![ValType::F64]),
            Op::F32ConvertI32U | Op::F32ConvertI32S | Op::F32ReinterpretI32 => {
                (vec![ValType::I32], vec![ValType::F32])
            }
            Op::F64ConvertI32U | Op::F64ConvertI32S => (vec![ValType::I32], vec![ValType::F64]),
            Op::F32ConvertI64U | Op::F32ConvertI64S => (vec![ValType::I64], vec![ValType::F32]),
            Op::F64ConvertI64U | Op::F64ConvertI64S | Op::F64ReinterpretI64 => {
                (vec![ValType::I64], vec![ValType::F64])
            }

            // # Reference instructions
            Op::RefNull { hty } => (
                vec![],
                vec![ValType::Ref(RefType::new(true, *hty).unwrap())],
            ),
            Op::RefIsNull => {
                let ValType::Ref(ref_type) = self.stack_type(self.stack.len() - 1) else {
                    panic!("ref.is_null expects a reference type")
                };
                assert!(ref_type.is_func_ref() || ref_type.is_extern_ref());
                (vec![ValType::Ref(ref_type)], vec![ValType::I32])
            }
            Op::RefFunc { .. } => (vec![], vec![ValType::Ref(RefType::FUNCREF)]),

            // TODO: # Vector instructions

            // # Parametric instructions
            Op::Select => {
                let len = self.stack.len();
                let ty = self.stack_type(len - 3);
                assert_eq!(ty, self.stack_type(len - 2));
                (vec![ty, ty, ValType::I32], vec![ty])
            }

            // # Variable instructions
            Op::GlobalGet { global_index } => {
                let Global::Mutable(global) = &self.module.globals[*global_index as usize] else {
                    panic!("immutable GlobalGet at DAG level");
                };
                (vec![], vec![global.val_type])
            }
            Op::GlobalSet { global_index } => {
                let Global::Mutable(global) = &self.module.globals[*global_index as usize] else {
                    panic!("GlobalSet on immutable global");
                };
                (vec![global.val_type], vec![])
            }

            // # Table instructions
            Op::TableGet { table } => {
                let ty = &self.module.table_types[*table as usize];
                (vec![ValType::I32], vec![ValType::Ref(*ty)])
            }
            Op::TableSet { table } => {
                let ty = &self.module.table_types[*table as usize];
                (vec![ValType::I32, ValType::Ref(*ty)], vec![])
            }
            Op::TableSize { .. } => (vec![], vec![ValType::I32]),
            Op::TableGrow { table } => {
                let ty = &self.module.table_types[*table as usize];
                (vec![ValType::Ref(*ty), ValType::I32], vec![ValType::I32])
            }
            Op::TableFill { table } => {
                let ty = &self.module.table_types[*table as usize];
                (vec![ValType::I32, ValType::Ref(*ty), ValType::I32], vec![])
            }
            Op::TableCopy { .. } | Op::TableInit { .. } => {
                (vec![ValType::I32, ValType::I32, ValType::I32], vec![])
            }
            Op::ElemDrop { .. } => (vec![], vec![]),

            // # Memory instructions
            // TODO: implement the vector instructions
            Op::I32Load { .. }
            | Op::I32Load8U { .. }
            | Op::I32Load8S { .. }
            | Op::I32Load16U { .. }
            | Op::I32Load16S { .. }
            | Op::MemoryGrow { .. } => (vec![ValType::I32], vec![ValType::I32]),
            Op::I64Load { .. }
            | Op::I64Load8U { .. }
            | Op::I64Load8S { .. }
            | Op::I64Load16U { .. }
            | Op::I64Load16S { .. }
            | Op::I64Load32U { .. }
            | Op::I64Load32S { .. } => (vec![ValType::I32], vec![ValType::I64]),
            Op::F32Load { .. } => (vec![ValType::I32], vec![ValType::F32]),
            Op::F64Load { .. } => (vec![ValType::I32], vec![ValType::F64]),
            Op::I32Store { .. } | Op::I32Store8 { .. } | Op::I32Store16 { .. } => {
                (vec![ValType::I32, ValType::I32], vec![])
            }
            Op::I64Store { .. }
            | Op::I64Store8 { .. }
            | Op::I64Store16 { .. }
            | Op::I64Store32 { .. } => (vec![ValType::I32, ValType::I64], vec![]),
            Op::F32Store { .. } => (vec![ValType::I32, ValType::F32], vec![]),
            Op::F64Store { .. } => (vec![ValType::I32, ValType::F64], vec![]),
            Op::MemorySize { .. } => (vec![], vec![ValType::I32]),
            Op::MemoryFill { .. } | Op::MemoryCopy { .. } | Op::MemoryInit { .. } => {
                (vec![ValType::I32, ValType::I32, ValType::I32], vec![])
            }
            Op::DataDrop { .. } => (vec![], vec![]),

            // # Control instructions
            Op::Nop | Op::Unreachable => (vec![], vec![]),
            Op::Call { function_index } => {
                let ty = &self.module.get_func_type(*function_index).ty;
                let inputs = ty.params().to_vec();
                let outputs = ty.results().to_vec();
                return Some((inputs, outputs));
            }
            Op::CallIndirect { type_index, .. } => {
                let ty = &self.module.get_type(*type_index).ty;
                let inputs = ty
                    .params()
                    .iter()
                    .cloned()
                    .chain(
                        std::iter::once(ValType::I32), // The last input is the entry index
                    )
                    .collect();
                let outputs = ty.results().to_vec();
                return Some((inputs, outputs));
            }

            // Instructions below are handled separately.
            // We return None for them:
            Op::LocalGet { .. }
            | Op::LocalSet { .. }
            | Op::LocalTee { .. }
            | Op::Drop
            | Op::Block { .. }
            | Op::Loop { .. }
            | Op::If { .. }
            | Op::Else
            | Op::End
            | Op::Br { .. }
            | Op::BrIf { .. }
            | Op::BrTable { .. }
            | Op::Return => return None,
            _ => todo!("{op:?}"),
        };

        Some(ty)
    }
}
