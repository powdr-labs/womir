use core::slice;
use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet, btree_map::Entry},
    marker::PhantomData,
    mem::MaybeUninit,
};

use itertools::Itertools;
use wasmparser::{
    BlockType, ContType, FuncType, FunctionBody, ModuleArity, Operator, OperatorsIterator, RefType,
    SubType, ValType,
};

use super::{ModuleContext, SystemCall};

enum Operation<'a> {
    Inputs,
    WASMOp(Operator<'a>),
    Block {
        // TODO: This local_idx_to_input doesn't really belong in the final output,
        // as it is used only to fixup the breaks. Find a better place to store it.
        local_idx_to_input: BTreeMap<u32, u32>,
        nodes: Vec<Node<'a>>,
    },
    Loop {
        local_idx_to_input: BTreeMap<u32, u32>,
        nodes: Vec<Node<'a>>,
    },
    // TODO: trasnform all the if ... else ... into block { block { br_if 0 ... bn 1 } ... },
    // Then we don't need to handle the complicated IfElse block.
    IfElse {
        local_idx_to_input: BTreeMap<u32, u32>,
        if_nodes: Vec<Node<'a>>,
        else_nodes: Vec<Node<'a>>,
    },
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct ValueOrigin {
    node: usize,
    output_idx: u32,
}

pub struct Node<'a> {
    operation: Operation<'a>,
    inputs: Vec<ValueOrigin>,
    output_types: Cow<'a, [ValType]>,
}

pub struct Dag<'a, S: SystemCall> {
    _todo: PhantomData<&'a S>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum BlockKind {
    Block,
    Loop,
    If,
    Else,
}

struct ReferencingBreak {
    path: Vec<u32>,
    /// Maps the local index to the value that it contained at the time of the break.
    locals_written: BTreeMap<u32, ValueOrigin>,
}

struct Block {
    blockty: BlockType,
    block_kind: BlockKind,
    /// As we traverse the program, we need to keep track of the breaks into this block,
    /// so we can consolidate the inputs and outputs of the block.
    breaks: Vec<ReferencingBreak>,
}

impl Block {
    /// The expected stack arguments when breaking into this block.
    /// Does not include the implict arguments given through the locals.
    fn break_args<'a, S: SystemCall>(&self, ctx: &'a ModuleContext<'a, S>) -> Cow<'a, [ValType]> {
        match self.block_kind {
            BlockKind::Loop => match self.blockty {
                // For loop, we need to return the inputs of the block.
                BlockType::Empty | BlockType::Type(_) => Cow::Owned(Vec::new()),
                BlockType::FuncType(f_idx) => {
                    let func_type = ctx.get_func_type(f_idx);
                    Cow::Borrowed(func_type.params())
                }
            },
            BlockKind::Block | BlockKind::If | BlockKind::Else => match self.blockty {
                // For block and if, we need to return the outputs of the block.
                BlockType::Empty => Cow::Owned(Vec::new()),
                BlockType::Type(ty) => Cow::Owned(vec![ty]),
                BlockType::FuncType(f_idx) => {
                    let func_type = ctx.get_func_type(f_idx);
                    Cow::Borrowed(func_type.results())
                }
            },
        }
    }
}

struct StackTracker<'a, S: SystemCall> {
    ctx: &'a ModuleContext<'a, S>,
    control_stack: Vec<Block>,
    dag_path: Vec<u32>,
}

impl<S: SystemCall> ModuleArity for StackTracker<'_, S> {
    fn sub_type_at(&self, type_idx: u32) -> Option<&SubType> {
        self.ctx.types.get(type_idx as usize)
    }

    fn tag_type_arity(&self, _at: u32) -> Option<(u32, u32)> {
        panic!("exception handling proposal not supported")
    }

    fn type_index_of_function(&self, function_idx: u32) -> Option<u32> {
        self.ctx.func_types.get(function_idx as usize).copied()
    }

    fn func_type_of_cont_type(&self, _c: &ContType) -> Option<&FuncType> {
        panic!("continuations proposal not supported")
    }

    fn sub_type_of_ref_type(&self, _rt: &RefType) -> Option<&SubType> {
        panic!("gc proposal not supported")
    }

    fn control_stack_height(&self) -> u32 {
        self.control_stack.len() as u32
    }

    fn label_block(&self, depth: u32) -> Option<(wasmparser::BlockType, wasmparser::FrameKind)> {
        self.control_stack.get(depth as usize + 1).map(|frame| {
            (
                frame.blockty,
                match frame.block_kind {
                    BlockKind::Block => wasmparser::FrameKind::Block,
                    BlockKind::Loop => wasmparser::FrameKind::Loop,
                    BlockKind::If => wasmparser::FrameKind::If,
                    BlockKind::Else => wasmparser::FrameKind::Else,
                    _ => unreachable!(),
                },
            )
        })
    }
}

impl<'a, S: SystemCall> Dag<'a, S> {
    pub fn load_function(
        ctx: &ModuleContext<'_, S>,
        func_idx: u32,
        body: FunctionBody,
    ) -> wasmparser::Result<Self> {
        // Lets assemble a kind of directed graph, where the nodes are the operations that
        // can input and output values, and the edges are the values. It is directed in a
        // sense that variables have one origin and multiple destinations.

        // We start by reading the input and local variables.
        let func_type = ctx.get_func_type(func_idx);
        let (mut nodes, mut locals) = read_locals(func_type, &body)?;

        // Now we follow the instructions in the function body.
        // For that we need to keep track of the stack and of which of our hypergraph edge is
        // currently each local variable. When a local is assigned, it becames a new edge.
        //
        // It is a little tricky with blocks, because we only know if a local is either read or
        // written after we have parsed the block. If a local is read, it becames a block input.
        // If a local is written, it becames a block output.
        let mut stack: Vec<ValueOrigin> = Vec::new();

        let ctrl_stack = StackTracker {
            ctx,
            control_stack: Vec::new(),
            dag_path: Vec::new(),
        };

        todo!()
    }
}

#[derive(Clone, Copy, Default)]
struct LocalRole {
    as_input: Option<u32>,
    as_output: bool,
}

/// Builds a DAG for a block of instructions.
fn build_dag_for_block<'a, S: SystemCall>(
    ctrl_stack: &mut StackTracker<'a, S>,
    operators: &mut OperatorsIterator<'a>,
    inputs: Cow<'a, [ValType]>,
    locals_types: &[ValType],
) -> wasmparser::Result<(Vec<Node<'a>>, Vec<LocalRole>)> {
    // We must track whether each local is an input and/or an output.
    let mut locals_roles: Vec<LocalRole> = vec![Default::default(); locals_types.len()];

    // We must track what each local is relative to the local DAG
    let mut locals = locals_types
        .iter()
        .map(|val_type| Value::UnusedLocal {
            val_type: *val_type,
        })
        .collect::<Vec<_>>();

    // The first node in a block are the inputs, but we still don't know the complete
    // picture, as locals may be read, which will make them inputs.
    let num_inputs = inputs.len() as u32;
    let mut nodes = vec![Node {
        operation: Operation::Inputs,
        inputs: Vec::new(),
        output_types: inputs,
    }];

    // To follow the instructions in the block body, we need to keep track of the stack.
    let mut stack: Vec<ValueOrigin> = (0..num_inputs)
        .map(|output_idx| ValueOrigin {
            node: 0,
            output_idx,
        })
        .collect();

    while let Some(operator) = operators.next() {
        let operator = operator?;

        // Most operators creates a new node that consumes some inputs and produces
        // some outputs. We will handle here the special cases that are no so simple.
        match operator {
            // First we handle the special stack and local manipulation operators that
            // don't create nodes. Instructions local.* and drop simply move around
            // the references between the stack and the locals, and most of the time
            // can be resolved statically.
            Operator::LocalGet { local_index } => {
                // LocalGet simply pushes a local value to the stack, and it can be
                // resolved immediatelly without creating a new node.

                // We may need to mark the local as an input, if it is not already.
                let value = local_get(&mut nodes, &mut locals, &mut locals_roles, local_index);
                stack.push(value);
            }
            Operator::LocalSet { local_index } => {
                locals[local_index as usize] = Value::Defined(stack.pop().unwrap());
                locals_roles[local_index as usize].as_output = true;
            }
            Operator::LocalTee { local_index } => {
                locals[local_index as usize] = Value::Defined(stack.last().unwrap().clone());
                locals_roles[local_index as usize].as_output = true;
            }
            Operator::Drop => {
                // Drop could be a node that consumes a value and produces nothing,
                // but since it has no side effects, we can just resolve it statically.
                stack.pop().unwrap();
            }
            // We now handle the break and return operators. They generate data consuming
            // nodes, but breaks are very special in that we don't fully know the locals
            // that migh become outputs until we finish parsing the block, so we need to keep
            // track of all the breaks, pending
            Operator::Return => {
                todo!()
            }
            Operator::Br { relative_depth } => {
                if relative_depth as usize == ctrl_stack.control_stack.len() {
                    // This is a return
                    todo!()
                } else {
                    // This is a inner block break
                    let target_block = ctrl_stack
                        .control_stack
                        .get_mut(relative_depth as usize)
                        .unwrap();

                    let expected_inputs = target_block.break_args(ctrl_stack.ctx);
                    assert!(stack.len() >= expected_inputs.len());
                    let inputs = stack.split_off(stack.len() - expected_inputs.len());
                    assert!(types_matches(&nodes, &expected_inputs, &inputs));

                    let node_idx = nodes.len();
                    nodes.push(Node {
                        operation: Operation::WASMOp(operator),
                        // These inputs are not completely resolved yet. They will be
                        // resolved when we finish parsing the block they refer to.
                        // We will include the outputs from locals that were written
                        // at every break to this block.
                        inputs,
                        output_types: Cow::Owned(Vec::new()),
                    });

                    // Save the path to the node in the breaks list.
                    // The path is relative to the block that is being broken.
                    let mut path = ctrl_stack.dag_path
                        [(ctrl_stack.dag_path.len() - relative_depth as usize)..]
                        .to_vec();
                    path.push(node_idx as u32);
                    target_block.breaks.push(ReferencingBreak {
                        path,
                        locals_written: locals_roles
                            .iter()
                            .enumerate()
                            .filter_map(|(i, role)| {
                                if role.as_output {
                                    let Value::Defined(local) = locals[i] else {
                                        unreachable!()
                                    };
                                    Some((i as u32, local))
                                } else {
                                    None
                                }
                            })
                            .collect(),
                    });
                }
            }
            Operator::BrIf { relative_depth } => {
                todo!()
            }
            Operator::BrTable { targets } => {
                todo!()
            }
            // Blocks are the last set of special operators. They call this function
            // recursively to build the DAG for the block, and then must use its control stack output
            // to compute the final inputs and outputs of the block, and ajust the referenced breaks.
            Operator::Block { blockty } => {
                // We need to push the block to the control stack, and then call this function
                // recursively to build the DAG for the block.
                ctrl_stack.control_stack.push(Block {
                    blockty,
                    block_kind: BlockKind::Block,
                    breaks: Vec::new(),
                });
                ctrl_stack.dag_path.push(nodes.len() as u32);

                let stack_inputs = match blockty {
                    BlockType::Empty | BlockType::Type(_) => Cow::Owned(Vec::new()),
                    BlockType::FuncType(f_idx) => {
                        let func_type = ctrl_stack.ctx.get_func_type(f_idx);
                        Cow::Borrowed(func_type.params())
                    }
                };
                assert!(stack_inputs.len() <= stack.len());
                let mut inputs = stack.split_off(stack.len() - stack_inputs.len());
                assert!(types_matches(&nodes, &stack_inputs, &inputs));

                let (mut block_nodes, block_local_roles) =
                    build_dag_for_block(ctrl_stack, operators, stack_inputs, locals_types)?;

                // Undo the pushes to the control stack
                let ctrl_block = ctrl_stack.control_stack.pop().unwrap();
                ctrl_stack.dag_path.pop();

                // Before creating a node for this block, we need to calculate which locals
                // are inputs/outputs.

                // For a block, local inputs are whatever returned:
                let mut local_idx_to_input = BTreeMap::new();
                let local_inputs: std::vec::IntoIter<(u32, u32)> = block_local_roles
                    .iter()
                    .enumerate()
                    .filter_map(|(local_index, role)| {
                        if let Some(input_index) = role.as_input {
                            local_idx_to_input.insert(local_index as u32, input_index);
                            Some((input_index, local_index as u32))
                        } else {
                            None
                        }
                    })
                    .sorted();

                // Extend the inputs with the locals that were found to be inputs.
                for (input_index, local_index) in local_inputs {
                    assert_eq!(input_index, inputs.len() as u32);
                    inputs.push(local_get(
                        &mut nodes,
                        &mut locals,
                        &mut locals_roles,
                        local_index,
                    ));
                }

                // For a block, local outputs are the merge of the outputs in all the breaks
                let mut local_outputs = BTreeSet::new();
                for br in ctrl_block.breaks.iter() {
                    for local_index in br.locals_written.keys() {
                        local_outputs.insert(*local_index);
                    }
                }

                let mut output_types = match blockty {
                    BlockType::Empty => Vec::new(),
                    BlockType::Type(ty) => vec![ty],
                    BlockType::FuncType(f_idx) => {
                        let func_type = ctrl_stack.ctx.get_func_type(f_idx);
                        func_type.results().to_vec()
                    }
                };

                // Push the stack outputs
                for i in 0..output_types.len() {
                    stack.push(ValueOrigin {
                        node: nodes.len(),
                        output_idx: i as u32,
                    })
                }

                // Extend the outputs with the locals that were found to be outputs.
                for idx in local_outputs.iter() {
                    output_types.push(locals_types[*idx as usize]);

                    // Also set the local with the value of the output.
                    locals[*idx as usize] = Value::Defined(ValueOrigin {
                        node: nodes.len(),
                        output_idx: (output_types.len() - 1) as u32,
                    });
                    locals_roles[*idx as usize].as_output = true;
                }

                let mut node = Node {
                    operation: Operation::Block {
                        nodes: block_nodes,
                        local_idx_to_input,
                    },
                    inputs,
                    output_types: Cow::Owned(output_types),
                };

                // Fixup the breaks to include all the locals that must be output
                for br in ctrl_block.breaks {
                    fixup_break(&mut node, &local_outputs, &locals_types, br);
                }

                nodes.push(node);
            }
            _ => todo!(),
        }
    }

    Ok((nodes, locals_roles))
}

fn fixup_break(
    toplevel_node: &mut Node,
    local_outputs: &BTreeSet<u32>,
    locals_types: &[ValType],
    br: ReferencingBreak,
) {
    // Find out what local inputs we will need.
    let new_inputs = local_outputs
        .iter()
        .filter_map(|local_index| {
            (!br.locals_written.contains_key(local_index)).then(|| {
                // The local was not known as an output at parse time, which means we
                // will have to forward it from the block inputs.
                *local_index
            })
        })
        .collect_vec();

    // Ensure the needed local inputs are available all the way to the toplevel node.
    ensure_local_is_input(toplevel_node, without_last(&br.path), new_inputs);

    // Get the break node that is missing the outputs from the locals.
    let (break_node, local_inputs_map) = get_nodes_from_path(toplevel_node, &br.path);

    // Adds the extra inputs to the break node.
    for local_index in local_outputs.iter() {
        // The outputs registered at the time of the parsing
        // are a subset of the outputs that we need to add.
        let value = match br.locals_written.get(local_index) {
            Some(value) => *value,
            None => {
                // The output was not known at the time, so we just forward the
                // unmodified local from the block inputs.

                // By this point, we already ensured the local is a block input.
                let input_idx = local_inputs_map[local_index];

                ValueOrigin {
                    node: 0,
                    output_idx: input_idx,
                }
            }
        };

        break_node.inputs.push(value);
    }
}

fn without_last<T>(slice: &[T]) -> &[T] {
    let len = slice.len();
    &slice[..len - 1]
}

fn ensure_local_is_input<'a, 'b>(
    node: &'a mut Node<'b>,
    path: &[u32],
    required_inputs: Vec<u32>,
) -> u32 {
    todo!()
}

fn get_nodes_from_path<'a, 'b, 'ret>(
    mut node: &'a mut Node<'b>,
    path: &[u32],
) -> (&'ret mut Node<'b>, &'ret mut BTreeMap<u32, u32>)
where
    'a: 'ret,
    'b: 'ret,
{
    let mut path_iter = path.iter();

    // We know path has at least one element.
    let mut node_idx = *path_iter.next().unwrap();
    loop {
        let (local_inputs_map, nodes) = match &mut node.operation {
            Operation::Block {
                local_idx_to_input,
                nodes,
            }
            | Operation::Loop {
                local_idx_to_input,
                nodes,
            } => (local_idx_to_input, nodes),

            Operation::IfElse {
                local_idx_to_input,
                if_nodes,
                else_nodes,
            } => {
                // Consume one extra path element to choose branch
                let branch = *path_iter.next().unwrap();
                (
                    local_idx_to_input,
                    match branch {
                        0 => if_nodes,
                        1 => else_nodes,
                        _ => unreachable!(),
                    },
                )
            }
            _ => unreachable!(),
        };

        node = &mut nodes[node_idx as usize];
        if let Some(next_idx) = path_iter.next() {
            node_idx = *next_idx;
        } else {
            return (node, local_inputs_map);
        }
    }
}

fn local_get(
    nodes: &mut [Node],
    locals: &mut [Value],
    locals_roles: &mut [LocalRole],
    local_index: u32,
) -> ValueOrigin {
    let local = &mut locals[local_index as usize];
    match local {
        Value::UnusedLocal { val_type } => {
            // We are reading a value from an unused local, we need mark it as an input.
            let block_inputs = &mut nodes[0].output_types;
            let output_idx = block_inputs.len() as u32;
            block_inputs.to_mut().push(*val_type);
            locals_roles[local_index as usize].as_input = Some(output_idx);

            // The local is now an input, we need to reference it.
            let value = ValueOrigin {
                node: 0,
                output_idx,
            };

            *local = Value::Defined(value);
            value
        }
        Value::Defined(value) => *value,
    }
}

fn types_matches(nodes: &[Node], expected_types: &[ValType], inputs: &[ValueOrigin]) -> bool {
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

/// Reads the function arguments and the explicit locals declaration.
fn read_locals<'a>(
    func_type: &'a FuncType,
    body: &FunctionBody,
) -> wasmparser::Result<(Vec<Node<'a>>, Vec<Value>)> {
    // The locals are the function arguments and the explicit locals declaration.

    // Function arguments originates from the special FunctionArgs node.
    let num_args = func_type.params().len() as u32;
    let args = Node {
        operation: Operation::Inputs,
        inputs: Vec::new(),
        output_types: Cow::Borrowed(func_type.params()),
    };

    let mut locals: Vec<Value> = (0..num_args as u32)
        .map(|output_idx| {
            Value::Defined(ValueOrigin {
                node: 0,
                output_idx,
            })
        })
        .collect();

    let nodes = vec![args];

    // Explicit locals are not materialized until used.
    for local in body.get_locals_reader()? {
        let (count, val_type) = local?;
        for _ in 0..count {
            locals.push(Value::UnusedLocal { val_type });
        }
    }

    Ok((nodes, locals))
}

/// Returns a constant with the default value for the given type.
/// This is used to materialize the locals that are read before being written.
fn default_const_for_type(value_type: ValType) -> Operation<'static> {
    match value_type {
        ValType::I32 => Operation::WASMOp(Operator::I32Const { value: 0 }),
        ValType::I64 => Operation::WASMOp(Operator::I64Const { value: 0 }),
        ValType::F32 => Operation::WASMOp(Operator::F32Const { value: 0.0.into() }),
        ValType::F64 => Operation::WASMOp(Operator::F64Const { value: 0.0.into() }),
        ValType::V128 => Operation::WASMOp(Operator::V128Const {
            // Apparently there is no way to instantiate a V128 value.
            // TODO: Fix this when issue is resolved: https://github.com/bytecodealliance/wasm-tools/issues/2101
            value: unsafe { MaybeUninit::zeroed().assume_init() },
        }),
        ValType::Ref(ref_type) => Operation::WASMOp(Operator::RefNull {
            hty: ref_type.heap_type(),
        }),
    }
}
