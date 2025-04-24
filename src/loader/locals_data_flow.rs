//! This module makes explicit the locals usage inside the blocks.
//!
//! Blocks have explicitly defined inputs and outputs, but since locals
//! can be used inside blocks, they act as alternative ways to pass
//! values into and out of blocks.
//!
//! This module makes explicit what locals are used either as inputs
//! or outputs to blocks.
//!
//! TODO: There is an optimization opportunity here, which is to track
//! locals permutation: if some locals are read into a block, but in
//! the end they are just output unmodified (either on stack or on some
//! local), this can be resolved statically when building the DAG,
//! eliding copies.

use std::{
    collections::{BTreeSet, VecDeque},
    rc::Rc,
};

use itertools::Itertools;
use wasmparser::{FuncType, LocalsReader, Operator, ValType};

use super::{
    Instruction as Ins, ModuleContext, SystemCall,
    block_tree::{self, BlockTree, Kind},
};

pub struct LiftedBlockTree<'a> {
    pub func_type: &'a FuncType,
    /// The first locals are arguments to the function, the rest are local variables.
    pub local_types: Vec<ValType>,
    pub elements: Vec<Element<'a>>,
}

pub fn lift_data_flow<'a, S: SystemCall>(
    ctx: &'a ModuleContext<'a, S>,
    func_idx: u32,
    locals_reader: LocalsReader<'a>,
    block_tree: BlockTree<'a>,
) -> wasmparser::Result<LiftedBlockTree<'a>> {
    let func_type = ctx.get_func_type(func_idx);
    let local_types = read_locals(func_type, locals_reader)?;

    let mut elements = Vec::new();

    for elem in block_tree.elements {
        let elem = match elem {
            block_tree::Element::Instruction(instruction) => Element::Ins(instruction),
            block_tree::Element::Child {
                block_kind,
                interface_type,
                elements,
            } => Element::Block(process_block(
                ctx,
                &mut VecDeque::new(),
                block_kind,
                interface_type,
                elements,
            )),
        };
        elements.push(elem);
    }

    // TODO: iterate again, until all the inputs and outputs are exposed.

    Ok(LiftedBlockTree {
        func_type,
        local_types,
        elements,
    })
}

/// Reads the function arguments and the explicit locals declaration.
fn read_locals<'a>(
    func_type: &'a FuncType,
    locals_reader: LocalsReader<'a>,
) -> wasmparser::Result<Vec<ValType>> {
    // The first locals are the function arguments.
    let mut local_types = func_type.params().iter().map(|t| *t).collect_vec();

    // The rest of the locals are explicitly defined local variables.
    for local in locals_reader {
        let (count, val_type) = local?;
        local_types.extend((0..count).map(|_| val_type));
    }

    Ok(local_types)
}

fn process_block<'a, S: SystemCall>(
    ctx: &ModuleContext<'a, S>,
    control_stack: &mut VecDeque<BlockStackEntry>,
    block_kind: Kind,
    interface_type: Rc<FuncType>,
    elements: Vec<block_tree::Element<'a>>,
) -> Block<'a> {
    // Push and pop from the front because it is indexed by the relative depth.
    control_stack.push_front(BlockStackEntry {
        break_locals: BTreeSet::new(),
    });
    let (new_elements, mut input_locals, mut output_locals) =
        process_elems(ctx, control_stack, BTreeSet::new(), elements);
    let this_entry = control_stack.pop_front().unwrap();

    let (block_kind, carried_locals) = match block_kind {
        Kind::Block => {
            // In a Block, breaks to it are outputs.
            output_locals.extend(this_entry.break_locals.iter());
            (Kind::Block, BTreeSet::new())
        }
        Kind::Loop => {
            // In a Loop, breaks to it are inputs.
            input_locals.extend(this_entry.break_locals.iter());
            (Kind::Loop, this_entry.break_locals)
        }
    };

    Block {
        block_kind,
        interface_type,
        input_locals,
        output_locals,
        carried_locals,
        elements: new_elements,
    }
}

fn process_elems<'a, S: SystemCall>(
    ctx: &ModuleContext<'a, S>,
    control_stack: &mut VecDeque<BlockStackEntry>,
    mut local_outputs: BTreeSet<u32>,
    elements: Vec<block_tree::Element<'a>>,
) -> (Vec<Element<'a>>, BTreeSet<u32>, BTreeSet<u32>) {
    let mut local_inputs = BTreeSet::new();

    let mut block_can_end = true;

    let elements = elements
        .into_iter()
        .map(|elem| match elem {
            block_tree::Element::Child {
                block_kind,
                interface_type,
                elements,
            } => {
                let block = process_block(ctx, control_stack, block_kind, interface_type, elements);

                local_inputs.extend(block.input_locals.iter());
                local_outputs.extend(block.output_locals.iter());

                Element::Block(block)
            }
            block_tree::Element::Instruction(ins) => {
                match &ins {
                    // Local variables operations
                    Ins::WASMOp(Operator::LocalGet { local_index }) => {
                        local_inputs.insert(*local_index);
                    }
                    Ins::WASMOp(Operator::LocalSet { local_index })
                    | Ins::WASMOp(Operator::LocalTee { local_index }) => {
                        local_outputs.insert(*local_index);
                    }

                    // Break operations
                    Ins::WASMOp(Operator::Br { relative_depth }) => {
                        block_can_end = false;
                        control_stack[*relative_depth as usize]
                            .break_locals
                            .extend(local_outputs.iter());
                    }
                    Ins::BrTable { targets } => {
                        block_can_end = false;
                        for relative_depth in targets {
                            control_stack[*relative_depth as usize]
                                .break_locals
                                .extend(local_outputs.iter());
                        }
                    }
                    Ins::WASMOp(Operator::BrIf { relative_depth })
                    | Ins::BrIfZero { relative_depth } => {
                        control_stack[*relative_depth as usize]
                            .break_locals
                            .extend(local_outputs.iter());
                    }

                    // Unreachable operation
                    Ins::WASMOp(Operator::Unreachable) => {
                        block_can_end = false;
                    }

                    // All other operations
                    Ins::WASMOp(_) => {}
                }

                Element::Ins(ins)
            }
        })
        .collect();

    // This block ended with a break or unreachable instruction,
    // so it has no fallthrough outputs.
    if !block_can_end {
        local_outputs.clear();
    }

    (elements, local_inputs, local_outputs)
}

struct BlockStackEntry {
    break_locals: BTreeSet<u32>,
}

struct Block<'a> {
    block_kind: Kind,
    interface_type: Rc<FuncType>,
    input_locals: BTreeSet<u32>,
    output_locals: BTreeSet<u32>,
    // Carried locals are a subset of the inputs that must be carried over to any breaks and output.
    // This is used in loops, so that if a previous iteration changed some local, the new value must
    // be carried through all the breaks and output in the future iterations.
    carried_locals: BTreeSet<u32>,
    elements: Vec<Element<'a>>,
}

pub enum Element<'a> {
    Ins(Ins<'a>),
    Block(Block<'a>),
}
