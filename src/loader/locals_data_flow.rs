//! This module makes explicit the locals usage inside the blocks.
//!
//! Blocks have explicitly defined inputs and outputs, but since locals
//! can be used inside blocks, they act as alternative ways to pass
//! values into and out of blocks.
//!
//! This module makes explicit what locals are used either as inputs
//! or outputs to blocks.

use std::{collections::BTreeSet, rc::Rc};

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
            block_tree::Element::Instruction(instruction) => instruction.into(),
            block_tree::Element::Child {
                block_kind,
                interface_type,
                elements,
            } => process_block(
                ctx,
                &local_types,
                &mut Vec::new(),
                block_kind,
                interface_type,
                elements,
            ),
        };
        elements.push(elem);
    }

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
    local_types: &[ValType],
    control_stack: &mut Vec<BlockStackEntry>,
    block_kind: Kind,
    interface_type: Rc<FuncType>,
    elements: Vec<block_tree::Element<'a>>,
) -> Element<'a> {
    control_stack.push(BlockStackEntry {});

    match block_kind {
        Kind::Block => {
            process_block_block(ctx, local_types, control_stack, interface_type, elements)
        }
        Kind::Loop => process_loop_block(ctx, local_types, control_stack, interface_type, elements),
    }
}

fn process_block_block<'a, S: SystemCall>(
    ctx: &ModuleContext<'a, S>,
    local_types: &[ValType],
    control_stack: &mut Vec<BlockStackEntry>,
    interface_type: Rc<FuncType>,
    elements: Vec<block_tree::Element<'a>>,
) -> Element<'a> {
    let elements = process_elems(ctx, elements);

    todo!()
}

fn process_loop_block<'a, S: SystemCall>(
    ctx: &ModuleContext<'a, S>,
    local_types: &[ValType],
    control_stack: &mut Vec<BlockStackEntry>,
    interface_type: Rc<FuncType>,
    elements: Vec<block_tree::Element<'a>>,
) -> Element<'a> {
    todo!()
}

fn process_elems<'a, S: SystemCall>(
    ctx: &ModuleContext<'a, S>,
    elements: Vec<block_tree::Element<'a>>,
) -> Vec<Element<'a>> {
    let mut local_inputs = BTreeSet::new();
    let mut local_outputs = BTreeSet::new();

    let mut block_can_end = true;

    elements
        .into_iter()
        .map(|elem| match elem {
            block_tree::Element::Instruction(ins) => {
                match ins {
                    // Local variables operations
                    Ins::WASMOp(Operator::LocalGet { local_index }) => {
                        local_inputs.insert(local_index);
                    }
                    Ins::WASMOp(Operator::LocalSet { local_index })
                    | Ins::WASMOp(Operator::LocalTee { local_index }) => {
                        local_outputs.insert(local_index);
                    }

                    // Break operations
                    Ins::WASMOp(Operator::Br { relative_depth }) => {
                        block_can_end = false;
                        todo!()
                    }
                    Ins::BrTable { targets } => {
                        block_can_end = false;
                        todo!()
                    }
                    Ins::WASMOp(Operator::BrIf { relative_depth })
                    | Ins::BrIfZero { relative_depth } => {}

                    // Unreachable operation
                    Ins::WASMOp(Operator::Unreachable) => {
                        block_can_end = false;
                    }

                    // All other operations
                    Ins::WASMOp(_) => {}
                }

                ins.into()
            }
            block_tree::Element::Child {
                block_kind,
                interface_type,
                elements,
            } => process_block(ctx, &mut Vec::new(), block_kind, interface_type, elements),
        })
        .collect()
}

struct BlockStackEntry {}

pub enum Element<'a> {
    Ins(Ins<'a>),
    Block {
        block_kind: Kind,
        interface_type: Rc<FuncType>,
        input_locals: Vec<u32>,  // sorted
        output_locals: Vec<u32>, // sorted
        elements: Vec<Element<'a>>,
    },
}

impl<'a> From<Ins<'a>> for Element<'a> {
    fn from(instruction: Ins<'a>) -> Self {
        Element::Ins(instruction)
    }
}
