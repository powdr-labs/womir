use std::{collections::BTreeSet, iter::Peekable, rc::Rc};

use wasmparser::{BlockType, Operator, OperatorsIterator, OperatorsReader, ValType};

use crate::loader::{FuncType, Global};

use super::{Block, BlockKind, CommonProgram, Element, Instruction};

/// BlockTree is a simplified representation of a WASM function.
///
/// It is a tree of blocks, whose root is the Function block.
///
/// There are only two kinds of blocks: "Block" and "Loop". The if-else sequence:
/// ```text
/// if
///     <if_block>
/// else
///     <else_block>
/// end
/// ```
///
/// is turned into:
/// ```text
/// block
///     block
///         br_if 0
///         <else_block>
///         br 1
///     end
///     <if_block>
/// end
/// ```
///
/// or, in the case else is empty:
/// ```text
/// block
///     br_if_zero 0
///     <if_block>
/// end
/// ```
///
/// The block contents are simplified:
///  - `return` is turned into the appropriate `br`;
///  - explicit `br` is inserted at the end of every block that would otherwise fall through (function body included);
///  - a consequence of the previous, loops are only exited through breaks. An outer block is added to the loop if
///    needed to break out of it;
///  - dead code is removed after non-fallthrough loops and `br`, `br_table` and `unreachable` instructions;
///  - `global.get` that refers to constants are turned into the appropriate constant instruction (it is important this
///    is done early on, before the const optimizations).
#[derive(Debug)]
pub struct BlockTree<'a> {
    pub elements: Vec<Element<'a>>,
}

impl<'a> BlockTree<'a> {
    pub fn load_function(
        ctx: &CommonProgram<'a>,
        op_reader: OperatorsReader<'a>,
    ) -> wasmparser::Result<Self> {
        let mut op_reader = op_reader.into_iter().peekable();

        let mut elements = Vec::new();
        let (ending, can_falltrhough) = parse_contents(ctx, &mut op_reader, 0, &mut elements)?;
        assert_eq!(ending, Ending::End);

        if can_falltrhough {
            // Emit the implicit br at the end of the function
            elements.push(Instruction::WASMOp(Operator::Br { relative_depth: 0 }).into());
        }

        Ok(Self { elements })
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Ending {
    End,
    Else,
}

fn parse_contents<'a>(
    ctx: &CommonProgram<'a>,
    op_reader: &mut Peekable<OperatorsIterator<'a>>,
    stack_level: u32,
    output_elements: &mut Vec<Element<'a>>,
) -> wasmparser::Result<(Ending, bool)> {
    let mut last_can_fallthrough = true;
    let (ending, can_fallthrough) = loop {
        let op = op_reader.next().unwrap()?;
        last_can_fallthrough = match op {
            Operator::If { blockty } => {
                // Parse the if contents of the if tranformation.
                let mut elements = vec![Instruction::WASMOp(Operator::Nop).into()]; // Placeholder for the conditional break
                let (ending, if_can_fallthrough) =
                    parse_contents(ctx, op_reader, stack_level + 1, &mut elements)?;

                if if_can_fallthrough {
                    // Emit the implict br at the end of the block
                    elements.push(Instruction::WASMOp(Operator::Br { relative_depth: 0 }).into());
                }

                let interface_type = get_type(ctx, blockty);

                // The newly generated if block has the same type as the original if block, plus one extra
                // parameter for the condition.
                let params = {
                    let mut params = interface_type.ty.params().to_vec();
                    // The condition:
                    params.push(ValType::I32);
                    params
                };

                match ending {
                    Ending::End => {
                        // Emit the simpler version of the if without an else, using BrIfZero
                        // Skips the if elements when condition is false.
                        elements[0] = Instruction::BrIfZero { relative_depth: 0 }.into();
                    }
                    Ending::Else => {
                        // The condition of the if is checked at the start of the inner block, skipping the
                        // else elements in it if the condition is true.
                        let mut inner_elements =
                            vec![Instruction::WASMOp(Operator::BrIf { relative_depth: 0 }).into()];

                        // Read the else block.
                        let (ending, else_can_fallthrough) =
                            parse_contents(ctx, op_reader, stack_level + 1, &mut inner_elements)?;
                        assert_eq!(ending, Ending::End);

                        // The else block is one level deeper than the outer block, so we need to
                        // adjust all the external br references in it, including 0 (which becomes
                        // 1, the outer block).
                        for element in &mut inner_elements[1..] {
                            increment_outer_br_references(element, 0);
                        }

                        // At the end of the else block, the if part must be skipped, so
                        // we jump to the end of the outer block (unless else is already being
                        // skipped by some br inside it).
                        if else_can_fallthrough {
                            inner_elements.push(
                                Instruction::WASMOp(Operator::Br { relative_depth: 1 }).into(),
                            );
                        }

                        // The inner block has the same inputs as the outer block,
                        // and needs to propagate the inputs as outputs to the true block,
                        // minus the condition.
                        let inner_type =
                            new_func_type(params.clone(), params[0..params.len() - 1].to_vec());

                        // The first thing in the outer block is the inner block
                        let inner_block = Block {
                            block_kind: BlockKind::Block,
                            interface_type: inner_type,
                            elements: inner_elements,
                            input_locals: BTreeSet::new(),
                            output_locals: BTreeSet::new(),
                            carried_locals: BTreeSet::new(),
                        }
                        .into();
                        elements[0] = inner_block;
                    }
                }

                output_elements.push(
                    Block {
                        block_kind: BlockKind::Block,
                        interface_type: new_func_type(params, interface_type.ty.results().to_vec()),
                        elements,
                        input_locals: BTreeSet::new(),
                        output_locals: BTreeSet::new(),
                        carried_locals: BTreeSet::new(),
                    }
                    .into(),
                );

                true
            }
            Operator::Else => {
                // End of the current block with and Else
                break (Ending::Else, last_can_fallthrough);
            }
            Operator::End => {
                // End of the current block with and End
                break (Ending::End, last_can_fallthrough);
            }
            Operator::Block { blockty } => {
                // Start of a new block
                let mut block_contents = Vec::new();
                let (ending, can_fallthrough) =
                    parse_contents(ctx, op_reader, stack_level + 1, &mut block_contents)?;
                assert_eq!(ending, Ending::End);

                if can_fallthrough {
                    // Emit the implict br at the end of the block
                    block_contents
                        .push(Instruction::WASMOp(Operator::Br { relative_depth: 0 }).into());
                }

                output_elements.push(
                    Block {
                        block_kind: BlockKind::Block,
                        interface_type: get_type(ctx, blockty),
                        elements: block_contents,
                        input_locals: BTreeSet::new(),
                        output_locals: BTreeSet::new(),
                        carried_locals: BTreeSet::new(),
                    }
                    .into(),
                );

                true
            }
            Operator::Loop { blockty } => {
                // Start of a new loop

                let mut elements = Vec::new();
                let (ending, can_fallthrough) =
                    parse_contents(ctx, op_reader, stack_level + 1, &mut elements)?;
                assert_eq!(ending, Ending::End);

                let interface_type = get_type(ctx, blockty);
                let input_type = new_func_type(interface_type.ty.params().iter().cloned(), []);

                let mut loop_block = Block {
                    block_kind: BlockKind::Loop,
                    // After the transformatin, a loop block only has inputs.
                    // Because either it doesn't fall through, or the output belongs
                    // to the generated outer block.
                    interface_type: input_type,
                    elements,
                    input_locals: BTreeSet::new(),
                    output_locals: BTreeSet::new(),
                    carried_locals: BTreeSet::new(),
                };

                let block = if can_fallthrough {
                    // We need to place a Block around this loop, so we can emit the implicit br.
                    // For that, we must adjust the break references that are >= 1.
                    for element in &mut loop_block.elements {
                        increment_outer_br_references(element, 1);
                    }

                    // Emit the implicit br to out of the loop.
                    loop_block
                        .elements
                        .push(Instruction::WASMOp(Operator::Br { relative_depth: 1 }).into());

                    let outer_elements = vec![
                        loop_block.into(),
                        // No br instruction needed because the loop was adjusted to not fall through.
                    ];

                    Block {
                        block_kind: BlockKind::Block,
                        interface_type,
                        elements: outer_elements,
                        input_locals: BTreeSet::new(),
                        output_locals: BTreeSet::new(),
                        carried_locals: BTreeSet::new(),
                    }
                } else {
                    loop_block
                };

                output_elements.push(block.into());

                can_fallthrough
            }
            Operator::Br { relative_depth } => {
                output_elements.push(Instruction::WASMOp(Operator::Br { relative_depth }).into());

                false
            }
            Operator::BrIf { relative_depth } => {
                output_elements.push(Instruction::WASMOp(Operator::BrIf { relative_depth }).into());

                true
            }
            Operator::BrTable { targets } => {
                let mut t = targets
                    .targets()
                    .collect::<wasmparser::Result<Vec<u32>>>()?;
                // Default target goes last.
                t.push(targets.default());
                output_elements.push(Instruction::BrTable { targets: t }.into());

                false
            }
            Operator::Return => {
                // Add the equivalent br operator to the contents
                output_elements.push(
                    Instruction::WASMOp(Operator::Br {
                        relative_depth: stack_level,
                    })
                    .into(),
                );

                false
            }
            Operator::Unreachable => {
                output_elements.push(Instruction::WASMOp(op).into());

                false
            }
            Operator::GlobalGet { global_index } => {
                // If the global is a constant, replace it with the constant value.
                match &ctx.globals[global_index as usize] {
                    Global::Mutable(..) => {
                        // Mutable globals are not constants, so we leave the operator as is.
                        output_elements.push(Instruction::WASMOp(op).into());
                    }
                    Global::Immutable(operator) => {
                        output_elements.push(Instruction::WASMOp(operator.clone()).into());
                    }
                }

                true
            }
            op => {
                // Add the operator to the contents
                output_elements.push(Instruction::WASMOp(op).into());

                true
            }
        };

        if !last_can_fallthrough {
            discard_dead_code(op_reader)?;
        }
    };

    Ok((ending, can_fallthrough))
}

fn increment_outer_br_references(element: &mut Element, minimum_depth: u32) {
    match element {
        Element::Ins(Instruction::WASMOp(Operator::Br { relative_depth }))
        | Element::Ins(Instruction::WASMOp(Operator::BrIf { relative_depth }))
        | Element::Ins(Instruction::BrIfZero { relative_depth }) => {
            if *relative_depth >= minimum_depth {
                *relative_depth += 1;
            }
        }
        Element::Ins(Instruction::BrTable { targets }) => {
            for target in targets {
                if *target >= minimum_depth {
                    *target += 1;
                }
            }
        }
        Element::Block(block) => {
            for element in &mut block.elements {
                increment_outer_br_references(element, minimum_depth + 1);
            }
        }
        _ => {}
    }
}

fn get_type(ctx: &CommonProgram, blockty: BlockType) -> Rc<FuncType> {
    match blockty {
        BlockType::Empty => new_func_type([], []),
        BlockType::FuncType(idx) => ctx.get_type_rc(idx),
        BlockType::Type(t) => new_func_type([], [t]),
    }
}

/// Some instructions unconditionally divert the control flow, leaving everithing between
/// themselves and the end of the current block unreachable.
///
/// Call this function after processing such instructions to discard the unreachable code.
fn discard_dead_code(op_reader: &mut Peekable<OperatorsIterator<'_>>) -> wasmparser::Result<()> {
    // Discard unreachable code
    let mut stack_count = 0;

    // We do a peek loop so we leave Else and End operators in the iterator,
    // to be handled by the caller.
    while let Some(operator) = op_reader.peek() {
        match operator {
            Ok(Operator::Block { .. }) | Ok(Operator::Loop { .. }) | Ok(Operator::If { .. }) => {
                stack_count += 1;
            }
            Ok(Operator::Else) => {
                if stack_count == 0 {
                    break;
                }
            }
            Ok(Operator::End) => {
                if stack_count == 0 {
                    break;
                }
                stack_count -= 1;
            }
            Ok(_) => {}
            Err(_) => {
                return Err(op_reader.next().unwrap().unwrap_err());
            }
        }
        op_reader.next();
    }

    Ok(())
}

fn new_func_type(
    params: impl IntoIterator<Item = ValType>,
    results: impl IntoIterator<Item = ValType>,
) -> Rc<FuncType> {
    Rc::new(FuncType {
        unique_id: u32::MAX, // Placeholder, not used in BlockTree
        ty: wasmparser::FuncType::new(params, results),
    })
}
