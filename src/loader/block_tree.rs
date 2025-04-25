use std::{collections::BTreeSet, iter::Peekable, rc::Rc};

use wasmparser::{BlockType, FuncType, Operator, OperatorsIterator, OperatorsReader};

use super::{Block, BlockKind, Element, Instruction, ModuleContext, SystemCall};

/// BlockTree is a simplified representation of a WASM function.
///
/// It is a tree of blocks, whose root is the Function block.
///
/// There are only two kinds of blocks: "Block" and "Loop". The if-else sequence:
/// ```
/// if
///     <if_block>
/// else
///     <else_block>
/// end
/// ```
///
/// is turned into:
/// ```
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
/// ```
/// block
///     br_if_zero 0
///     <if_block>
/// end
/// ```
///
/// The block contents are simplified: `return` is turned into the appropriate
/// `br`, and dead code after `br`, `br_table` and `unreachable` instructions is removed.
pub struct BlockTree<'a> {
    pub elements: Vec<Element<'a>>,
}

impl<'a> BlockTree<'a> {
    pub fn load_function<S: SystemCall>(
        ctx: &ModuleContext<S>,
        op_reader: OperatorsReader<'a>,
    ) -> wasmparser::Result<Self> {
        let mut op_reader = op_reader.into_iter().peekable();

        let mut elements = Vec::new();
        let ending = parse_contents(ctx, &mut op_reader, 0, 0, &mut elements)?;
        assert_eq!(ending, Ending::End);

        Ok(Self { elements })
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Ending {
    End,
    Else,
}

fn parse_contents<'a, S: SystemCall>(
    ctx: &ModuleContext<S>,
    op_reader: &mut Peekable<OperatorsIterator<'a>>,
    stack_level: u32,
    stack_offset: u32,
    output_elements: &mut Vec<Element<'a>>,
) -> wasmparser::Result<Ending> {
    let ending = loop {
        let op = op_reader.next().unwrap()?;
        match op {
            Operator::If { blockty } => {
                // Parse the if contents of the if tranformation.
                let mut elements = vec![Instruction::WASMOp(Operator::Nop).into()]; // Placeholder for the conditional break
                let ending =
                    parse_contents(ctx, op_reader, stack_level + 1, stack_offset, &mut elements)?;

                let interface_type = get_type(ctx, blockty);

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

                        // Read the else block. It will end up one level deeper than the original block,
                        // so we need to add an offset to the relative depth of its inner breaks.
                        let ending = parse_contents(
                            ctx,
                            op_reader,
                            stack_level + 2,
                            stack_offset + 1,
                            &mut inner_elements,
                        )?;
                        assert_eq!(ending, Ending::End);

                        // At the end of the else block, the if part must be skipped, so
                        // we jump to the end of the outer block.
                        inner_elements
                            .push(Instruction::WASMOp(Operator::Br { relative_depth: 1 }).into());

                        // The inputs of the inner block are the same as the outer block, but it has
                        // no proper output.
                        let inner_type =
                            Rc::new(FuncType::new(interface_type.params().iter().cloned(), []));

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
                        interface_type: get_type(ctx, blockty),
                        elements,
                        input_locals: BTreeSet::new(),
                        output_locals: BTreeSet::new(),
                        carried_locals: BTreeSet::new(),
                    }
                    .into(),
                );
            }
            Operator::Else => {
                // End of the current block with and Else
                break Ending::Else;
            }
            Operator::End => {
                // End of the current block with and End
                break Ending::End;
            }
            Operator::Block { blockty } | Operator::Loop { blockty } => {
                // Start of a new block
                let block_type = match op {
                    Operator::Block { .. } => BlockKind::Block,
                    Operator::Loop { .. } => BlockKind::Loop,
                    _ => unreachable!(),
                };

                let mut block_contents = Vec::new();
                let ending = parse_contents(
                    ctx,
                    op_reader,
                    stack_level + 1,
                    stack_offset,
                    &mut block_contents,
                )?;
                assert_eq!(ending, Ending::End);

                output_elements.push(
                    Block {
                        block_kind: block_type,
                        interface_type: get_type(ctx, blockty),
                        elements: block_contents,
                        input_locals: BTreeSet::new(),
                        output_locals: BTreeSet::new(),
                        carried_locals: BTreeSet::new(),
                    }
                    .into(),
                );
            }
            Operator::Br { relative_depth } => {
                output_elements.push(
                    Instruction::WASMOp(Operator::Br {
                        relative_depth: relative_depth + stack_offset,
                    })
                    .into(),
                );
                discard_dead_code(op_reader)?;
            }
            Operator::BrIf { relative_depth } => {
                output_elements.push(
                    Instruction::WASMOp(Operator::BrIf {
                        relative_depth: relative_depth + stack_offset,
                    })
                    .into(),
                );
            }
            Operator::BrTable { targets } => {
                let targets = targets
                    .targets()
                    .map(|target| target.map(|t| t + stack_offset))
                    .collect::<wasmparser::Result<Vec<u32>>>()?;
                output_elements.push(Instruction::BrTable { targets }.into());

                discard_dead_code(op_reader)?;
            }
            Operator::Return => {
                // Add the equivalent br operator to the contents
                output_elements.push(
                    Instruction::WASMOp(Operator::Br {
                        relative_depth: stack_level,
                    })
                    .into(),
                );
                discard_dead_code(op_reader)?;
            }
            Operator::Unreachable => {
                output_elements.push(Instruction::WASMOp(op).into());
                discard_dead_code(op_reader)?;
            }
            op => {
                // Add the operator to the contents
                output_elements.push(Instruction::WASMOp(op).into());
            }
        }
    };

    Ok(ending)
}

fn get_type<S: SystemCall>(ctx: &ModuleContext<S>, blockty: BlockType) -> Rc<FuncType> {
    match blockty {
        BlockType::Empty => Rc::new(FuncType::new([], [])),
        BlockType::FuncType(idx) => ctx.get_func_type_rc(idx),
        BlockType::Type(t) => Rc::new(FuncType::new([t], [])),
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
