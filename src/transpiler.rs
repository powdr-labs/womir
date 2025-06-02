use crate::loader::dag::Operation;
use petravm_asm::parser::InstructionsWithLabels as I;
use wasmparser::{FuncType, Operator as Op, RefType, ValType};

pub fn transpile(op: &Op) -> I {
    match op {
        /*
        Op::I32Add { .. } => {}
                    // ## binop
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
                        let global = &self.module.p.globals[*global_index as usize];
                        (vec![], vec![global.val_type])
                    }
                    Op::GlobalSet { global_index } => {
                        let global = &self.module.p.globals[*global_index as usize];
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
                        let ty = self.module.get_func_type(*function_index);
                        let inputs = ty.params().to_vec();
                        let outputs = ty.results().to_vec();
                        return Some((inputs, outputs));
                    }
                    Op::CallIndirect { type_index, .. } => {
                        let ty = self.module.get_type(*type_index);
                        let inputs = ty.params().to_vec();
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
        */
        _ => I::Label("unimp".to_string(), None),
    }
}
