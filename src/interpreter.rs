use core::panic;
use std::collections::HashMap;
use std::ops::Range;

use itertools::Itertools;
use wasmparser::Operator as Op;

use crate::generic_ir::{Directive, GenericIrSetting as S};
use crate::linker;
use crate::loader::{Global, Program, Segment, WASM_PAGE_SIZE, func_idx_to_label, word_count_type};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VRomValue {
    Unassigned,
    Future(u32),
    Concrete(u32),
}

impl From<u32> for VRomValue {
    fn from(value: u32) -> Self {
        VRomValue::Concrete(value)
    }
}

pub struct Interpreter<'a, E: ExternalFunctions> {
    // TODO: maybe these 4 initial fields should be unique per `run()` call?
    pc: u32,
    fp: u32,
    future_counter: u32,
    future_assignments: HashMap<u32, u32>,
    vrom: Vec<VRomValue>,
    ram: HashMap<u32, u32>,
    program: Program<'a, S>,
    external_functions: E,
    flat_program: Vec<Directive<'a>>,
    labels: HashMap<String, linker::LabelValue>,
}

pub trait ExternalFunctions {
    fn call(&mut self, module: &str, func: &str, args: &[u32]) -> Vec<u32>;
}

impl<'a, E: ExternalFunctions> Interpreter<'a, E> {
    pub fn new(program: Program<'a, S>, external_functions: E) -> Self {
        let (flat_program, labels) = linker::link(&program.functions, 0x1);

        let ram = program
            .c
            .initial_memory
            .iter()
            .filter_map(|(addr, value)| {
                let value = match value {
                    crate::loader::MemoryEntry::Value(v) => *v,
                    crate::loader::MemoryEntry::FuncAddr(idx) => {
                        let label = func_idx_to_label(*idx);
                        labels[&label].pc
                    }
                    crate::loader::MemoryEntry::FuncFrameSize(func_idx) => {
                        let label = func_idx_to_label(*func_idx);
                        labels[&label].frame_size.unwrap()
                    }
                };

                if value == 0 {
                    None
                } else {
                    Some((*addr, value))
                }
            })
            .collect::<HashMap<_, _>>();

        let mut interpreter = Self {
            pc: 0,
            fp: 0,
            future_counter: 0,
            future_assignments: HashMap::new(),
            // We leave 0 unused for convention = successful termination.
            vrom: vec![VRomValue::Unassigned],
            ram,
            program,
            external_functions,
            flat_program,
            labels,
        };

        if let Some(start_function) = interpreter.program.c.start_function {
            let label = func_idx_to_label(start_function);
            interpreter.run(&label, &[]);
        }

        interpreter
    }

    fn get_mem<'b>(&'b mut self) -> MemoryAccessor<'b, 'a, E> {
        MemoryAccessor::new(self.program.c.memory.unwrap(), self)
    }

    pub fn run(&mut self, func_name: &str, inputs: &[u32]) -> Vec<u32> {
        let func_label = &self.labels[func_name];

        let func_type = &self
            .program
            .c
            .get_func_type(func_label.func_idx.unwrap())
            .ty;
        let n_inputs: u32 = func_type
            .params()
            .iter()
            .map(|ty| word_count_type::<S>(*ty))
            .sum();
        assert_eq!(inputs.len(), n_inputs as usize);

        let n_outputs: u32 = func_type
            .results()
            .iter()
            .map(|ty| word_count_type::<S>(*ty))
            .sum();

        self.pc = func_label.pc;
        self.fp = self.allocate(func_label.frame_size.unwrap());
        let first_fp = self.fp;

        self.set_vrom_relative_u32(0..1, 0); // final return pc
        self.set_vrom_relative_u32(1..2, 0); // return fp success
        self.set_vrom_relative_range(2..2 + inputs.len() as u32, inputs);

        let output_start = 2 + inputs.len() as u32;
        self.set_vrom_relative_range_future(output_start..output_start + n_outputs);

        self.run_loop();

        // We assume that all output futures have been resolved.
        (output_start..output_start + n_outputs)
            .map(|i| self.get_vrom_absolute_u32(first_fp + i))
            .collect::<Vec<u32>>()
    }

    fn run_loop(&mut self) {
        let mut cycles = 0usize;
        let final_fp = loop {
            let instr = self.flat_program[self.pc as usize].clone();
            log::trace!("PC: {}, FP: {}, Instr: {instr}", self.pc, self.fp);

            let mut should_inc_pc = true;

            match instr {
                Directive::Label { .. } => {
                    should_inc_pc = false;
                    // do nothing
                }
                Directive::Return { ret_pc, ret_fp } => {
                    let pc = self.get_vrom_relative_u32(ret_pc..ret_pc + 1);
                    let fp = self.get_vrom_relative_u32(ret_fp..ret_fp + 1);
                    if pc == 0 {
                        break fp;
                    } else {
                        self.pc = pc;
                        self.fp = fp;
                    }
                    should_inc_pc = false;
                }
                Directive::WASMOp {
                    op,
                    mut inputs,
                    output,
                } => match op {
                    Op::Nop => {
                        // No operation, just continue
                    }
                    Op::I32Const { value } => {
                        self.set_vrom_relative_u32(output.unwrap(), value as u32);
                    }
                    Op::F32Const { value } => {
                        self.set_vrom_relative_u32(output.unwrap(), value.bits());
                    }
                    Op::I64Const { value } => {
                        self.set_vrom_relative_u64(output.unwrap(), value as u64);
                    }
                    Op::F64Const { value } => {
                        let value = value.bits();
                        self.set_vrom_relative_u64(output.unwrap(), value);
                    }
                    Op::I32Add => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);
                        let r = a.wrapping_add(b);

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64Add => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);
                        let r = a.wrapping_add(b);

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I32Sub => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);
                        let r = a.wrapping_sub(b);

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64Sub => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);
                        let r = a.wrapping_sub(b);

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I32Mul => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);
                        let r = a.wrapping_mul(b);

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64Mul => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);
                        let r = a.wrapping_mul(b);

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I32DivU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);

                        if b == 0 {
                            panic!("integer divide by zero in I32DivU");
                        }

                        let r = a / b;

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32DivS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a) as i32;
                        let b = self.get_vrom_relative_u32(b) as i32;

                        if b == 0 {
                            panic!("integer divide by zero in I32DivS");
                        }
                        if a == i32::MIN && b == -1 {
                            panic!("integer overflow in I32DivS");
                        }

                        let r = a.wrapping_div(b) as u32;

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64DivU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);

                        if b == 0 {
                            panic!("integer divide by zero in I64DivU");
                        }

                        let r = a / b;

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I64DivS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a) as i64;
                        let b = self.get_vrom_relative_u64(b) as i64;

                        if b == 0 {
                            panic!("integer divide by zero in I64DivS");
                        }
                        if a == i64::MIN && b == -1 {
                            panic!("integer overflow in I64DivS");
                        }

                        let r = a.wrapping_div(b) as u64;

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I32RemU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);

                        if b == 0 {
                            panic!("integer divide by zero in I32RemU");
                        }

                        let r = a % b;

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32RemS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a) as i32;
                        let b = self.get_vrom_relative_u32(b) as i32;

                        if b == 0 {
                            panic!("integer divide by zero in I32RemS");
                        }

                        let r = a.wrapping_rem(b);

                        self.set_vrom_relative_u32(c, r as u32);
                    }
                    Op::I64RemU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);

                        if b == 0 {
                            panic!("integer divide by zero in I64RemU");
                        }

                        let r = a % b;

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I64RemS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a) as i64;
                        let b = self.get_vrom_relative_u64(b) as i64;

                        if b == 0 {
                            panic!("integer divide by zero in I64RemS");
                        }

                        let r = a.wrapping_rem(b);

                        self.set_vrom_relative_u64(c, r as u64);
                    }
                    Op::I32LtU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);

                        let r = if a < b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64LtU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);
                        let r = if a < b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32LtS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a) as i32;
                        let b = self.get_vrom_relative_u32(b) as i32;

                        let r = if a < b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64LtS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a) as i64;
                        let b = self.get_vrom_relative_u64(b) as i64;
                        let r = if a < b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32LeS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a) as i32;
                        let b = self.get_vrom_relative_u32(b) as i32;

                        let r = if a <= b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64LeS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a) as i64;
                        let b = self.get_vrom_relative_u64(b) as i64;
                        let r = if a <= b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32LeU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);

                        let r = if a <= b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64LeU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);
                        let r = if a <= b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32GtU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);
                        let r = if a > b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64GtU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);
                        let r = if a > b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32GtS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a) as i32;
                        let b = self.get_vrom_relative_u32(b) as i32;

                        let r = if a > b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64GtS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a) as i64;
                        let b = self.get_vrom_relative_u64(b) as i64;
                        let r = if a > b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32GeS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a) as i32;
                        let b = self.get_vrom_relative_u32(b) as i32;

                        let r = if a >= b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64GeS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a) as i64;
                        let b = self.get_vrom_relative_u64(b) as i64;
                        let r = if a >= b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32GeU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);

                        let r = if a >= b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64GeU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);
                        let r = if a >= b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32And => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);
                        let r = a & b;

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32Or => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);
                        let r = a | b;

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64And => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);
                        let r = a & b;

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I64Or => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);
                        let r = a | b;

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I64Xor => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);
                        let r = a ^ b;

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I32Xor => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);
                        let r = a ^ b;

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32Shl => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);

                        let r = a.wrapping_shl(b);

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64Shl => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);

                        let r = a.wrapping_shl(b as u32);

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I64Rotl => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b);

                        let r = a.rotate_left(b as u32);

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I32ShrU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b) & 0x1F;

                        let r = a.wrapping_shr(b);

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64ShrU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b) as u32;

                        let r = a.wrapping_shr(b);

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I32ShrS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a) as i32;
                        let b = self.get_vrom_relative_u32(b) & 0x1F;

                        let r = a.wrapping_shr(b);

                        self.set_vrom_relative_u32(c, r as u32);
                    }
                    Op::I64ShrS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a) as i64;
                        let b = self.get_vrom_relative_u64(b) as u32;

                        let r = a.wrapping_shr(b);

                        self.set_vrom_relative_u64(c, r as u64);
                    }
                    Op::I32Rotl => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b) & 0x1F;

                        let r = a.rotate_left(b);

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32Rotr => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b) & 0x1F;

                        let r = a.rotate_right(b);

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64Rotr => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let b = self.get_vrom_relative_u64(b) as u32;

                        let r = a.rotate_right(b);

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I32Clz => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);

                        let r = a.leading_zeros();

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64Clz => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);

                        let r = a.leading_zeros() as u64;

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I32Ctz => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);

                        let r = a.trailing_zeros();

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64Ctz => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);

                        let r = a.trailing_zeros() as u64;

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I32Popcnt => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);

                        let r = a.count_ones();

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I64Popcnt => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);

                        let r = a.count_ones() as u64;

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::I32Extend8S => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);

                        let r = (a as u8) as i8 as i32;

                        self.set_vrom_relative_u32(c, r as u32);
                    }
                    Op::I64Extend8S => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);

                        let r = (a as u8) as i8 as i64;

                        self.set_vrom_relative_u64(c, r as u64);
                    }
                    Op::I32Extend16S => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);

                        let r = (a as u16) as i16 as i32;

                        self.set_vrom_relative_u32(c, r as u32);
                    }
                    Op::I64Extend16S => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);

                        let r = (a as u16) as i16 as i64;

                        self.set_vrom_relative_u64(c, r as u64);
                    }
                    Op::I64Extend32S => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);

                        let r = (a as u32) as i32 as i64;

                        self.set_vrom_relative_u64(c, r as u64);
                    }
                    Op::I64ExtendI32U => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a);

                        self.set_vrom_relative_u64(c, a as u64);
                    }
                    Op::I64ExtendI32S => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u32(a) as i32;

                        self.set_vrom_relative_u64(c, a as u64);
                    }
                    Op::I32Eq | Op::I64Eq => {
                        let a = self
                            .get_vrom_relative_range(inputs[0].clone())
                            .collect_vec();
                        let b = self.get_vrom_relative_range(inputs[1].clone());
                        let c = output.unwrap();

                        let val = if b.eq(a) { 1 } else { 0 };
                        self.set_vrom_relative_u32(c, val);
                    }
                    Op::I32Ne | Op::I64Ne => {
                        let a = self
                            .get_vrom_relative_range(inputs[0].clone())
                            .collect_vec();
                        let b = self.get_vrom_relative_range(inputs[1].clone());
                        let c = output.unwrap();

                        let val = if !b.eq(a) { 1 } else { 0 };
                        self.set_vrom_relative_u32(c, val);
                    }
                    Op::I32Eqz | Op::I64Eqz => {
                        let mut a = self.get_vrom_relative_range(inputs[0].clone());
                        let c = output.unwrap();

                        let val = if a.all(|x| x == 0) { 1 } else { 0 };
                        drop(a);
                        self.set_vrom_relative_u32(c, val);
                    }
                    Op::I32WrapI64 => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);

                        let r = a as u32;

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::F32Add => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(self.get_vrom_relative_u32(a));
                        let b = f32::from_bits(self.get_vrom_relative_u32(b));

                        let r = a + b;
                        let r = r.to_bits();

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::F32Sub => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(self.get_vrom_relative_u32(a));
                        let b = f32::from_bits(self.get_vrom_relative_u32(b));

                        let r = a - b;
                        let r = r.to_bits();

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::F32Div => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(self.get_vrom_relative_u32(a));
                        let b = f32::from_bits(self.get_vrom_relative_u32(b));

                        if b == 0f32 {
                            panic!("integer divide by zero in I32DivU");
                        }

                        let r = a / b;
                        let r = r.to_bits();

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::F32Neg => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(self.get_vrom_relative_u32(a));

                        let r = -a;
                        let r = r.to_bits();

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::F64Neg => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = self.get_vrom_relative_u64(a);
                        let r = -f64::from_bits(a);
                        let r = r.to_bits();

                        self.set_vrom_relative_u64(c, r);
                    }
                    Op::F32Eq => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(self.get_vrom_relative_u32(a));
                        let b = f32::from_bits(self.get_vrom_relative_u32(b));

                        let r = if a == b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::F32Lt => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(self.get_vrom_relative_u32(a));
                        let b = f32::from_bits(self.get_vrom_relative_u32(b));

                        let r = if a < b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::F32Gt => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(self.get_vrom_relative_u32(a));
                        let b = f32::from_bits(self.get_vrom_relative_u32(b));

                        let r = if a > b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::Select => {
                        let condition = self.get_vrom_relative_u32(inputs[2].clone());

                        let selected = inputs[if condition != 0 { 0 } else { 1 }].clone();
                        let value = selected.map(|r| self.get_vrom_relative(r)).collect_vec();

                        let output = output.unwrap();
                        for (output_reg, value) in output.zip_eq(value) {
                            self.set_vrom_relative(output_reg, value);
                        }
                    }
                    Op::GlobalGet { global_index } => {
                        let Global::Mutable(global_info) =
                            self.program.c.globals[global_index as usize]
                        else {
                            panic!("immutable GlobalGet should have been resolved at compile time");
                        };
                        let output = output.unwrap();

                        let size = word_count_type::<S>(global_info.val_type);
                        assert_eq!(size, output.len() as u32);

                        let value = (0..size)
                            .map(|i| self.get_ram(global_info.address + 4 * i))
                            .collect_vec();
                        self.set_vrom_relative_range(output, &value);
                    }
                    Op::GlobalSet { global_index } => {
                        let Global::Mutable(global_info) =
                            self.program.c.globals[global_index as usize]
                        else {
                            panic!("GlobalSet expects a mutable global");
                        };

                        let origin = inputs.pop().unwrap();
                        assert!(
                            inputs.is_empty(),
                            "GlobalSet should have no additional inputs"
                        );

                        let size = word_count_type::<S>(global_info.val_type);
                        assert_eq!(origin.len(), size as usize);

                        let value = self.get_vrom_relative_range(origin).collect_vec();
                        for (i, value) in value.into_iter().enumerate() {
                            self.set_ram(global_info.address + 4 * i as u32, value);
                        }
                    }
                    Op::I32Store8 { memarg }
                    | Op::I32Store16 { memarg }
                    | Op::I64Store8 { memarg }
                    | Op::I64Store16 { memarg }
                    | Op::I64Store32 { memarg }
                    | Op::I32Store { memarg }
                    | Op::F32Store { memarg } => {
                        let (mask, byte_count) = match op {
                            Op::I32Store8 { .. } | Op::I64Store8 { .. } => (0xff, 1),
                            Op::I32Store16 { .. } | Op::I64Store16 { .. } => (0xffff, 2),
                            Op::I32Store { .. } | Op::F32Store { .. } | Op::I64Store32 { .. } => {
                                (0xffffffff, 4)
                            }
                            _ => unreachable!(),
                        };

                        let addr =
                            self.get_vrom_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        // input[1] might have 1 or 2 words, but we only need the first word
                        let val_input = inputs[1].start..(inputs[1].start + 1);
                        let new_value = mask & self.get_vrom_relative_u32(val_input);

                        assert_eq!(memarg.memory, 0);
                        let mut memory = self.get_mem();

                        // First word to be written:
                        let word_addr = addr & !3;
                        let old_value = memory.get_word(word_addr).expect("Out of bounds read");
                        let first_shift = (addr & 3) * 8;
                        let value =
                            (old_value & !(mask << first_shift)) | (new_value << first_shift);
                        memory
                            .set_word(word_addr, value)
                            .expect("Out of bounds write");

                        // If some part of the value is in the next word, we need to write it, too.
                        if first_shift + byte_count * 8 > 32 {
                            let word_addr = word_addr + 4;
                            let old_value = memory.get_word(word_addr).expect("Out of bounds read");
                            let second_shift = 32 - first_shift;
                            let value =
                                (old_value & !(mask >> second_shift)) | (new_value >> second_shift);
                            memory
                                .set_word(word_addr, value)
                                .expect("Out of bounds write");
                        }
                    }
                    Op::I64Store { memarg } | Op::F64Store { memarg } => {
                        let addr =
                            self.get_vrom_relative_u32(inputs[0].clone()) + memarg.offset as u32;
                        let value = self
                            .get_vrom_relative_range(inputs[1].clone())
                            .collect_vec();

                        assert_eq!(memarg.memory, 0);
                        let mut memory = self.get_mem();
                        memory
                            .write_contiguous(addr, &value)
                            .expect("Out of bounds write");
                    }
                    Op::I32Load { memarg }
                    | Op::I64Load { memarg }
                    | Op::F32Load { memarg }
                    | Op::F64Load { memarg } => {
                        let output_reg = output.unwrap();
                        let word_len = output_reg.len() as u32;

                        assert_eq!(inputs.len(), 1);
                        let addr =
                            self.get_vrom_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = self.get_mem();
                        let value = memory
                            .read_contiguous_bytes(addr, word_len * 4)
                            .expect("Out of bounds read");

                        self.set_vrom_relative_range(output_reg, &value);
                    }
                    Op::I32Load8U { memarg } | Op::I64Load8U { memarg } => {
                        let output_reg = output.unwrap();
                        let word_len = output_reg.len() as u32;

                        assert_eq!(inputs.len(), 1);
                        let addr =
                            self.get_vrom_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = self.get_mem();

                        let byte = memory
                            .read_contiguous_bytes(addr, 1)
                            .expect("Out of bounds read")[0]
                            & 0xff;

                        let value = [byte, 0];
                        self.set_vrom_relative_range(output_reg, &value[0..word_len as usize]);
                    }
                    Op::I32Load8S { memarg } | Op::I64Load8S { memarg } => {
                        let output_reg = output.unwrap();
                        let word_len = output_reg.len() as u32;

                        assert_eq!(inputs.len(), 1);
                        let addr =
                            self.get_vrom_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = self.get_mem();

                        let byte = memory
                            .read_contiguous_bytes(addr, 1)
                            .expect("Out of bounds read")[0];

                        let signed = byte as i8 as i64;

                        let value = [signed as u32, (signed >> 32) as u32];
                        self.set_vrom_relative_range(output_reg, &value[0..word_len as usize]);
                    }
                    Op::I32Load16U { memarg } | Op::I64Load16U { memarg } => {
                        let output_reg = output.unwrap();
                        let word_len = output_reg.len() as u32;

                        assert_eq!(inputs.len(), 1);
                        let addr =
                            self.get_vrom_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = self.get_mem();

                        let bytes = memory
                            .read_contiguous_bytes(addr, 2)
                            .expect("Out of bounds read")[0]
                            & 0xffff;

                        let value = [bytes, 0];
                        self.set_vrom_relative_range(output_reg, &value[0..word_len as usize]);
                    }
                    Op::I32Load16S { memarg } | Op::I64Load16S { memarg } => {
                        let output_reg = output.unwrap();
                        let word_len = output_reg.len() as u32;

                        assert_eq!(inputs.len(), 1);
                        let addr =
                            self.get_vrom_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = self.get_mem();

                        let value = memory
                            .read_contiguous_bytes(addr, 2)
                            .expect("Out of bounds read")[0];

                        let signed = value as i16 as i64;

                        let value = [signed as u32, (signed >> 32) as u32];
                        self.set_vrom_relative_range(output_reg, &value[0..word_len as usize]);
                    }
                    Op::I64Load32U { memarg } => {
                        let output_reg = output.unwrap();

                        assert_eq!(inputs.len(), 1);
                        let addr =
                            self.get_vrom_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = self.get_mem();

                        let word = memory
                            .read_contiguous_bytes(addr, 4)
                            .expect("Out of bounds read")[0];

                        self.set_vrom_relative_range(output_reg, &[word, 0]);
                    }
                    Op::I64Load32S { memarg } => {
                        let output_reg = output.unwrap();

                        assert_eq!(inputs.len(), 1);
                        let addr =
                            self.get_vrom_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = self.get_mem();

                        let word = memory
                            .read_contiguous_bytes(addr, 4)
                            .expect("Out of bounds read")[0];

                        let signed = word as i32 as i64;
                        let value = [signed as u32, (signed >> 32) as u32];
                        self.set_vrom_relative_range(output_reg, &value);
                    }
                    Op::MemoryGrow { mem } => {
                        let extra_pages = self.get_vrom_relative_u32(inputs[0].clone());

                        assert_eq!(mem, 0, "Only memory 0 is supported in this interpreter");
                        let mut memory = self.get_mem();

                        let old_num_pages = memory.get_size() / WASM_PAGE_SIZE;
                        let new_num_pages = old_num_pages + extra_pages;

                        let result = if new_num_pages > memory.get_max_num_pages() {
                            0xFFFFFFFF // WASM spec says to return -1 on failure
                        } else {
                            memory.set_num_pages(new_num_pages);
                            old_num_pages
                        };

                        self.set_vrom_relative_u32(output.unwrap(), result);
                    }
                    Op::MemoryCopy { dst_mem, src_mem } => {
                        assert_eq!(dst_mem, 0);
                        assert_eq!(src_mem, 0);

                        let dst = self.get_vrom_relative_u32(inputs[0].clone());
                        let src = self.get_vrom_relative_u32(inputs[1].clone());
                        let size = self.get_vrom_relative_u32(inputs[2].clone());
                        let mut remaining = size % 4;

                        let mut memory = self.get_mem();
                        // Load the entire thing into memory, this is the easiest way to
                        // handle overlapping copies.
                        let mut data = memory
                            .read_contiguous_bytes(src, size)
                            .expect("Out of bounds read");
                        if remaining > 0 {
                            let last_word = data.pop().unwrap();
                            // Zero the bytes that were not to be copied.
                            let mut mask = !(!0 << (remaining * 8));
                            let mut last_word = last_word & mask;

                            // We now need to write the remaining bytes in either 1 or 2
                            // words, depending on the alignment of the destination.
                            let dst_byte_addr = dst + size - remaining - 1;
                            let mut dst_word_addr = dst_byte_addr & !0x3; // align to 4 bytes
                            // Does it fit completely in the last word?
                            let mut space_in_word = 4 - (dst_byte_addr % 4);
                            if space_in_word < remaining {
                                // Doesn't fit, write the second to last word.
                                remaining -= space_in_word;
                                let rshift = remaining * 8;
                                let old_value =
                                    memory.get_word(dst_word_addr).expect("Out of bounds read");
                                let new_value =
                                    (old_value & !(mask >> rshift)) | (last_word >> rshift);
                                memory
                                    .set_word(dst_word_addr, new_value)
                                    .expect("Out of bounds write");

                                mask >>= space_in_word * 8;
                                last_word &= mask;
                                dst_word_addr += 4;
                                space_in_word = 4;
                            }

                            // Write the last word.
                            let lshift = (space_in_word - remaining) * 8;
                            let old_value =
                                memory.get_word(dst_word_addr).expect("Out of bounds read");
                            let new_value = (old_value & !(mask << lshift)) | (last_word << lshift);
                            memory
                                .set_word(dst_word_addr, new_value)
                                .expect("Out of bounds write");
                        }
                        memory
                            .write_contiguous(dst, &data)
                            .expect("Out of bounds write");
                    }
                    Op::TableGet { table } => {
                        assert_eq!(inputs[0].len(), 1);
                        let index = self.get_vrom_relative_u32(inputs[0].clone());

                        let table = TableAccessor::new(self.program.c.tables[table as usize], self);
                        let entry = table
                            .get_entry(index)
                            .expect("TableGet: index out of bounds");

                        let output_reg = output.unwrap();
                        self.set_vrom_relative_range(output_reg, &entry);
                    }
                    _ => todo!("Unsupported WASM operator: {op:?}"),
                },
                Directive::AllocateFrameI {
                    target_frame,
                    result_ptr,
                } => {
                    let frame_size = self.labels[&target_frame].frame_size.unwrap();
                    let ptr = self.allocate(frame_size);
                    self.set_vrom_relative_u32(result_ptr..result_ptr + 1, ptr);
                }
                Directive::AllocateFrameV {
                    frame_size,
                    result_ptr,
                } => {
                    let frame_size = self.get_vrom_relative_u32(frame_size..frame_size + 1);
                    let ptr = self.allocate(frame_size);
                    self.set_vrom_relative_u32(result_ptr..result_ptr + 1, ptr);
                }
                Directive::Copy {
                    src_word,
                    dest_word,
                } => {
                    let value = self.get_vrom_relative(src_word);
                    self.set_vrom_relative(dest_word, value);
                }
                Directive::CopyIntoFrame {
                    src_word,
                    dest_frame,
                    dest_word,
                } => {
                    let value = self.get_vrom_relative(src_word);
                    let target_ptr =
                        self.get_vrom_relative_u32(dest_frame..dest_frame + 1) + dest_word;
                    self.set_vrom_absolute(target_ptr, value);
                }
                Directive::Call {
                    target,
                    new_frame_ptr,
                    saved_ret_pc,
                    saved_caller_fp,
                } => {
                    let prev_pc = self.pc;
                    self.pc = self.labels[&target].pc;
                    should_inc_pc = false;

                    let prev_fp = self.fp;
                    self.fp = self.get_vrom_relative_u32(new_frame_ptr..new_frame_ptr + 1);

                    self.set_vrom_relative_u32(saved_ret_pc..saved_ret_pc + 1, prev_pc + 1);
                    self.set_vrom_relative_u32(saved_caller_fp..saved_caller_fp + 1, prev_fp);
                }
                Directive::CallIndirect {
                    target_pc,
                    new_frame_ptr,
                    saved_ret_pc,
                    saved_caller_fp,
                } => {
                    let prev_pc = self.pc;
                    self.pc = self.get_vrom_relative_u32(target_pc..target_pc + 1);
                    should_inc_pc = false;

                    let prev_fp = self.fp;
                    self.fp = self.get_vrom_relative_u32(new_frame_ptr..new_frame_ptr + 1);

                    self.set_vrom_relative_u32(saved_ret_pc..saved_ret_pc + 1, prev_pc + 1);
                    self.set_vrom_relative_u32(saved_caller_fp..saved_caller_fp + 1, prev_fp);
                }
                Directive::ImportedCall {
                    module,
                    function,
                    inputs,
                    outputs,
                } => {
                    let args = inputs
                        .into_iter()
                        .flatten()
                        .map(|addr| self.get_vrom_relative_u32(addr..addr + 1))
                        .collect_vec();
                    let result = self.external_functions.call(module, function, &args);
                    for (value, output) in result.into_iter().zip_eq(outputs.into_iter().flatten())
                    {
                        self.set_vrom_relative_u32(output..output + 1, value);
                    }
                }
                Directive::JumpAndActivateFrame {
                    target,
                    new_frame_ptr,
                    saved_caller_fp,
                } => {
                    self.pc = self.labels[&target].pc;
                    should_inc_pc = false;

                    let prev_fp = self.fp;
                    self.fp = self.get_vrom_relative_u32(new_frame_ptr..new_frame_ptr + 1);

                    if let Some(saved_caller_fp) = saved_caller_fp {
                        self.set_vrom_relative_u32(saved_caller_fp..saved_caller_fp + 1, prev_fp);
                    }
                }
                Directive::JumpIf { target, condition } => {
                    let target = self.labels[&target].pc;
                    let cond = self.get_vrom_relative_u32(condition..condition + 1);
                    if cond != 0 {
                        self.pc = target;
                        should_inc_pc = false;
                    }
                }
                Directive::Jump { target } => {
                    self.pc = self.labels[&target].pc;
                    should_inc_pc = false;
                }
                Directive::JumpOffset { offset } => {
                    let offset = self.get_vrom_relative_u32(offset..offset + 1);
                    // Offset starts with 0, so we don't prevent the natural increment of the PC.
                    self.pc += offset;
                }
                Directive::Trap { reason } => {
                    panic!("Trap encountered: {reason:?}");
                }
            }

            if should_inc_pc {
                self.pc += 1;
            }

            cycles += 1;
        };

        if final_fp == 0 {
            log::info!("Program terminated successfully with cycles: {cycles}.");
        } else {
            log::info!("Program terminated with cycles: {cycles}, final frame pointer: {final_fp}");
        }
    }

    fn get_ram(&self, byte_addr: u32) -> u32 {
        *self.ram.get(&byte_addr).unwrap_or(&0)
    }

    fn set_ram(&mut self, byte_addr: u32, value: u32) {
        if value == 0 {
            self.ram.remove(&byte_addr);
        } else {
            self.ram.insert(byte_addr, value);
        }
    }

    fn get_vrom_absolute_u32(&mut self, addr: u32) -> u32 {
        let value = &mut self.get_vrom_absolute(addr);
        match *value {
            VRomValue::Concrete(v) => v,
            VRomValue::Future(future) => {
                // Resolve the future if it has been assigned.
                if let Some(resolved_value) = self.future_assignments.get(&future) {
                    *value = VRomValue::Concrete(*resolved_value);
                    *resolved_value
                } else {
                    panic!(
                        "Can not convert future {future} to u32. It has not been assigned a value yet."
                    );
                }
            }
            VRomValue::Unassigned => {
                panic!("Can not convert unassigned to u32");
            }
        }
    }

    fn get_vrom_relative_u32(&mut self, addr: Range<u32>) -> u32 {
        assert_eq!(addr.len(), 1, "Expected a single address range");
        self.get_vrom_absolute_u32(self.fp + addr.start)
    }

    fn get_vrom_relative_u64(&mut self, addr: Range<u32>) -> u64 {
        assert_eq!(addr.len(), 2, "Expected a single address range");
        let low = self.get_vrom_absolute_u32(self.fp + addr.start);
        let high = self.get_vrom_absolute_u32(self.fp + addr.start + 1);
        (low as u64) | ((high as u64) << 32)
    }

    fn get_vrom_relative_range(&mut self, addr: Range<u32>) -> impl Iterator<Item = u32> {
        addr.map(|i| self.get_vrom_absolute_u32(self.fp + i))
    }

    fn get_vrom_relative(&mut self, addr: u32) -> VRomValue {
        self.get_vrom_absolute(self.fp + addr)
    }

    fn get_vrom_absolute(&mut self, addr: u32) -> VRomValue {
        let value = self.vrom[addr as usize];
        let value = match value {
            VRomValue::Concrete(_) => value,
            VRomValue::Future(future) => {
                // Resolve the future if it has been assigned.
                if let Some(resolved_value) = self.future_assignments.get(&future) {
                    let value = VRomValue::Concrete(*resolved_value);
                    self.vrom[addr as usize] = value;
                    value
                } else {
                    value
                }
            }
            VRomValue::Unassigned => {
                // The only reason to read an unassigned value is to assign it later,
                // so it must become a Future.
                let value = VRomValue::Future(self.new_future());
                self.vrom[addr as usize] = value;
                value
            }
        };

        log::trace!("Reading VRom address {addr}: {value:?}");
        value
    }

    fn set_vrom_relative(&mut self, addr: u32, value: VRomValue) {
        self.set_vrom_absolute(self.fp + addr, value);
    }

    fn set_vrom_absolute(&mut self, addr: u32, value: VRomValue) {
        let slot = &mut self.vrom[addr as usize];
        log::trace!("Setting VRom address {addr}: {value:?}");
        match (*slot, value) {
            (VRomValue::Unassigned, VRomValue::Unassigned) => {
                // This is important to catch to prevent bugs.
                panic!("Attempted to assign an unassigned value to VRom");
            }
            (VRomValue::Unassigned, _) => {
                *slot = value;
            }
            (VRomValue::Future(future), VRomValue::Concrete(value)) => {
                // Assigning Concrete values to Futures materializes it.
                if let Some(old_value) = self.future_assignments.insert(future, value) {
                    assert_eq!(old_value, value, "Attempted to overwrite a value in VRom")
                }
                log::debug!("Future {future} materialized to value {value}");
            }
            (_, _) => {
                assert_eq!(*slot, value, "Attempted to overwrite a value in VRom");
            }
        }
    }

    fn set_vrom_relative_u32(&mut self, addr: Range<u32>, value: u32) {
        assert_eq!(addr.len(), 1, "Expected a single address range");
        self.set_vrom_relative(addr.start, value.into());
    }

    fn set_vrom_relative_u64(&mut self, addr: Range<u32>, value: u64) {
        self.set_vrom_relative_range(addr, &[value as u32, (value >> 32) as u32]);
    }

    fn set_vrom_relative_range(&mut self, addr: Range<u32>, values: &[u32]) {
        assert_eq!(
            addr.len(),
            values.len(),
            "Address range and values length mismatch"
        );
        for (addr, &value) in addr.zip(values.iter()) {
            self.set_vrom_relative(addr, value.into());
        }
    }

    fn set_vrom_relative_range_future(&mut self, addr: Range<u32>) {
        for i in addr {
            let future = self.new_future();
            self.set_vrom_relative(i, VRomValue::Future(future));
        }
    }

    fn allocate(&mut self, size: u32) -> u32 {
        let addr = self.vrom.len();
        self.vrom
            .resize_with(addr + size as usize, || VRomValue::Unassigned);
        addr as u32
    }

    fn new_future(&mut self) -> u32 {
        let future = self.future_counter;
        self.future_counter += 1;
        future
    }
}

struct MemoryAccessor<'a, 'b, E: ExternalFunctions> {
    segment: Segment,
    interpreter: &'a mut Interpreter<'b, E>,
    byte_size: u32,
}

impl<'a, 'b, E: ExternalFunctions> MemoryAccessor<'a, 'b, E> {
    fn new(segment: Segment, interpreter: &'a mut Interpreter<'b, E>) -> Self {
        let byte_size = interpreter.get_ram(segment.start) * WASM_PAGE_SIZE;
        MemoryAccessor {
            segment,
            interpreter,
            byte_size,
        }
    }

    fn get_max_num_pages(&self) -> u32 {
        self.interpreter.get_ram(self.segment.start + 4)
    }

    fn set_num_pages(&mut self, num_pages: u32) {
        self.interpreter.set_ram(self.segment.start, num_pages);
        self.byte_size = num_pages * WASM_PAGE_SIZE;
    }

    fn get_size(&self) -> u32 {
        self.byte_size
    }

    fn get_word(&self, byte_addr: u32) -> Result<u32, ()> {
        assert_eq!(byte_addr % 4, 0, "Address must be word-aligned");
        if byte_addr >= self.get_size() {
            return Err(());
        }
        let ram_addr = self.segment.start + 8 + byte_addr;
        let value = self.interpreter.get_ram(ram_addr);
        log::trace!("Reading Memory word at {ram_addr}: {value}");
        Ok(value)
    }

    fn set_word(&mut self, byte_addr: u32, value: u32) -> Result<(), ()> {
        assert_eq!(byte_addr % 4, 0, "Address must be word-aligned");
        if byte_addr >= self.get_size() {
            return Err(());
        }
        let ram_addr = self.segment.start + 8 + byte_addr;
        self.interpreter.set_ram(ram_addr, value);
        log::trace!("Writing Memory word at {ram_addr}: {value}");
        Ok(())
    }

    fn write_contiguous(&mut self, byte_addr: u32, data: &[u32]) -> Result<(), ()> {
        if byte_addr % 4 == 0 {
            // Simple aligned writes
            for (i, &value) in data.iter().enumerate() {
                let addr = byte_addr + (i as u32 * 4);
                self.set_word(addr, value)?;
            }
        } else if !data.is_empty() {
            // Unaligned writes
            let offset_bytes = (byte_addr % 4) as usize;
            let shift = (offset_bytes * 8) as u32;
            let high_shift = 32u32 - shift;

            let first_word_addr = byte_addr & !3;

            // Handle first partial word
            let old_first_word = self.get_word(first_word_addr)?;
            let first_keep_mask = (1u32 << shift) - 1;
            let mut carry_over = data[0] >> high_shift; // Bytes to write into next word
            let new_first_word = (old_first_word & first_keep_mask) | (data[0] << shift);
            self.set_word(first_word_addr, new_first_word)?;

            // Handle full middle words
            for (i, d) in data.iter().enumerate().skip(1) {
                let current_addr = first_word_addr + (i as u32 * 4);

                let combined = carry_over | (d << shift);
                self.set_word(current_addr, combined)?;
                carry_over = d >> high_shift;
            }

            // Final partial word (or single-word case)
            let final_addr = first_word_addr + ((data.len() as u32) * 4);
            let old_final_word = self.get_word(final_addr)?;
            let final_keep_mask = 0xFFFFFFFFu32 << (offset_bytes * 8);
            let new_final_word =
                (old_final_word & final_keep_mask) | (carry_over & !final_keep_mask);
            self.set_word(final_addr, new_final_word)?;
        }
        Ok(())
    }

    /// Reads a contiguous block of memory starting at `byte_addr` for `num_bytes`.
    ///
    /// The high bytes of the last returned word can be anything if `num_bytes` is
    /// not a multiple of 4.
    fn read_contiguous_bytes(&self, byte_addr: u32, num_bytes: u32) -> Result<Vec<u32>, ()> {
        let num_words = (num_bytes + 3) / 4;
        let mut data = Vec::with_capacity(num_words as usize);
        let offset_bytes = byte_addr % 4;
        if offset_bytes == 0 {
            // Simple aligned reads
            for i in 0..num_words {
                let addr = byte_addr + (i * 4);
                data.push(self.get_word(addr)?);
            }
        } else if num_words > 0 {
            // Unaligned reads
            let shift = offset_bytes * 8;
            let high_shift = 32 - shift;

            let first_word_addr = byte_addr & !3;

            // Read first partial word
            let first_word = self.get_word(first_word_addr)?;
            let mut lower_bits = first_word >> shift;

            // Before doing the general case loop, we need to decide if
            // the lower bits of the last word are sufficient to complete
            // the number of bytes requested.
            let num_bytes_last_word = (num_bytes - 1) % 4 + 1; // From 1 to 4 bytes needed in the last word
            let num_bytes_carried_over = 4 - offset_bytes;
            let extra_reading_iter = if num_bytes_carried_over >= num_bytes_last_word {
                // The final read is not needed to form the last word.
                0
            } else {
                // We need to read one more word to get the remaining bytes
                1
            };

            // Do all the full words
            for i in 1..(num_words + extra_reading_iter) {
                let current_addr = first_word_addr + (i * 4);
                let word = self.get_word(current_addr)?;
                data.push(lower_bits | (word << high_shift));
                lower_bits = word >> shift;
            }

            // Handle the last word, if we skipped the last read
            if extra_reading_iter == 0 {
                data.push(lower_bits);
            }
        }
        Ok(data)
    }
}

struct TableAccessor<'a, 'b, E: ExternalFunctions> {
    segment: Segment,
    interpreter: &'a mut Interpreter<'b, E>,
    size: u32,
}

impl<'a, 'b, E: ExternalFunctions> TableAccessor<'a, 'b, E> {
    fn new(segment: Segment, interpreter: &'a mut Interpreter<'b, E>) -> Self {
        let size = interpreter.get_ram(segment.start);
        TableAccessor {
            segment,
            interpreter,
            size,
        }
    }

    /// Returns the size of the table in number of elements.
    fn _get_size(&self) -> u32 {
        self.size
    }

    fn _get_max_size(&self) -> u32 {
        self.interpreter.get_ram(self.segment.start + 4)
    }

    fn get_entry(&self, index: u32) -> Result<[u32; 3], ()> {
        if index >= self.size {
            return Err(());
        }
        let base_addr = self.segment.start + 8 + index * 12; // Each entry is 3 u32s (12 bytes)
        let type_idx = self.interpreter.get_ram(base_addr);
        let frame_size = self.interpreter.get_ram(base_addr + 4);
        let pc = self.interpreter.get_ram(base_addr + 8);
        Ok([type_idx, frame_size, pc])
    }
}
