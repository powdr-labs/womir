use std::collections::HashMap;

use itertools::Itertools;
use wasmparser::Operator as Op;

use crate::linker;
use crate::loader::flattening::Directive;
use crate::loader::{Program, func_idx_to_label, word_count_type};

#[derive(Debug, Clone, Copy)]
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

impl VRomValue {
    pub fn as_u32(&self) -> u32 {
        match self {
            VRomValue::Unassigned => panic!("Cannot convert unassigned to u32"),
            VRomValue::Future(_) => panic!("Cannot convert future to u32"),
            VRomValue::Concrete(value) => *value,
        }
    }
}

pub struct Interpreter<'a, E: ExternalFunctions> {
    // TODO: maybe these 3 initial fields should be unique per `run()` call?
    pc: u32,
    fp: u32,
    future_counter: u32,
    vrom: Vec<VRomValue>,
    ram: HashMap<u32, u32>,
    program: Program<'a>,
    external_functions: E,
    flat_program: Vec<Directive<'a>>,
    labels: HashMap<String, linker::LabelValue>,
}

pub trait ExternalFunctions {
    fn call(&mut self, module: &str, func: &str, args: &[u32]) -> Vec<u32>;
}

impl<'a, E: ExternalFunctions> Interpreter<'a, E> {
    pub fn new(program: Program<'a>, external_functions: E) -> Self {
        let (flat_program, labels) = linker::link(&program.functions, 0x1);

        let ram = program
            .initial_memory
            .iter()
            .filter_map(|(addr, value)| {
                let value = match value {
                    crate::loader::MemoryEntry::Value(v) => *v,
                    crate::loader::MemoryEntry::FuncAddr(idx) => {
                        let label = func_idx_to_label(*idx);
                        labels[&label].func_idx.unwrap()
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
            .collect();

        let mut interpreter = Self {
            pc: 0,
            fp: 0,
            future_counter: 0,
            // We leave 0 unused for convention = successful termination.
            vrom: vec![VRomValue::Unassigned],
            ram,
            program,
            external_functions,
            flat_program,
            labels,
        };

        if let Some(start_function) = interpreter.program.start_function {
            let label = func_idx_to_label(start_function);
            interpreter.run(&label, &[]);
        }

        interpreter
    }

    pub fn run(&mut self, func_name: &str, inputs: &[u32]) -> Vec<u32> {
        let func_label = &self.labels[func_name];

        let func_type = self.program.get_func_type(func_label.func_idx.unwrap());
        let n_inputs: u32 = func_type
            .params()
            .iter()
            .map(|ty| word_count_type(*ty, 4))
            .sum();
        assert_eq!(inputs.len(), n_inputs as usize);

        let n_outputs = func_type
            .results()
            .iter()
            .map(|ty| word_count_type(*ty, 4))
            .sum();

        self.pc = func_label.pc;
        self.fp = self.allocate(func_label.frame_size.unwrap());
        let first_fp = self.fp;

        self.set_vrom_relative_u32(0, 0); // final return pc
        self.set_vrom_relative_u32(1, 0); // return fp success
        self.set_vrom_relative_range(2, inputs);

        let output_start = 2 + inputs.len() as u32;
        self.set_vrom_relative_range_future(output_start, n_outputs);

        self.run_loop();

        // We assume that all output futures have been resolved.
        (output_start..output_start + n_outputs)
            .map(|i| self.get_vrom_absolute(first_fp + i).as_u32())
            .collect::<Vec<u32>>()
    }

    fn run_loop(&mut self) {
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
                    let pc = self.get_vrom_relative(ret_pc).as_u32();
                    let fp = self.get_vrom_relative(ret_fp).as_u32();
                    if pc == 0 {
                        break fp;
                    } else {
                        self.pc = pc;
                        self.fp = fp;
                    }
                }
                Directive::WASMOp {
                    op,
                    mut inputs,
                    output,
                } => match op {
                    Op::I32Const { value } => {
                        let output_reg = output.clone().unwrap().next().unwrap();
                        self.set_vrom_relative_u32(output_reg, value as u32);
                    }
                    Op::I32Add => {
                        let a = inputs[0].start;
                        let b = inputs[1].start;
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative(a).as_u32();
                        let b = self.get_vrom_relative(b).as_u32();
                        let r = a.wrapping_add(b);

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32Sub => {
                        let a = inputs[0].start;
                        let b = inputs[1].start;
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative(a).as_u32();
                        let b = self.get_vrom_relative(b).as_u32();
                        let r = a.wrapping_sub(b);

                        self.set_vrom_relative_u32(c, r);
                    }

                    Op::I32Mul => {
                        let a = inputs[0].start;
                        let b = inputs[1].start;
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative(a).as_u32();
                        let b = self.get_vrom_relative(b).as_u32();
                        let r = a.wrapping_mul(b);

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32GtU => {
                        let a = inputs[0].start;
                        let b = inputs[1].start;
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative(a).as_u32();
                        let b = self.get_vrom_relative(b).as_u32();
                        let r = if a > b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32And => {
                        let a = inputs[0].start;
                        let b = inputs[1].start;
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative(a).as_u32();
                        let b = self.get_vrom_relative(b).as_u32();
                        let r = a & b;

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32ShrU => {
                        let a = inputs[0].start;
                        let b = inputs[1].start;
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative(a).as_u32();
                        let b = self.get_vrom_relative(b).as_u32();
                        let r = a >> b;

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::GlobalGet { global_index } => {
                        let global_info = self.program.globals[global_index as usize];
                        let output = output.unwrap();

                        let size = word_count_type(global_info.val_type, 4);
                        assert_eq!(size, output.len() as u32);

                        for (i, output_reg) in output.enumerate() {
                            let value = self.get_ram(global_info.address + 4 * i as u32);
                            self.set_vrom_relative_u32(output_reg, value);
                        }
                    }
                    Op::GlobalSet { global_index } => {
                        let global_info = self.program.globals[global_index as usize];

                        let origin = inputs.pop().unwrap();
                        assert!(
                            inputs.is_empty(),
                            "GlobalSet should have no additional inputs"
                        );

                        let size = word_count_type(global_info.val_type, 4);
                        assert_eq!(origin.len(), size as usize);

                        for (i, origin) in origin.enumerate() {
                            let value = self.get_vrom_relative(origin).as_u32();
                            self.set_ram(global_info.address + 4 * i as u32, value);
                        }
                    }
                    _ => todo!("Unsupported WASM operator: {op:?}"),
                },
                Directive::AllocateFrameI {
                    target_frame,
                    result_ptr,
                } => {
                    let frame_size = self.labels[&target_frame].frame_size.unwrap();
                    let ptr = self.allocate(frame_size);
                    self.set_vrom_relative_u32(result_ptr, ptr);
                }
                Directive::CopyIntoFrame {
                    src_word,
                    dest_frame,
                    dest_word,
                } => {
                    let value = self.get_vrom_relative(src_word);
                    let target_ptr = self.get_vrom_relative(dest_frame).as_u32() + dest_word;
                    self.set_vrom_absolute(target_ptr, value);
                }
                Directive::JumpAndActivateFrame {
                    target,
                    new_frame_ptr,
                    saved_caller_fp,
                } => {
                    self.pc = self.labels[&target].pc;
                    should_inc_pc = false;

                    let prev_fp = self.fp;
                    self.fp = self.get_vrom_relative(new_frame_ptr).as_u32();

                    if let Some(saved_caller_fp) = saved_caller_fp {
                        self.set_vrom_relative_u32(saved_caller_fp, prev_fp);
                    }
                }
                Directive::JumpIf { target, condition } => {
                    let target = self.labels[&target].pc;
                    let cond = self.get_vrom_relative(condition).as_u32();
                    if cond != 0 {
                        self.pc = target;
                        should_inc_pc = false;
                    }
                }
                Directive::Jump { target } => {
                    self.pc = self.labels[&target].pc;
                    should_inc_pc = false;
                }
                _ => todo!(),
            }

            if should_inc_pc {
                self.pc += 1;
            }
        };

        if final_fp == 0 {
            log::trace!("Program terminated successfully.");
        } else {
            log::trace!("Program terminated with final frame pointer: {final_fp}");
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

    fn get_vrom_relative(&self, addr: u32) -> VRomValue {
        self.vrom[(self.fp + addr) as usize]
    }

    fn get_vrom_absolute(&self, addr: u32) -> VRomValue {
        self.vrom[addr as usize]
    }

    fn set_vrom_relative(&mut self, addr: u32, value: VRomValue) {
        self.vrom[(self.fp + addr) as usize] = value;
    }

    fn set_vrom_absolute(&mut self, addr: u32, value: VRomValue) {
        self.vrom[addr as usize] = value;
    }

    fn set_vrom_relative_u32(&mut self, addr: u32, value: u32) {
        self.vrom[(self.fp + addr) as usize] = value.into();
    }

    fn set_vrom_relative_range(&mut self, addr: u32, values: &[u32]) {
        for (i, &value) in values.iter().enumerate() {
            self.vrom[(self.fp + addr + i as u32) as usize] = value.into();
        }
    }

    fn set_vrom_relative_range_future(&mut self, addr: u32, amount: u32) {
        for i in addr..addr + amount {
            let future = self.new_future();
            self.vrom[(self.fp + i) as usize] = VRomValue::Future(future);
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
