use core::panic;
use std::collections::HashMap;

use wasmparser::Operator as Op;

use crate::linker;
use crate::loader::flattening::Directive;
use crate::loader::{Program, Segment, func_idx_to_label, word_count_type};

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
            future_assignments: HashMap::new(),
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
            .map(|i| self.get_vrom_absolute_u32(first_fp + i))
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
                    let pc = self.get_vrom_relative_u32(ret_pc);
                    let fp = self.get_vrom_relative_u32(ret_fp);
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

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);
                        let r = a.wrapping_add(b);

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32Sub => {
                        let a = inputs[0].start;
                        let b = inputs[1].start;
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);
                        let r = a.wrapping_sub(b);

                        self.set_vrom_relative_u32(c, r);
                    }

                    Op::I32Mul => {
                        let a = inputs[0].start;
                        let b = inputs[1].start;
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);
                        let r = a.wrapping_mul(b);

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32GtU => {
                        let a = inputs[0].start;
                        let b = inputs[1].start;
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);
                        let r = if a > b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32And => {
                        let a = inputs[0].start;
                        let b = inputs[1].start;
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);
                        let r = a & b;

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32ShrU => {
                        let a = inputs[0].start;
                        let b = inputs[1].start;
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative_u32(a);
                        let b = self.get_vrom_relative_u32(b);
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
                            let value = self.get_vrom_relative_u32(origin);
                            self.set_ram(global_info.address + 4 * i as u32, value);
                        }
                    }
                    Op::I32Store { memarg } => {
                        let addr = self.get_vrom_relative_u32(inputs[0].start);
                        let value = self.get_vrom_relative_u32(inputs[1].start);

                        assert_eq!(memarg.memory, 0);
                        let mut memory = MemoryAccessor::new(self.program.memory.unwrap(), self);
                        memory
                            .write_contiguous(addr, &[value])
                            .expect("Out of bounds write");
                    }
                    Op::I64Store { memarg } => {
                        let addr = self.get_vrom_relative_u32(inputs[0].start);
                        let value = self.get_vrom_relative_u32(inputs[1].start);

                        assert_eq!(memarg.memory, 0);
                        let mut memory = MemoryAccessor::new(self.program.memory.unwrap(), self);
                        memory
                            .write_contiguous(addr, &[value])
                            .expect("Out of bounds write");
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
                    let target_ptr = self.get_vrom_relative_u32(dest_frame) + dest_word;
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
                    self.fp = self.get_vrom_relative_u32(new_frame_ptr);

                    self.set_vrom_relative_u32(saved_ret_pc, prev_pc + 1);
                    self.set_vrom_relative_u32(saved_caller_fp, prev_fp);
                }
                Directive::JumpAndActivateFrame {
                    target,
                    new_frame_ptr,
                    saved_caller_fp,
                } => {
                    self.pc = self.labels[&target].pc;
                    should_inc_pc = false;

                    let prev_fp = self.fp;
                    self.fp = self.get_vrom_relative_u32(new_frame_ptr);

                    if let Some(saved_caller_fp) = saved_caller_fp {
                        self.set_vrom_relative_u32(saved_caller_fp, prev_fp);
                    }
                }
                Directive::JumpIf { target, condition } => {
                    let target = self.labels[&target].pc;
                    let cond = self.get_vrom_relative_u32(condition);
                    if cond != 0 {
                        self.pc = target;
                        should_inc_pc = false;
                    }
                }
                Directive::Jump { target } => {
                    self.pc = self.labels[&target].pc;
                    should_inc_pc = false;
                }
                _ => todo!("Unsupported directive: {instr:?}"),
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

    fn get_vrom_relative_u32(&mut self, addr: u32) -> u32 {
        self.get_vrom_absolute_u32(self.fp + addr)
    }

    fn get_vrom_relative(&self, addr: u32) -> VRomValue {
        self.vrom[(self.fp + addr) as usize]
    }

    fn get_vrom_absolute(&self, addr: u32) -> VRomValue {
        self.vrom[addr as usize]
    }

    fn set_vrom_relative(&mut self, addr: u32, value: VRomValue) {
        self.set_vrom_absolute(self.fp + addr, value);
    }

    fn set_vrom_absolute(&mut self, addr: u32, value: VRomValue) {
        let slot = &mut self.vrom[addr as usize];
        match (*slot, value) {
            (VRomValue::Unassigned, _) => {
                *slot = value;
            }
            (VRomValue::Future(future), VRomValue::Concrete(value)) => {
                // Assigning Concrete values to Futures materializes it.
                self.future_assignments
                    .insert(future, value)
                    .map(|old_value| {
                        assert_eq!(old_value, value, "Attempted to overwrite a value in VRom");
                    });
                log::debug!("Future {future} materialized to value {value}");
            }
            (_, _) => {
                assert_eq!(*slot, value, "Attempted to overwrite a value in VRom");
            }
        }
    }

    fn set_vrom_relative_u32(&mut self, addr: u32, value: u32) {
        self.set_vrom_relative(addr, value.into());
    }

    fn set_vrom_relative_range(&mut self, addr: u32, values: &[u32]) {
        for (i, &value) in values.iter().enumerate() {
            self.set_vrom_relative(addr + i as u32, value.into());
        }
    }

    fn set_vrom_relative_range_future(&mut self, addr: u32, amount: u32) {
        for i in addr..addr + amount {
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
}

impl<'a, 'b, E: ExternalFunctions> MemoryAccessor<'a, 'b, E> {
    fn new(segment: Segment, interpreter: &'a mut Interpreter<'b, E>) -> Self {
        MemoryAccessor {
            segment,
            interpreter,
        }
    }

    fn get_size(&self) -> u32 {
        self.interpreter.get_ram(self.segment.start)
    }
    fn set_size(&mut self, size: u32) {
        self.interpreter.set_ram(self.segment.start, size);
    }
    fn get_max_size(&self) -> u32 {
        self.interpreter.get_ram(self.segment.start + 4)
    }

    fn get_word(&self, byte_addr: u32) -> Result<u32, ()> {
        assert_eq!(byte_addr % 4, 0, "Address must be word-aligned");
        if byte_addr >= self.get_size() {
            return Err(());
        }
        let ram_addr = self.segment.start + 8 + byte_addr;
        Ok(self.interpreter.get_ram(ram_addr))
    }

    fn set_word(&mut self, byte_addr: u32, value: u32) -> Result<(), ()> {
        assert_eq!(byte_addr % 4, 0, "Address must be word-aligned");
        if byte_addr >= self.get_size() {
            return Err(());
        }
        let ram_addr = self.segment.start + 8 + byte_addr;
        self.interpreter.set_ram(ram_addr, value);
        Ok(())
    }

    fn write_contiguous(&mut self, byte_addr: u32, data: &[u32]) -> Result<(), ()> {
        if byte_addr % 4 == 0 {
            // Simple aligned writes
            for (i, &value) in data.iter().enumerate() {
                let addr = byte_addr + (i as u32 * 4);
                self.set_word(addr, value)?;
            }
        } else {
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
            for i in 1..data.len() {
                let current_addr = first_word_addr + (i as u32 * 4);

                let combined = carry_over | (data[i] << shift);
                self.set_word(current_addr, combined)?;
                carry_over = data[i] >> high_shift;
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
}
