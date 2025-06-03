use std::collections::HashMap;

use wasmparser::Operator as Op;

use crate::linker;
use crate::loader::Program;
use crate::loader::flattening::Directive;

#[derive(Debug, Clone, Copy)]
enum VRomValue {
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
            VRomValue::Future(_) => panic!("Cannot convert future to u32"),
            VRomValue::Concrete(value) => *value,
        }
    }
}

pub struct Interpreter<'a> {
    pc: u32,
    fp: u32,
    next_free_ptr: u32,
    vrom: HashMap<u32, VRomValue>,
    future_counter: u32,
    program: Program<'a>,
    flat_program: Vec<Directive<'a>>,
    labels: HashMap<String, (u32, Option<u32>)>,
    function_pcs: HashMap<u32, u32>,
}

impl<'a> Interpreter<'a> {
    pub fn new(program: &Program<'a>) -> Self {
        let (flat_program, function_pcs, labels) = linker::link(&program.functions, 0x1);

        Interpreter {
            pc: 0,
            fp: 0,
            // We leave 0 unused for convention = successful termination.
            next_free_ptr: 1,
            vrom: HashMap::new(),
            future_counter: 0,
            program: program.clone(),
            flat_program,
            labels,
            function_pcs,
        }
    }

    pub fn run(&mut self, main_name: &str, inputs: &[u32]) -> Vec<u32> {
        // TODO
        // First call start_function if it exists, then call main.

        let main_idx = self
            .program
            .exported_functions
            .iter()
            .find(|(_, name)| **name == main_name)
            .map(|(idx, _)| idx)
            .expect("No main function found");

        let main_func_type = self.program.get_func_type(*main_idx);
        let n_outputs = main_func_type.results().len();
        let main_func = &self.program.functions[*main_idx as usize];

        log::trace!("Main function index: {main_idx}");
        log::trace!("Main function type: {main_func_type:#?}");
        log::trace!("Main function frame size: {}", main_func.frame_size);

        self.pc = self.function_pcs[main_idx];
        self.fp = self.allocate(main_func.frame_size);
        let first_fp = self.fp;

        self.set_vrom_relative_u32(0, 0); // final return pc
        self.set_vrom_relative_u32(1, 0); // return fp success
        self.set_vrom_relative_range(2, inputs);

        let output_start = 2 + inputs.len() as u32;
        self.set_vrom_relative_range_future(output_start, n_outputs as u32);

        self.run_loop();

        // We assume that all output futures have been resolved.
        (output_start..output_start + n_outputs as u32)
            .map(|i| self.get_vrom_absolute(first_fp + i).as_u32())
            .collect::<Vec<u32>>()
    }

    fn run_loop(&mut self) {
        let final_fp = loop {
            let instr = self.flat_program[self.pc as usize].clone();
            log::trace!("PC: {}, FP: {}, Instr: {instr}", self.pc, self.fp);

            let mut should_inc_pc = true;

            match instr {
                Directive::Label { id, frame_size } => {
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
                Directive::WASMOp { op, inputs, output } => match op {
                    Op::I32Const { value } => {
                        let output_reg = output.clone().unwrap().next().unwrap();
                        self.set_vrom_relative_u32(output_reg, value as u32);
                    }
                    Op::I32Add => {
                        let a = inputs[0].clone().next().unwrap();
                        let b = inputs[1].clone().next().unwrap();
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative(a).as_u32();
                        let b = self.get_vrom_relative(b).as_u32();
                        let r = a.wrapping_add(b);

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32Sub => {
                        let a = inputs[0].clone().next().unwrap();
                        let b = inputs[1].clone().next().unwrap();
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative(a).as_u32();
                        let b = self.get_vrom_relative(b).as_u32();
                        let r = a.wrapping_sub(b);

                        self.set_vrom_relative_u32(c, r);
                    }

                    Op::I32Mul => {
                        let a = inputs[0].clone().next().unwrap();
                        let b = inputs[1].clone().next().unwrap();
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative(a).as_u32();
                        let b = self.get_vrom_relative(b).as_u32();
                        let r = a.wrapping_mul(b);

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32GtU => {
                        let a = inputs[0].clone().next().unwrap();
                        let b = inputs[1].clone().next().unwrap();
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative(a).as_u32();
                        let b = self.get_vrom_relative(b).as_u32();
                        let r = if a > b { 1 } else { 0 };

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32And => {
                        let a = inputs[0].clone().next().unwrap();
                        let b = inputs[1].clone().next().unwrap();
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative(a).as_u32();
                        let b = self.get_vrom_relative(b).as_u32();
                        let r = a & b;

                        self.set_vrom_relative_u32(c, r);
                    }
                    Op::I32ShrU => {
                        let a = inputs[0].clone().next().unwrap();
                        let b = inputs[1].clone().next().unwrap();
                        let c = output.unwrap().next().unwrap();

                        let a = self.get_vrom_relative(a).as_u32();
                        let b = self.get_vrom_relative(b).as_u32();
                        let r = a >> b;

                        self.set_vrom_relative_u32(c, r);
                    }
                    _ => todo!(),
                },
                Directive::AllocateFrameI {
                    target_frame,
                    result_ptr,
                } => {
                    let frame_size = self.labels[&target_frame].1.unwrap_or(0);
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
                    self.pc = self.labels[&target].0;
                    should_inc_pc = false;

                    let prev_fp = self.fp;
                    self.fp = self.get_vrom_relative(new_frame_ptr).as_u32();

                    if let Some(saved_caller_fp) = saved_caller_fp {
                        self.set_vrom_relative_u32(saved_caller_fp, prev_fp);
                    }
                }
                Directive::JumpIf { target, condition } => {
                    let target = self.labels[&target].0;
                    let cond = self.get_vrom_relative(condition).as_u32();
                    if cond != 0 {
                        self.pc = target;
                        should_inc_pc = false;
                    }
                }
                Directive::Jump { target } => {
                    self.pc = self.labels[&target].0;
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

    fn get_vrom_relative(&self, addr: u32) -> VRomValue {
        self.vrom[&(self.fp + addr)]
    }

    fn get_vrom_absolute(&self, addr: u32) -> VRomValue {
        self.vrom[&addr]
    }

    fn set_vrom_relative(&mut self, addr: u32, value: VRomValue) {
        self.vrom.insert(self.fp + addr, value);
    }

    fn set_vrom_absolute(&mut self, addr: u32, value: VRomValue) {
        self.vrom.insert(addr, value);
    }

    fn set_vrom_relative_u32(&mut self, addr: u32, value: u32) {
        self.vrom.insert(self.fp + addr, value.into());
    }

    fn set_vrom_relative_range(&mut self, addr: u32, values: &[u32]) {
        for (i, &value) in values.iter().enumerate() {
            self.vrom.insert(self.fp + addr + i as u32, value.into());
        }
    }

    fn set_vrom_relative_range_future(&mut self, addr: u32, amount: u32) {
        for i in addr..addr + amount {
            let future = self.new_future();
            self.vrom.insert(self.fp + i, VRomValue::Future(future));
        }
    }

    fn allocate(&mut self, size: u32) -> u32 {
        let addr = self.next_free_ptr;
        self.next_free_ptr += size;
        addr
    }

    fn new_future(&mut self) -> u32 {
        let future = self.future_counter;
        self.future_counter += 1;
        future
    }
}
