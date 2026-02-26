pub mod generic_ir;
pub mod linker;

use crate::interpreter::trace::Tracer;
use crate::loader::Module;
use crate::loader::{
    FunctionRef, Global, MemoryEntry, Program, Segment, WASM_PAGE_SIZE,
    settings::func_idx_to_label, word_count_type, word_count_types,
};
use crate::{
    interpreter::generic_ir::{Directive, GenericIrSetting as S},
    loader::FunctionAsm,
};
use core::panic;
use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::Display;
use std::ops::Range;
use wasmparser::Operator as Op;

// How a null reference is represented in the VROM
pub const NULL_REF: [u32; 3] = [
    u32::MAX, // Function type: this is an invalid function type, so that calling a null reference will trap
    0,        // Frame size: any value here would do, so we choose 0
    0,        // Address: 0 is an invalid function address because START_ROM_ADDR > 0
];

/// We need 2 kinds of register banks, chosen by the execution model:
/// - Write-once registers
/// - Read-write registers
trait RegisterBank {
    /// Allocate `size` registers and return the starting address.
    /// Only valid for write-once execution model.
    fn allocate(&mut self, size: u32) -> u32;

    /// Get the value at the given absolute address.
    fn get(&mut self, addr: u32) -> RegisterValue;

    /// Set a concrete u32 value at the given absolute address.
    fn set(&mut self, addr: u32, value: u32);

    /// Copy a range of u32 values (potentially futures) from one register range to another.
    fn copy_range(&mut self, src: Range<u32>, dest: Range<u32>);

    /// Set a future value at the given absolute address.
    /// Only valid for write-once execution model.
    fn set_future(&mut self, addr: u32);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RegisterValue {
    Unassigned,
    Future(u32),
    Concrete(u32),
}

impl RegisterValue {
    fn as_concrete(&self) -> u32 {
        match self {
            RegisterValue::Concrete(v) => *v,
            RegisterValue::Future(future) => {
                panic!(
                    "Can not convert future {future} to u32. It has not been assigned a value yet."
                );
            }
            RegisterValue::Unassigned => {
                panic!("Can not convert unassigned to u32");
            }
        }
    }
}

impl Display for RegisterValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RegisterValue::Unassigned => write!(f, "U"),
            RegisterValue::Future(fut) => write!(f, "F{}", fut),
            RegisterValue::Concrete(value) => write!(f, "{}", value),
        }
    }
}

struct WriteOnceRegisterBank {
    regs: Vec<RegisterValue>,
    future_counter: u32,
    future_assignments: HashMap<u32, u32>,
}

impl WriteOnceRegisterBank {
    fn new() -> Self {
        Self {
            // We leave 0 unused for convention = successful termination.
            regs: vec![RegisterValue::Unassigned],
            future_counter: 0,
            future_assignments: HashMap::new(),
        }
    }

    fn new_future(&mut self) -> u32 {
        let future = self.future_counter;
        self.future_counter += 1;
        future
    }

    fn copy_word(&mut self, src: u32, dest: u32) {
        let value = self.get(src);
        let dest_slot = &mut self.regs[dest as usize];
        match (*dest_slot, value) {
            (RegisterValue::Unassigned, RegisterValue::Unassigned) => {
                // This is important to catch to prevent bugs.
                panic!("Attempted to assign an unassigned value to register");
            }
            (RegisterValue::Unassigned, _) => {
                *dest_slot = value;
            }
            (RegisterValue::Future(future), RegisterValue::Concrete(v)) => {
                // Assigning Concrete values to Futures materializes it.
                if let Some(old_value) = self.future_assignments.insert(future, v) {
                    assert_eq!(old_value, v, "Attempted to overwrite a value in register");
                }
                log::debug!("Future {future} materialized to value {v}");
            }
            (_, _) => {
                assert_eq!(
                    *dest_slot, value,
                    "Attempted to overwrite a value in register"
                );
            }
        }
    }
}

impl RegisterBank for WriteOnceRegisterBank {
    fn allocate(&mut self, size: u32) -> u32 {
        let addr = self.regs.len();
        self.regs
            .resize_with(addr + size as usize, || RegisterValue::Unassigned);
        addr as u32
    }

    fn get(&mut self, addr: u32) -> RegisterValue {
        let value = self.regs[addr as usize];
        match value {
            RegisterValue::Concrete(_) => value,
            RegisterValue::Future(future) => {
                // Resolve the future if it has been assigned.
                if let Some(resolved_value) = self.future_assignments.get(&future) {
                    let value = RegisterValue::Concrete(*resolved_value);
                    self.regs[addr as usize] = value;
                    value
                } else {
                    value
                }
            }
            RegisterValue::Unassigned => {
                // The only reason to read an unassigned value is to assign it later,
                // so it must become a Future.
                let value = RegisterValue::Future(self.new_future());
                self.regs[addr as usize] = value;
                value
            }
        }
    }

    fn set(&mut self, addr: u32, value: u32) {
        let slot = &mut self.regs[addr as usize];
        match *slot {
            RegisterValue::Unassigned => {
                *slot = RegisterValue::Concrete(value);
            }
            RegisterValue::Future(future) => {
                // Assigning Concrete values to Futures materializes it.
                if let Some(old_value) = self.future_assignments.insert(future, value) {
                    assert_eq!(
                        old_value, value,
                        "Attempted to overwrite a value in register"
                    );
                }
                log::debug!("Future {future} materialized to value {value}");
            }
            RegisterValue::Concrete(existing) => {
                assert_eq!(
                    existing, value,
                    "Attempted to overwrite a value in register"
                );
            }
        }
    }

    fn copy_range(&mut self, src: Range<u32>, dest: Range<u32>) {
        for (src_reg, dest_reg) in src.zip_eq(dest) {
            self.copy_word(src_reg, dest_reg);
        }
    }

    fn set_future(&mut self, addr: u32) {
        let future = self.new_future();
        let slot = &mut self.regs[addr as usize];
        match *slot {
            RegisterValue::Unassigned => {
                *slot = RegisterValue::Future(future);
            }
            _ => {
                panic!("Attempted to set future on non-unassigned register");
            }
        }
    }
}

struct ReadWriteRegisterBank {
    regs: Vec<u32>,
}

impl ReadWriteRegisterBank {
    fn new() -> Self {
        Self { regs: Vec::new() }
    }
}

impl RegisterBank for ReadWriteRegisterBank {
    fn get(&mut self, addr: u32) -> RegisterValue {
        let value = self.regs.get(addr as usize).copied().unwrap_or(0);
        RegisterValue::Concrete(value)
    }

    fn set(&mut self, addr: u32, value: u32) {
        let addr = addr as usize;
        if addr >= self.regs.len() {
            self.regs.resize(addr + 1, 0);
        }
        self.regs[addr] = value;
    }

    fn copy_range(&mut self, src: Range<u32>, dest: Range<u32>) {
        assert_eq!(src.len(), dest.len());
        if src.len() == 1 {
            // Optimize the common case of copying a single word to avoid the overhead of collect_vec()
            let value = self.get(src.start).as_concrete();
            self.set(dest.start, value);
        } else {
            // Read all the values first to allow for overlapping src and dest
            let value = src.map(|addr| self.get(addr).as_concrete()).collect_vec();
            for (dest, value) in dest.zip_eq(value) {
                self.set(dest, value);
            }
        }
    }

    fn allocate(&mut self, _size: u32) -> u32 {
        unreachable!("Allocation is not supported in read-write execution model");
    }

    fn set_future(&mut self, _addr: u32) {
        unreachable!("Futures are not supported in read-write execution model");
    }
}

pub struct Interpreter<'a, E: ExternalFunctions> {
    // TODO: maybe these 6 initial fields should be unique per `run()` call?
    pc: u32,
    fp: u32,
    regs: Box<dyn RegisterBank>,
    ram: Ram,
    call_stack: Vec<u32>,
    trace_enabled: bool,
    // Unchanging across `run()` calls:
    exec_model: ExecutionModel,
    func_stack_sizes: Vec<u32>,
    module: Module<'a>,
    external_functions: E,
    flat_program: Vec<Directive<'a>>,
    labels: HashMap<String, linker::LabelValue>,
    addr_to_func_id: HashMap<u32, u32>,
}

pub enum ExternalCallResult {
    Values(Vec<u32>),
    Exit(u32),
}

pub enum RunResult {
    Ok(Vec<u32>),
    Exit(u32),
}

pub trait ExternalFunctions {
    fn call(
        &mut self,
        module: &str,
        func: &str,
        args: &[u32],
        mem: &mut Option<MemoryAccessor<'_>>,
    ) -> ExternalCallResult;
}

struct Ram(HashMap<u32, u32>);

impl Ram {
    fn get(&self, byte_addr: u32) -> u32 {
        *self.0.get(&byte_addr).unwrap_or(&0)
    }

    fn set(&mut self, byte_addr: u32, value: u32) {
        if value == 0 {
            self.0.remove(&byte_addr);
        } else {
            self.0.insert(byte_addr, value);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutionModel {
    WriteOnceRegisters,
    InfiniteRegisters,
}

impl<'a, E: ExternalFunctions> Interpreter<'a, E> {
    pub fn new(
        program: Program<'a, FunctionAsm<Directive<'a>>>,
        exec_model: ExecutionModel,
        external_functions: E,
        trace_enabled: bool,
    ) -> Self {
        const START_ROM_ADDR: u32 = 0x1;

        let mut func_stack_sizes = Vec::new();
        let regs = if exec_model == ExecutionModel::WriteOnceRegisters {
            func_stack_sizes.extend(program.functions.iter().map(|f| f.frame_size.unwrap()));
            Box::new(WriteOnceRegisterBank::new()) as Box<dyn RegisterBank>
        } else {
            Box::new(ReadWriteRegisterBank::new()) as Box<dyn RegisterBank>
        };

        let (flat_program, labels) = linker::link(program.functions, START_ROM_ADDR);

        let ram = program
            .m
            .initial_memory
            .iter()
            .filter_map(|(addr, value)| {
                let value = match value {
                    MemoryEntry::Value(v) => *v,
                    MemoryEntry::FuncAddr(idx) => {
                        let label = func_idx_to_label(*idx);
                        labels[&label].pc
                    }
                    MemoryEntry::FuncFrameSize(func_idx) => {
                        if exec_model == ExecutionModel::WriteOnceRegisters {
                            let label = func_idx_to_label(*func_idx);
                            labels[&label].frame_size.unwrap()
                        } else {
                            0
                        }
                    }
                    MemoryEntry::NullFuncType => NULL_REF[FunctionRef::<S>::TYPE_ID],
                    MemoryEntry::NullFuncFrameSize => NULL_REF[FunctionRef::<S>::FUNC_FRAME_SIZE],
                    MemoryEntry::NullFuncAddr => NULL_REF[FunctionRef::<S>::FUNC_ADDR],
                };

                if value == 0 {
                    None
                } else {
                    Some((*addr, value))
                }
            })
            .collect::<HashMap<_, _>>();

        let addr_to_func_id = labels
            .iter()
            .filter_map(|(_, label)| label.func_idx.map(|func_idx| (label.pc, func_idx)))
            .collect::<HashMap<_, _>>();
        let mut interpreter = Self {
            pc: 0,
            fp: 0,
            regs,
            ram: Ram(ram),
            exec_model,
            call_stack: Vec::new(),
            trace_enabled,
            func_stack_sizes,
            module: program.m,
            external_functions,
            flat_program,
            labels,
            addr_to_func_id,
        };

        if let Some(start_function) = interpreter.module.start_function {
            let label = func_idx_to_label(start_function);
            if let RunResult::Exit(code) = interpreter.run(&label, &[]) {
                panic!("Start function exited with code {code}");
            }
        }

        interpreter
    }

    fn get_mem<'b>(&'b mut self) -> MemoryAccessor<'b> {
        MemoryAccessor::new(self.module.memory.unwrap(), &mut self.ram)
    }

    pub fn run(&mut self, func_name: &str, inputs: &[u32]) -> RunResult {
        let func_label = &self.labels[func_name];

        let func_type = &self.module.get_func_type(func_label.func_idx.unwrap()).ty;
        let n_inputs: u32 = word_count_types::<S>(func_type.params());
        assert_eq!(inputs.len(), n_inputs as usize);

        let n_outputs: u32 = word_count_types::<S>(func_type.results());
        self.pc = func_label.pc;

        let outputs_range = match self.exec_model {
            ExecutionModel::WriteOnceRegisters => {
                // Use WOM calling convention
                self.fp = self.allocate(func_label.frame_size.unwrap());
                let mut regs = Tracer::new(self);

                regs.set_reg_relative_u32(0..1, 0); // final return pc
                regs.set_reg_relative_u32(1..2, 0); // return fp success
                regs.set_reg_relative_range(2..2 + inputs.len() as u32, inputs);

                let output_start = 2 + inputs.len() as u32;
                regs.set_reg_relative_range_future(output_start..output_start + n_outputs);

                // We assume that all output futures will be resolved after run_loop()
                output_start..output_start + n_outputs
            }
            ExecutionModel::InfiniteRegisters => {
                // Use RW calling convention
                self.fp = 1;
                let mut regs = Tracer::new(self);

                regs.set_reg_relative_range(0..inputs.len() as u32, inputs);
                let ret_pc_reg = n_inputs.max(n_outputs);
                regs.set_reg_relative_u32(ret_pc_reg..(ret_pc_reg + 1), 0); // final return pc
                regs.set_reg_relative_u32(ret_pc_reg + 1..ret_pc_reg + 2, 0); // return fp success

                0..n_outputs
            }
        };

        let first_fp = self.fp;
        // Push the initial function address onto the stack for instrumentation
        self.call_stack.push(self.addr_to_func_id[&self.pc]);
        let exit_code = self.run_loop();
        // Pop the initial function address
        self.call_stack.pop();

        if let Some(code) = exit_code {
            return RunResult::Exit(code);
        }

        RunResult::Ok(
            outputs_range
                .map(|i| self.regs.get(first_fp + i).as_concrete())
                .collect::<Vec<u32>>(),
        )
    }

    fn run_loop(&mut self) -> Option<u32> {
        let mut cycles = 0usize;

        let mut t = Tracer::new(self);
        let final_fp = loop {
            t.reset();

            let instr = t.i.flat_program[t.i.pc as usize].clone();

            let mut should_inc_pc = true;

            match instr {
                Directive::Label { .. } => {
                    should_inc_pc = false;
                    // do nothing
                }
                Directive::Return { ret_pc, ret_fp } => {
                    let pc = t.get_reg_relative_u32(ret_pc..ret_pc + 1);
                    let fp = t.get_reg_relative_u32(ret_fp..ret_fp + 1);
                    if pc == 0 {
                        break fp;
                    } else {
                        // Pop the current function from the stack
                        t.i.call_stack.pop();
                        t.i.pc = pc;
                        t.i.fp = fp;
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
                        t.set_reg_relative_u32(output.unwrap(), value as u32);
                    }
                    Op::F32Const { value } => {
                        t.set_reg_relative_u32(output.unwrap(), value.bits());
                    }
                    Op::I64Const { value } => {
                        t.set_reg_relative_u64(output.unwrap(), value as u64);
                    }
                    Op::F64Const { value } => {
                        let value = value.bits();
                        t.set_reg_relative_u64(output.unwrap(), value);
                    }
                    Op::I32Add => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b);
                        let r = a.wrapping_add(b);

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64Add => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);
                        let r = a.wrapping_add(b);

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I32Sub => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b);
                        let r = a.wrapping_sub(b);

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64Sub => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);
                        let r = a.wrapping_sub(b);

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I32Mul => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b);
                        let r = a.wrapping_mul(b);

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64Mul => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);
                        let r = a.wrapping_mul(b);

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I32DivU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b);

                        if b == 0 {
                            panic!("integer divide by zero in I32DivU");
                        }

                        let r = a / b;

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I32DivS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a) as i32;
                        let b = t.get_reg_relative_u32(b) as i32;

                        if b == 0 {
                            panic!("integer divide by zero in I32DivS");
                        }
                        if a == i32::MIN && b == -1 {
                            panic!("integer overflow in I32DivS");
                        }

                        let r = a.wrapping_div(b) as u32;

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64DivU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);

                        if b == 0 {
                            panic!("integer divide by zero in I64DivU");
                        }

                        let r = a / b;

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I64DivS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a) as i64;
                        let b = t.get_reg_relative_u64(b) as i64;

                        if b == 0 {
                            panic!("integer divide by zero in I64DivS");
                        }
                        if a == i64::MIN && b == -1 {
                            panic!("integer overflow in I64DivS");
                        }

                        let r = a.wrapping_div(b) as u64;

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I32RemU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b);

                        if b == 0 {
                            panic!("integer divide by zero in I32RemU");
                        }

                        let r = a % b;

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I32RemS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a) as i32;
                        let b = t.get_reg_relative_u32(b) as i32;

                        if b == 0 {
                            panic!("integer divide by zero in I32RemS");
                        }

                        let r = a.wrapping_rem(b);

                        t.set_reg_relative_u32(c, r as u32);
                    }
                    Op::I64RemU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);

                        if b == 0 {
                            panic!("integer divide by zero in I64RemU");
                        }

                        let r = a % b;

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I64RemS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a) as i64;
                        let b = t.get_reg_relative_u64(b) as i64;

                        if b == 0 {
                            panic!("integer divide by zero in I64RemS");
                        }

                        let r = a.wrapping_rem(b);

                        t.set_reg_relative_u64(c, r as u64);
                    }
                    Op::I32LtU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b);

                        let r = if a < b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64LtU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);
                        let r = if a < b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I32LtS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a) as i32;
                        let b = t.get_reg_relative_u32(b) as i32;

                        let r = if a < b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64LtS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a) as i64;
                        let b = t.get_reg_relative_u64(b) as i64;
                        let r = if a < b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I32LeS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a) as i32;
                        let b = t.get_reg_relative_u32(b) as i32;

                        let r = if a <= b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64LeS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a) as i64;
                        let b = t.get_reg_relative_u64(b) as i64;
                        let r = if a <= b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I32LeU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b);

                        let r = if a <= b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64LeU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);
                        let r = if a <= b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I32GtU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b);
                        let r = if a > b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64GtU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);
                        let r = if a > b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I32GtS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a) as i32;
                        let b = t.get_reg_relative_u32(b) as i32;

                        let r = if a > b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64GtS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a) as i64;
                        let b = t.get_reg_relative_u64(b) as i64;
                        let r = if a > b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I32GeS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a) as i32;
                        let b = t.get_reg_relative_u32(b) as i32;

                        let r = if a >= b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64GeS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a) as i64;
                        let b = t.get_reg_relative_u64(b) as i64;
                        let r = if a >= b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I32GeU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b);

                        let r = if a >= b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64GeU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);
                        let r = if a >= b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I32And => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b);
                        let r = a & b;

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I32Or => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b);
                        let r = a | b;

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64And => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);
                        let r = a & b;

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I64Or => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);
                        let r = a | b;

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I64Xor => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);
                        let r = a ^ b;

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I32Xor => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b);
                        let r = a ^ b;

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I32Shl => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b);

                        let r = a.wrapping_shl(b);

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64Shl => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);

                        let r = a.wrapping_shl(b as u32);

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I64Rotl => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b);

                        let r = a.rotate_left(b as u32);

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I32ShrU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b) & 0x1F;

                        let r = a.wrapping_shr(b);

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64ShrU => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b) as u32;

                        let r = a.wrapping_shr(b);

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I32ShrS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a) as i32;
                        let b = t.get_reg_relative_u32(b) & 0x1F;

                        let r = a.wrapping_shr(b);

                        t.set_reg_relative_u32(c, r as u32);
                    }
                    Op::I64ShrS => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a) as i64;
                        let b = t.get_reg_relative_u64(b) as u32;

                        let r = a.wrapping_shr(b);

                        t.set_reg_relative_u64(c, r as u64);
                    }
                    Op::I32Rotl => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b) & 0x1F;

                        let r = a.rotate_left(b);

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I32Rotr => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);
                        let b = t.get_reg_relative_u32(b) & 0x1F;

                        let r = a.rotate_right(b);

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64Rotr => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let b = t.get_reg_relative_u64(b) as u32;

                        let r = a.rotate_right(b);

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I32Clz => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);

                        let r = a.leading_zeros();

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64Clz => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);

                        let r = a.leading_zeros() as u64;

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I32Ctz => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);

                        let r = a.trailing_zeros();

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64Ctz => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);

                        let r = a.trailing_zeros() as u64;

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I32Popcnt => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);

                        let r = a.count_ones();

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::I64Popcnt => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);

                        let r = a.count_ones() as u64;

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::I32Extend8S => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);

                        let r = (a as u8) as i8 as i32;

                        t.set_reg_relative_u32(c, r as u32);
                    }
                    Op::I64Extend8S => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);

                        let r = (a as u8) as i8 as i64;

                        t.set_reg_relative_u64(c, r as u64);
                    }
                    Op::I32Extend16S => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);

                        let r = (a as u16) as i16 as i32;

                        t.set_reg_relative_u32(c, r as u32);
                    }
                    Op::I64Extend16S => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);

                        let r = (a as u16) as i16 as i64;

                        t.set_reg_relative_u64(c, r as u64);
                    }
                    Op::I64Extend32S => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);

                        let r = (a as u32) as i32 as i64;

                        t.set_reg_relative_u64(c, r as u64);
                    }
                    Op::I64ExtendI32U => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a);

                        t.set_reg_relative_u64(c, a as u64);
                    }
                    Op::I64ExtendI32S => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u32(a) as i32;

                        t.set_reg_relative_u64(c, a as u64);
                    }
                    Op::I32Eq | Op::I64Eq => {
                        let a = t.get_reg_relative_range(inputs[0].clone()).collect_vec();
                        let b = t.get_reg_relative_range(inputs[1].clone());
                        let c = output.unwrap();

                        let val = if b.eq(a) { 1 } else { 0 };
                        t.set_reg_relative_u32(c, val);
                    }
                    Op::I32Ne | Op::I64Ne => {
                        let a = t.get_reg_relative_range(inputs[0].clone()).collect_vec();
                        let b = t.get_reg_relative_range(inputs[1].clone());
                        let c = output.unwrap();

                        let val = if !b.eq(a) { 1 } else { 0 };
                        t.set_reg_relative_u32(c, val);
                    }
                    Op::I32Eqz | Op::I64Eqz => {
                        let mut a = t.get_reg_relative_range(inputs[0].clone());
                        let c = output.unwrap();

                        let val = if a.all(|x| x == 0) { 1 } else { 0 };
                        drop(a);
                        t.set_reg_relative_u32(c, val);
                    }
                    Op::I32WrapI64 => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);

                        let r = a as u32;

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::F32Add => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(t.get_reg_relative_u32(a));
                        let b = f32::from_bits(t.get_reg_relative_u32(b));

                        let r = a + b;
                        let r = r.to_bits();

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::F32Sub => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(t.get_reg_relative_u32(a));
                        let b = f32::from_bits(t.get_reg_relative_u32(b));

                        let r = a - b;
                        let r = r.to_bits();

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::F32Div => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(t.get_reg_relative_u32(a));
                        let b = f32::from_bits(t.get_reg_relative_u32(b));

                        if b == 0f32 {
                            panic!("integer divide by zero in I32DivU");
                        }

                        let r = a / b;
                        let r = r.to_bits();

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::F32Neg => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(t.get_reg_relative_u32(a));

                        let r = -a;
                        let r = r.to_bits();

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::F64Neg => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();

                        let a = t.get_reg_relative_u64(a);
                        let r = -f64::from_bits(a);
                        let r = r.to_bits();

                        t.set_reg_relative_u64(c, r);
                    }
                    Op::F64Abs => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();
                        let a = f64::from_bits(t.get_reg_relative_u64(a));
                        t.set_reg_relative_u64(c, a.abs().to_bits());
                    }
                    Op::F64Ceil => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();
                        let a = f64::from_bits(t.get_reg_relative_u64(a));
                        t.set_reg_relative_u64(c, a.ceil().to_bits());
                    }
                    Op::F64Floor => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();
                        let a = f64::from_bits(t.get_reg_relative_u64(a));
                        t.set_reg_relative_u64(c, a.floor().to_bits());
                    }
                    Op::F64Trunc => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();
                        let a = f64::from_bits(t.get_reg_relative_u64(a));
                        t.set_reg_relative_u64(c, a.trunc().to_bits());
                    }
                    Op::F64Nearest => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();
                        let a = f64::from_bits(t.get_reg_relative_u64(a));
                        t.set_reg_relative_u64(c, a.round_ties_even().to_bits());
                    }
                    Op::F64Sqrt => {
                        let a = inputs[0].clone();
                        let c = output.unwrap();
                        let a = f64::from_bits(t.get_reg_relative_u64(a));
                        t.set_reg_relative_u64(c, a.sqrt().to_bits());
                    }
                    Op::F64Add => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        let b = f64::from_bits(t.get_reg_relative_u64(inputs[1].clone()));
                        t.set_reg_relative_u64(output.unwrap(), (a + b).to_bits());
                    }
                    Op::F64Sub => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        let b = f64::from_bits(t.get_reg_relative_u64(inputs[1].clone()));
                        t.set_reg_relative_u64(output.unwrap(), (a - b).to_bits());
                    }
                    Op::F64Mul => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        let b = f64::from_bits(t.get_reg_relative_u64(inputs[1].clone()));
                        t.set_reg_relative_u64(output.unwrap(), (a * b).to_bits());
                    }
                    Op::F64Div => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        let b = f64::from_bits(t.get_reg_relative_u64(inputs[1].clone()));
                        t.set_reg_relative_u64(output.unwrap(), (a / b).to_bits());
                    }
                    Op::F64Eq => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        let b = f64::from_bits(t.get_reg_relative_u64(inputs[1].clone()));
                        t.set_reg_relative_u32(output.unwrap(), if a == b { 1 } else { 0 });
                    }
                    Op::F64Ne => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        let b = f64::from_bits(t.get_reg_relative_u64(inputs[1].clone()));
                        t.set_reg_relative_u32(output.unwrap(), if a != b { 1 } else { 0 });
                    }
                    Op::F64Lt => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        let b = f64::from_bits(t.get_reg_relative_u64(inputs[1].clone()));
                        t.set_reg_relative_u32(output.unwrap(), if a < b { 1 } else { 0 });
                    }
                    Op::F64Le => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        let b = f64::from_bits(t.get_reg_relative_u64(inputs[1].clone()));
                        t.set_reg_relative_u32(output.unwrap(), if a <= b { 1 } else { 0 });
                    }
                    Op::F64Gt => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        let b = f64::from_bits(t.get_reg_relative_u64(inputs[1].clone()));
                        t.set_reg_relative_u32(output.unwrap(), if a > b { 1 } else { 0 });
                    }
                    Op::F64Ge => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        let b = f64::from_bits(t.get_reg_relative_u64(inputs[1].clone()));
                        t.set_reg_relative_u32(output.unwrap(), if a >= b { 1 } else { 0 });
                    }
                    Op::F64Copysign => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        let b = f64::from_bits(t.get_reg_relative_u64(inputs[1].clone()));
                        t.set_reg_relative_u64(output.unwrap(), a.copysign(b).to_bits());
                    }
                    Op::F64Min => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        let b = f64::from_bits(t.get_reg_relative_u64(inputs[1].clone()));
                        t.set_reg_relative_u64(output.unwrap(), a.min(b).to_bits());
                    }
                    Op::F64Max => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        let b = f64::from_bits(t.get_reg_relative_u64(inputs[1].clone()));
                        t.set_reg_relative_u64(output.unwrap(), a.max(b).to_bits());
                    }
                    Op::F64ConvertI32S => {
                        let a = t.get_reg_relative_u32(inputs[0].clone()) as i32;
                        t.set_reg_relative_u64(output.unwrap(), (a as f64).to_bits());
                    }
                    Op::F64ConvertI32U => {
                        let a = t.get_reg_relative_u32(inputs[0].clone());
                        t.set_reg_relative_u64(output.unwrap(), (a as f64).to_bits());
                    }
                    Op::F64ConvertI64S => {
                        let a = t.get_reg_relative_u64(inputs[0].clone()) as i64;
                        t.set_reg_relative_u64(output.unwrap(), (a as f64).to_bits());
                    }
                    Op::F64ConvertI64U => {
                        let a = t.get_reg_relative_u64(inputs[0].clone());
                        t.set_reg_relative_u64(output.unwrap(), (a as f64).to_bits());
                    }
                    Op::F64PromoteF32 => {
                        let a = f32::from_bits(t.get_reg_relative_u32(inputs[0].clone()));
                        t.set_reg_relative_u64(output.unwrap(), (a as f64).to_bits());
                    }
                    Op::F64ReinterpretI64 => {
                        // Just copy the bits (already stored as u64)
                        let a = t.get_reg_relative_u64(inputs[0].clone());
                        t.set_reg_relative_u64(output.unwrap(), a);
                    }
                    Op::I64ReinterpretF64 => {
                        let a = t.get_reg_relative_u64(inputs[0].clone());
                        t.set_reg_relative_u64(output.unwrap(), a);
                    }
                    Op::I32TruncF64S => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        t.set_reg_relative_u32(output.unwrap(), a as i32 as u32);
                    }
                    Op::I32TruncF64U => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        t.set_reg_relative_u32(output.unwrap(), a as u32);
                    }
                    Op::I64TruncF64S => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        t.set_reg_relative_u64(output.unwrap(), a as i64 as u64);
                    }
                    Op::I64TruncF64U => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        t.set_reg_relative_u64(output.unwrap(), a as u64);
                    }
                    Op::F32DemoteF64 => {
                        let a = f64::from_bits(t.get_reg_relative_u64(inputs[0].clone()));
                        t.set_reg_relative_u32(output.unwrap(), (a as f32).to_bits());
                    }
                    Op::F32Mul => {
                        let a = f32::from_bits(t.get_reg_relative_u32(inputs[0].clone()));
                        let b = f32::from_bits(t.get_reg_relative_u32(inputs[1].clone()));
                        t.set_reg_relative_u32(output.unwrap(), (a * b).to_bits());
                    }
                    Op::F32ConvertI32S => {
                        let a = t.get_reg_relative_u32(inputs[0].clone()) as i32;
                        t.set_reg_relative_u32(output.unwrap(), (a as f32).to_bits());
                    }
                    Op::F32ConvertI32U => {
                        let a = t.get_reg_relative_u32(inputs[0].clone());
                        t.set_reg_relative_u32(output.unwrap(), (a as f32).to_bits());
                    }
                    Op::F32ConvertI64S => {
                        let a = t.get_reg_relative_u64(inputs[0].clone()) as i64;
                        t.set_reg_relative_u32(output.unwrap(), (a as f32).to_bits());
                    }
                    Op::F32ConvertI64U => {
                        let a = t.get_reg_relative_u64(inputs[0].clone());
                        t.set_reg_relative_u32(output.unwrap(), (a as f32).to_bits());
                    }
                    Op::F32Eq => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(t.get_reg_relative_u32(a));
                        let b = f32::from_bits(t.get_reg_relative_u32(b));

                        let r = if a == b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::F32Lt => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(t.get_reg_relative_u32(a));
                        let b = f32::from_bits(t.get_reg_relative_u32(b));

                        let r = if a < b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::F32Gt => {
                        let a = inputs[0].clone();
                        let b = inputs[1].clone();
                        let c = output.unwrap();

                        let a = f32::from_bits(t.get_reg_relative_u32(a));
                        let b = f32::from_bits(t.get_reg_relative_u32(b));

                        let r = if a > b { 1 } else { 0 };

                        t.set_reg_relative_u32(c, r);
                    }
                    Op::Select | Op::TypedSelect { .. } => {
                        let condition = t.get_reg_relative_u32(inputs[2].clone());

                        let selected = inputs[if condition != 0 { 0 } else { 1 }].clone();
                        let output = output.unwrap();
                        t.copy_reg_range_relative(selected, output);
                    }
                    Op::GlobalGet { global_index } => {
                        let Global::Mutable(global_info) =
                            t.i.module.globals[global_index as usize]
                        else {
                            panic!("immutable GlobalGet should have been resolved at compile time");
                        };
                        let output = output.unwrap();

                        let size = word_count_type::<S>(global_info.val_type);
                        assert_eq!(size, output.len() as u32);

                        let value = (0..size)
                            .map(|i| t.i.ram.get(global_info.address + 4 * i))
                            .collect_vec();
                        t.set_reg_relative_range(output, &value);
                    }
                    Op::GlobalSet { global_index } => {
                        let Global::Mutable(global_info) =
                            t.i.module.globals[global_index as usize]
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

                        let value = t.get_reg_relative_range(origin).collect_vec();
                        for (i, value) in value.into_iter().enumerate() {
                            t.i.ram.set(global_info.address + 4 * i as u32, value);
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

                        let addr = t.get_reg_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        // input[1] might have 1 or 2 words, but we only need the first word
                        let val_input = inputs[1].start..(inputs[1].start + 1);
                        let new_value = mask & t.get_reg_relative_u32(val_input);

                        assert_eq!(memarg.memory, 0);
                        let mut memory = t.i.get_mem();

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
                        let addr = t.get_reg_relative_u32(inputs[0].clone()) + memarg.offset as u32;
                        let value = t.get_reg_relative_range(inputs[1].clone()).collect_vec();

                        assert_eq!(memarg.memory, 0);
                        let mut memory = t.i.get_mem();
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
                        let addr = t.get_reg_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = t.i.get_mem();
                        let value = memory.read_contiguous_bytes(addr, word_len * 4);

                        if value.is_err() {
                            panic!(
                                "Out of bounds read addr {addr} len {}, input: {:?}, offset: {}",
                                word_len * 4,
                                inputs[0],
                                memarg.offset
                            );
                        }
                        let value = value.unwrap();

                        t.set_reg_relative_range(output_reg, &value);
                    }
                    Op::I32Load8U { memarg } | Op::I64Load8U { memarg } => {
                        let output_reg = output.unwrap();
                        let word_len = output_reg.len() as u32;

                        assert_eq!(inputs.len(), 1);
                        let addr = t.get_reg_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = t.i.get_mem();

                        let byte = memory
                            .read_contiguous_bytes(addr, 1)
                            .expect("Out of bounds read")[0]
                            & 0xff;

                        let value = [byte, 0];
                        t.set_reg_relative_range(output_reg, &value[0..word_len as usize]);
                    }
                    Op::I32Load8S { memarg } | Op::I64Load8S { memarg } => {
                        let output_reg = output.unwrap();
                        let word_len = output_reg.len() as u32;

                        assert_eq!(inputs.len(), 1);
                        let addr = t.get_reg_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = t.i.get_mem();

                        let byte = memory
                            .read_contiguous_bytes(addr, 1)
                            .expect("Out of bounds read")[0];

                        let signed = byte as i8 as i64;

                        let value = [signed as u32, (signed >> 32) as u32];
                        t.set_reg_relative_range(output_reg, &value[0..word_len as usize]);
                    }
                    Op::I32Load16U { memarg } | Op::I64Load16U { memarg } => {
                        let output_reg = output.unwrap();
                        let word_len = output_reg.len() as u32;

                        assert_eq!(inputs.len(), 1);
                        let addr = t.get_reg_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = t.i.get_mem();

                        let bytes = memory
                            .read_contiguous_bytes(addr, 2)
                            .expect("Out of bounds read")[0]
                            & 0xffff;

                        let value = [bytes, 0];
                        t.set_reg_relative_range(output_reg, &value[0..word_len as usize]);
                    }
                    Op::I32Load16S { memarg } | Op::I64Load16S { memarg } => {
                        let output_reg = output.unwrap();
                        let word_len = output_reg.len() as u32;

                        assert_eq!(inputs.len(), 1);
                        let addr = t.get_reg_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = t.i.get_mem();

                        let value = memory
                            .read_contiguous_bytes(addr, 2)
                            .expect("Out of bounds read")[0];

                        let signed = value as i16 as i64;

                        let value = [signed as u32, (signed >> 32) as u32];
                        t.set_reg_relative_range(output_reg, &value[0..word_len as usize]);
                    }
                    Op::I64Load32U { memarg } => {
                        let output_reg = output.unwrap();

                        assert_eq!(inputs.len(), 1);
                        let addr = t.get_reg_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = t.i.get_mem();

                        let word = memory
                            .read_contiguous_bytes(addr, 4)
                            .expect("Out of bounds read")[0];

                        t.set_reg_relative_range(output_reg, &[word, 0]);
                    }
                    Op::I64Load32S { memarg } => {
                        let output_reg = output.unwrap();

                        assert_eq!(inputs.len(), 1);
                        let addr = t.get_reg_relative_u32(inputs[0].clone()) + memarg.offset as u32;

                        assert_eq!(memarg.memory, 0);
                        let memory = t.i.get_mem();

                        let word = memory
                            .read_contiguous_bytes(addr, 4)
                            .expect("Out of bounds read")[0];

                        let signed = word as i32 as i64;
                        let value = [signed as u32, (signed >> 32) as u32];
                        t.set_reg_relative_range(output_reg, &value);
                    }
                    Op::MemorySize { mem } => {
                        assert_eq!(mem, 0, "Only memory 0 is supported in this interpreter");
                        let memory = t.i.get_mem();
                        let num_pages = memory.get_size() / WASM_PAGE_SIZE;
                        t.set_reg_relative_u32(output.unwrap(), num_pages);
                    }
                    Op::MemoryGrow { mem } => {
                        let extra_pages = t.get_reg_relative_u32(inputs[0].clone());

                        assert_eq!(mem, 0, "Only memory 0 is supported in this interpreter");
                        let mut memory = t.i.get_mem();

                        let old_num_pages = memory.get_size() / WASM_PAGE_SIZE;
                        let new_num_pages = old_num_pages + extra_pages;

                        let result = if new_num_pages > memory.get_max_num_pages() {
                            0xFFFFFFFF // WASM spec says to return -1 on failure
                        } else {
                            memory.set_num_pages(new_num_pages);
                            old_num_pages
                        };

                        t.set_reg_relative_u32(output.unwrap(), result);
                    }
                    Op::MemoryFill { mem } => {
                        assert_eq!(mem, 0);

                        let dst = t.get_reg_relative_u32(inputs[0].clone());
                        let value = t.get_reg_relative_u32(inputs[1].clone()) as u8;
                        let mut byte_size = t.get_reg_relative_u32(inputs[2].clone());

                        let mut memory = t.i.get_mem();

                        // write the first misaligned bytes
                        let misalignment = dst & 3;
                        let mut dst_word = dst & !3;
                        if misalignment != 0 {
                            let mut word = memory
                                .get_word(dst_word)
                                .expect("Out of bounds read")
                                .to_le_bytes();
                            for i in misalignment..4 {
                                if byte_size == 0 {
                                    break;
                                }
                                word[i as usize] = value;
                                byte_size -= 1;
                            }
                            memory
                                .set_word(dst_word, u32::from_le_bytes(word))
                                .expect("Out of bounds write");
                            dst_word += 4;
                        }

                        // write the middle aligned words
                        let num_full_words = byte_size / 4;
                        let full_word = u32::from_le_bytes([value; 4]);
                        memory
                            .write_contiguous(dst_word, &vec![full_word; num_full_words as usize])
                            .expect("Out of bounds write");
                        byte_size -= num_full_words * 4;
                        dst_word += num_full_words * 4;

                        // write the last misaligned bytes
                        if byte_size > 0 {
                            let mut word = memory
                                .get_word(dst_word)
                                .expect("Out of bounds read")
                                .to_le_bytes();
                            for i in 0..byte_size {
                                word[i as usize] = value;
                            }
                            memory
                                .set_word(dst_word, u32::from_le_bytes(word))
                                .expect("Out of bounds write");
                        }
                    }
                    Op::MemoryCopy { dst_mem, src_mem } => {
                        assert_eq!(dst_mem, 0);
                        assert_eq!(src_mem, 0);

                        let dst = t.get_reg_relative_u32(inputs[0].clone());
                        let src = t.get_reg_relative_u32(inputs[1].clone());
                        let size = t.get_reg_relative_u32(inputs[2].clone());
                        let remaining = size % 4;

                        let mut memory = t.i.get_mem();
                        // Load the entire thing into memory, this is the easiest way to
                        // handle overlapping copies.
                        let mut data = memory
                            .read_contiguous_bytes(src, size)
                            .expect("Out of bounds read");
                        if remaining > 0 {
                            let last_word = data.pop().unwrap();
                            // Zero the bytes that were not to be copied.
                            let mask = !(!0u32 << (remaining * 8));
                            let last_word = last_word & mask;

                            // Destination byte address where remaining bytes start.
                            let dst_start = dst + size - remaining;
                            let byte_offset = dst_start % 4;
                            let dst_word_addr = dst_start & !0x3;

                            // How many remaining bytes fit in the first destination word?
                            let first_chunk = remaining.min(4 - byte_offset);

                            // Write first chunk at the correct byte offset within the word.
                            let lshift = byte_offset * 8;
                            let chunk_mask = !(!0u32 << (first_chunk * 8));
                            let old_value =
                                memory.get_word(dst_word_addr).expect("Out of bounds read");
                            let new_value = (old_value & !(chunk_mask << lshift))
                                | ((last_word & chunk_mask) << lshift);
                            memory
                                .set_word(dst_word_addr, new_value)
                                .expect("Out of bounds write");

                            if first_chunk < remaining {
                                // Remaining bytes spill into the next word.
                                let second_chunk = remaining - first_chunk;
                                let shifted_data = last_word >> (first_chunk * 8);
                                let chunk_mask2 = !(!0u32 << (second_chunk * 8));
                                let old_value2 = memory
                                    .get_word(dst_word_addr + 4)
                                    .expect("Out of bounds read");
                                let new_value2 =
                                    (old_value2 & !chunk_mask2) | (shifted_data & chunk_mask2);
                                memory
                                    .set_word(dst_word_addr + 4, new_value2)
                                    .expect("Out of bounds write");
                            }
                        }
                        memory
                            .write_contiguous(dst, &data)
                            .expect("Out of bounds write");
                    }
                    Op::TableGet { table } => {
                        assert_eq!(inputs[0].len(), 1);
                        let index = t.get_reg_relative_u32(inputs[0].clone());

                        let table =
                            TableAccessor::new(t.i.module.tables[table as usize], &mut t.i.ram);
                        let entry = table
                            .get_entry(index)
                            .expect("TableGet: index out of bounds");

                        let output_reg = output.unwrap();
                        t.set_reg_relative_range(output_reg, &entry);
                    }
                    Op::TableSet { table } => {
                        assert_eq!(inputs[0].len(), 1);
                        let index = t.get_reg_relative_u32(inputs[0].clone());
                        let value = t
                            .get_reg_relative_range(inputs[1].clone())
                            .collect_array()
                            .unwrap();

                        let mut table =
                            TableAccessor::new(t.i.module.tables[table as usize], &mut t.i.ram);
                        table
                            .set_entry(index, value)
                            .expect("TableSet: index out of bounds");
                    }
                    Op::RefFunc { function_index } => {
                        let func_type = t.i.module.get_func_type(function_index).unique_id;
                        let frame_size = t.i.func_stack_sizes[function_index as usize];
                        let addr = t.i.labels[&func_idx_to_label(function_index)].pc;

                        t.set_reg_relative_range(output.unwrap(), &[func_type, frame_size, addr]);
                    }
                    Op::RefNull { .. } => {
                        t.set_reg_relative_range(output.unwrap(), &NULL_REF);
                    }
                    Op::RefIsNull => {
                        let mut input = inputs[0].clone();
                        let output = output.unwrap();

                        // Read the address part of the reference struct
                        input.start += FunctionRef::<S>::FUNC_ADDR as u32;
                        let addr = t.get_reg_relative_u32(input);

                        t.set_reg_relative_u32(
                            output,
                            if addr == NULL_REF[FunctionRef::<S>::FUNC_ADDR] {
                                1
                            } else {
                                0
                            },
                        );
                    }
                    _ => todo!("Unsupported WASM operator: {op:?}"),
                },
                Directive::AllocateFrameI {
                    target_frame,
                    result_ptr,
                } => {
                    let frame_size = t.i.labels[&target_frame].frame_size.unwrap();
                    let ptr = t.i.allocate(frame_size);
                    t.set_reg_relative_u32(result_ptr..result_ptr + 1, ptr);
                }
                Directive::AllocateFrameV {
                    frame_size,
                    result_ptr,
                } => {
                    let frame_size = t.get_reg_relative_u32(frame_size..frame_size + 1);
                    let ptr = t.i.allocate(frame_size);
                    t.set_reg_relative_u32(result_ptr..result_ptr + 1, ptr);
                }
                Directive::Copy {
                    src_word,
                    dest_word,
                } => {
                    t.copy_reg_range_relative(src_word..src_word + 1, dest_word..dest_word + 1);
                }
                Directive::CopyIntoFrame {
                    src_word,
                    dest_frame,
                    dest_word,
                } => {
                    t.copy_reg_into_frame(src_word, dest_frame, dest_word);
                }
                Directive::RwCall {
                    target,
                    new_frame_offset,
                    saved_ret_pc,
                    saved_caller_fp,
                } => {
                    let prev_pc = t.i.pc;
                    t.i.pc = t.i.labels[&target].pc;
                    should_inc_pc = false;

                    // Push the new function id for instrumentation
                    t.i.call_stack.push(t.i.addr_to_func_id[&t.i.pc]);

                    let prev_fp = t.i.fp;
                    t.i.fp += new_frame_offset;

                    t.set_reg_relative_u32(saved_ret_pc..saved_ret_pc + 1, prev_pc + 1);
                    t.set_reg_relative_u32(saved_caller_fp..saved_caller_fp + 1, prev_fp);
                }
                Directive::RwCallIndirect {
                    target_pc,
                    new_frame_offset,
                    saved_ret_pc,
                    saved_caller_fp,
                } => {
                    let prev_pc = t.i.pc;
                    t.i.pc = t.get_reg_relative_u32(target_pc..target_pc + 1);
                    should_inc_pc = false;

                    t.i.call_stack.push(t.i.addr_to_func_id[&t.i.pc]);

                    let prev_fp = t.i.fp;
                    t.i.fp += new_frame_offset;

                    t.set_reg_relative_u32(saved_ret_pc..saved_ret_pc + 1, prev_pc + 1);
                    t.set_reg_relative_u32(saved_caller_fp..saved_caller_fp + 1, prev_fp);
                }
                Directive::WomCall {
                    target,
                    new_frame_ptr,
                    saved_ret_pc,
                    saved_caller_fp,
                } => {
                    let prev_pc = t.i.pc;
                    t.i.pc = t.i.labels[&target].pc;
                    should_inc_pc = false;

                    t.i.call_stack.push(t.i.addr_to_func_id[&t.i.pc]);

                    let prev_fp = t.i.fp;
                    t.i.fp = t.get_reg_relative_u32(new_frame_ptr..new_frame_ptr + 1);

                    t.set_reg_relative_u32(saved_ret_pc..saved_ret_pc + 1, prev_pc + 1);
                    t.set_reg_relative_u32(saved_caller_fp..saved_caller_fp + 1, prev_fp);
                }
                Directive::WomCallIndirect {
                    target_pc,
                    new_frame_ptr,
                    saved_ret_pc,
                    saved_caller_fp,
                } => {
                    let prev_pc = t.i.pc;
                    t.i.pc = t.get_reg_relative_u32(target_pc..target_pc + 1);
                    should_inc_pc = false;

                    t.i.call_stack.push(t.i.addr_to_func_id[&t.i.pc]);

                    let prev_fp = t.i.fp;
                    t.i.fp = t.get_reg_relative_u32(new_frame_ptr..new_frame_ptr + 1);

                    t.set_reg_relative_u32(saved_ret_pc..saved_ret_pc + 1, prev_pc + 1);
                    t.set_reg_relative_u32(saved_caller_fp..saved_caller_fp + 1, prev_fp);
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
                        .map(|addr| t.get_reg_relative_u32(addr..addr + 1))
                        .collect_vec();
                    let mut accessor = if let Some(mem) = t.i.module.memory {
                        Some(MemoryAccessor::new(mem, &mut t.i.ram))
                    } else {
                        None
                    };
                    let result =
                        t.i.external_functions
                            .call(module, function, &args, &mut accessor);
                    match result {
                        ExternalCallResult::Exit(code) => return Some(code),
                        ExternalCallResult::Values(values) => {
                            for (value, output) in
                                values.into_iter().zip_eq(outputs.into_iter().flatten())
                            {
                                t.set_reg_relative_u32(output..output + 1, value);
                            }
                        }
                    }
                }
                Directive::JumpAndActivateFrame {
                    target,
                    new_frame_ptr,
                    saved_caller_fp,
                } => {
                    t.i.pc = t.i.labels[&target].pc;
                    should_inc_pc = false;

                    let prev_fp = t.i.fp;
                    t.i.fp = t.get_reg_relative_u32(new_frame_ptr..new_frame_ptr + 1);

                    if let Some(saved_caller_fp) = saved_caller_fp {
                        t.set_reg_relative_u32(saved_caller_fp..saved_caller_fp + 1, prev_fp);
                    }
                }
                Directive::JumpIf { target, condition } => {
                    let target = t.i.labels[&target].pc;
                    let cond = t.get_reg_relative_u32(condition..condition + 1);
                    if cond != 0 {
                        t.i.pc = target;
                        should_inc_pc = false;
                    }
                }
                Directive::JumpIfZero { target, condition } => {
                    let target = t.i.labels[&target].pc;
                    let cond = t.get_reg_relative_u32(condition..condition + 1);
                    if cond == 0 {
                        t.i.pc = target;
                        should_inc_pc = false;
                    }
                }
                Directive::Jump { target } => {
                    t.i.pc = t.i.labels[&target].pc;
                    should_inc_pc = false;
                }
                Directive::JumpOffset { offset } => {
                    let offset = t.get_reg_relative_u32(offset..offset + 1);
                    // Offset starts with 0, so we don't prevent the natural increment of the PC.
                    t.i.pc += offset;
                }
                Directive::Trap { reason } => {
                    panic!("Trap encountered: {reason:?}");
                }
            }

            t.print_trace();

            if should_inc_pc {
                t.i.pc += 1;
            }

            cycles += 1;
        };

        if final_fp == 0 {
            log::info!("Program terminated successfully with cycles: {cycles}.");
        } else {
            log::info!("Program terminated with cycles: {cycles}, final frame pointer: {final_fp}");
        }
        None
    }

    fn allocate(&mut self, size: u32) -> u32 {
        self.regs.allocate(size)
    }
}

mod trace {
    use itertools::Itertools;

    use crate::interpreter::{ExternalFunctions, Interpreter, RegisterValue};
    use std::{fmt::Display, ops::Range};

    pub struct Tracer<'a, 'b, E: ExternalFunctions> {
        pub i: &'a mut Interpreter<'b, E>,
        original_pc: u32,
        original_fp: u32,
        reads: Vec<ReadOp>,
        writes: Vec<WriteOp>,
    }

    impl<'a, 'b, E: ExternalFunctions> Tracer<'a, 'b, E> {
        pub fn new(i: &'a mut Interpreter<'b, E>) -> Tracer<'a, 'b, E> {
            Tracer {
                original_pc: i.pc,
                original_fp: i.fp,
                i,
                reads: Vec::new(),
                writes: Vec::new(),
            }
        }

        pub fn get_reg_relative_u32(&mut self, addr: Range<u32>) -> u32 {
            assert_eq!(addr.len(), 1, "Expected a single address range");
            self.get_reg(addr.start)
        }

        pub fn get_reg_relative_u64(&mut self, addr: Range<u32>) -> u64 {
            assert_eq!(addr.len(), 2, "Expected a single address range");
            let low = self.get_reg(addr.start);
            let high = self.get_reg(addr.start + 1);
            (low as u64) | ((high as u64) << 32)
        }

        pub fn get_reg_relative_range(
            &mut self,
            addr: Range<u32>,
        ) -> impl Iterator<Item = u32> + '_ {
            addr.map(|i| self.get_reg(i))
        }

        pub fn copy_reg_range_relative(&mut self, src: Range<u32>, dest: Range<u32>) {
            self.copy_reg_range(src, self.i.fp, dest);
        }

        pub fn copy_reg_into_frame(&mut self, src: u32, dest_frame: u32, dest: u32) {
            let target_fp = self.get_reg(dest_frame);
            self.copy_reg_range(src..src + 1, target_fp, dest..dest + 1);
        }

        pub fn set_reg_relative_u32(&mut self, addr: Range<u32>, value: u32) {
            assert_eq!(addr.len(), 1, "Expected a single address range");
            self.set_reg(addr.start, value);
        }

        pub fn set_reg_relative_u64(&mut self, addr: Range<u32>, value: u64) {
            self.set_reg_relative_range(addr, &[value as u32, (value >> 32) as u32]);
        }

        pub fn set_reg_relative_range(&mut self, addr: Range<u32>, values: &[u32]) {
            assert_eq!(
                addr.len(),
                values.len(),
                "Address range and values length mismatch"
            );
            for (addr, &value) in addr.zip(values.iter()) {
                self.set_reg(addr, value);
            }
        }

        pub fn set_reg_relative_range_future(&mut self, addr: Range<u32>) {
            for i in addr {
                self.i.regs.set_future(self.i.fp + i);
            }
        }

        pub fn print_trace(&self) {
            if !self.i.trace_enabled {
                return;
            }

            print!(
                "{} ({}): {}",
                self.i.call_stack.iter().format(","),
                self.original_pc,
                self.i.flat_program[self.original_pc as usize],
            );

            if !(self.reads.is_empty() && self.writes.is_empty()) {
                print!(" ({}", self.reads.iter().format(" "));
                if !self.writes.is_empty() {
                    if !self.reads.is_empty() {
                        print!(" | ");
                    }
                    print!(
                        "{}",
                        self.writes
                            .iter()
                            .map(|w| DisplayWriteOp {
                                original_fp: self.original_fp,
                                write_op: w
                            })
                            .format(" ")
                    );
                }
                print!(")");
            }

            println!();
        }

        pub fn reset(&mut self) {
            self.original_pc = self.i.pc;
            self.original_fp = self.i.fp;
            self.reads.clear();
            self.writes.clear();
        }

        fn get_reg(&mut self, offset: u32) -> u32 {
            let addr = self.i.fp + offset;
            let value = self.i.regs.get(addr).as_concrete();
            self.reads.push(ReadOp {
                addr: offset,
                value: RegisterValue::Concrete(value),
            });
            value
        }

        fn set_reg(&mut self, offset: u32, value: u32) {
            let addr = self.i.fp + offset;
            self.i.regs.set(addr, value);
            self.writes.push(WriteOp {
                offset,
                fp: self.i.fp,
                value: RegisterValue::Concrete(value),
            });
        }

        fn copy_reg_range(
            &mut self,
            src_offset: Range<u32>,
            dest_fp: u32,
            dest_offset: Range<u32>,
        ) {
            let src_addr = (src_offset.start + self.i.fp)..(src_offset.end + self.i.fp);
            let dest_addr = (dest_offset.start + dest_fp)..(dest_offset.end + dest_fp);
            self.i.regs.copy_range(src_addr.clone(), dest_addr.clone());

            for (src_offset, dest_addr) in src_offset.zip_eq(dest_addr) {
                let value = self.i.regs.get(dest_addr);
                self.reads.push(ReadOp {
                    addr: src_offset,
                    value,
                });
                self.writes.push(WriteOp {
                    offset: dest_addr - dest_fp,
                    fp: dest_fp,
                    value,
                });
            }
        }
    }

    struct ReadOp {
        addr: u32,
        value: RegisterValue,
    }

    impl Display for ReadOp {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "r:{}={}", self.addr, self.value)
        }
    }

    struct WriteOp {
        fp: u32,
        offset: u32,
        value: RegisterValue,
    }

    struct DisplayWriteOp<'a> {
        original_fp: u32,
        write_op: &'a WriteOp,
    }

    impl Display for DisplayWriteOp<'_> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if self.original_fp == self.write_op.fp {
                write!(f, "w:{}={}", self.write_op.offset, self.write_op.value)
            } else {
                write!(
                    f,
                    "w:{}[{}]={}",
                    self.write_op.fp, self.write_op.offset, self.write_op.value
                )
            }
        }
    }
}

pub struct MemoryAccessor<'a> {
    segment: Segment,
    ram: &'a mut Ram,
    byte_size: u32,
}

#[derive(Debug)]
pub enum MemoryAccessError {
    // accessed address and current memory size
    OutOfBounds(u32, u32),
}

impl<'a> MemoryAccessor<'a> {
    fn new(segment: Segment, ram: &'a mut Ram) -> Self {
        let byte_size = ram.get(segment.start) * WASM_PAGE_SIZE;
        MemoryAccessor {
            segment,
            ram,
            byte_size,
        }
    }

    fn get_max_num_pages(&self) -> u32 {
        self.ram.get(self.segment.start + 4)
    }

    fn set_num_pages(&mut self, num_pages: u32) {
        self.ram.set(self.segment.start, num_pages);
        self.byte_size = num_pages * WASM_PAGE_SIZE;
    }

    fn get_size(&self) -> u32 {
        self.byte_size
    }

    pub fn get_word(&self, byte_addr: u32) -> Result<u32, MemoryAccessError> {
        assert_eq!(byte_addr % 4, 0, "Address must be word-aligned");
        if byte_addr >= self.get_size() {
            return Err(MemoryAccessError::OutOfBounds(byte_addr, self.get_size()));
        }
        let ram_addr = self.segment.start + 8 + byte_addr;
        let value = self.ram.get(ram_addr);
        Ok(value)
    }

    pub fn set_word(&mut self, byte_addr: u32, value: u32) -> Result<(), MemoryAccessError> {
        assert_eq!(byte_addr % 4, 0, "Address must be word-aligned");
        if byte_addr >= self.get_size() {
            return Err(MemoryAccessError::OutOfBounds(byte_addr, self.get_size()));
        }
        let ram_addr = self.segment.start + 8 + byte_addr;
        self.ram.set(ram_addr, value);
        Ok(())
    }

    fn write_contiguous(&mut self, byte_addr: u32, data: &[u32]) -> Result<(), MemoryAccessError> {
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
    fn read_contiguous_bytes(
        &self,
        byte_addr: u32,
        num_bytes: u32,
    ) -> Result<Vec<u32>, MemoryAccessError> {
        let num_words = num_bytes.div_ceil(4);
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

struct TableAccessor<'a> {
    segment: Segment,
    ram: &'a mut Ram,
    size: u32,
}

impl<'a> TableAccessor<'a> {
    fn new(segment: Segment, ram: &'a mut Ram) -> Self {
        let size = ram.get(segment.start);
        TableAccessor { segment, ram, size }
    }

    /// Returns the size of the table in number of elements.
    fn _get_size(&self) -> u32 {
        self.size
    }

    fn _get_max_size(&self) -> u32 {
        self.ram.get(self.segment.start + 4)
    }

    fn get_entry(&self, index: u32) -> Result<[u32; 3], ()> {
        if index >= self.size {
            return Err(());
        }
        let base_addr = self.segment.start + 8 + index * 12; // Each entry is 3 u32s (12 bytes)
        let type_idx = self.ram.get(base_addr);
        let frame_size = self.ram.get(base_addr + 4);
        let pc = self.ram.get(base_addr + 8);
        Ok([type_idx, frame_size, pc])
    }

    fn set_entry(&mut self, index: u32, value: [u32; 3]) -> Result<(), ()> {
        if index >= self.size {
            return Err(());
        }
        let base_addr = self.segment.start + 8 + index * 12; // Each entry is 3 u32s (12 bytes)
        self.ram.set(base_addr, value[0]);
        self.ram.set(base_addr + 4, value[1]);
        self.ram.set(base_addr + 8, value[2]);
        Ok(())
    }
}
