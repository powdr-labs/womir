use std::collections::HashMap;

use wasmparser::Operator as Op;

use crate::loader::flattening::{Directive, WriteOnceASM};

pub fn link<'a>(
    program: &[WriteOnceASM<'a>],
    init_pc: u32,
) -> (
    Vec<Directive<'a>>,
    HashMap<u32, u32>,
    HashMap<String, (u32, Option<u32>)>,
) {
    let mut pc: u32 = init_pc;

    let nop = Directive::WASMOp {
        op: Op::Nop,
        inputs: vec![],
        output: None,
    };

    let mut flat_program = vec![nop];

    let mut function_pcs = HashMap::new();
    let mut labels = HashMap::new();
    for fun in program {
        function_pcs.insert(fun.func_idx, pc);
        flat_program.extend(
            fun.directives
                .clone()
                .into_iter()
                .filter(|d| !matches!(d, Directive::Label { .. })),
        );
        for instr in &fun.directives {
            if let Directive::Label { id, frame_size } = instr {
                labels.insert(id.clone(), (pc, frame_size.clone()));
            } else {
                pc += 1;
            }
        }
    }
    (flat_program, function_pcs, labels)
}
