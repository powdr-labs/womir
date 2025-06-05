use std::collections::HashMap;

use wasmparser::Operator as Op;

use crate::loader::flattening::{Directive, WriteOnceASM};

pub struct LabelValue {
    pub pc: u32,
    pub frame_size: Option<u32>,
    pub func_idx: Option<u32>,
}

pub fn link<'a>(
    program: &[WriteOnceASM<'a>],
    init_pc: u32,
) -> (Vec<Directive<'a>>, HashMap<String, LabelValue>) {
    let mut pc: u32 = init_pc;

    let nop = Directive::WASMOp {
        op: Op::Nop,
        inputs: vec![],
        output: None,
    };

    let mut flat_program = vec![nop];

    let mut labels = HashMap::new();
    for fun in program {
        let func_pc = pc;
        flat_program.extend(
            fun.directives
                .clone()
                .into_iter()
                .filter(|d| !matches!(d, Directive::Label { .. })),
        );
        for instr in &fun.directives {
            if let Directive::Label { id, frame_size } = instr {
                labels.insert(
                    id.clone(),
                    LabelValue {
                        pc,
                        frame_size: frame_size.clone(),
                        func_idx: (pc == func_pc).then_some(fun.func_idx),
                    },
                );
            } else {
                pc += 1;
            }
        }
    }
    (flat_program, labels)
}
