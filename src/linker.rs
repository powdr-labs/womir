use std::collections::HashMap;

use crate::loader::flattening::WriteOnceASM;

pub struct Label<'a> {
    pub id: &'a str,
    pub frame_size: Option<u32>,
}

pub trait Directive: Clone {
    fn nop() -> Self;
    fn as_label(&self) -> Option<Label>;
}

#[derive(Debug)]
pub struct LabelValue {
    pub pc: u32,
    pub frame_size: Option<u32>,
    pub func_idx: Option<u32>,
}

pub fn link<D: Directive>(
    program: &[WriteOnceASM<D>],
    init_pc: u32,
) -> (Vec<D>, HashMap<String, LabelValue>) {
    let mut pc: u32 = init_pc;

    let mut flat_program = vec![D::nop(); init_pc as usize];

    let mut labels = HashMap::new();
    for fun in program {
        let func_pc = pc;
        flat_program.extend(
            fun.directives
                .clone()
                .into_iter()
                .filter(|d| d.as_label().is_none()),
        );
        for instr in &fun.directives {
            if let Some(Label { id, frame_size }) = instr.as_label() {
                labels.insert(
                    id.to_string(),
                    LabelValue {
                        pc,
                        frame_size,
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
