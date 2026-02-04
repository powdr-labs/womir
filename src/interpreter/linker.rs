use std::collections::HashMap;

use crate::loader::FunctionAsm;

pub struct Label<'a> {
    pub id: &'a str,
    pub frame_size: Option<u32>,
}

pub trait Directive: Clone {
    fn nop() -> Self;
    fn as_label(&self) -> Option<Label<'_>>;
}

#[derive(Debug)]
pub struct LabelValue {
    pub pc: u32,
    pub frame_size: Option<u32>,
    pub func_idx: Option<u32>,
}

pub fn link<D: Directive>(
    program: Vec<FunctionAsm<D>>,
    init_pc: u32,
) -> (Vec<D>, HashMap<String, LabelValue>) {
    let mut flat_program = vec![D::nop(); init_pc as usize];
    let mut labels = HashMap::new();

    for fun in program {
        let func_pc = flat_program.len() as u32;
        for d in fun.directives {
            match d.as_label() {
                Some(Label { id, frame_size }) => {
                    let pc = flat_program.len() as u32;
                    labels.insert(
                        id.to_string(),
                        LabelValue {
                            pc,
                            frame_size,
                            func_idx: (pc == func_pc).then_some(fun.func_idx),
                        },
                    );
                }
                None => {
                    flat_program.push(d);
                }
            }
        }
    }
    (flat_program, labels)
}
