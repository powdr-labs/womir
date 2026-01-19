//! This module flattens the DAG structure, generating an assembly-like representation.
//!
//! The algorithm is straightforward and linear, as most of the complexity was handled
//! in earlier passes (notably register allocation).

use std::sync::atomic::AtomicU32;

use crate::loader::{
    Module,
    rwm::{register_allocation::AllocatedDag, settings::Settings},
};

pub struct Asm<D> {
    pub func_idx: u32,
    pub directives: Vec<D>,
}

pub fn flatten_dag<'a, S: Settings<'a>>(
    s: &S,
    prog: &Module<'a>,
    label_gen: &AtomicU32,
    dag: AllocatedDag<'a>,
    func_idx: u32,
) -> Asm<S::Directive> {
    unimplemented!()
}
