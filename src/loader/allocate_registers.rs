use std::marker::PhantomData;

use super::dag::Dag;

/// An assembly-like representation for a write-once memory machine.
pub struct WriteOnceASM<'a> {
    _a: PhantomData<&'a ()>,
}

pub fn allocate_registers<'a>(dag: Dag<'a>) -> WriteOnceASM<'a> {
    todo!()
}
