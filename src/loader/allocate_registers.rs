//! This module does the infinite, write-once register allocation.
//!
//! TODO: I think the optimal register allocation algorithm looks something like
//! following the program bottom-up, branching on labels to all possible jumps
//! to it, which are necessarily above it, because we are processing a single
//! frame and only down jumps are allowed (loops are handled separately). We allocate
//! registers optimistically through the branches of the reverse execution paths,
//! and backtrack, PROLOG-style, when there is a conflict of the same register
//! being written twice on the same path. Thr fact that there are no back jumps
//! guarantees termination. The exact algorithm is not entirely clear to me.
//!
//! For now, I will just use a naive, top-down allocation, with a
//! different register for each write, and copy whenever necessary.

use std::marker::PhantomData;

use super::dag::Dag;

/// An assembly-like representation for a write-once memory machine.
pub struct WriteOnceASM<'a> {
    _a: PhantomData<&'a ()>,
}

pub fn allocate_registers<'a>(dag: Dag<'a>) -> WriteOnceASM<'a> {
    todo!()
}
