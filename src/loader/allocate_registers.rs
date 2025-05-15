//! This module does the infinite, write-once register allocation.
//!
//! The algorithm requires multiple passes, and goes like this:
//!
//! Pass #1: for each DAG/frame, we do a bottom-up traversal,
//! assigning registers to the labels outputs, matching with their
//! respective break inputs, and detect whether or not there is a
//! conflict, where multiple instructions would write to the same
//! register in the same execution path. In the end, we will have a
//! partial register assignment for some nodes, where conflicts for
//! break inputs are explicitly marked.
//!
//! Pass #2: we will do a top-down traversal of the DAG, completing
//! the register assignment for the node outputs that were not
//! assigned (included the ones that triggered a conflict in the
//! previous pass). When we encounter a break, we copy the correct
//! output to the conflicted register just before the break. Since
//! the conflict was detected per execution path, we can be sure that
//! no register will be written to more than once in the same path.
//! If a break output was not conflicted, we can be sure that the
//! correct value is already in the expected register.
//!
//! TODO: this is still not perfectly optimal, since there might be
//! permutations of register assignments through different execution
//! paths that would avoid the need for some copies.
//!
//! Pass #3: we flatten all the DAGs, loops included, into a single
//! assembly-like representation.

use std::marker::PhantomData;
use wasmparser::{Operator as Op, ValType};

use super::blockless_dag::BlocklessDag;

/// An assembly-like representation for a write-once memory machine.
pub struct WriteOnceASM<'a> {
    _a: PhantomData<&'a ()>,
}

pub fn allocate_registers<'a>(dag: BlocklessDag<'a>) -> WriteOnceASM<'a> {
    todo!()
}
