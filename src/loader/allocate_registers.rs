//! This module does the infinite, write-once register allocation.
//!
//! The algorithm requires multiple passes, and goes like this:
//!
//! Pass #1: we will flatten the blocks that belong in a single
//! frame, so that just loops will have independent DAGs.
//! Non-loop blocks will be merged into a single DAG, with labels
//! delimiting the jump points. One important property of this
//! structure is that jumps are never backwards.
//!
//! Pass #2: for each DAG/frame, we do a bottom-up traversal,
//! assigning registers to the labels outputs, matching with their
//! respective break inputs, and detect whether or not there is a
//! conflict, where multiple instructions would write to the same
//! register in the same execution path. In the end, we will have a
//! partial register assignment for some nodes, where conflicts for
//! break inputs are explicitly marked.
//!
//! Pass #3: we will do a top-down traversal of the DAG, completing
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
//! Pass #4: we flatten all the DAGs, loops included, into a single
//! assembly-like representation.

use std::marker::PhantomData;
use wasmparser::{Operator as Op, ValType};

use super::dag::{Dag, ValueOrigin};

/// An assembly-like representation for a write-once memory machine.
pub struct WriteOnceASM<'a> {
    _a: PhantomData<&'a ()>,
}

pub fn allocate_registers<'a>(dag: Dag<'a>) -> WriteOnceASM<'a> {
    todo!()
}

#[derive(Debug)]
struct BreakTarget {
    /// The frame depth to break to.
    relative_depth: u32,
    /// The label inside the target block/frame.
    label: u32,
}

#[derive(Debug)]
pub enum Operation<'a> {
    Inputs,
    WASMOp(Op<'a>),

    Label {
        /// This label is unique to this block/frame. A complete jump target
        /// will also include the depth of the frame stack.
        id: u32,
    },

    Loop {
        sub_dag: Dag<'a>,
        /// The possible break targets for this block, relative to the itself
        /// (i.e. 0 is itself, 1 is the parent block, 2 is the block above it, etc).
        break_targets: Vec<u32>,
    },

    // All the Br variations below are only used for jumps out of the current
    // block/frame.
    Br(BreakTarget),
    BrIf(BreakTarget),
    BrIfZero(BreakTarget),
    BrTable {
        targets: Vec<TableTarget<BreakTarget>>,
    },

    // All the Jump variations below are only used for jumps inside the current
    // block/frame.
    Jump(u32),
    JumpIf(u32),
    JumpIfZero(u32),
    JumpTable {
        targets: Vec<TableTarget<u32>>,
    },

    // The following other jump that doesn't fit above.
    IterateOrReturn {
        /// Maximum depth means return, otherwise iterate the loop at the given depth.
        depth: u32,
    },
}

#[derive(Debug)]
pub struct TableTarget<T> {
    pub target: T,
    /// For each of the nodes inputs, this is the permutation of the inputs that
    /// each break target will receive.
    pub input_permutation: Vec<u32>,
}

#[derive(Debug)]
pub struct Node<'a> {
    pub operation: Operation<'a>,
    pub inputs: Vec<ValueOrigin>,
    pub output_types: Vec<ValType>,
}

#[derive(Debug)]
pub struct BlocklessDag<'a> {
    pub nodes: Vec<Node<'a>>,
}
