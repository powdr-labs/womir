# Constant Collapse Pass

**Source:** `dag/const_collapse.rs`

**Input:** `PlainDag` (the DAG after construction)
**Output:** `ConstCollapsedDag` (same DAG, with some constant references replaced by inline constants)

## Purpose

This optional optimization pass identifies constant values that can be folded
into the instructions that consume them, eliminating the need for a separate
register to hold the constant. This is driven by the target ISA: if the ISA
supports immediate operands on certain instructions (e.g., RISC-V's `addi`),
the constant can be inlined directly.

## How It Works

The pass is gated by `Settings::get_const_collapse_processor()`. If the ISA
implementor returns `None`, no collapsing is performed and the DAG passes
through unchanged.

If a processor function is provided, the pass walks every `WASMOp` node in the
DAG and checks whether any of its inputs reference constant nodes. For each
such node, it calls the processor with the operator and a slice of
`MaybeConstant` values describing each input:

- **`NonConstant`**: The input is not a constant.
- **`ReferenceConstant { value, must_collapse }`**: The input references a
  constant node with a known value. The processor can set `must_collapse` to
  `true` to indicate the constant should be inlined.
- **`CollapsedConstant(value)`**: The input is already an inline constant
  (from a previous pass; not expected in the default pipeline).

When `must_collapse` is set to `true`, the pass replaces the `NodeInput::Reference`
with a `NodeInput::Constant`, severing the dependency on the constant node.

## Example

Before collapse:
```
Node 0: Inputs            → [x]
Node 1: i32.const 5       → [5]
Node 2: i32.add           ← [(0,0), (1,0)]   → [result]
```

If the ISA processor recognizes that `i32.add` with a constant second operand
can become an "add immediate" instruction, it sets `must_collapse = true` for
input 1. After collapse:

```
Node 0: Inputs            → [x]
Node 1: i32.const 5       → [5]        (may now be unused)
Node 2: i32.add           ← [(0,0), Constant(5)]   → [result]
```

Node 1 is now potentially dangling (no references to it). The dangling removal
pass will clean it up later.

## Recursion Into Blocks

The pass recurses into block sub-DAGs. For non-loop blocks, it propagates
knowledge of which block inputs are constants, so that constants flowing through
block boundaries can also be collapsed inside the block.

For loops, constant inputs are **not** propagated, because a loop input might be
constant on the first iteration but different on subsequent iterations (it could
be updated by a break back to the loop header). In practice, optimized WASM
rarely has constant loop inputs anyway.

## Statistics

The pass returns the total count of collapsed constants, which is aggregated in
`Statistics::constants_collapsed`.
