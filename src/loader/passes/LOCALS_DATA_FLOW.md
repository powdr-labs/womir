# Locals Data Flow Pass

**Source:** `locals_data_flow.rs`

**Input:** `BlockTree` (normalized block tree from parsing)
**Output:** `LiftedBlockTree` (block tree with explicit local variable flow)

## Purpose

In WASM, local variables are implicit mutable state that can flow freely in and
out of blocks without being declared in the block's type. This pass makes that
flow explicit: for every block, it computes which locals must be provided as
inputs and which are produced as outputs, so that later passes can treat blocks
as pure functions of their inputs.

After this pass, local variables are no longer "magic" — they are just
additional block inputs and outputs alongside the stack values declared in the
block's interface type.

## What It Computes

For each block, the pass fills in three sets:

### `input_locals: BTreeSet<u32>`

The set of local indices that the block reads (directly or through nested
blocks/breaks) before any internal write. These locals must be provided to the
block as inputs, in addition to its stack parameters.

### `output_locals: BTreeSet<u32>` (blocks only)

The set of local indices that the block's break instructions write. Since the
block tree pass guarantees all blocks are exited via breaks, these represent the
locals modified by the block that are visible to the parent scope.

### `carried_locals: BTreeSet<u32>` (loops only)

The set of local indices that are carried across loop iterations. When a break
targets a loop (i.e., continues to the next iteration), any locals it modifies
must be provided as loop inputs on every iteration.

## Example

Consider this WASM function:
```wasm
(func (param $x i32) (result i32)
    (local $acc i32)
    (local.set $acc (i32.const 0))
    (block $exit (result i32)
        (loop $loop
            ;; acc = acc + x
            (local.set $acc (i32.add (local.get $acc) (local.get $x)))
            ;; if acc > 100, break with acc
            (br_if $exit (i32.gt_s (local.get $acc) (i32.const 100)))
            ;; continue loop
            (br $loop)
        )
        (unreachable)
    )
)
```

After lifting, the block and loop annotations would be:
- **$exit block:** `input_locals = {$acc, $x}`, `output_locals = {$acc}`
  (break to $exit carries $acc)
- **$loop:** `input_locals = {$acc, $x}`, `carried_locals = {$acc}`
  (break back to $loop carries $acc)

The key insight is that `$x` is read inside the loop but never written, so it
appears as an input at every level. `$acc` is both read and written, so it
appears as both an input and a carried/output local.

## Algorithm

The pass works by iterating over each block until a fixed point is reached:

1. **Push the block onto a control stack.** The control stack tracks what
   locals each nesting level expects from breaks targeting it.

2. **Scan the block's elements:**
   - `local.get` → Mark the local as an input of the current block.
   - `local.set` / `local.tee` → Mark the local as an output of the current
     scope (tracked in `local_outputs` on the control stack entry).
   - `br` / `br_if` / `br_if_zero` / `br_table` → Process the break target:
     all locals output by scopes up to the target depth, plus all carried
     locals of intervening loops, are added as break locals for the target.
   - Nested blocks → Recurse; the sub-block's `input_locals` become inputs of
     the current block, and its `output_locals` become outputs of the current
     scope.

3. **Pop the block from the control stack** and assemble the final
   `input_locals`, `output_locals`, and `carried_locals`.

4. **Repeat until stable.** If any set grew during the scan, the block is
   reprocessed. This handles cases where a break target's locals requirements
   propagate to inner blocks that didn't know about them yet.

## The Control Stack

Each entry in the control stack tracks:

- `old_break_locals`: The break locals known from the previous iteration (for
  convergence checking).
- `new_break_locals`: The break locals discovered during the current iteration.
- `carried_locals`: For loops, the locals that must be carried across
  iterations.
- `local_outputs`: The locals written (via `local.set`/`local.tee`) at this
  scope level.

## Design Notes

- The fixed-point iteration is necessary because a break can target an outer
  block, and the locals it requires may depend on locals computed by other
  breaks at different nesting levels. Each iteration propagates this information
  one level further.

- The sets are `BTreeSet<u32>` for deterministic ordering, which ensures that
  locals are always laid out in the same order in the block interface.

- After this pass, every local variable reference (`local.get`, `local.set`)
  still exists in the instruction stream. They will be resolved into DAG node
  references by the DAG construction pass.
