# Flattening Pass

**Source:** `flattening/mod.rs`, `flattening/sequence_parallel_copies.rs`

**Input:** `AllocatedDag` (DAG with concrete register assignments)
**Output:** `FunctionAsm<S::Directive>` (linear sequence of assembly-like directives)

## Purpose

The flattening pass converts the DAG representation into a linear sequence of
instructions. By this point, all the hard decisions (register allocation, copy
minimization) have already been made. The flattening is a straightforward, linear
traversal that emits directives through the `rwm::Settings` trait.

## Algorithm

The pass does a forward traversal over the DAG nodes, processing each one into
directives:

### Node Types

- **Inputs:** At the function level, emits the function label (and an exported name
  alias if the function is exported). At loop level, emits nothing (the loop label
  is emitted by the parent Loop node).

- **Label:** Emits a label directive.

- **Loop:** Copies loop inputs to where the loop body expects them (if they are not
  already there), emits the loop label, then recursively processes the loop body.
  A control stack tracks the allocation context for each nesting level.

- **Br (unconditional break):** Emits the copies needed to place break inputs at
  their target locations, then emits a jump. Three kinds of targets:
  - **Forward label:** Jump to a label in the current block.
  - **Loop back-edge:** Jump to the loop's header label, with copies to set up
    the next iteration's inputs.
  - **Function return:** Copy outputs to the return slots, then emit a `return`
    instruction (which reads RA and FP from their known positions).

- **BrIf / BrIfZero (conditional break):** Combines a conditional jump with the
  break logic. The pass tries several strategies in order of preference:
  1. If the target is a plain jump (no copies needed) and the ISA supports the
     matching condition, emit a single conditional jump.
  2. If the ISA supports the inverse condition, emit: inverse-conditional-jump to
     continuation, then the full break code, then the continuation label.
  3. If only the matching condition is available, emit: conditional-jump to jump
     code, then jump to continuation, then jump code, then continuation label.

- **BrTable:** Handles multi-way branching. Emits a bounds check for the default
  case, then a relative jump (jump table) into per-target jump code. Targets that
  are plain jumps are inlined into the jump table; complex targets get an extra
  indirection through a local label.

- **Call:** For imported functions, emits a direct imported-call directive. For
  local functions, prepares the call frame: copies inputs to the expected positions,
  emits the call instruction (with frame offset, RA, and FP locations), then copies
  outputs from the return slots to where consumers expect them.

- **CallIndirect:** Like a normal call, but first loads the function reference from
  the table, checks the function type against the expected signature (trapping on
  mismatch), then emits an indirect call.

- **WASMOp:** Delegates directly to `emit_wasm_op` with the resolved input
  registers/constants and output register.

- **Unreachable:** Emits a trap.

## Parallel Copy Sequencing

A critical sub-problem in flattening is emitting register copies correctly when
multiple values need to move simultaneously (e.g., setting up a loop iteration's
inputs, or preparing function call arguments). The naive approach of emitting copies
one by one can fail when source and destination registers overlap.

### The Problem

Consider needing to move `r0 → r1` and `r1 → r0` (a swap). Doing them sequentially
would overwrite `r1` before reading it. More generally, the copy set forms a directed
graph that may contain:

1. **Trees:** Leaves are destination-only; root is source-only. Safe to copy in
   reverse topological order.
2. **Cycles:** Every register is both source and destination. Requires a temporary
   register to break the cycle.
3. **Cycles with attached trees:** A single cycle with trees branching off. The
   tree-pruning phase naturally breaks the cycle through source-swapping.

### The Algorithm (`sequence_parallel_copies.rs`)

**Phase 1 — Tree pruning:**
1. Find all "tree ends" (registers with no outgoing edges, i.e., destination-only).
2. For each tree end, emit the copy from its source and remove the edge.
3. Apply **source-swapping**: transfer the source's remaining outgoing edges to the
   just-written destination. This is the key insight — since the destination now
   holds the same value as the original source, it can serve as the source for
   remaining copies, potentially breaking a connected cycle.
4. If the original source now has no outgoing edges but has an incoming edge, it
   becomes a new tree end. Repeat until no tree ends remain.

**Phase 2 — Cycle breaking:**
1. The remaining graph consists only of pure cycles.
2. Pick a temporary register — either reuse a destination register from Phase 1
   (since it was already written and can serve double duty before Phase 1's copies
   execute), or allocate a new `Temp` register.
3. For each cycle: save one value to temp, rotate the rest, restore from temp.

**Output ordering:** Phase 2 copies are emitted first, then Phase 1 copies in
reverse. This ensures the temporary register is not overwritten by Phase 1 copies
before it is consumed by Phase 2.

### Correctness Guarantee

Every destination register appears exactly once (precondition). The algorithm
produces a valid sequential ordering that achieves the same effect as executing all
copies simultaneously. At most one temporary register is needed, and it is avoided
entirely when the copy graph is acyclic or has trees attached to cycles.

## Temporary Register Allocation

During flattening, some operations need temporary registers (e.g., loading a
function reference for indirect calls, or the temp register for parallel copies).
The `Context` struct provides `allocate_tmp_type` which:

1. Lazily computes the set of free register gaps at the current node by examining
   the occupation map from register allocation.
2. Allocates from the first gap that fits.
3. For function call nodes, can also allocate temporaries in the callee's frame
   space (after the calling convention prelude).

## Settings Trait

The flattening pass is parameterized by `rwm::Settings`, which provides all the
`emit_*` methods. This trait defines how each operation maps to the target ISA's
directives. The reference implementation is `GenericIrSetting` in
`src/interpreter/generic_ir.rs`.

Key emission methods used by flattening:
- `emit_label`, `emit_jump`, `emit_trap`
- `emit_copy` — Single-word register copy
- `emit_conditional_jump` — Jump on a boolean condition
- `emit_conditional_jump_cmp_immediate` — Jump on comparison with immediate (for BrTable bounds)
- `emit_relative_jump` — Jump by offset (for BrTable dispatch)
- `emit_return` — Function return (restores RA/FP)
- `emit_function_call`, `emit_indirect_call` — Local and indirect calls
- `emit_imported_call` — Imported (external) function call
- `emit_wasm_op` — Generic WASM instruction emission
