# Register Allocation Pass

**Source:** `register_allocation/mod.rs`, `register_allocation/occupation_tracker.rs`

**Input:** `LivenessDag` (DAG annotated with liveness information)
**Output:** `AllocatedDag` (same DAG structure, annotated with `Allocation` data per block)

## Purpose

This pass assigns concrete register numbers to every value in the DAG. It uses the
liveness information from the previous pass to reuse registers once their values are
no longer needed. The allocator also applies heuristics to minimize the number of
register-to-register copies that the flattening pass will need to emit.

## Algorithm Overview

The allocation is done **bottom-up** (from the last node to the first), following
execution paths independently. This reverse traversal is key: by the time we allocate
a value, we already know where its consumers expect it to be, allowing us to propose
register assignments that avoid copies.

The main function is `optimistic_allocation`, which:

1. Fixes the function input registers at positions 0, 1, 2, ... (tightly packed
   according to word count per type).
2. Reserves space for the return address (RA) and frame pointer (FP) after
   `MAX(input_words, output_words)`, per the calling convention.
3. Runs the recursive bottom-up allocation on all nodes.

### Optimistic Allocation Strategy

The allocator is called "optimistic" because it tries to place values at hinted
locations (where their consumers expect them), falling back to the first available
gap only when the hint is unavailable. This two-phase approach avoids copies when
possible while guaranteeing correctness.

For each node, processed in reverse order:

- **Generic WASM operations:** Inputs and outputs are allocated wherever there is
  space. No special hinting is needed.

- **Function calls (Call/CallIndirect):** The allocator first determines the call
  frame start (the first register after all currently occupied ones). Then it tries
  to place each input at the exact register where the callee expects it, saving a
  copy if successful. Function outputs are pre-allocated at their natural position
  on the call frame.

- **Labels:** Outputs are allocated at whatever position is available. Break
  instructions targeting this label will try to match these positions.

- **Breaks (Br/BrIf/BrIfZero):** For each break input, the allocator tries to
  place it at the same register where the target (loop input, label output, or
  function return slot) expects it. This is the main copy-saving mechanism.

- **BrTable:** Each target's input permutation is processed like a regular break.
  The selector input is allocated separately.

- **Loops:** A child occupation tracker is created, inheriting the parent's blocked
  registers. Two heuristics minimize copies for loop inputs:
  1. If the loop input is the last usage of a value in the outer scope, reuse its
     register for the loop input.
  2. If the loop input is a "redirected input" (forwarded unchanged across
     iterations, as detected by the liveness pass), force the same register
     allocation, always saving a copy.

## Occupation Tracker

The `OccupationTracker` (`occupation_tracker.rs`) is the core data structure that
tracks which registers are occupied at each point in the program.

### Data Model

It maintains an `IntervalMap<usize, usize>` that maps **liveness ranges** (expressed
as node index ranges) to allocation entries. Each entry records:

- **`AllocationType`**: What kind of allocation it is:
  - `Value(ValueOrigin)` — A normal DAG value.
  - `FunctionFrame` — Space reserved for a callee's frame during a function call.
  - `SubBlockInternal` — Registers used inside a loop body, blocked at the parent level.
  - `BlockedRegistersAtParent` — Parent-level registers inherited by a sub-tracker.
  - `ExplicitlyBlocked` — Reserved registers (e.g., RA/FP slots).

- **`reg_range: Range<u32>`** — The register range this allocation occupies.

### Key Operations

- **`try_allocate(origin, size)`**: Allocates a value at the first available gap.
  Returns `None` if already allocated.

- **`try_allocate_with_hint(origin, hint)`**: Tries to place a value at a specific
  register range. If the hint is occupied, falls back to first-fit. Returns whether
  the hint was used.

- **`set_allocation(origin, range)`**: Forces an allocation at a specific range
  (used for fixed positions like function inputs).

- **`reserve_range(range)`**: Permanently blocks a register range (used for RA/FP).

- **`allocate_fn_call(call_index, output_sizes)`**: Reserves a function call frame
  starting after all currently occupied registers. Pre-allocates outputs at their
  natural positions on the frame.

- **`make_sub_tracker(sub_block_index, sub_liveness)`**: Creates a child tracker
  for a loop body, with all registers occupied at the loop's node index blocked.

- **`project_from_sub_tracker(sub_block_index, sub_tracker)`**: After processing a
  loop, blocks the registers that the loop body used internally, preventing the
  parent from overwriting them with values that need to survive across the loop.

### Gap-Finding Algorithm

When a hint is not available, `allocate_where_possible` uses a simple first-fit
strategy: it consolidates all occupied ranges into sorted, non-overlapping intervals,
then scans for the first gap large enough to fit the requested size. If no gap exists,
it allocates at the end.

## Statistics

The pass tracks `register_copies_saved`: the total number of word-level copies that
were avoided by successfully placing values at their hinted locations. This metric
is aggregated across all functions and reported at the end of compilation.

## Output

The `Allocation` struct stored in the output `AllocatedDag` contains:

- `nodes_outputs: BTreeMap<ValueOrigin, Range<u32>>` — The concrete register range
  assigned to each value.
- `occupation: Occupation` — The full register occupation map, used by the flattening
  pass to find free registers for temporary allocations.
- `labels: HashMap<u32, usize>` — Maps label IDs to their node indices, for quick
  lookup when processing breaks.
- `call_frames: HashMap<usize, u32>` — Maps call node indices to the start register
  of their callee frame.
