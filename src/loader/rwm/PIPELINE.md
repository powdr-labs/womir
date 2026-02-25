# RWM Pipeline Overview

The read-write registers (RWM) pipeline converts a blockless DAG into a linear
sequence of assembly-like directives for machines with standard read-write registers.

## Stages

```
BlocklessDag                   (from common pipeline)
    │
    ▼
LivenessDag                    liveness_dag.rs
    │  Annotates each value with its last usage, and
    │  detects loop inputs that are forwarded unchanged.
    │
    ▼
RegisterAllocatedDag           register_allocation/
    │  Assigns concrete register numbers to all values,
    │  using liveness to reuse registers and heuristics
    │  to minimize copies.
    │
    ▼
PlainFlatAsm                   flattening/
    │  Linearizes the DAG into directives, emitting
    │  copies where register assignments don't match,
    │  and handling control flow, calls, and jumps.
    │
    ▼
DumbJumpOptFlatAsm             ../wom/dumb_jump_removal.rs
       Removes unconditional jumps to the immediately
       following label.
```

## Detailed Documentation

Each pass has its own documentation file:

- **[LIVENESS_ANALYSIS.md](LIVENESS_ANALYSIS.md)** — Forward analysis computing
  last-usage information and loop input redirection detection.

- **[REGISTER_ALLOCATION.md](REGISTER_ALLOCATION.md)** — Bottom-up optimistic
  register allocation with hint-based placement and occupation tracking.

- **[FLATTENING.md](FLATTENING.md)** — DAG linearization, parallel copy sequencing,
  and directive emission through the Settings trait.

- **[JUMP_REMOVAL.md](JUMP_REMOVAL.md)** — Peephole pass removing redundant
  unconditional jumps.

- **[CALLING_CONVENTION.md](CALLING_CONVENTION.md)** — Frame layout and calling
  convention for stacked read-write registers.

## Key Design Decisions

### Bottom-Up Register Allocation

The allocation runs in reverse node order. This means that by the time a value is
allocated, we already know where its consumers want it. The allocator can then
propose ("hint") register placements that align with consumer expectations, avoiding
copies. This is the main source of optimization in the pipeline.

### Nested Occupation Tracking

Loops create a nested scope for register allocation. The parent's occupied registers
are inherited as blocked ranges in the child tracker. After the loop body is
processed, registers used internally by the loop are projected back to the parent as
blocked, preventing the parent from placing long-lived values in registers that the
loop would overwrite.

### Parallel Copy Resolution

When multiple values need to move simultaneously (loop back-edges, function calls),
the flattening pass uses a graph-based algorithm to find a valid sequential ordering.
It handles trees with topological sorting, and breaks cycles with at most one
temporary register.

### Separation of Concerns

The pipeline cleanly separates liveness analysis, register allocation, and code
emission into distinct passes. This makes each pass simpler and easier to test in
isolation, at the cost of one extra traversal compared to a fused approach.
