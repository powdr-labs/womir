# Common Pipeline Overview

The common pipeline is the shared frontend that both the WOM and RWM backends
consume. It takes raw WebAssembly bytecode and progressively transforms it into
a blockless DAG — a flat, optimized, register-based intermediate representation
that is ready for backend-specific lowering.

## Stages

```
WASM bytecode
    │
    ▼
Unparsed                          (raw function body bytes)
    │
    ▼
BlockTree                         block_tree.rs
    │  Parses WASM operators into a tree of blocks and
    │  loops. Normalizes if-else into block+br_if,
    │  converts return into br, removes dead code, and
    │  inlines constant globals.
    │
    ▼
LiftedBlockTree                   locals_data_flow.rs
    │  Makes locals data flow explicit: exposes every
    │  local read/write as a block input or output, so
    │  later passes can treat locals like any other value.
    │
    ▼
PlainDag                          dag/mod.rs
    │  Builds a directed acyclic graph where nodes are
    │  operations and edges are values. The WASM stack
    │  and locals are fully resolved into node references.
    │
    ▼
ConstCollapsedDag                 dag/const_collapse.rs
    │  (Optional) Collapses constant values into the
    │  instructions that use them, if the target ISA
    │  supports immediate operands.
    │
    ▼
ConstDedupDag                     dag/const_dedup.rs
    │  Deduplicates identical constant definitions so
    │  each unique constant is defined at most once per
    │  scope.
    │
    ▼
DanglingOptDag                    dag/dangling_removal.rs
    │  Removes pure nodes whose outputs are never used.
    │  Also trims unused block inputs and outputs.
    │
    ▼
BlocklessDag                      blockless_dag.rs
       Flattens non-loop blocks into a single linear
       sequence with labels. Only loops retain their
       own sub-DAG. Forward-only jumps target labels;
       backward jumps target loop headers.
```

## What Happens After

The `BlocklessDag` is the handoff point to the backend pipelines:

- **WOM pipeline** (`src/loader/wom/`): Flattens the DAG into write-once
  register directives using frame allocation. See `wom/` for details.

- **RWM pipeline** (`src/loader/rwm/`): Performs liveness analysis, register
  allocation, and flattening into read-write register directives. See
  `rwm/PIPELINE.md` for details.

## Detailed Documentation

Each pass has its own documentation file:

- **[BLOCK_TREE.md](BLOCK_TREE.md)** — Parsing WASM operators into a
  normalized block tree with structural simplifications.

- **[LOCALS_DATA_FLOW.md](LOCALS_DATA_FLOW.md)** — Lifting locals into
  explicit block inputs and outputs.

- **[DAG_CONSTRUCTION.md](DAG_CONSTRUCTION.md)** — Building the value DAG from
  the lifted block tree, resolving the stack and locals.

- **[CONST_COLLAPSE.md](CONST_COLLAPSE.md)** — ISA-driven constant folding
  into immediate operands.

- **[CONST_DEDUP.md](CONST_DEDUP.md)** — Deduplicating identical constant
  nodes across scopes.

- **[DANGLING_REMOVAL.md](DANGLING_REMOVAL.md)** — Dead node elimination and
  unused output pruning.

- **[BLOCKLESS_DAG.md](BLOCKLESS_DAG.md)** — Flattening block structure into
  labels and converting to the blockless representation.

## Key Design Decisions

### DAG Over SSA

The IR uses a DAG (directed acyclic graph) rather than a traditional SSA form.
Each node represents an operation, each edge represents a value. Values are
identified by their origin: `(node_index, output_index)`. This is a natural fit
because WASM's structured control flow guarantees that non-loop blocks can be
inlined into the parent, producing a flat sequence of forward-only jumps.

### Locals Are Lifted Early

WASM locals act as implicit mutable state that crosses block boundaries. By
lifting them into explicit block inputs and outputs in the `LiftedBlockTree`
pass, all subsequent passes can treat the IR as purely value-based, with no
hidden state. This simplifies the DAG construction and all downstream
optimizations.

### Loops Are Special

Throughout the pipeline, loops receive special treatment:

- **Block tree:** Loops are wrapped in an outer block if they can fall through,
  ensuring loops are only exited via breaks.
- **DAG construction:** Loops create nested sub-DAGs with their own input
  nodes; breaks to a loop target its inputs (next iteration), while breaks to a
  block target its outputs.
- **Blockless DAG:** Only loops retain their own sub-DAG. Non-loop blocks are
  inlined into the parent frame with labels for jump targets.

This distinction reflects a fundamental property: blocks have forward-only
control flow (can be inlined), while loops have backward edges (need their own
frame).

### Optimization Order

The three DAG optimizations run in a specific order for good reason:

1. **Constant collapse** runs first because it changes reference inputs into
   inline constants, potentially making the original constant nodes unused.
2. **Constant dedup** runs second because collapse may have severed some
   references, leaving duplicate constants that can now be merged.
3. **Dangling removal** runs last as a cleanup pass, garbage-collecting any
   nodes that the previous passes made unreachable.
