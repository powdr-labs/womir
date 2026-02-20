# Dangling Removal Pass

**Source:** `dag/dangling_removal.rs`

**Input:** `ConstDedupDag` (DAG after constant deduplication)
**Output:** `DanglingOptDag` (DAG with unused nodes and outputs removed)

## Purpose

This pass is a dead code elimination step for the DAG. It removes:

1. **Dangling nodes:** Nodes whose outputs are never used by any other node and
   that have no side effects (pure computations whose results are discarded).
2. **Unused block outputs:** Block outputs that are never consumed by the parent
   DAG.
3. **Unused block inputs:** Block inputs (for non-loop blocks) that are never
   read inside the block.

This pass is the natural cleanup after constant collapse and dedup, which may
leave constant nodes unreferenced. It also catches dead code patterns in the
original WASM.

## Algorithm

The pass operates in two phases, recursing into block sub-DAGs:

### Phase 1: Bottom-Up Usage Analysis

Starting from the last node and working backward:

1. **Recurse into blocks** to clean their sub-DAGs first.
2. **Check each node:** Is any of its outputs referenced by a later node? If
   not, and the node has no side effects, mark it for removal.
3. **Mark inputs as used:** For every node that is kept, mark all of its inputs'
   origins as used.

### Phase 2: Top-Down Removal and Remapping

Traverse the nodes forward:

1. **Remove marked nodes** from the node list.
2. **Remap references:** All `ValueOrigin` references in remaining nodes are
   adjusted to account for removed nodes (shifted indices) and removed block
   outputs (shifted output indices).
3. **Fix break inputs:** Break instructions targeting blocks that had outputs
   removed get their corresponding inputs removed as well.

## What Counts as Pure

A node is considered pure (safe to remove if unused) if its operation is one of:

- Constants (`i32.const`, `i64.const`, `f32.const`, `f64.const`, `v128.const`)
- Arithmetic, bitwise, and comparison operations
- Type conversion operations
- Reference operations (`ref.null`, `ref.is_null`, `ref.func`)
- `select` / `typed_select`
- `global.get` (reading state has no side effects)
- Memory and table reads (`i32.load`, `table.get`, `memory.size`, etc.)

Everything else is considered to have side effects and is never removed, even if
its outputs are unused. This includes stores, calls, `global.set`, table
mutations, and `unreachable`.

## Example

Before removal:
```
Node 0: Inputs            → [x]
Node 1: i32.const 5       → [five]        (unused after const collapse)
Node 2: i32.add           ← [(0,0), Constant(5)]  → [result]
Node 3: i32.const 99      → [ninety_nine] (never used at all)
Node 4: br 0              ← [(2,0)]
```

After removal, nodes 1 and 3 are pure and unused:
```
Node 0: Inputs            → [x]
Node 1: i32.add           ← [(0,0), Constant(5)]  → [result]
Node 2: br 0              ← [(1,0)]
```

All references are remapped: what was `(2,0)` becomes `(1,0)`.

## Block Output Pruning

When a block has outputs that the parent never reads, those outputs are removed
from the block node's `output_types`, and the corresponding break inputs are
removed from all breaks targeting that block. This cascading effect may make
additional nodes inside the block dangling, which are then caught by the
recursive application of the same pass inside the block.

## Block Input Pruning

For non-loop blocks, if an input is never read by any node inside the block, it
is removed from the `Inputs` node's output types and from the parent's block
node's inputs. Loop inputs are not pruned, as it would require adjusting all
back-edge breaks, which is more complex.

## Statistics

The pass returns:
- `removed_nodes`: Total pure nodes removed across all scopes.
- `removed_block_outputs`: Total unused block outputs pruned.
