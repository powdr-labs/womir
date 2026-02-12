# Liveness Analysis Pass

**Source:** `liveness_dag.rs`

**Input:** `BlocklessDag` (from the common pipeline)
**Output:** `LivenessDag` (same DAG structure, annotated with `Liveness` data per block)

## Purpose

The liveness analysis pass takes the blockless DAG produced by the common pipeline and
annotates it with information about when each value is last used. This information is
essential for the register allocation pass that follows, enabling it to reuse registers
once their values are no longer needed.

## What It Computes

For each block (the function body and each loop body), the pass produces a `Liveness`
struct containing:

### `last_usage`: HashMap<(node_index, output_index), node_index>

Maps each value (identified by its producing node and output index) to the index of the
last node that reads it. This tells the register allocator exactly when a register can
be freed.

For example, if node 3 produces a value at output 0, and the last node that uses it is
node 7, then `last_usage[(3, 0)] = 7`. After node 7, the register holding this value
can be reused by another value.

Values that are never used by any other node have their last usage set to their own
node index (i.e., they are dead immediately after being produced).

### `redirected_inputs`: Vec<u32>

A sorted, deduplicated list of loop input indices that are simply forwarded unchanged
to the next iteration. This is an optimization hint for register allocation: if a loop
input is always passed through without modification, the register allocator can keep it
in the same register across all iterations, avoiding unnecessary copies at each loop
back-edge.

## Algorithm

The pass does a single forward traversal over the nodes in each block:

1. **Forward scan:** For each node, iterate over its inputs. If an input references
   another node's output, update `last_usage` for that output to the current node index.
   Also initialize each node's own outputs with `last_usage = current_index` (dead by
   default).

2. **Recursive processing of loops:** When a `Loop` operation is encountered, the pass
   recurses into the loop's sub-DAG. Before recursing, it sets up a control stack entry
   to track input redirection.

3. **Input redirection tracking:** For loop blocks, the pass tracks which inputs are
   simply forwarded as-is to the next iteration. It does this by examining every break
   instruction that targets the loop and checking whether each break input is a direct
   reference to the corresponding loop input (node 0). The tracking accounts for nested
   loops by mapping input indices through the control stack.

## Control Stack

The pass maintains a `VecDeque<ControlStackEntry>` to track nested loop contexts:

- `is_input_redirected: Vec<bool>` — One flag per loop input, initially all `true`.
  Set to `false` when any break to this loop provides a value other than the
  corresponding input passed through unchanged.

- `input_map: HashMap<u32, u32>` — Maps input indices of the current loop to
  output indices of the parent block's input node. This is needed to trace redirected
  inputs through nested loops. For example, if loop input 2 comes from the parent
  block's input 5, then `input_map[2] = 5`.

## Design Notes

- The liveness information is conservative (pessimistic): `last_usage` reflects the
  last usage across *all* control flow paths, not just the path currently being taken.
  A TODO in the code notes that per-path liveness could yield better register allocation.

- A TODO also suggests that this pass could potentially be merged with register
  allocation itself, using a bottom-up traversal similar to the WOM flattening pass.

- The pass handles all break variants (`Br`, `BrIf`, `BrIfZero`, `BrTable`) when
  checking input redirection. For conditional breaks, only the non-condition inputs
  are checked. For `BrTable`, each target's input permutation is respected.
