# DAG Construction Pass

**Source:** `dag/mod.rs`

**Input:** `LiftedBlockTree` (block tree with explicit locals data flow)
**Output:** `Dag` (directed acyclic graph of value-producing nodes)

## Purpose

This pass eliminates the WASM stack and local variables entirely, replacing them
with a directed acyclic graph where every value has a single explicit origin.
Nodes in the graph are operations (WASM instructions, blocks, loops, breaks),
and edges are values flowing from producers to consumers. After this pass, the
IR is fully register-like — there is no stack, no locals, just values identified
by `(node_index, output_index)` pairs.

## Core Data Structures

### Node

Each node has:
- **`operation`**: What the node does (`Inputs`, `WASMOp`, `BrIfZero`,
  `BrTable`, or `Block`).
- **`inputs: Vec<NodeInput>`**: The values this node consumes. Each input is
  either a `Reference(ValueOrigin)` pointing to another node's output, or a
  `Constant(WasmValue)` (only after the constant collapse pass).
- **`output_types: Vec<ValType>`**: The types of values this node produces.

### ValueOrigin

A `(node_index, output_index)` pair identifying a specific output of a specific
node. This is the "register name" in the DAG world.

### Dag

A `Dag` is simply a `Vec<Node>`. Node 0 is always an `Inputs` node whose
outputs are the block's input values.

## Algorithm

The pass simulates WASM execution using two structures that track where each
value lives:

- **Stack** (`Vec<ValueOrigin>`): Mirrors the WASM operand stack, but instead
  of holding values, it holds references to the nodes that produced them.
- **Locals** (`Vec<Value>`): Maps each local index to either a `ValueOrigin`
  (if the local has been set) or `UnusedLocal` (if it has never been written).

The pass walks the instruction sequence in order. For each instruction:

1. **Stack/local manipulation** (`local.get`, `local.set`, `local.tee`,
   `drop`): Resolved purely by moving references between the stack and locals
   arrays. No DAG nodes are created.

2. **Break instructions** (`br`, `br_if`, `br_if_zero`, `br_table`): Pop the
   appropriate values from the stack and collect the required local values (as
   determined by the locals data flow pass). These become the break node's
   inputs. The break targets are looked up in a block stack to determine what
   types are expected.

3. **Regular WASM operations**: Pop inputs from the stack, create a new node,
   push the node's outputs onto the stack.

4. **Blocks and loops**: Recursively build a sub-DAG. The block's stack and
   local inputs (from the lifted block tree) become the inputs to the new
   sub-DAG. The block's outputs go back onto the parent's stack and locals.

## Example

Consider this WASM fragment (inside a function with `$x` as parameter 0):
```wasm
local.get $x      ;; push $x
i32.const 1       ;; push 1
i32.add           ;; pop both, push ($x + 1)
```

The resulting DAG nodes would be:

```
Node 0: Inputs                → outputs: [$x]
Node 1: WASMOp(i32.const 1)  → outputs: [1]
Node 2: WASMOp(i32.add)      ← inputs: [(0,0), (1,0)]
                              → outputs: [result]
```

`local.get` does not create a node — it just pushes `(0, 0)` onto the stack
(referring to the first output of the Inputs node). The `i32.add` node
references both the input parameter and the constant.

## Block Handling

Blocks in the DAG are represented as a single node with an embedded sub-DAG:

```
Node N: Block {
    kind: Block | Loop,
    sub_dag: Dag { nodes: [...] }
}
inputs: [stack values..., local values...]
output_types: [stack results..., local results...]
```

Inside the sub-DAG, node 0 (`Inputs`) provides the block's input values. Breaks
to the block provide the block's output values.

### Blocks vs. Loops

The key difference is what break targets mean:

- **Block:** A `br 0` targets the block's *outputs*. The break carries the
  values that become the block's results.
- **Loop:** A `br 0` targets the loop's *inputs*. The break carries the values
  that become the next iteration's inputs.

This means a block's outputs are determined by its breaks, while a loop's
inputs may be updated by breaks back to it.

## Unused Locals

When a local is read before being written (its initial value is used), the pass
materializes a default constant for it (0 for numeric types, `ref.null` for
reference types). This happens at the function level only — inside blocks,
attempting to read an uninitialized local triggers a panic, because the locals
data flow pass should have already ensured it is provided as a block input.

## Design Notes

- The pass produces a DAG, not a general graph, because WASM's structured
  control flow guarantees that non-loop value dependencies are always acyclic.
  Loops create nested sub-DAGs, so even loop back-edges don't introduce cycles
  at any single DAG level.

- Constants at this stage are represented as zero-input `WASMOp` nodes (e.g.,
  `WASMOp(i32.const 42)`). The constant collapse and dedup passes will later
  optimize them.

- The `BreakArgs` struct on the block stack tracks both the expected stack types
  and the expected local indices for each break target, combining the
  information from the block's interface type and the lifted locals data flow.
