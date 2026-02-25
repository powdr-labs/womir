# Constant Deduplication Pass

**Source:** `dag/const_dedup.rs`

**Input:** `ConstCollapsedDag` (DAG after constant collapse)
**Output:** `ConstDedupDag` (DAG with deduplicated constants)

## Purpose

After the DAG is constructed, the same constant value may be defined by multiple
independent nodes (e.g., two different `i32.const 0` instructions). This pass
deduplicates them: all references to a given constant value are remapped to
point to the first definition of that constant in the current scope.

This reduces the number of nodes in the DAG and, more importantly, saves
registers in the final output — without deduplication, each constant definition
would occupy its own register.

## Algorithm

The pass does a single forward traversal over the nodes, maintaining two maps:

### `const_to_origin: HashMap<WasmValue, Option<ValueOrigin>>`

Maps each known constant value to the node that defines it. The `Option` is
`Some(origin)` if the constant is defined at the current depth, or `None` if it
is known from an outer scope but not yet materialized at this depth.

### `origin_to_const: HashMap<ValueOrigin, WasmValue>`

The reverse map: for every node that defines a constant, records what constant
value it produces.

For each node:

1. **Remap inputs:** If an input references a node that produces a known
   constant, and a previous definition of that constant exists, redirect the
   input to the earlier definition.

2. **Record constants:** If the node itself defines a constant, add it to both
   maps. If a previous definition already exists, the node is now a duplicate
   (it will be cleaned up by the dangling removal pass).

3. **Recurse into blocks:** For non-loop blocks, the parent's constant
   knowledge is inherited. If a constant from the parent scope is needed inside
   the block, a new block input is added to thread it through.

4. **Loops start fresh:** Loop sub-DAGs start with empty maps, because
   constants should be redefined inside the loop rather than copied through the
   iteration interface (which would add unnecessary loop inputs).

## Example

Before deduplication:
```
Node 0: Inputs            → [x]
Node 1: i32.const 0       → [zero_a]
Node 2: i32.add           ← [(0,0), (1,0)]   → [x_plus_0]
Node 3: i32.const 0       → [zero_b]      (duplicate!)
Node 4: i32.sub           ← [(0,0), (3,0)]   → [x_minus_0]
```

After deduplication, node 4's input is remapped to node 1:
```
Node 0: Inputs            → [x]
Node 1: i32.const 0       → [zero]
Node 2: i32.add           ← [(0,0), (1,0)]   → [x_plus_0]
Node 3: i32.const 0       → [zero_b]      (now unreferenced)
Node 4: i32.sub           ← [(0,0), (1,0)]   → [x_minus_0]
```

Node 3 is now dangling and will be removed by the dangling removal pass.

## Cross-Block Deduplication

When a constant is defined in the parent scope and needed inside a child block,
the pass adds a new input to the block to thread the constant through, rather
than allowing the block to redefine it. This ensures that the constant occupies
a single register even across block boundaries.

This does not apply to loops, where constants are cheaper to redefine than to
carry as loop inputs.

## Statistics

The pass returns the total count of deduplicated constants, which is aggregated
in `Statistics::constants_deduplicated`.
