# Block Tree Pass

**Source:** `block_tree.rs`

**Input:** Raw WASM function bytecode (`Unparsed`)
**Output:** `BlockTree` (tree of `Block` and `Instruction` elements)

## Purpose

This is the first pass in the compilation pipeline. It takes the raw stream of
WASM operators and parses them into a tree structure where control flow is
represented by nested blocks and loops, and instructions within each block form
a linear sequence.

The pass also normalizes several WASM patterns into simpler, more uniform
representations that are easier for subsequent passes to handle.

## Normalizations

### If-Else to Block + BrIf

WASM's `if-else-end` construct is desugared into blocks with conditional
breaks. This reduces the number of control flow constructs that later passes
need to handle.

**If without else:**
```
;; Original WASM         ;; Normalized BlockTree
if                        block (params..., i32) -> (results...)
    <if_body>                 br_if_zero 0      ;; skip if_body when false
end                           <if_body>
                          end
```

**If with else:**
```
;; Original WASM         ;; Normalized BlockTree
if                        block (params..., i32) -> (results...)
    <if_body>                 block (params..., i32) -> (params...)
else                              br_if 0       ;; skip else_body when true
    <else_body>                   <else_body>
end                               br 1          ;; skip if_body
                              end
                              <if_body>
                          end
```

The condition value is carried as an extra block input and consumed by the
conditional break at the top.

### Return to Br

WASM `return` is converted to a `br` targeting the outermost block (the
function body). This makes the function body just another block, simplifying
break handling.

```
;; Original              ;; Normalized
return                    br <function_depth>
```

### Explicit Fallthrough Breaks

Every block that can fall through gets an explicit `br 0` appended. This
guarantees that all blocks are exited via a break instruction, which simplifies
the locals data flow pass (it can assume all values leave blocks through break
inputs).

```
;; Original              ;; Normalized
block                     block
    i32.const 42              i32.const 42
end                           br 0        ;; explicit fallthrough
                          end
```

### Loop Wrapping

When a loop can fall through (i.e., it doesn't always branch back to the loop
header or exit via a break), an outer block is added around it. The fallthrough
becomes a break to the outer block. This ensures loops are only exited through
breaks.

```
;; Original              ;; Normalized
loop                      block -> (results...)
    <body>                    loop (params...)
end                               <body>
                                  br 1    ;; exit to outer block
                              end
                          end
```

### Dead Code Removal

After any instruction that unconditionally diverts control flow (`br`,
`br_table`, `unreachable`, or a non-fallthrough loop), all subsequent
instructions up to the next `end` or `else` are discarded.

```
;; Original              ;; Normalized
br 0                      br 0
i32.const 1               ;; dead code removed
i32.add                   ;; dead code removed
```

### Constant Global Inlining

`global.get` on immutable globals is replaced with the global's constant
initializer. This is done early because it enables the downstream constant
optimization passes to work with these values.

```
;; Original (global 0 is immutable, initialized to 42)
global.get 0              ;; Normalized: i32.const 42
```

## Output Structure

The output `BlockTree` is a `Vec<Element>` where each `Element` is either:

- **`Instruction`**: A WASM operator, a `BrIfZero`, or a `BrTable`.
- **`Block`**: A nested block containing:
  - `block_kind`: `Block` or `Loop`
  - `interface_type`: The block's input and output types
  - `elements`: The block's contents (recursively)
  - `input_locals`, `output_locals`, `carried_locals`: Initially empty; filled
    by the next pass

At this stage, all blocks have well-defined stack-level interfaces (params and
results), but local variable flow is still implicit.
