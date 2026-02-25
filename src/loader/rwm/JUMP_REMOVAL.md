# Jump Removal Pass

**Source:** `../wom/dumb_jump_removal.rs` (shared between WOM and RWM pipelines)

**Input:** `FunctionAsm<S::Directive>` (`PlainFlatAsm` — linear directive sequence)
**Output:** `FunctionAsm<S::Directive>` (`DumbJumpOptFlatAsm` — optimized directive sequence)

## Purpose

This is a simple peephole optimization that removes unconditional jumps whose target
is the immediately following instruction. These "dumb jumps" are an artifact of the
DAG representation, where all breaks are explicit, even when the target
happens to be placed right after the jump.

## Algorithm

The pass does a single linear scan over the directive sequence, examining each
consecutive pair of directives:

1. For each directive, check if it is an unconditional local jump (via
   `Settings::to_plain_local_jump`).
2. If it is, check whether the next directive is a label matching the jump target
   (via `Settings::is_label`).
3. If both conditions hold, drop the jump — it is redundant.
4. Otherwise, keep the directive.

## Why This Happens

The flattening pass emits jumps for every break instruction in the DAG. When a
break targets a label that happens to appear immediately after the break in the
linearized output, the resulting jump is unnecessary. This is common in patterns
like:

```
  ; end of if-true branch
  jump label_42       ; ← dumb jump, label_42 is right below
label_42:
  ; continuation
```

The flattening pass does not attempt to detect this during emission. Instead, this cheap
post-processing pass cleans them up.

## Statistics

The pass returns the count of removed jumps, which is aggregated in the
`Statistics::useless_jumps_removed` counter.
