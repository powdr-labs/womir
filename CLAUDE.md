# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

WOMIR (Write Once Memory IR) is a compiler from WebAssembly to an intermediate representation that flattens stack and locals into abstract infinite registers. It supports two execution models: write-once memory (WOM) and read-write (RW) registers, making it suitable for zkVMs and other specialized virtual machines.

## Common Development Commands

```bash
# Build the project
cargo build --release

# Run all tests (requires wabt installed)
cargo test

# Run a specific test
cargo test test_name

# Compile a WASM file (dumps IR to ir_dump.txt, default: WOM pipeline)
cargo run --bin womir -- compile <wasm_file>

# Compile using the read-write registers pipeline
cargo run --bin womir -- -e rw compile <wasm_file>

# Run a function from a WASM file
cargo run --bin womir -- run <wasm_file> <function> --func-inputs 1,2 --data-inputs 3,4

# Run with read-write registers execution model
cargo run --bin womir -- -e rw run <wasm_file> <function> --func-inputs 1,2 --data-inputs 3,4

# Format code
cargo fmt

# Run clippy linter
cargo clippy --all-targets --all-features -- -D warnings
```

## Testing Requirements

- Install `wabt` (WebAssembly Binary Toolkit) for WAT to WASM conversion in tests
- Install WebAssembly target: `rustup target add wasm32-unknown-unknown`

## Key Architecture

### Compilation Pipeline

Functions are processed in parallel through stages defined by the `FunctionProcessingStage` trait (`src/loader/mod.rs`).

**Common stages** (shared by both pipelines, defined in `CommonStages`):

1. `Unparsed` → `BlockTree`: Parse WASM operators into block-based tree
2. `BlockTree` → `LiftedBlockTree`: Expose locals reads/writes as block inputs/outputs
3. `LiftedBlockTree` → `PlainDag`: Build DAG representation
4. DAG optimization passes: `ConstCollapsedDag` → `ConstDedupDag` → `DanglingOptDag`
5. `DanglingOptDag` → `BlocklessDag`: Convert to blockless representation with labels

**WOM pipeline** (`src/loader/wom/`, `WomStages`):

6. `BlocklessDag` → `PlainFlatAsm`: Flatten DAG with frame allocation for write-once semantics
7. `PlainFlatAsm` → `DumbJumpOptFlatAsm`: Remove useless jumps (final output)

**RWM pipeline** (`src/loader/rwm/`, `RWMStages`):

6. `BlocklessDag` → `LivenessDag`: Attach liveness information for register allocation
7. `LivenessDag` → `RegisterAllocatedDag`: Allocate read-write registers based on liveness
8. `RegisterAllocatedDag` → `PlainFlatAsm`: Flatten DAG into assembly-like IR
9. `PlainFlatAsm` → `DumbJumpOptFlatAsm`: Remove useless jumps (final output)

### Core Modules

- **`src/loader/`**: Main compilation pipeline
  - `mod.rs`: `FunctionProcessingStage` trait, `CommonStages` enum, parallel processing
  - `passes/`: Common transformation passes (block_tree, blockless_dag, dag optimizations)
  - `wom/`: Write-once memory pipeline (flattening with frame allocation, jump removal)
  - `rwm/`: Read-write registers pipeline (liveness analysis, register allocation, flattening)
  - `settings.rs`: Base `Settings` trait defining target ISA requirements

- **`src/interpreter/`**: Test interpreter for the generic IR
  - `mod.rs`: `Interpreter` supporting both `WriteOnceRegisters` and `InfiniteRegisters` execution models
  - `generic_ir.rs`: `GenericIrSetting` (implements both `WomSettings` and `RwmSettings`), `Directive` enum
  - `linker.rs`: Label resolution and linking

### Settings Traits

The `Settings` trait hierarchy (`src/loader/settings.rs`) is the key extension point for targeting different ISAs:

- **`Settings`** (base): Word size, pointer width, jump conditions, label/jump emission
- **`wom::Settings`** (`src/loader/wom/settings.rs`): Frame allocation, copy-into/from-frame, non-deterministic outputs
- **`rwm::Settings`** (`src/loader/rwm/settings.rs`): Register copy, function calls, WASM op emission

`GenericIrSetting` in `src/interpreter/generic_ir.rs` implements all three traits and serves as the reference ISA.

### Memory Models

The project supports two execution models for infinite registers:

**Write-Once Memory (WOM)**:
- Registers can only be written once, with states: `Unassigned`, `Future`, `Concrete`
- Requires `AllocateFrame`, `CopyFromFrame`, `CopyIntoFrame` instructions
- Supports "reading from the future" (non-deterministic output binding)

**Read-Write Registers (RWM)**:
- Standard read-write register semantics
- Liveness-based register allocation reduces register copies
- Calling convention documented in `src/loader/rwm/CALLING_CONVENTION.md`

Both models use RAM for globals and WASM linear memory.

## External Functions

The interpreter supports external functions through the `ExternalFunctions` trait. Default implementations include:
- `env.read_u32`: Read input values
- `env.abort`: Trigger abort
- `gojs.*`: Go JS runtime support (e.g., `runtime.getRandomData`)