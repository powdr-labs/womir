# WOMIR - Write-Once Memory IR

WOMIR is a compiler pipeline from [WebAssembly](https://webassembly.org/) to machines with infinite registers and two possible execution models: write-once memory (WOM) and read-write (RW) registers.

In the WOM model, machines provide as many registers as needed, but each register can only be written once.
To differentiate between multiple calls of the same function, or multiple iterations of the same loop, references to registers are relative
to a frame pointer managed by loops and function calls. This execution model fits naturally with zkVMs, where the execution trace is immutable anyway.

In the RW model, machines provide standard read-write registers with liveness-based register allocation to minimize register usage.

WOMIR transforms a WebAssembly program into an intermediate representation (IR). In this IR, WASM local variables and the operand stack are represented
as edges of a directed acyclic graph (DAG). From this structure, WOMIR can generate a user-defined, assembly-like representation of the program.

## Targets

WOMIR can target ISAs for machines with arbitrarily many general-purpose registers,
a special frame pointer (FP) register, and instructions that operate on registers relative to
the frame pointer.

In addition to model-specific operations, the IR preserves most WebAssembly operations. Therefore, the
target ISA must also allow for implementing them.

These targets are currently under development:

- [womir-openvm](https://github.com/powdr-labs/womir-openvm)

## Interpreter

WOMIR has its own generic ISA and a corresponding [interpreter](https://github.com/powdr-labs/womir/tree/main/src/interpreter) that supports both execution models and is used for testing.

## Contributing

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as below, without any additional terms or conditions.

### Requirements

To run the tests, you need to install [wabt](https://github.com/WebAssembly/wabt).

## License

This project is licensed under either of

<!-- markdown-link-check-disable -->
- [Apache License, Version 2.0](https://www.apache.org/licenses/LICENSE-2.0) ([`LICENSE-APACHE`](LICENSE-APACHE))
- [MIT license](https://opensource.org/licenses/MIT) ([`LICENSE-MIT`](LICENSE-MIT))
<!-- markdown-link-check-enable -->

at your option.
