# WOMIR - Write-Once Memory IR

WOMIR is a compiler pipeline from [WebAssembly](https://webassembly.org/) to machines with a very particular execution model: write-once memory (WOM) machines.

Instead of a fixed register bank or a stack, these machines provide as many registers as needed, but each register can only be written once.
To differentiate between multiple calls of the same function, or multiple iterations of the same loop, references to registers are relative
to a frame pointer managed by loops and function calls. This execution model fits naturally with zkVMs, where the execution trace is immutable anyway.

WOMIR transforms a WebAssembly program into an intermediate representation (IR). In this IR, WASM local variables and the operand stack are represented
as edges of a directed acyclic graph (DAG). From this structure, WOMIR can generate a user-defined, assembly-like representation of the WOM program.

WOMIR was initially designed for [PetraVM](https://github.com/PetraProver/PetraVM), developed through a collaboration between
[powdr](https://www.powdr.org/) and [Irreducible](https://www.irreducible.com/).

## Targets

WOMIR can target ISAs for WOM machines that have arbitrarily many general-purpose registers,
a special frame pointer (FP) register, and instructions that operate on registers relative to
the frame pointer. It also enforces that no register is written more than once in the same frame.

In addition to WOM-specific operations, the IR preserves most WebAssembly operations. Therefore, the
target ISA must also allow for implementing them.

These targets are currently under development:

- [womir-openvm](https://github.com/powdr-labs/womir-openvm)
- [PetraVM](https://github.com/PetraProver/PetraVM)

## Interpreter

WOMIR has its own ISA and a corresponding [interpreter](https://github.com/powdr-labs/womir/blob/main/src/interpreter.rs) that are used for testing.

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
