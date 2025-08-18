# 🤮 WOMIR - Write Once Memory IR

WOMIR is a compiler from [WebAssembly](https://webassembly.org/) to an IR that flattens stack and locals into abstract infinite registers, with the goal of optimizing local accesses in VMs that can benefit such knowledge, especially zkVMs. The IR does not have a DSL and is represented only in a Rust library.

WOMIR is designed for optimal compilation to [PetraVM](https://github.com/PetraProver/PetraVM), developed through a collaboration between [powdr](https://www.powdr.org/) and [Irreducible](https://www.irreducible.com/).

## Targets

The IR can target any ISA that supports the usual MIPS/RISC-V style instructions and has RAM. ISAs that have a write once memory region may benefit heavily from infinite registers. This is especially true for zkVMs.

Under development:

- [ ] [PetraVM](https://github.com/PetraProver/PetraVM)

## Interpreter

WOMIR has an [interpreter](https://github.com/powdr-labs/womir/blob/main/src/interpreter.rs) that is used for testing.

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
