use std::str::FromStr;

use loader::SystemCall;

mod loader;

enum NoSystemCall {}

impl FromStr for NoSystemCall {
    type Err = ();

    fn from_str(_s: &str) -> Result<Self, Self::Err> {
        Err(())
    }
}

impl SystemCall for NoSystemCall {
    fn function_type(&self) -> (Vec<wasmparser::ValType>, Vec<wasmparser::ValType>) {
        unreachable!()
    }
}

fn main() -> wasmparser::Result<()> {
    env_logger::init();

    // TODO: do proper command line argument parsing
    let args: Vec<String> = std::env::args().collect();
    let wasm_file = std::fs::read(&args[1]).unwrap();

    let program = loader::load_wasm::<NoSystemCall>(&wasm_file)?;

    todo!()
}
