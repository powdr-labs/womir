mod interpreter;
mod linker;
mod loader;

fn main() -> wasmparser::Result<()> {
    env_logger::init();

    // TODO: do proper command line argument parsing
    let args: Vec<String> = std::env::args().collect();
    let wasm_file = std::fs::read(&args[1]).unwrap();

    let _program = loader::load_wasm(&wasm_file)?;

    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_interpreter(file_name: &str, main_function: &str, inputs: &[u32], outputs: &[u32]) {
        let path = format!("{}/sample-programs/{file_name}", env!("CARGO_MANIFEST_DIR"));
        let wasm_file = std::fs::read(path).unwrap();
        let program = loader::load_wasm(&wasm_file).unwrap();
        let mut interpreter = interpreter::Interpreter::new(&program);
        let got_output = interpreter.run(main_function, inputs);
        assert_eq!(got_output, outputs);
    }

    #[test]
    fn test_fib() {
        test_interpreter("fib_loop.wasm", "fib", &[10], &[55]);
    }

    #[test]
    fn test_collatz() {
        test_interpreter("collatz.wasm", "collatz", &[1 << 22], &[22]);
        test_interpreter("collatz.wasm", "collatz", &[310], &[86]);
    }
}
