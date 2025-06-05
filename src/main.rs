use crate::interpreter::{ExternalFunctions, Interpreter};

mod interpreter;
mod linker;
mod loader;

struct Externals {
    values: Vec<u32>,
    counter: usize,
}

impl Externals {
    fn new(values: Vec<u32>) -> Self {
        Self { values, counter: 0 }
    }
}

impl ExternalFunctions for Externals {
    fn call(&mut self, module: &str, function: &str, args: &[u32]) -> Vec<u32> {
        match (module, function) {
            ("env", "read_u32") => {
                let val = self.values[self.counter];
                self.counter = (self.counter + 1) % self.values.len();
                vec![val]
            }
            ("env", "abort") => {
                panic!("Abort called with args: {:?}", args);
            }
            _ => {
                panic!(
                    "External function not implemented: {module}.{function} with args: {:?}",
                    args
                );
            }
        }
    }
}

fn main() -> wasmparser::Result<()> {
    env_logger::init();

    // TODO: do proper command line argument parsing
    let args: Vec<String> = std::env::args().collect();

    let wasm_file_path = &args[1];

    let func_name = args.get(2);
    let inputs: Vec<u32> = args[3..]
        .iter()
        .filter_map(|s| s.parse::<u32>().ok())
        .collect();

    let wasm_file = std::fs::read(&wasm_file_path).unwrap();

    let program = loader::load_wasm(&wasm_file)?;

    if let Some(func_name) = func_name {
        let mut interpreter = Interpreter::new(program, Externals::new(vec![25, 5]));
        log::info!("Executing function: {func_name}");
        let outputs = interpreter.run(func_name, &inputs);
        println!("Outputs: {:?}", outputs);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_interpreter(file_name: &str, main_function: &str, inputs: &[u32], outputs: &[u32]) {
        let path = format!("{}/sample-programs/{file_name}", env!("CARGO_MANIFEST_DIR"));
        let wasm_file = std::fs::read(path).unwrap();
        let program = loader::load_wasm(&wasm_file).unwrap();
        let mut interpreter = interpreter::Interpreter::new(program, Externals::new(Vec::new()));
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
