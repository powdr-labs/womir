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

    #[test]
    fn test_wasm_i32() {
        test_wasm("wasm_testsuite/i32.wast", None);
    }

    #[test]
    fn test_wasm_address() {
        env_logger::init();
        test_wasm("wasm_testsuite/address.wast", None);
    }

    #[test]
    fn test_wasm_br() {
        test_wasm("wasm_testsuite/br.wast", None);
    }

    fn test_wasm(case: &str, functions: Option<&[&str]>) {
        match extract_wast_test_info(case) {
            Ok(asserts) => {
                // println!("assert cases: {asserts:#?}");
                asserts
                    .iter()
                    .filter(|assert_case| {
                        if let Some(functions) = functions {
                            functions.contains(&assert_case.function_name.as_str())
                        } else {
                            true
                        }
                    })
                    .for_each(|assert_case| {
                        println!("Assert test case: {assert_case:#?}");
                        test_interpreter(
                            &assert_case.module,
                            &assert_case.function_name,
                            &assert_case.args,
                            &assert_case.expected,
                        );
                    });
            }
            Err(e) => panic!("Error extracting wast test info: {e}"),
        }
    }

    use serde::Deserialize;
    use std::fs;
    use std::process::Command;

    #[derive(Debug, Deserialize)]
    struct TestFile {
        commands: Vec<CommandEntry>,
    }

    #[derive(Debug, Deserialize)]
    #[serde(tag = "type")]
    enum CommandEntry {
        #[serde(rename = "module")]
        Module { filename: String },
        #[serde(rename = "assert_return")]
        AssertReturn { action: Action, expected: Vec<Val> },
        #[serde(other)]
        Other,
    }

    #[derive(Debug)]
    pub struct AssertCase {
        pub module: String,
        pub function_name: String,
        pub args: Vec<u32>,
        pub expected: Vec<u32>,
    }

    #[derive(Debug, Deserialize)]
    pub struct Action {
        #[serde(rename = "type")]
        action_type: String,
        field: Option<String>,
        args: Option<Vec<Val>>,
    }

    #[derive(Debug, Deserialize)]
    pub struct Val {
        #[serde(rename = "type")]
        val_type: String,
        value: serde_json::Value,
    }

    pub fn extract_wast_test_info(
        wast_path: &str,
    ) -> Result<Vec<AssertCase>, Box<dyn std::error::Error>> {
        let json_output_path = format!("{}/sample-programs/test.json", env!("CARGO_MANIFEST_DIR"));

        let output = Command::new("wast2json")
            .arg(wast_path)
            .arg("-o")
            .arg(json_output_path.clone())
            .output()?;

        if !output.status.success() {
            return Err(format!(
                "wast2json failed: {}",
                String::from_utf8_lossy(&output.stderr)
            )
            .into());
        }

        let json_text = fs::read_to_string(json_output_path)?;
        let test_file: TestFile = serde_json::from_str(&json_text)?;
        let entries = test_file.commands;

        let mut module_file = None;
        let mut assert_returns = Vec::new();

        let forbidden_types = ["f32", "f64", "i64", "i128"];
        for entry in entries {
            match entry {
                CommandEntry::Module { filename } => {
                    module_file = Some(filename);
                }
                CommandEntry::AssertReturn { action, expected } => {
                    if let Some(function_name) = action.field {
                        let args = action.args.unwrap_or_default();
                        if args
                            .iter()
                            .any(|a| forbidden_types.iter().any(|t| a.val_type.contains(t)))
                        {
                            continue;
                        }
                        let args = args
                            .iter()
                            .map(|a| a.value.as_str().unwrap().parse::<u32>().unwrap())
                            .collect::<Vec<_>>();
                        if expected
                            .iter()
                            .any(|a| forbidden_types.iter().any(|t| a.val_type.contains(t)))
                        {
                            continue;
                        }
                        let expected = expected
                            .iter()
                            .map(|a| a.value.as_str().unwrap().parse::<u32>().unwrap())
                            .collect::<Vec<_>>();
                        assert_returns.push(AssertCase {
                            module: module_file.clone().unwrap(),
                            function_name,
                            args,
                            expected,
                        });
                    }
                }
                CommandEntry::Other => {}
            }
        }

        Ok(assert_returns)
    }
}
