use itertools::Itertools;

use crate::interpreter::{ExternalFunctions, Interpreter};

mod interpreter;
mod linker;
mod loader;

struct DataInput {
    values: Vec<u32>,
}

impl DataInput {
    fn new(values: Vec<u32>) -> Self {
        Self { values }
    }
}

impl ExternalFunctions for DataInput {
    fn call(&mut self, module: &str, function: &str, args: &[u32]) -> Vec<u32> {
        match (module, function) {
            ("env", "read_u32") => {
                vec![self.values[args[0] as usize]]
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
    let func_inputs = args
        .get(3)
        .unwrap_or(&String::new())
        .split(',')
        .filter_map(|s| s.parse::<u32>().ok())
        .collect_vec();

    let data_inputs = args
        .get(4)
        .unwrap_or(&String::new())
        .split(',')
        .filter_map(|s| s.parse::<u32>().ok())
        .collect_vec();

    let wasm_file = std::fs::read(&wasm_file_path).unwrap();

    let program = loader::load_wasm(&wasm_file)?;

    if let Some(func_name) = func_name {
        let mut interpreter = Interpreter::new(program, DataInput::new(data_inputs));
        log::info!("Executing function: {func_name}");
        let outputs = interpreter.run(func_name, &func_inputs);
        println!("Outputs: {:?}", outputs);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_log::test;

    fn test_interpreter(path: &str, main_function: &str, inputs: &[u32], outputs: &[u32]) {
        let wasm_file = std::fs::read(path).unwrap();
        let program = loader::load_wasm(&wasm_file).unwrap();
        let mut interpreter = interpreter::Interpreter::new(program, DataInput::new(Vec::new()));
        let got_output = interpreter.run(main_function, inputs);
        assert_eq!(got_output, outputs);
    }

    fn test_interpreter_from_sample_programs(
        path: &str,
        main_function: &str,
        inputs: &[u32],
        outputs: &[u32],
    ) {
        let path = format!("{}/sample-programs/{path}", env!("CARGO_MANIFEST_DIR"));
        test_interpreter(&path, main_function, inputs, outputs);
    }

    #[test]
    fn test_fib() {
        test_interpreter_from_sample_programs("fib_loop.wasm", "fib", &[10], &[55]);
    }

    #[test]
    fn test_collatz() {
        test_interpreter_from_sample_programs("collatz.wasm", "collatz", &[1 << 22], &[22]);
        test_interpreter_from_sample_programs("collatz.wasm", "collatz", &[310], &[86]);
    }

    #[test]
    fn test_wasm_address() {
        test_wasm("wasm_testsuite/address.wast", None);
    }

    #[test]
    fn test_wasm_block() {
        test_wasm("wasm_testsuite/block.wast", None);
    }

    #[test]
    fn test_wasm_br_if() {
        test_wasm("wasm_testsuite/br_if.wast", None);
    }

    #[test]
    fn test_wasm_br_table() {
        test_wasm("wasm_testsuite/br_table.wast", None);
    }

    #[test]
    fn test_wasm_br() {
        test_wasm("wasm_testsuite/br.wast", None);
    }

    #[test]
    fn test_wasm_i32() {
        test_wasm("wasm_testsuite/i32.wast", None);
    }

    fn test_wasm(case: &str, functions: Option<&[&str]>) {
        match extract_wast_test_info(case) {
            Ok(modules) => {
                for (mod_name, asserts) in modules {
                    println!("Module: {}", mod_name.display());

                    let wasm_file = std::fs::read(mod_name).unwrap();
                    let program = loader::load_wasm(&wasm_file).unwrap();
                    let mut interpreter =
                        interpreter::Interpreter::new(program, DataInput::new(Vec::new()));

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
                            let got_output =
                                interpreter.run(&assert_case.function_name, &assert_case.args);
                            assert_eq!(got_output, assert_case.expected);
                        });
                }
            }
            Err(e) => panic!("Error extracting wast test info: {e}"),
        }
    }

    use serde::Deserialize;
    use std::fs::{self, File};
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use tempfile::NamedTempFile;
    use tempfile::tempdir;

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
    ) -> Result<Vec<(PathBuf, Vec<AssertCase>)>, Box<dyn std::error::Error>> {
        let temp_file = NamedTempFile::with_prefix("test")?;
        let Some(parent_dir) = temp_file.path().parent() else {
            panic!("Could not determine parent directory.");
        };
        let json_output_path = temp_file.path().to_owned();

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

        let mut assert_returns_per_module = Vec::new();

        for entry in entries {
            match entry {
                CommandEntry::Module { filename } => {
                    assert_returns_per_module.push((parent_dir.join(filename), Vec::new()));
                }
                CommandEntry::AssertReturn { action, expected } => {
                    if let Some(function_name) = action.field {
                        let args = action.args.unwrap_or_default();

                        let args = args.iter().flat_map(parse_val).collect::<Vec<_>>();

                        let expected = expected.iter().flat_map(parse_val).collect::<Vec<_>>();
                        assert_returns_per_module
                            .last_mut()
                            .unwrap()
                            .1
                            .push(AssertCase {
                                function_name,
                                args,
                                expected,
                            });
                    }
                }
                CommandEntry::Other => {}
            }
        }

        Ok(assert_returns_per_module)
    }

    fn parse_val(val: &Val) -> Vec<u32> {
        match val.val_type.as_str() {
            "i32" | "f32" => vec![val.value.as_str().unwrap().parse::<u32>().unwrap()],
            "i64" | "f64" => {
                let v = val.value.as_str().unwrap().parse::<u64>().unwrap();
                vec![v as u32, (v >> 32) as u32]
            }
            // three bytes to be compatible with our `funcref`
            "externref" => vec![0, 0, val.value.as_str().unwrap().parse::<u32>().unwrap()],
            _ => todo!(),
        }
    }
}
