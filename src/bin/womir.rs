use std::{
    fs::File,
    io::{BufWriter, Write},
};

use clap::{Parser, Subcommand};
use womir::{
    interpreter::{
        ExecutionModel, ExternalFunctions, Interpreter, MemoryAccessor,
        generic_ir::{Directive, GenericIrSetting},
    },
    loader::{FunctionAsm, PartiallyParsedProgram, Program, rwm::RWMStages, wom::WomStages},
};

struct DataInput {
    values: <Vec<u32> as IntoIterator>::IntoIter,
}

impl DataInput {
    fn new(values: Vec<u32>) -> Self {
        Self {
            values: values.into_iter(),
        }
    }
}

impl ExternalFunctions for DataInput {
    fn call(
        &mut self,
        module: &str,
        function: &str,
        args: &[u32],
        mem: &mut Option<MemoryAccessor<'_>>,
    ) -> Vec<u32> {
        match (module, function) {
            ("env", "read_u32") => {
                vec![self.values.next().expect("Not enough input values")]
            }
            ("env", "abort") => {
                panic!("Abort called with args: {:?}", args);
            }
            ("gojs", fname) => {
                log::trace!("Calling syscall {fname} with args: {:?}", args);
                if "runtime.getRandomData" == fname {
                    let mem = mem.as_mut().unwrap();
                    let sp = args[0];

                    // Interpret the arguments from the stack:
                    let dst_lo = mem.get_word(sp + 8).unwrap();
                    let dst_hi = mem.get_word(sp + 12).unwrap();
                    let dst: u64 = (dst_lo as u64) | ((dst_hi as u64) << 32);
                    let len_lo = mem.get_word(sp + 16).unwrap();
                    let len_hi = mem.get_word(sp + 20).unwrap();
                    let len: u64 = len_lo as u64 | ((len_hi as u64) << 32);

                    log::trace!("Writing random data of len {len} to {dst}");

                    assert_eq!(len % 4, 0);

                    // The meaning of a random number in ZK is not well defined.
                    // Either it is a prover provided value, or it is derived from
                    // the input. Regardless, it is not the same thing we expect
                    // in normal computing. So, for lack of a better alternative,
                    // we just write a constant pattern here.
                    const RAND_VAL: u32 = 0;
                    for i in 0..(len / 4) {
                        mem.set_word((dst + i * 4) as u32, RAND_VAL).unwrap();
                    }
                }
                vec![]
            }
            _ => {
                panic!(
                    "External function not implemented: module: {module}, function: {function} with args: {:?}",
                    args
                );
            }
        }
    }
}

fn main() -> wasmparser::Result<()> {
    env_logger::init();

    fn parse_exec_model(s: &str) -> Result<ExecutionModel, String> {
        match s {
            "wom" | "write-once" => Ok(ExecutionModel::WriteOnceRegisters),
            "rw" | "infinite" => Ok(ExecutionModel::InfiniteRegisters),
            _ => Err(format!("Invalid execution model: {s}")),
        }
    }

    /// Simple CLI for the `womir` binary.
    ///
    /// Two subcommands are supported:
    ///   compile <wasm-file>
    ///   run <wasm-file> <function> --func-inputs 1,2 --data-inputs 3,4
    #[derive(Parser)]
    #[command(author, version, about = "womir tool: compile or run a Wasm file", long_about = None)]
    struct Cli {
        /// Execution model (wom = write-once registers, rw = infinite/read-write registers)
        #[arg(short = 'e', long = "exec-model", default_value = "wom", global = true, value_parser = parse_exec_model)]
        exec_model: ExecutionModel,
        #[command(subcommand)]
        command: Command,
    }

    #[derive(Subcommand)]
    enum Command {
        /// Load and process the Wasm file (writes IR dump)
        Compile {
            /// Path to the wasm file to load
            wasm_file: String,
        },

        /// Run a function from the Wasm file
        Run {
            /// Path to the wasm file to load
            wasm_file: String,

            /// Function name to execute
            function: String,

            /// Comma separated function inputs (u32)
            #[arg(long = "func-inputs", value_delimiter = ',', value_parser = clap::value_parser!(u32))]
            func_inputs: Vec<u32>,

            /// Comma separated data inputs (u32)
            #[arg(long = "data-inputs", value_delimiter = ',', value_parser = clap::value_parser!(u32))]
            data_inputs: Vec<u32>,
        },
    }

    let cli = Cli::parse();

    match cli.command {
        Command::Compile { wasm_file } => {
            let wasm_bytes = std::fs::read(&wasm_file).unwrap();
            let program = womir::loader::load_wasm(GenericIrSetting::default(), &wasm_bytes)?;
            let program = process_functions(cli.exec_model, program)?;

            if let Err(err) = dump_ir(&program) {
                log::error!("Failed to dump IR: {err}");
            }

            Ok(())
        }
        Command::Run {
            wasm_file,
            function,
            func_inputs,
            data_inputs,
        } => {
            let wasm_bytes = std::fs::read(&wasm_file).unwrap();
            let program = womir::loader::load_wasm(GenericIrSetting::default(), &wasm_bytes)?;
            let program = process_functions(cli.exec_model, program)?;

            if let Err(err) = dump_ir(&program) {
                log::error!("Failed to dump IR: {err}");
            }

            let mut interpreter =
                Interpreter::new(program, cli.exec_model, DataInput::new(data_inputs));
            log::info!("Executing function: {function}");
            let outputs = interpreter.run(&function, &func_inputs);
            log::info!("Outputs: {:?}", outputs);

            Ok(())
        }
    }
}

fn process_functions<'a>(
    exec_model: ExecutionModel,
    program: PartiallyParsedProgram<'a, GenericIrSetting<'a>>,
) -> wasmparser::Result<Program<'a, FunctionAsm<Directive<'a>>>> {
    match exec_model {
        ExecutionModel::InfiniteRegisters => {
            program.default_par_process_all_functions::<RWMStages<GenericIrSetting>>()
        }
        ExecutionModel::WriteOnceRegisters => {
            program.default_par_process_all_functions::<WomStages<GenericIrSetting>>()
        }
    }
}

fn dump_ir(program: &Program<FunctionAsm<Directive>>) -> std::io::Result<()> {
    let mut file = BufWriter::new(File::create("ir_dump.txt")?);
    for (i, func) in program.functions.iter().enumerate() {
        writeln!(file, "Function {i}:")?;
        for directive in &func.directives {
            writeln!(file, "  {directive}")?;
        }
    }
    file.flush()?;
    log::info!("IR dump written to ir_dump.txt");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;
    use std::fs;
    use std::path::PathBuf;
    use std::process::Command;
    use tempfile::NamedTempFile;
    use test_log::test;
    use womir::interpreter::NULL_REF;

    fn test_interpreter(
        path: &str,
        main_function: &str,
        func_inputs: &[u32],
        data_inputs: Vec<u32>,
        outputs: &[u32],
    ) {
        println!(
            "Run function: {main_function} with inputs: {func_inputs:?} and data inputs: {data_inputs:?}"
        );
        let wasm_file = std::fs::read(path).unwrap();
        let program = womir::loader::load_wasm(GenericIrSetting::default(), &wasm_file)
            .unwrap()
            .default_process_all_functions::<WomStages<GenericIrSetting>>()
            .unwrap();
        let mut interpreter = Interpreter::new(
            program,
            ExecutionModel::WriteOnceRegisters,
            DataInput::new(data_inputs),
        );
        let got_output = interpreter.run(main_function, func_inputs);
        assert_eq!(got_output, outputs);
    }

    fn test_interpreter_from_sample_programs(
        path: &str,
        main_function: &str,
        func_inputs: &[u32],
        data_inputs: Vec<u32>,
        outputs: &[u32],
    ) {
        let path = format!("{}/sample-programs/{path}", env!("CARGO_MANIFEST_DIR"));
        test_interpreter(&path, main_function, func_inputs, data_inputs, outputs);
    }

    /// This test requires the directory and the package name to be the same in `case`.
    fn test_interpreter_rust(
        case: &str,
        main_function: &str,
        func_inputs: &[u32],
        data_inputs: Vec<u32>,
        outputs: &[u32],
    ) {
        let path = format!("{}/sample-programs/{case}", env!("CARGO_MANIFEST_DIR"));
        build_wasm(&PathBuf::from(&path));
        let wasm_path = format!("{path}/target/wasm32-unknown-unknown/release/{case}.wasm",);
        test_interpreter(&wasm_path, main_function, func_inputs, data_inputs, outputs);
    }

    fn build_wasm(path: &PathBuf) {
        assert!(path.exists(), "Target directory does not exist: {path:?}",);

        let output = Command::new("cargo")
            .arg("build")
            .arg("--release")
            .arg("--target")
            .arg("wasm32-unknown-unknown")
            .current_dir(path)
            .output()
            .expect("Failed to run cargo build");

        if !output.status.success() {
            eprintln!("stderr:\n{}", String::from_utf8_lossy(&output.stderr));
            eprintln!("stdout:\n{}", String::from_utf8_lossy(&output.stdout));
        }

        assert!(output.status.success(), "cargo build failed for {path:?}",);
    }

    #[test]
    fn test_sqrt() {
        test_interpreter_rust("sqrt", "main", &[0, 0], vec![9, 3], &[0]);
    }

    #[test]
    fn test_vec_grow() {
        test_interpreter_rust("vec_grow", "vec_grow", &[5], vec![], &[]);
    }

    #[test]
    fn test_vec_median() {
        test_interpreter_rust(
            "vec_median",
            "vec_median",
            &[],
            vec![5, 11, 15, 75, 6, 5, 1, 4, 7, 3, 2, 9, 2],
            &[],
        );
    }

    #[test]
    fn test_keccak() {
        test_interpreter_rust("keccak", "main", &[0, 0], vec![], &[0]);
    }

    #[test]
    fn test_keccak_with_inputs() {
        test_interpreter_rust("keccak_with_inputs", "main", &[0, 0], vec![1, 0x29], &[0]);
        test_interpreter_rust("keccak_with_inputs", "main", &[0, 0], vec![2, 0x51], &[0]);
        test_interpreter_rust("keccak_with_inputs", "main", &[0, 0], vec![5, 0xf2], &[0]);
        test_interpreter_rust("keccak_with_inputs", "main", &[0, 0], vec![10, 0x9b], &[0]);
    }

    #[test]
    fn test_fib() {
        test_interpreter_from_sample_programs("fib_loop.wasm", "fib", &[10], vec![], &[55]);
    }

    #[test]
    fn test_add() {
        test_interpreter_from_sample_programs(
            "add.wasm",
            "add",
            &[666, (-624_i32) as u32],
            vec![],
            &[42],
        );
    }

    #[test]
    fn test_collatz() {
        test_interpreter_from_sample_programs("collatz.wasm", "collatz", &[1 << 22], vec![], &[22]);
        test_interpreter_from_sample_programs("collatz.wasm", "collatz", &[310], vec![], &[86]);
    }

    #[test]
    fn test_merkle_tree() {
        // Judging by the binary, this program comes from Rust, but I don't have its source code.
        test_interpreter_from_sample_programs("merkle-tree.wasm", "main", &[0, 0], vec![], &[0]);
    }

    #[test]
    fn test_keeper_js() {
        // This is program is a stripped down version of geth, compiled for Go's js target.
        // Source: https://github.com/ethereum/go-ethereum/tree/master/cmd/keeper
        // Compile command:
        //   GOOS=js GOARCH=wasm go -gcflags=all=-d=softfloat build -tags "example" -o keeper.wasm
        test_interpreter_from_sample_programs("keeper_js.wasm", "run", &[0, 0], vec![], &[]);
    }

    #[test]
    fn test_wasm_address() {
        test_wasm("wasm_testsuite/address.wast", None);
    }

    #[test]
    fn test_wasm_align() {
        test_wasm("wasm_testsuite/align.wast", None);
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
    fn test_wasm_call() {
        test_wasm("wasm_testsuite/call.wast", None);
    }

    #[test]
    fn test_wasm_data() {
        test_wasm("wasm_testsuite/data.wast", None);
    }

    #[test]
    fn test_wasm_call_indirect() {
        test_wasm("wasm_testsuite/call_indirect.wast", None);
    }

    #[test]
    fn test_wasm_func() {
        test_wasm("wasm_testsuite/func.wast", None);
    }

    #[test]
    fn test_wasm_i32() {
        test_wasm("wasm_testsuite/i32.wast", None);
    }

    #[test]
    fn test_wasm_forward() {
        test_wasm("wasm_testsuite/forward.wast", None);
    }

    #[test]
    fn test_wasm_i64() {
        test_wasm("wasm_testsuite/i64.wast", None);
    }

    #[test]
    fn test_wasm_if() {
        test_wasm("wasm_testsuite/if.wast", None);
    }

    #[test]
    fn test_wasm_labels() {
        test_wasm("wasm_testsuite/labels.wast", None);
    }

    #[test]
    fn test_wasm_load() {
        test_wasm("wasm_testsuite/load.wast", None);
    }

    #[test]
    fn test_wasm_local_get() {
        test_wasm("wasm_testsuite/local_get.wast", None);
    }

    #[test]
    fn test_wasm_local_set() {
        test_wasm("wasm_testsuite/local_set.wast", None);
    }

    #[test]
    fn test_wasm_local_tee() {
        test_wasm("wasm_testsuite/local_tee.wast", None);
    }

    #[test]
    fn test_wasm_loop() {
        test_wasm("wasm_testsuite/loop.wast", None);
    }

    #[test]
    fn test_wasm_memory_fill() {
        test_wasm("wasm_testsuite/memory_fill.wast", None);
    }

    #[test]
    fn test_wasm_ref_is_null() {
        test_wasm("wasm_testsuite/ref_is_null.wast", None);
    }

    #[test]
    fn test_wasm_ref_null() {
        test_wasm("wasm_testsuite/ref_null.wast", None);
    }

    #[test]
    fn test_wasm_return() {
        test_wasm("wasm_testsuite/return.wast", None);
    }

    #[test]
    fn test_wasm_switch() {
        test_wasm("wasm_testsuite/switch.wast", None);
    }

    #[test]
    fn test_wasm_stack() {
        test_wasm("wasm_testsuite/stack.wast", None);
    }

    #[test]
    fn test_wasm_start() {
        test_wasm("wasm_testsuite/start.wast", None);
    }

    #[test]
    fn test_wasm_store() {
        test_wasm("wasm_testsuite/store.wast", None);
    }

    #[test]
    fn test_wasm_select() {
        test_wasm("wasm_testsuite/select.wast", None);
    }

    #[test]
    fn test_wasm_unwind() {
        test_wasm("wasm_testsuite/unwind.wast", None);
    }

    struct SpectestExternalFunctions;

    impl ExternalFunctions for SpectestExternalFunctions {
        fn call(
            &mut self,
            module: &str,
            function: &str,
            args: &[u32],
            _mem: &mut Option<MemoryAccessor<'_>>,
        ) -> Vec<u32> {
            /* From https://github.com/WebAssembly/spec/tree/main/interpreter#spectest-host-module
            (func (export "print"))
            (func (export "print_i32") (param i32))
            (func (export "print_i64") (param i64))
            (func (export "print_f32") (param f32))
            (func (export "print_f64") (param f64))
            (func (export "print_i32_f32") (param i32 f32))
            (func (export "print_f64_f64") (param f64 f64))
            */
            assert_eq!(module, "spectest", "Unexpected module: {module}");
            match function {
                "print" => println!(),
                "print_i32" => println!("{}", args[0] as i32),
                "print_i64" => println!("{}", (args[0] as u64 & ((args[1] as u64) << 32)) as i64),
                "print_f32" => println!("{}", f32::from_bits(args[0])),
                "print_f64" => println!(
                    "{}",
                    f64::from_bits((args[0] as u64) | ((args[1] as u64) << 32))
                ),
                "print_i32_f32" => {
                    println!("{} {}", args[0] as i32, f32::from_bits(args[1]))
                }
                "print_f64_f64" => {
                    println!(
                        "{} {}",
                        f64::from_bits(args[0] as u64 | ((args[1] as u64) << 32)),
                        f64::from_bits(args[2] as u64 | ((args[3] as u64) << 32))
                    )
                }
                _ => panic!(
                    "Unexpected function: {function} in module {module} with args: {:?}",
                    args
                ),
            }
            Vec::new()
        }
    }

    fn test_wasm(case: &str, functions: Option<&[&str]>) {
        match extract_wast_test_info(case) {
            Ok(modules) => {
                for (mod_name, line, asserts) in modules {
                    println!("Testing module: {} at line {line}", mod_name.display());
                    let wasm_file = std::fs::read(mod_name).unwrap();
                    let program = womir::loader::load_wasm(GenericIrSetting::default(), &wasm_file)
                        .unwrap()
                        .default_par_process_all_functions::<RWMStages<GenericIrSetting>>()
                        .unwrap();
                    let mut interpreter = Interpreter::new(
                        program,
                        ExecutionModel::InfiniteRegisters,
                        SpectestExternalFunctions,
                    );

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

    #[derive(Debug, Deserialize)]
    struct TestFile {
        commands: Vec<CommandEntry>,
    }

    #[derive(Debug, Deserialize)]
    #[serde(tag = "type")]
    enum CommandEntry {
        #[serde(rename = "module")]
        Module { filename: String, line: usize },
        #[serde(rename = "assert_return")]
        AssertReturn {
            action: Action,
            expected: Vec<Val>,
            line: usize,
        },
        #[serde(rename = "action")]
        Action {
            action: Action,
            expected: Vec<Val>,
            line: usize,
        },
        #[serde(other)]
        Other,
    }

    #[derive(Debug)]
    pub struct AssertCase {
        pub function_name: String,
        pub args: Vec<u32>,
        pub expected: Vec<u32>,
        pub _line: usize,
    }

    #[derive(Debug, Deserialize)]
    pub struct Action {
        #[serde(rename = "type")]
        _action_type: String,
        field: Option<String>,
        args: Option<Vec<Val>>,
    }

    #[derive(Debug, Deserialize)]
    pub struct Val {
        #[serde(rename = "type")]
        val_type: String,
        value: serde_json::Value,
    }

    // TODO: refactor complex type
    #[allow(clippy::type_complexity)]
    pub fn extract_wast_test_info(
        wast_path: &str,
    ) -> Result<Vec<(PathBuf, usize, Vec<AssertCase>)>, Box<dyn std::error::Error>> {
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
                CommandEntry::Module { filename, line } => {
                    assert_returns_per_module.push((parent_dir.join(filename), line, Vec::new()));
                }
                CommandEntry::AssertReturn {
                    action,
                    expected,
                    line,
                }
                | CommandEntry::Action {
                    action,
                    expected,
                    line,
                } => {
                    if let Some(function_name) = action.field {
                        let args = action.args.unwrap_or_default();

                        let args = args.iter().flat_map(parse_val).collect::<Vec<_>>();

                        let expected = expected.iter().flat_map(parse_val).collect::<Vec<_>>();
                        assert_returns_per_module
                            .last_mut()
                            .unwrap()
                            .2
                            .push(AssertCase {
                                function_name,
                                args,
                                expected,
                                _line: line,
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
            "externref" => {
                let val = val.value.as_str().unwrap();
                if val == "null" {
                    NULL_REF.into()
                } else {
                    // use three bytes to be compatible with our `funcref`
                    // we don't care much about its representation, only
                    // that it is not a null reference.
                    vec![0, val.parse::<u32>().unwrap(), 1]
                }
            }
            "funcref" => {
                let val = val.value.as_str().unwrap();
                if val == "null" {
                    NULL_REF.into()
                } else {
                    panic!("Unexpected funcref value: {val}");
                }
            }
            _ => todo!(),
        }
    }
}
