use bincode::enc::write::Writer;
use cairo_lang_compiler::{compile_cairo_project_at_path, CompilerConfig};
use cairo_lang_sierra::{ids::ConcreteTypeId, program_registry::ProgramRegistryError};
use cairo_lang_sierra_to_casm::{compiler::CompilationError, metadata::MetadataError};
use cairo_run::Cairo1RunConfig;
use cairo_vm::{
    air_public_input::PublicInputError,
    cairo_run::EncodeTraceError,
    types::{errors::program_errors::ProgramError, layout_name::LayoutName},
    vm::errors::{
        memory_errors::MemoryError, runner_errors::RunnerError, trace_errors::TraceError,
        vm_errors::VirtualMachineError,
    },
    Felt252,
};
use clap::{Parser, ValueHint};
use itertools::Itertools;
use std::{
    io::{self, Write},
    path::PathBuf,
};
use thiserror::Error;

pub mod cairo_run;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    #[clap(value_parser, value_hint=ValueHint::FilePath)]
    filename: PathBuf,
    #[clap(long = "trace_file", value_parser)]
    trace_file: Option<PathBuf>,
    #[structopt(long = "memory_file")]
    memory_file: Option<PathBuf>,
    #[clap(long = "layout", default_value = "plain", value_enum)]
    layout: LayoutName,
    #[clap(long = "proof_mode", value_parser)]
    proof_mode: bool,
    #[clap(long = "air_public_input", requires = "proof_mode")]
    air_public_input: Option<PathBuf>,
    #[clap(
        long = "air_private_input",
        requires_all = ["proof_mode", "trace_file", "memory_file"] 
    )]
    air_private_input: Option<PathBuf>,
    #[clap(
        long = "cairo_pie_output",
        // We need to add these air_private_input & air_public_input or else
        // passing cairo_pie_output + either of these without proof_mode will not fail
        conflicts_with_all = ["proof_mode", "air_private_input", "air_public_input"]
    )]
    cairo_pie_output: Option<PathBuf>,
    // Arguments should be spaced, with array elements placed between brackets
    // For example " --args '1 2 [1 2 3]'" will yield 3 arguments, with the last one being an array of 3 elements
    #[clap(long = "args", default_value = "", value_parser=process_args)]
    args: FuncArgs,
    #[clap(long = "print_output", value_parser)]
    print_output: bool,
    #[clap(
        long = "append_return_values",
        // We need to add these air_private_input & air_public_input or else
        // passing cairo_pie_output + either of these without proof_mode will not fail
        conflicts_with_all = ["proof_mode", "air_private_input", "air_public_input"]
    )]
    append_return_values: bool,
}

#[derive(Debug, Clone)]
pub enum FuncArg {
    Array(Vec<Felt252>),
    Single(Felt252),
}

#[derive(Debug, Clone, Default)]
struct FuncArgs(Vec<FuncArg>);

fn process_args(value: &str) -> Result<FuncArgs, String> {
    if value.is_empty() {
        return Ok(FuncArgs::default());
    }
    let mut args = Vec::new();
    let mut input = value.split(' ');
    while let Some(value) = input.next() {
        // First argument in an array
        if value.starts_with('[') {
            let mut array_arg =
                vec![Felt252::from_dec_str(value.strip_prefix('[').unwrap()).unwrap()];
            // Process following args in array
            let mut array_end = false;
            while !array_end {
                if let Some(value) = input.next() {
                    // Last arg in array
                    if value.ends_with(']') {
                        array_arg
                            .push(Felt252::from_dec_str(value.strip_suffix(']').unwrap()).unwrap());
                        array_end = true;
                    } else {
                        array_arg.push(Felt252::from_dec_str(value).unwrap())
                    }
                }
            }
            // Finalize array
            args.push(FuncArg::Array(array_arg))
        } else {
            // Single argument
            args.push(FuncArg::Single(Felt252::from_dec_str(value).unwrap()))
        }
    }
    Ok(FuncArgs(args))
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("Invalid arguments")]
    Cli(#[from] clap::Error),
    #[error("Failed to interact with the file system")]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    EncodeTrace(#[from] EncodeTraceError),
    #[error(transparent)]
    VirtualMachine(#[from] VirtualMachineError),
    #[error(transparent)]
    Trace(#[from] TraceError),
    #[error(transparent)]
    PublicInput(#[from] PublicInputError),
    #[error(transparent)]
    Runner(#[from] RunnerError),
    #[error(transparent)]
    ProgramRegistry(#[from] Box<ProgramRegistryError>),
    #[error(transparent)]
    Compilation(#[from] Box<CompilationError>),
    #[error("Failed to compile to sierra:\n {0}")]
    SierraCompilation(String),
    #[error(transparent)]
    Metadata(#[from] MetadataError),
    #[error(transparent)]
    Program(#[from] ProgramError),
    #[error(transparent)]
    Memory(#[from] MemoryError),
    #[error("Program panicked with {0:?}")]
    RunPanic(Vec<Felt252>),
    #[error("Function signature has no return types")]
    NoRetTypesInSignature,
    #[error("No size for concrete type id: {0}")]
    NoTypeSizeForId(ConcreteTypeId),
    #[error("Concrete type id has no debug name: {0}")]
    TypeIdNoDebugName(ConcreteTypeId),
    #[error("No info in sierra program registry for concrete type id: {0}")]
    NoInfoForType(ConcreteTypeId),
    #[error("Failed to extract return values from VM")]
    FailedToExtractReturnValues,
    #[error("Function expects arguments of size {expected} and received {actual} instead.")]
    ArgumentsSizeMismatch { expected: i16, actual: i16 },
    #[error("Function param {param_index} only partially contains argument {arg_index}.")]
    ArgumentUnaligned {
        param_index: usize,
        arg_index: usize,
    },
}

pub struct FileWriter {
    buf_writer: io::BufWriter<std::fs::File>,
    bytes_written: usize,
}

impl Writer for FileWriter {
    fn write(&mut self, bytes: &[u8]) -> Result<(), bincode::error::EncodeError> {
        self.buf_writer
            .write_all(bytes)
            .map_err(|e| bincode::error::EncodeError::Io {
                inner: e,
                index: self.bytes_written,
            })?;

        self.bytes_written += bytes.len();

        Ok(())
    }
}

impl FileWriter {
    fn new(buf_writer: io::BufWriter<std::fs::File>) -> Self {
        Self {
            buf_writer,
            bytes_written: 0,
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        self.buf_writer.flush()
    }
}

fn run(args: impl Iterator<Item = String>) -> Result<Option<String>, Error> {
    let args = Args::try_parse_from(args)?;

    let cairo_run_config = Cairo1RunConfig {
        proof_mode: args.proof_mode,
        serialize_output: args.print_output,
        relocate_mem: args.memory_file.is_some() || args.air_public_input.is_some(),
        layout: args.layout,
        trace_enabled: args.trace_file.is_some() || args.air_public_input.is_some(),
        args: &args.args.0,
        finalize_builtins: args.air_private_input.is_some() || args.cairo_pie_output.is_some(),
        append_return_values: args.append_return_values,
    };

    let compiler_config = CompilerConfig {
        replace_ids: true,
        ..CompilerConfig::default()
    };

    let sierra_program = compile_cairo_project_at_path(&args.filename, compiler_config)
        .map_err(|err| Error::SierraCompilation(err.to_string()))?;

    let (runner, vm, _, serialized_output) =
        cairo_run::cairo_run_program(&sierra_program, cairo_run_config)?;

    if let Some(file_path) = args.air_public_input {
        let json = runner.get_air_public_input(&vm)?.serialize_json()?;
        std::fs::write(file_path, json)?;
    }

    if let (Some(file_path), Some(trace_file), Some(memory_file)) = (
        args.air_private_input,
        args.trace_file.clone(),
        args.memory_file.clone(),
    ) {
        // Get absolute paths of trace_file & memory_file
        let trace_path = trace_file
            .as_path()
            .canonicalize()
            .unwrap_or(trace_file.clone())
            .to_string_lossy()
            .to_string();
        let memory_path = memory_file
            .as_path()
            .canonicalize()
            .unwrap_or(memory_file.clone())
            .to_string_lossy()
            .to_string();

        let json = runner
            .get_air_private_input(&vm)
            .to_serializable(trace_path, memory_path)
            .serialize_json()
            .map_err(PublicInputError::Serde)?;
        std::fs::write(file_path, json)?;
    }

    if let Some(ref file_path) = args.cairo_pie_output {
        runner.get_cairo_pie(&vm)?.write_zip_file(file_path)?
    }

    if let Some(trace_path) = args.trace_file {
        let relocated_trace = runner
            .relocated_trace
            .ok_or(Error::Trace(TraceError::TraceNotRelocated))?;
        let trace_file = std::fs::File::create(trace_path)?;
        let mut trace_writer =
            FileWriter::new(io::BufWriter::with_capacity(3 * 1024 * 1024, trace_file));

        cairo_vm::cairo_run::write_encoded_trace(&relocated_trace, &mut trace_writer)?;
        trace_writer.flush()?;
    }
    if let Some(memory_path) = args.memory_file {
        let memory_file = std::fs::File::create(memory_path)?;
        let mut memory_writer =
            FileWriter::new(io::BufWriter::with_capacity(5 * 1024 * 1024, memory_file));

        cairo_vm::cairo_run::write_encoded_memory(&runner.relocated_memory, &mut memory_writer)?;
        memory_writer.flush()?;
    }

    Ok(serialized_output)
}

fn main() -> Result<(), Error> {
    match run(std::env::args()) {
        Err(Error::Cli(err)) => err.exit(),
        Ok(output) => {
            if let Some(output_string) = output {
                println!("Program Output : {}", output_string);
            }
            Ok(())
        }
        Err(Error::RunPanic(panic_data)) => {
            if !panic_data.is_empty() {
                let panic_data_string_list = panic_data
                    .iter()
                    .map(|m| {
                        // Try to parse to utf8 string
                        let msg = String::from_utf8(m.to_bytes_be().to_vec());
                        if let Ok(msg) = msg {
                            format!("{} ('{}')", m, msg)
                        } else {
                            m.to_string()
                        }
                    })
                    .join(", ");
                println!("Run panicked with: [{}]", panic_data_string_list);
            }
            Ok(())
        }
        Err(err) => Err(err),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;
    use rstest::rstest;

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/fibonacci.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/fibonacci.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_fibonacci_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "89");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/factorial.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/factorial.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_factorial_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "3628800");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/array_get.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/array_get.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_array_get_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "3");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/enum_flow.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/enum_flow.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_enum_flow_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "300");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/enum_match.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/enum_match.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_enum_match_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "10 3618502788666131213697322783095070105623107215331596699973092056135872020471");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/hello.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/hello.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_hello_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "1234");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/ops.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/ops.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_ops_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "6");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/print.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/print.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_print_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res.is_empty());
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/recursion.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/recursion.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_recursion_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "1154076154663935037074198317650845438095734251249125412074882362667803016453");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/sample.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/sample.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_sample_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "5050");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/poseidon.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/poseidon.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_poseidon_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "1099385018355113290651252669115094675591288647745213771718157553170111442461");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/poseidon_pedersen.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/poseidon_pedersen.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_poseidon_pedersen_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "1036257840396636296853154602823055519264738423488122322497453114874087006398");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/pedersen_example.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/pedersen_example.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_pedersen_example_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "1089549915800264549621536909767699778745926517555586332772759280702396009108");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/simple.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/simple.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_simple_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "true");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/simple_struct.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/simple_struct.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_simple_struct_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "100");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/dictionaries.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/dictionaries.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_dictionaries(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "1024");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/with_input/branching.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null", "--args", "0"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/with_input/branching.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null", "--args", "0"].as_slice())]
    fn test_run_branching_0(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "1");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/with_input/branching.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null", "--args", "17"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/with_input/branching.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null", "--args", "96"].as_slice())]
    fn test_run_branching_not_0(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "0");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/with_input/branching.cairo", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/with_input/branching.cairo", "--layout", "all_cairo", "--proof_mode"].as_slice())]
    fn test_run_branching_no_args(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Err(Error::ArgumentsSizeMismatch { expected, actual }) if expected == 1 && actual == 0);
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/with_input/branching.cairo", "--layout", "all_cairo","--args", "1 2 3"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/with_input/branching.cairo", "--layout", "all_cairo", "--proof_mode", "--args", "1 2 3"].as_slice())]
    fn test_run_branching_too_many_args(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Err(Error::ArgumentsSizeMismatch { expected, actual }) if expected == 1 && actual == 3);
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/with_input/array_input_sum.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null", "--args", "2 [1 2 3 4] 0 [9 8]"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/with_input/array_input_sum.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null", "--args", "2 [1 2 3 4] 0 [9 8]"].as_slice())]
    fn test_array_input_sum(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "12");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/struct_span_return.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/struct_span_return.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_struct_span_return(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "[[4 3] [2 1]]");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/with_input/tensor.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null", "--args", "[2 2] [1 2 3 4]"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/with_input/tensor.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null", "--args", "[2 2] [1 2 3 4]"].as_slice())]
    fn test_tensor(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res == "1");
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/nullable_dict.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/nullable_dict.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_nullable_dict_ok(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        assert_matches!(run(args), Ok(Some(res)) if res.is_empty());
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/felt_dict.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/felt_dict.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_felt_dict(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        let expected_output = "{66675: [8 9 10 11] 66676: [1 2 3]}";
        assert_matches!(run(args), Ok(Some(res)) if res == expected_output);
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/felt_span.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/felt_span.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_felt_span(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        let expected_output = "[8 9 10 11]";
        assert_matches!(run(args), Ok(Some(res)) if res == expected_output);
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/array_integer_tuple.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/array_integer_tuple.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_array_integer_tuple(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        let expected_output = "[1] 1";
        assert_matches!(run(args), Ok(Some(res)) if res == expected_output);
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/nullable_box_vec.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/nullable_box_vec.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_nullable_box_vec(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        let expected_output = "{0: 10 1: 20 2: 30} 3";
        assert_matches!(run(args), Ok(Some(res)) if res == expected_output);
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/dict_with_struct.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/dict_with_struct.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_dict_with_struct(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        let expected_output = "{0: 1 true 1: 1 false 2: 1 true}";
        assert_matches!(run(args), Ok(Some(res)) if res == expected_output);
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/felt_dict_squash.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/felt_dict_squash.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_felt_dict_squash(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        let expected_output = "{66675: [4 5 6] 66676: [1 2 3]}";
        assert_matches!(run(args), Ok(Some(res)) if res == expected_output);
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/null_ret.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/null_ret.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_null_ret(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        let expected_output = "null";
        assert_matches!(run(args), Ok(Some(res)) if res == expected_output);
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/bytes31_ret.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/bytes31_ret.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_bytes31_ret(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        let expected_output = "123";
        assert_matches!(run(args), Ok(Some(res)) if res == expected_output);
    }

    #[rstest]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/tensor_new.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--cairo_pie_output", "/dev/null"].as_slice())]
    #[case(["cairo1-run", "../cairo_programs/cairo-1-programs/tensor_new.cairo", "--print_output", "--trace_file", "/dev/null", "--memory_file", "/dev/null", "--layout", "all_cairo", "--proof_mode", "--air_public_input", "/dev/null", "--air_private_input", "/dev/null"].as_slice())]
    fn test_run_tensor_new(#[case] args: &[&str]) {
        let args = args.iter().cloned().map(String::from);
        let expected_output = "[1 2] [1 false 1 true]";
        assert_matches!(run(args), Ok(Some(res)) if res == expected_output);
    }
}
