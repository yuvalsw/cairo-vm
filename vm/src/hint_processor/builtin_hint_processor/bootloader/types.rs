use crate::{types::program::Program, vm::runners::cairo_pie::CairoPie};
use felt::Felt252;
use serde::Deserialize;
use std::path::Path;

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct BootloaderConfig {
    pub simple_bootloader_program_hash: Felt252,
    pub supported_cairo_verifier_program_hashes: Vec<Felt252>,
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub enum PackedOutput {
    Plain(Vec<Felt252>),
    Composite(Vec<Felt252>),
}

impl PackedOutput {
    // TODO: implement and define return type
    pub fn elements_for_hash(&self) -> Vec<()> {
        Default::default()
    }
}

#[derive(Deserialize, Debug, Clone, PartialEq)]
pub struct FactTopology {}

#[derive(Debug, Clone, PartialEq)]
pub enum Task {
    RunProgramTask(String), // TODO: need definition for RunProgramTask, at least its "program_input"
    CairoPieTask(CairoPie),
}

impl Task {
    pub fn get_program(&self) -> Program {
        // TODO: implement this method correctly
        Program::from_file(Path::new("../cairo_programs/fibonacci.json"), Some("main")).unwrap()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct SimpleBootloaderInput {
    pub fact_topologies_path: Option<String>,
    pub single_page: bool,
    pub tasks: Vec<Task>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BootloaderInput {
    pub simple_bootloader_input: SimpleBootloaderInput,
    pub bootloader_config: BootloaderConfig,
    pub packed_outputs: Vec<PackedOutput>,
}
