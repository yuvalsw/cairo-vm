pub mod cairo_run;
pub mod error;
// Re-export main struct and functions from crate for convenience
pub use crate::cairo_run::{cairo_run_program, Cairo1RunConfig, FuncArg};
// Re-export cairo_vm structs returned by this crate for ease of use
pub use cairo_vm::{
    types::relocatable::{MaybeRelocatable, Relocatable},
    vm::{runners::cairo_runner::CairoRunner, vm_core::VirtualMachine},
    Felt252,
};
