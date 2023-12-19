// Extensions to the VirtualMachine struct.
// These functions were implemented as part of the Python VM.
// Consider whether these should be added to the `VirtualMachine` implementation.

use crate::types::program::Program;
use crate::types::relocatable::Relocatable;
use crate::vm::errors::vm_errors::VirtualMachineError;
use crate::vm::vm_core::VirtualMachine;

fn load_debug_info(
    _vm: &mut VirtualMachine,
    program: &Program,
    _program_base: &Relocatable,
) -> Result<(), VirtualMachineError> {
    // Not implemented in the Rust VM
    // self.debug_file_contents.update(debug_info.file_contents)

    let instruction_locations = match &program.shared_program_data.instruction_locations {
        None => {
            return Ok(());
        }
        Some(instruction_locations) => instruction_locations,
    };

    for (_offset, _location_info) in instruction_locations {
        // TODO: this is not implemented in the Rust VM, do we need it?
        // self.instruction_debug_info[program_base + offset] = location_info
    }

    Ok(())
}

fn load_hints(
    vm: &mut VirtualMachine,
    program: &Program,
    program_base: &Relocatable,
) -> Result<(), VirtualMachineError> {
    Ok(())
}

pub fn vm_load_program(
    vm: &mut VirtualMachine,
    program: &Program,
    program_base: &Relocatable,
) -> Result<(), VirtualMachineError> {
    load_debug_info(vm, program, program_base)?;
    load_hints(vm, program, program_base)?;

    Ok(())
}
