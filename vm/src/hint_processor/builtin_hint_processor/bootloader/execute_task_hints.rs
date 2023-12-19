use crate::hint_processor::builtin_hint_processor::bootloader::program_hash::compute_program_hash_chain;
use crate::types::errors::math_errors::MathError;
use crate::types::relocatable::Relocatable;
use felt::Felt252;
use num_traits::ToPrimitive;
use starknet_crypto::FieldElement;
use std::collections::HashMap;

use crate::any_box;
use std::any::Any;

use crate::hint_processor::builtin_hint_processor::bootloader::fact_topologies::{
    get_program_task_fact_topology, FactTopology,
};
use crate::hint_processor::builtin_hint_processor::bootloader::program_loader::ProgramLoader;
use crate::hint_processor::builtin_hint_processor::bootloader::types::{BootloaderVersion, Task};
use crate::hint_processor::builtin_hint_processor::bootloader::vars;
use crate::hint_processor::builtin_hint_processor::hint_utils::{
    get_ptr_from_var_name, get_relocatable_from_var_name, insert_value_from_var_name,
};
use crate::hint_processor::hint_processor_definition::HintReference;
use crate::serde::deserialize_program::{ApTracking, BuiltinName};
use crate::types::exec_scope::ExecutionScopes;
use crate::vm::errors::hint_errors::HintError;
use crate::vm::runners::cairo_pie::CairoPie;
use crate::vm::runners::cairo_pie::{OutputBuiltinAdditionalData, StrippedProgram};
use crate::vm::vm_core::VirtualMachine;
use crate::vm::vm_memory::memory::Memory;

fn get_program_from_task(task: &Task) -> Result<StrippedProgram, HintError> {
    task.get_program()
        .map_err(|e| HintError::CustomHint(e.to_string().into_boxed_str()))
}

use self::util::load_cairo_pie;

/// Implements %{ ids.program_data_ptr = program_data_base = segments.add() %}.
///
/// Creates a new segment to store the program data.
pub fn allocate_program_data_segment(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let program_data_segment = vm.add_memory_segment();
    exec_scopes.insert_value(vars::PROGRAM_DATA_BASE, program_data_segment.clone());
    insert_value_from_var_name(
        "program_data_ptr",
        program_data_segment,
        vm,
        ids_data,
        ap_tracking,
    )?;

    Ok(())
}

fn field_element_to_felt(field_element: FieldElement) -> Felt252 {
    let bytes = field_element.to_bytes_be();
    Felt252::from_bytes_be(&bytes)
}

/// Implements
///
/// from starkware.cairo.bootloaders.simple_bootloader.utils import load_program
///
/// # Call load_program to load the program header and code to memory.
/// program_address, program_data_size = load_program(
///     task=task, memory=memory, program_header=ids.program_header,
///     builtins_offset=ids.ProgramHeader.builtin_list)
/// segments.finalize(program_data_base.segment_index, program_data_size)
pub fn load_program_hint(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let program_data_base: Relocatable = exec_scopes.get(vars::PROGRAM_DATA_BASE)?;
    let task: Task = exec_scopes.get(vars::TASK)?;
    let program = get_program_from_task(&task)?;

    let program_header_ptr = get_ptr_from_var_name("program_header", vm, ids_data, ap_tracking)?;

    // Offset of the builtin_list field in `ProgramHeader`, cf. execute_task.cairo
    let builtins_offset = 4;
    let mut program_loader = ProgramLoader::new(&mut vm.segments.memory, builtins_offset);
    let bootloader_version: BootloaderVersion = 0;
    let loaded_program = program_loader
        .load_program(&program_header_ptr, &program, Some(bootloader_version))
        .map_err(Into::<HintError>::into)?;

    vm.segments.finalize(
        Some(loaded_program.size),
        program_data_base.segment_index as usize,
        None,
    );

    exec_scopes.insert_value(vars::PROGRAM_ADDRESS, loaded_program.code_address);

    Ok(())
}

/*
Implements hint:
%{
    "from starkware.cairo.bootloaders.simple_bootloader.objects import (
        CairoPieTask,
        RunProgramTask,
        Task,
    )
    from starkware.cairo.bootloaders.simple_bootloader.utils import (
        load_cairo_pie,
        prepare_output_runner,
    )

    assert isinstance(task, Task)
    n_builtins = len(task.get_program().builtins)
    new_task_locals = {}
    if isinstance(task, RunProgramTask):
        new_task_locals['program_input'] = task.program_input
        new_task_locals['WITH_BOOTLOADER'] = True

        vm_load_program(task.program, program_address)
    elif isinstance(task, CairoPieTask):
        ret_pc = ids.ret_pc_label.instruction_offset_ - ids.call_task.instruction_offset_ + pc
        load_cairo_pie(
            task=task.cairo_pie, memory=memory, segments=segments,
            program_address=program_address, execution_segment_address= ap - n_builtins,
            builtin_runners=builtin_runners, ret_fp=fp, ret_pc=ret_pc)
    else:
        raise NotImplementedError(f'Unexpected task type: {type(task).__name__}.')

    output_runner_data = prepare_output_runner(
        task=task,
        output_builtin=output_builtin,
        output_ptr=ids.pre_execution_builtin_ptrs.output)
    vm_enter_scope(new_task_locals)"
%}
*/
pub fn call_task(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    // assert isinstance(task, Task)
    let task: Task = exec_scopes.get(vars::TASK)?;

    // n_builtins = len(task.get_program().builtins)
    let num_builtins = get_program_from_task(&task)?.builtins.len();

    let mut new_task_locals = HashMap::new();

    // TODO: remove clone here when RunProgramTask has proper variant data (not String)
    match task.clone() {
        // if isinstance(task, RunProgramTask):
        Task::Program(program_input) => {
            // new_task_locals['program_input'] = task.program_input
            new_task_locals.insert("program_input".to_string(), any_box![program_input]);
            // new_task_locals['WITH_BOOTLOADER'] = True
            new_task_locals.insert("WITH_BOOTLOADER".to_string(), any_box![true]);

            // TODO:
            // vm_load_program(task.program, program_address)
        }
        // elif isinstance(task, CairoPieTask):
        Task::Pie(task) => {
            let program_address: Relocatable = exec_scopes.get("program_address")?;

            // ret_pc = ids.ret_pc_label.instruction_offset_ - ids.call_task.instruction_offset_ + pc
            // load_cairo_pie(
            //     task=task.cairo_pie, memory=memory, segments=segments,
            //     program_address=program_address, execution_segment_address= ap - n_builtins,
            //     builtin_runners=builtin_runners, ret_fp=fp, ret_pc=ret_pc)
            load_cairo_pie(
                &task,
                vm,
                program_address,
                (vm.get_ap() - num_builtins)?,
                vm.get_fp(),
                vm.get_pc(),
            )?;
        }
    }

    // output_runner_data = prepare_output_runner(
    //     task=task,
    //     output_builtin=output_builtin,
    //     output_ptr=ids.pre_execution_builtin_ptrs.output)
    let pre_execution_builtin_ptrs_addr =
        get_relocatable_from_var_name(vars::PRE_EXECUTION_BUILTIN_PTRS, vm, ids_data, ap_tracking)?;
    let output = vm
        .get_integer(pre_execution_builtin_ptrs_addr)?
        .into_owned();
    let output_ptr = output
        .to_usize()
        .ok_or(MathError::Felt252ToUsizeConversion(Box::new(output)))?;
    let output_runner_data =
        util::prepare_output_runner(&task, vm.get_output_builtin()?, output_ptr)?;

    exec_scopes.insert_box(vars::OUTPUT_RUNNER_DATA, any_box!(output_runner_data));

    exec_scopes.enter_scope(new_task_locals);

    Ok(())
}

/// Implements
/// from starkware.cairo.bootloaders.simple_bootloader.utils import get_task_fact_topology
///
/// # Add the fact topology of the current task to 'fact_topologies'.
/// output_start = ids.pre_execution_builtin_ptrs.output
/// output_end = ids.return_builtin_ptrs.output
/// fact_topologies.append(get_task_fact_topology(
///     output_size=output_end - output_start,
///     task=task,
///     output_builtin=output_builtin,
///     output_runner_data=output_runner_data,
/// ))
pub fn append_fact_topologies(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let task: Task = exec_scopes.get(vars::TASK)?;
    let output_runner_data: OutputBuiltinAdditionalData =
        exec_scopes.get(vars::OUTPUT_RUNNER_DATA)?;
    let fact_topologies: &mut Vec<FactTopology> = exec_scopes.get_mut_ref(vars::FACT_TOPOLOGIES)?;

    let pre_execution_builtin_ptrs_addr =
        get_relocatable_from_var_name("pre_execution_builtin_ptrs", vm, ids_data, ap_tracking)?;
    let return_builtin_ptrs_addr =
        get_relocatable_from_var_name("return_builtin_ptrs", vm, ids_data, ap_tracking)?;

    // The output field is the first one in the BuiltinData struct
    let output_start = vm
        .get_integer(pre_execution_builtin_ptrs_addr)?
        .into_owned();
    let output_end = vm.get_integer(return_builtin_ptrs_addr)?.into_owned();
    let output_size = {
        let output_size_felt = output_end - output_start;
        output_size_felt
            .to_usize()
            .ok_or(MathError::Felt252ToUsizeConversion(Box::new(
                output_size_felt,
            )))
    }?;

    let output_builtin = vm.get_output_builtin()?;
    let fact_topology =
        get_program_task_fact_topology(output_size, &task, output_builtin, output_runner_data)
            .map_err(Into::<HintError>::into)?;
    fact_topologies.push(fact_topology);

    Ok(())
}

mod util {
    use crate::{
        types::relocatable::{relocate_address, relocate_value, MaybeRelocatable},
        vm::runners::{
            builtin_runner::{
                BuiltinRunner, OutputBuiltinRunner, SignatureBuiltinRunner, SIGNATURE_BUILTIN_NAME,
            },
            cairo_pie::{BuiltinAdditionalData, OutputBuiltinAdditionalData},
        },
    };

    // TODO: clean up / organize
    use super::*;

    pub(crate) fn load_cairo_pie(
        task: &CairoPie,
        vm: &mut VirtualMachine,
        program_address: Relocatable,
        execution_segment_address: Relocatable,
        ret_fp: Relocatable,
        ret_pc: Relocatable,
    ) -> Result<(), HintError> {
        // Load memory entries of the inner program.
        // This replaces executing hints in a non-trusted program.
        // We use a Vec as a mapping of usize -> usize to represent a relocation table, as used in
        // relocate_address() below. However, we also define an insertion fn to ensure "write-once"
        // behavior
        const RELOCATABLE_TABLE_SIZE: usize = 256;
        let mut segment_offsets = vec![0usize; RELOCATABLE_TABLE_SIZE];
        let mut segment_offsets_written = vec![false; RELOCATABLE_TABLE_SIZE];
        let mut write_once = |k: usize, v: usize| {
            if k >= RELOCATABLE_TABLE_SIZE {
                return Err(HintError::CustomHint(
                    format!("WriteOnce OOB (k: {}, v: {})", k, v)
                        .to_string()
                        .into_boxed_str()
                ));
            }

            return if segment_offsets_written[k] {
                Err(HintError::CustomHint(
                    format!("WriteOnce violation for k: {}, v: {}", k, v)
                        .to_string()
                        .into_boxed_str(),
                ))
            } else {
                segment_offsets[k] = v;
                segment_offsets_written[k] = true;
                Ok(())
            };
        };

        write_once(
            task.metadata.program_segment.index as usize,
            program_address.segment_index as usize,
        )?;
        write_once(
            task.metadata.execution_segment.index as usize,
            execution_segment_address.segment_index as usize,
        )?;
        write_once(
            task.metadata.ret_fp_segment.index as usize,
            ret_fp.segment_index as usize,
        )?;
        write_once(
            task.metadata.ret_pc_segment.index as usize,
            ret_pc.segment_index as usize,
        )?;

        // Returns the segment index for the given value.
        // Verifies that value is a RelocatableValue with offset 0.
        let extract_segment = |value, _value_name| -> Result<isize, HintError> {
            return match value {
                MaybeRelocatable::RelocatableValue(r) if r.offset != 0 => {
                    Err(HintError::WrongHintData)
                } // TODO: error
                MaybeRelocatable::RelocatableValue(r) if r.offset == 0 => Ok(r.segment_index),
                _ => Err(HintError::WrongHintData), // TODO: error
            };
        };

        let origin_execution_segment = Relocatable {
            segment_index: task.metadata.execution_segment.index,
            offset: 0,
        };

        // Set initial stack relocations.
        let mut idx = 0;
        for builtin in task.metadata.program.builtins.iter() {
            // task.memory is a CairoPieMemory, aka Vec<((usize, usize), MaybeRelocatable)>
            // Assumptions:
            //     * the (usize, usize) is a (segment_index, offset) pair
            //     * the Vec's order and packing is arbitrary, so we scan for matches
            let key: Relocatable = (origin_execution_segment + idx)?;
            let pie_mem_element = task
                .memory
                .iter()
                .find_map(|entry| {
                    return if entry.0 == (key.segment_index as usize, key.offset) {
                        Some(entry.1.clone())
                    } else {
                        None
                    };
                })
                .ok_or(HintError::EmptyKeys)?; // TODO: proper error

            let index = extract_segment(pie_mem_element, builtin)? as usize;
            assert!(index < RELOCATABLE_TABLE_SIZE);

            let mem_at = (execution_segment_address + idx)?;
            write_once(index, vm.get_relocatable(mem_at)?.segment_index as usize)?;
            idx += 1;
        }

        for segment_info in &task.metadata.extra_segments {
            let index = segment_info.index as usize;
            assert!(index < RELOCATABLE_TABLE_SIZE);
            // TODO: previous passed 'size' to add()
            write_once(index, vm.add_memory_segment().segment_index as usize)?;
        }

        let local_relocate_value = |value| -> Result<usize, HintError> {
            relocate_address(value, &segment_offsets)
                .map_err(|e| HintError::CustomHint(format!("Memory error: {}", e).into_boxed_str()))
        };

        let extend_additional_data = |data: &HashMap<Relocatable, (Felt252, Felt252)>,
                                      builtin: &mut SignatureBuiltinRunner|
         -> Result<(), HintError> {
            for (addr, signature) in data {
                let relocated_addr = local_relocate_value(*addr)?;
                if relocated_addr != builtin.base() {
                    return Err(HintError::CustomHint(
                        format!(
                            "expected relocated addr ({}) to equal builtin ({})",
                            relocated_addr,
                            builtin.base()
                        )
                        .into_boxed_str(),
                    ));
                }
                builtin.add_signature(*addr, signature).map_err(|e| {
                    HintError::CustomHint(format!("Memory error: {}", e).into_boxed_str())
                })?;
            }

            Ok(())
        };

        // Relocate builtin additional data.
        // This should occur before the memory relocation, since the signature builtin assumes that a
        // signature is added before the corresponding public key and message are both written to memory.
        let ecdsa_additional_data = task.additional_data.get("ecdsa_builtin");
        if let Some(ecdsa_additional_data) = ecdsa_additional_data {
            let ecdsa_builtin = vm
                .get_builtin_runners_as_mut()
                .iter_mut()
                .find(|builtin: &&mut BuiltinRunner| builtin.name() == SIGNATURE_BUILTIN_NAME)
                .ok_or(HintError::CustomHint(
                    "The task requires the ecdsa builtin but it is missing."
                        .to_string()
                        .into_boxed_str(),
                ))?;

            let signature_additional_data =
                if let BuiltinAdditionalData::Signature(ecdsa_additional_data) =
                    ecdsa_additional_data
                {
                    Ok(ecdsa_additional_data)
                } else {
                    Err(HintError::CustomHint(
                        "ECDSA builtin data should be of type Signature"
                            .to_string()
                            .into_boxed_str(),
                    ))
                }?;

            match ecdsa_builtin {
                BuiltinRunner::Signature(signature) => Ok(extend_additional_data(
                    signature_additional_data,
                    signature,
                )?),
                // TODO: better way to express this
                _ => Err(HintError::CustomHint(
                    "Unreachable".to_string().into_boxed_str(),
                )),
            }?;
        }

        // Relocate memory segment
        for item in &task.memory {
            let (segment_index, offset) = item.0;
            let segment_index = segment_index as isize;
            let _key = relocate_value(MaybeRelocatable::from((segment_index, offset)), &segment_offsets)?;

            let value = item.1.clone();
            let value = relocate_value(value, &segment_offsets)?;
            // TODO: previous impl checked prime number
            let res = vm.segments.memory.insert(
                Relocatable {
                    segment_index,
                    offset,
                },
                value.clone(),
            );
            
            println!("inserted ({}, {}) => {}, got res: {:?}", segment_index, offset, value, res);

            res?
        }

        Ok(())
    }

    /// Prepares the output builtin if the type of task is Task, so that pages of the inner program
    /// will be recorded separately.
    /// If the type of task is CairoPie, nothing should be done, as the program does not contain
    /// hints that may affect the output builtin.
    /// The return value of this function should be later passed to get_task_fact_topology().
    pub(crate) fn prepare_output_runner(
        task: &Task,
        output_builtin: &mut OutputBuiltinRunner,
        output_ptr: usize,
    ) -> Result<Option<OutputBuiltinAdditionalData>, HintError> {
        return match task {
            Task::Program(_) => {
                let output_state = match output_builtin.get_additional_data() {
                    BuiltinAdditionalData::Output(output_state) => Ok(output_state),
                    _ => Err(HintError::CustomHint(
                        "output_builtin's additional data is not type Output"
                            .to_string()
                            .into_boxed_str(),
                    )),
                }?;
                output_builtin.base = output_ptr;
                Ok(Some(output_state))
            }
            Task::Pie(_) => Ok(None),
        };
    }
}

/// Implements
/// # Validate hash.
/// from starkware.cairo.bootloaders.hash_program import compute_program_hash_chain
///
/// assert memory[ids.output_ptr + 1] == compute_program_hash_chain(task.get_program()), \
///   'Computed hash does not match input.'";
pub fn validate_hash(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let task: Task = exec_scopes.get(vars::TASK)?;
    let program = get_program_from_task(&task)?;

    let output_ptr = get_ptr_from_var_name("output_ptr", vm, ids_data, ap_tracking)?;
    let program_hash_ptr = (output_ptr + 1)?;

    let program_hash = vm
        .segments
        .memory
        .get_integer(program_hash_ptr)?
        .into_owned();

    // Compute the hash of the program
    let computed_program_hash = compute_program_hash_chain(&program, 0)
        .map_err(|e| {
            HintError::CustomHint(format!("Could not compute program hash: {e}").into_boxed_str())
        })?
        .into();
    let computed_program_hash = field_element_to_felt(computed_program_hash);

    if program_hash != computed_program_hash {
        return Err(HintError::AssertionFailed(
            "Computed hash does not match input"
                .to_string()
                .into_boxed_str(),
        ));
    }

    Ok(())
}

/// List of all builtins in the order used by the bootloader.
const ALL_BUILTINS: [BuiltinName; 8] = [
    BuiltinName::output,
    BuiltinName::pedersen,
    BuiltinName::range_check,
    BuiltinName::ecdsa,
    BuiltinName::bitwise,
    BuiltinName::ec_op,
    BuiltinName::keccak,
    BuiltinName::poseidon,
];

/// Writes the updated builtin pointers after the program execution to the given return builtins
/// address.
///     
/// `used_builtins` is the list of builtins used by the program and thus updated by it.
fn write_return_builtins(
    memory: &mut Memory,
    return_builtins_addr: &Relocatable,
    used_builtins: &[BuiltinName],
    used_builtins_addr: &Relocatable,
    pre_execution_builtins_addr: &Relocatable,
    _task: &Task,
) -> Result<(), HintError> {
    let mut used_builtin_offset: usize = 0;
    for (index, builtin) in ALL_BUILTINS.iter().enumerate() {
        if used_builtins.contains(builtin) {
            let builtin_value = memory
                .get_integer(used_builtins_addr + used_builtin_offset)?
                .into_owned();
            memory.insert_value(return_builtins_addr + index, builtin_value)?;
            used_builtin_offset += 1;

            // TODO: if isinstance(task, CairoPie) check
        }
        // The builtin is unused, hence its value is the same as before calling the program.
        else {
            let pre_execution_value = memory
                .get_integer(pre_execution_builtins_addr + index)?
                .into_owned();
            memory.insert_value(return_builtins_addr + index, pre_execution_value)?;
        }
    }
    Ok(())
}

/// Implements
/// from starkware.cairo.bootloaders.simple_bootloader.utils import write_return_builtins
///
/// # Fill the values of all builtin pointers after executing the task.
/// builtins = task.get_program().builtins
/// write_return_builtins(
///     memory=memory, return_builtins_addr=ids.return_builtin_ptrs.address_,
///     used_builtins=builtins, used_builtins_addr=ids.used_builtins_addr,
///     pre_execution_builtins_addr=ids.pre_execution_builtin_ptrs.address_, task=task)
///
/// vm_enter_scope({'n_selected_builtins': n_builtins})
///
/// This hint looks at the builtins written by the program and merges them with the stored
/// pre-execution values (stored in a struct named ids.pre_execution_builtin_ptrs) to
/// create a final BuiltinData struct for the program.
pub fn write_return_builtins_hint(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
) -> Result<(), HintError> {
    let task: Task = exec_scopes.get(vars::TASK)?;
    let n_builtins: usize = exec_scopes.get(vars::N_BUILTINS)?;

    // builtins = task.get_program().builtins
    let program = get_program_from_task(&task)?;
    let builtins = &program.builtins;

    // write_return_builtins(
    //     memory=memory, return_builtins_addr=ids.return_builtin_ptrs.address_,
    //     used_builtins=builtins, used_builtins_addr=ids.used_builtins_addr,
    //     pre_execution_builtins_addr=ids.pre_execution_builtin_ptrs.address_, task=task)
    let return_builtins_addr =
        get_relocatable_from_var_name("return_builtin_ptrs", vm, ids_data, ap_tracking)?;
    let used_builtins_addr =
        get_ptr_from_var_name("used_builtins_addr", vm, ids_data, ap_tracking)?;
    let pre_execution_builtins_addr =
        get_relocatable_from_var_name("pre_execution_builtin_ptrs", vm, ids_data, ap_tracking)?;

    write_return_builtins(
        &mut vm.segments.memory,
        &return_builtins_addr,
        builtins,
        &used_builtins_addr,
        &pre_execution_builtins_addr,
        &task,
    )?;

    // vm_enter_scope({'n_selected_builtins': n_builtins})
    let n_builtins: Box<dyn Any> = Box::new(n_builtins);
    exec_scopes.enter_scope(HashMap::from([(
        vars::N_SELECTED_BUILTINS.to_string(),
        n_builtins,
    )]));

    Ok(())
}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;
    use rstest::{fixture, rstest};
    use std::path::Path;

    use crate::any_box;
    use crate::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::BuiltinHintProcessor;
    use crate::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::HintProcessorData;
    use crate::hint_processor::builtin_hint_processor::hint_code;
    use felt::Felt252;

    use crate::hint_processor::builtin_hint_processor::hint_utils::get_ptr_from_var_name;
    use crate::hint_processor::hint_processor_definition::HintProcessorLogic;
    use crate::types::relocatable::Relocatable;
    use crate::utils::test_utils::*;
    use crate::vm::runners::builtin_runner::{BuiltinRunner, OutputBuiltinRunner};
    use crate::vm::runners::cairo_pie::{BuiltinAdditionalData, PublicMemoryPage};

    use super::*;

    #[rstest]
    fn test_allocate_program_data_segment() {
        let mut vm = vm!();
        // Allocate space for program_data_ptr
        vm.run_context.fp = 1;
        add_segments!(vm, 2);
        let ids_data = ids_data!["program_data_ptr"];
        let expected_program_data_segment_index = vm.segments.num_segments();

        let mut exec_scopes = ExecutionScopes::new();
        let ap_tracking = ApTracking::new();

        allocate_program_data_segment(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        let program_data_ptr =
            get_ptr_from_var_name("program_data_ptr", &mut vm, &ids_data, &ap_tracking)
                .expect("program_data_ptr is not set");

        let program_data_base: Relocatable = exec_scopes
            .get(vars::PROGRAM_DATA_BASE)
            .expect(format!("{} is not set", vars::PROGRAM_DATA_BASE).as_ref());

        assert_eq!(program_data_ptr, program_data_base);
        // Check that we allocated a new segment and that the pointers point to it
        assert_eq!(
            vm.segments.num_segments(),
            expected_program_data_segment_index + 1
        );
        assert_eq!(
            program_data_ptr,
            Relocatable {
                segment_index: expected_program_data_segment_index as isize,
                offset: 0
            }
        );
    }

    #[fixture]
    fn fibonacci() -> Program {
        let program_content =
            include_bytes!("../../../../../cairo_programs/fibonacci.json").to_vec();

        Program::from_bytes(&program_content, Some("main"))
            .expect("Loading example program failed unexpectedly")
    }

    #[fixture]
    fn fibonacci_pie() -> CairoPie {
        let pie_file =
            Path::new("../cairo_programs/manually_compiled/fibonacci_cairo_pie/fibonacci_pie.zip");
        CairoPie::from_file(pie_file).expect("Failed to load the program PIE")
    }

    #[fixture]
    fn field_arithmetic_program() -> Program {
        let program_content =
            include_bytes!("../../../../../cairo_programs/field_arithmetic.json").to_vec();

        Program::from_bytes(&program_content, Some("main"))
            .expect("Loading example program failed unexpectedly")
    }

    #[rstest]
    fn test_load_program(fibonacci: Program) {
        let task = Task::Program(fibonacci.clone());

        let mut vm = vm!();
        vm.run_context.fp = 1;
        // Set program_header_ptr to (2, 0)
        vm.segments = segments![((1, 0), (2, 0))];
        let program_header_ptr = Relocatable::from((2, 0));
        add_segments!(vm, 1);

        let mut exec_scopes = ExecutionScopes::new();
        exec_scopes.insert_value(vars::PROGRAM_DATA_BASE, program_header_ptr.clone());
        exec_scopes.insert_value(vars::TASK, task);

        let ids_data = ids_data!["program_header"];
        let ap_tracking = ApTracking::new();

        load_program_hint(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Note that we do not check the loaded content in memory here, this is tested
        // in `program_loader.rs`

        // The Fibonacci program has no builtins -> the header size is 4
        let header_size = 4;
        let expected_code_address = &program_header_ptr + header_size;

        let program_address: Relocatable = exec_scopes.get(vars::PROGRAM_ADDRESS).unwrap();
        assert_eq!(program_address, expected_code_address);

        // Check that the segment was finalized
        let expected_program_size = header_size + fibonacci.shared_program_data.data.len();
        assert_eq!(
            vm.segments.segment_sizes[&(program_address.segment_index as usize)],
            expected_program_size
        );
    }

    #[rstest]
    fn test_call_task(fibonacci: Program) {
        let mut vm = vm!();

        // Allocate space for pre-execution (8 felts), which mimics the `BuiltinData` struct in the
        // Bootloader's Cairo code. Our code only uses the first felt (`output` field in the struct)
        vm.segments = segments![((1, 0), 0)];
        vm.run_context.fp = 8;
        add_segments!(vm, 1);

        let ids_data = non_continuous_ids_data![(vars::PRE_EXECUTION_BUILTIN_PTRS, -8)];

        let mut exec_scopes = ExecutionScopes::new();

        let mut output_builtin = OutputBuiltinRunner::new(true);
        output_builtin.initialize_segments(&mut vm.segments);
        vm.builtin_runners
            .push(BuiltinRunner::Output(output_builtin));

        let task = Task::Program(fibonacci);
        exec_scopes.insert_box(vars::TASK, Box::new(task));

        assert_matches!(
            run_hint!(
                vm,
                ids_data.clone(),
                hint_code::EXECUTE_TASK_CALL_TASK,
                &mut exec_scopes
            ),
            Ok(())
        );
    }


    #[rstest]
    fn test_call_cairo_pie_task(fibonacci_pie: CairoPie) {
        let mut vm = vm!();

        // Allocate space for pre-execution (8 felts), which mimics the `BuiltinData` struct in the
        // Bootloader's Cairo code. Our code only uses the first felt (`output` field in the struct)
        // We set the program header pointer at (1, 8) and make it point to the start of segment #2.
        vm.segments = segments![((1, 0), 0), ((1, 8), (2, 0))];
        vm.run_context.ap = 9;
        vm.run_context.fp = 9;
        add_segments!(vm, 1);

        let program_header_ptr = Relocatable::from((2, 0));
        let ids_data = non_continuous_ids_data![
            (vars::PRE_EXECUTION_BUILTIN_PTRS, -9),
            ("program_header", -1)
        ];
        let ap_tracking = ApTracking::new();

        let mut exec_scopes = ExecutionScopes::new();

        let mut output_builtin = OutputBuiltinRunner::new(true);
        output_builtin.initialize_segments(&mut vm.segments);
        vm.builtin_runners
            .push(BuiltinRunner::Output(output_builtin));

        let task = Task::Pie(fibonacci_pie);
        exec_scopes.insert_value(vars::TASK, task);
        exec_scopes.insert_value(vars::PROGRAM_DATA_BASE, program_header_ptr.clone());

        // Load the program in memory
        load_program_hint(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Failed to load Cairo PIE task in the VM memory");

        // Execute it
        call_task(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .unwrap_or_else(|e| panic!("Hint failed unexpectedly: {}", e));
    }

    #[rstest]
    fn test_append_fact_topologies(fibonacci: Program) {
        let task = Task::Program(fibonacci.clone());

        let mut vm = vm!();

        // Allocate space for the pre-execution and return builtin structs (2 x 8 felts).
        // The pre-execution struct starts at (1, 0) and the return struct at (1, 8).
        // We only set the output values to 0 and 10, respectively, to get an output size of 10.
        vm.segments = segments![((1, 0), 0), ((1, 8), 10),];
        vm.run_context.fp = 16;
        add_segments!(vm, 1);

        let tree_structure = vec![1, 2, 3, 4];
        let program_output_data = OutputBuiltinAdditionalData {
            base: 0,
            pages: HashMap::from([
                (1, PublicMemoryPage { start: 0, size: 7 }),
                (2, PublicMemoryPage { start: 7, size: 3 }),
            ]),
            attributes: HashMap::from([("gps_fact_topology".to_string(), tree_structure.clone())]),
        };
        let mut output_builtin = OutputBuiltinRunner::new(true);
        output_builtin.set_state(program_output_data.clone());
        output_builtin.initialize_segments(&mut vm.segments);
        vm.builtin_runners
            .push(BuiltinRunner::Output(output_builtin));

        let ids_data = non_continuous_ids_data![
            ("pre_execution_builtin_ptrs", -16),
            ("return_builtin_ptrs", -8),
        ];

        let ap_tracking = ApTracking::new();

        let mut exec_scopes = ExecutionScopes::new();

        let output_runner_data = OutputBuiltinAdditionalData {
            base: 0,
            pages: HashMap::new(),
            attributes: HashMap::new(),
        };
        exec_scopes.insert_value(vars::OUTPUT_RUNNER_DATA, output_runner_data.clone());
        exec_scopes.insert_value(vars::TASK, task);
        exec_scopes.insert_value(vars::FACT_TOPOLOGIES, Vec::<FactTopology>::new());

        append_fact_topologies(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Check that the fact topology matches the data from the output builtin
        let fact_topologies: Vec<FactTopology> = exec_scopes.get(vars::FACT_TOPOLOGIES).unwrap();
        assert_eq!(fact_topologies.len(), 1);

        let fact_topology = &fact_topologies[0];
        assert_eq!(fact_topology.page_sizes, vec![0, 7, 3]);
        assert_eq!(fact_topology.tree_structure, tree_structure);

        // Check that the output builtin was updated
        let output_builtin_additional_data = vm.get_output_builtin().unwrap().get_additional_data();
        assert!(matches!(
            output_builtin_additional_data,
            BuiltinAdditionalData::Output(data) if data == output_runner_data,
        ));
    }

    #[rstest]
    fn test_write_output_builtins(field_arithmetic_program: Program) {
        let task = Task::Program(field_arithmetic_program.clone());

        let mut vm = vm!();
        // Allocate space for all the builtin list structs (3 x 8 felts).
        // The pre-execution struct starts at (1, 0), the used builtins list at (1, 8)
        // and the return struct at (1, 16).
        // Initialize the pre-execution struct to [1, 2, 3, 4, 5, 6, 7, 8].
        // Initialize the used builtins to {range_check: 30, bitwise: 50} as these two
        // are used by the field arithmetic program. Note that the used builtins list
        // does not contain empty elements (i.e. offsets are 8 and 9 instead of 10 and 12).
        vm.segments = segments![
            ((1, 0), 1),
            ((1, 1), 2),
            ((1, 2), 3),
            ((1, 3), 4),
            ((1, 4), 5),
            ((1, 5), 6),
            ((1, 6), 7),
            ((1, 7), 8),
            ((1, 8), 30),
            ((1, 9), 50),
            ((1, 24), (1, 8)),
        ];
        vm.run_context.fp = 25;
        add_segments!(vm, 1);

        // Note that used_builtins_addr is a pointer to the used builtins list at (1, 8)
        let ids_data = non_continuous_ids_data![
            ("pre_execution_builtin_ptrs", -25),
            ("return_builtin_ptrs", -9),
            ("used_builtins_addr", -1),
        ];
        let ap_tracking = ApTracking::new();

        let mut exec_scopes = ExecutionScopes::new();
        let n_builtins = field_arithmetic_program.builtins.len();
        exec_scopes.insert_value(vars::N_BUILTINS, n_builtins);
        exec_scopes.insert_value(vars::TASK, task);

        write_return_builtins_hint(&mut vm, &mut exec_scopes, &ids_data, &ap_tracking)
            .expect("Hint failed unexpectedly");

        // Check that the return builtins were written correctly
        let return_builtins = vm
            .segments
            .memory
            .get_integer_range(Relocatable::from((1, 16)), 8)
            .expect("Return builtin was not properly written to memory.");

        let expected_builtins = vec![1, 2, 30, 4, 50, 6, 7, 8];
        for (expected, actual) in std::iter::zip(expected_builtins, return_builtins) {
            assert_eq!(Felt252::from(expected), actual.into_owned());
        }

        // Check that the exec scope changed
        assert_eq!(
            exec_scopes.data.len(),
            2,
            "A new scope should have been declared"
        );
        assert_eq!(
            exec_scopes.data[1].len(),
            1,
            "The new scope should only contain one variable"
        );
        let n_selected_builtins: usize = exec_scopes
            .get(vars::N_SELECTED_BUILTINS)
            .expect("n_selected_builtins should be set");
        assert_eq!(n_selected_builtins, n_builtins);
    }
}
