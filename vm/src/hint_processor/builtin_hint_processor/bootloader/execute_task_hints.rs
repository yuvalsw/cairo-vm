use crate::hint_processor::builtin_hint_processor::bootloader::program_hash::compute_program_hash_chain;
use crate::hint_processor::builtin_hint_processor::bootloader::types::Task;
use crate::types::relocatable::Relocatable;
use felt::Felt252;
use starknet_crypto::FieldElement;
use std::collections::HashMap;

use crate::hint_processor::builtin_hint_processor::bootloader::vars;
use crate::hint_processor::builtin_hint_processor::hint_utils::{
    get_ptr_from_var_name, insert_value_from_var_name,
};
use crate::hint_processor::hint_processor_definition::HintReference;
use crate::serde::deserialize_program::ApTracking;
use crate::types::exec_scope::ExecutionScopes;
use crate::vm::errors::hint_errors::HintError;
use crate::vm::vm_core::VirtualMachine;
use crate::any_box;
use crate::vm::runners::cairo_pie::CairoPie;

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
    let program = task.get_program();

    let output_ptr = get_ptr_from_var_name("output_ptr", vm, ids_data, ap_tracking)?;
    let program_hash_ptr = (output_ptr + 1)?;

    let program_hash = vm
        .segments
        .memory
        .get_integer(program_hash_ptr)?
        .into_owned();

    // Compute the hash of the program
    let computed_program_hash = compute_program_hash_chain(program, 0)
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
    _ids_data: &HashMap<String, HintReference>,
    _ap_tracking: &ApTracking,
) -> Result<(), HintError> {

    // assert isinstance(task, Task)
    let task: Task = exec_scopes.get(vars::TASK)?;

    // n_builtins = len(task.get_program().builtins)
    let num_builtins = task.get_program().builtins.len();

    let mut new_task_locals = HashMap::new();

    match task {
        // if isinstance(task, RunProgramTask):
        Task::RunProgramTask(program_input) => {

            // new_task_locals['program_input'] = task.program_input
            new_task_locals.insert("program_input".to_string(), any_box![program_input]);
            // new_task_locals['WITH_BOOTLOADER'] = True
            new_task_locals.insert("WITH_BOOTLOADER".to_string(), any_box![true]);

            // vm_load_program(task.program, program_address)
        },
        // elif isinstance(task, CairoPieTask):
        Task::CairoPieTask(task) => {
            let program_address: Relocatable = exec_scopes.get("program_address")?;
            
            // TODO:
            let fixme = Relocatable { segment_index: 0, offset: 0 };

            // ret_pc = ids.ret_pc_label.instruction_offset_ - ids.call_task.instruction_offset_ + pc
            // load_cairo_pie(
            //     task=task.cairo_pie, memory=memory, segments=segments,
            //     program_address=program_address, execution_segment_address= ap - n_builtins,
            //     builtin_runners=builtin_runners, ret_fp=fp, ret_pc=ret_pc)
            load_cairo_pie(
                &task,
                vm,
                program_address,
                vm.get_ap().segment_index as usize - num_builtins,
                fixme,
                fixme,
            )?;

        }
        // else:
        #[allow(unreachable_patterns)] // TODO: we probably don't need this match arm, it makes it look similar to the original hint code though
        _ => {
            // raise NotImplementedError(f'Unexpected task type: {type(task).__name__}.')
            // TODO: proper error
            return Err(HintError::WrongHintData);
        }
    }

    // TODO:
    /*
    output_runner_data = prepare_output_runner(
        task=task,
        output_builtin=output_builtin,
        output_ptr=ids.pre_execution_builtin_ptrs.output)
    */

    exec_scopes.enter_scope(new_task_locals);

    Ok(())
}

mod util {
    use crate::types::relocatable::{MaybeRelocatable, relocate_value};

    // TODO: clean up / organize
    use super::*;

    pub(crate) fn load_cairo_pie(
        task: &CairoPie,
        vm: &mut VirtualMachine,
        // _segments: (),
        program_address: Relocatable,
        execution_segment_address: usize,
        // _builtin_runners: (),
        ret_fp: Relocatable,
        ret_pc: Relocatable,
    ) -> Result<(), HintError> {
        // Load memory entries of the inner program.
        // This replaces executing hints in a non-trusted program.
        // TODO: review: the original type was `WriteOnceDict`, which works quite differently than a Vec.
        //       we use a fixed size here to prevent unbounded vec size.
        const RELOCATABLE_TABLE_SIZE: usize = 256;
        let mut segment_offsets = vec![0usize; RELOCATABLE_TABLE_SIZE];
        segment_offsets[task.metadata.program_segment.index as usize] = program_address.segment_index as usize;
        segment_offsets[task.metadata.execution_segment.index as usize] =  execution_segment_address;
        segment_offsets[task.metadata.ret_fp_segment.index as usize] = ret_fp.segment_index as usize;
        segment_offsets[task.metadata.ret_pc_segment.index as usize] = ret_pc.segment_index as usize;

        // Returns the segment index for the given value.
        // Verifies that value is a RelocatableValue with offset 0.
        let extract_segment = |value, _value_name| -> Result<isize, HintError> {
            return match value {
                MaybeRelocatable::RelocatableValue(r) if r.offset != 0 => Err(HintError::WrongHintData), // TODO: error
                MaybeRelocatable::RelocatableValue(r) if r.offset == 0 => Ok(r.segment_index),
                _ => Err(HintError::WrongHintData) // TODO: error
            }
        };

        let origin_execution_segment = Relocatable { segment_index: task.metadata.execution_segment.index, offset: 0 };

        // Set initial stack relocations.
        let mut idx = 0;
        for builtin in task.metadata.program.builtins.iter() {
            // task.memory is a CairoPieMemory, aka Vec<((usize, usize), MaybeRelocatable)>
            // Assumptions:
            //     * the (usize, usize) is a (segment_index, offset) pair
            //     * the Vec's order and packing is arbitrary, so we scan for matches
            let key: Relocatable = (origin_execution_segment + idx)?;
            // TODO: review clone() here (into_iter() takes ownership)
            let pie_mem_element = task.memory.clone().into_iter().find_map(|entry| {
                return if entry.0 == (key.segment_index as usize, key.offset) {
                    Some(entry.1)
                } else {
                    None
                }
            }).ok_or(HintError::EmptyKeys)?; // TODO: proper error

            let index = extract_segment(pie_mem_element, builtin)? as usize;
            assert!(index < RELOCATABLE_TABLE_SIZE);

            let mem_at = Relocatable {
                segment_index: (execution_segment_address + idx) as isize,
                offset: 0
            };
            segment_offsets.insert(index, vm.get_relocatable(mem_at)?.segment_index as usize); // TODO: should be Relocatable, also TODO: type conversion
            idx += 1;
        }

        for segment_info in &task.metadata.extra_segments {
            let index = segment_info.index as usize;
            assert!(index < RELOCATABLE_TABLE_SIZE);
            // TODO: previous passed 'size' to add()
            segment_offsets[index] = vm.add_memory_segment().segment_index as usize;
        }

        let _local_relocate_value = |value| {
            return relocate_value(value, &segment_offsets);
        };

        // TODO: process ecdsa builtin

        for _item in &task.memory {
            // TODO: relocate memory, perhaps using Memory's relocation table (add_relocation_rule() calls) 
            //       and then call relocate_memory()?
        }


        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;
    use assert_matches::assert_matches;

    use crate::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::BuiltinHintProcessor;
    use crate::hint_processor::builtin_hint_processor::builtin_hint_processor_definition::HintProcessorData;
    use crate::hint_processor::builtin_hint_processor::hint_code;
    use crate::hint_processor::builtin_hint_processor::hint_utils::get_ptr_from_var_name;
    use crate::hint_processor::hint_processor_definition::HintProcessorLogic;
    use crate::types::relocatable::Relocatable;
    use crate::utils::test_utils::*;
    use crate::any_box;

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

    #[test]
    fn test_call_task() {
        let mut vm = vm!();
        let ids_data = HashMap::<String, HintReference>::new();
        let mut exec_scopes = ExecutionScopes::new();

        let task = Task::RunProgramTask("fixme".to_string());
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
}
