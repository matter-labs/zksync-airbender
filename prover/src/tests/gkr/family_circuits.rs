use super::*;
use crate::definitions::produce_initial_permutation_product_contribution;
use ::field::baby_bear::base::BabyBearField;
use ::field::baby_bear::ext4::BabyBearExt4;
use common_constants::INITIAL_PC;
use cs::definitions::INITIAL_TIMESTAMP;
use cs::definitions::*;
use cs::gkr_circuits::opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization;
use cs::gkr_circuits::process_binary_into_separate_tables_ext;
use cs::tables::TableDriver;
use field::Field;
use riscv_transpiler::ir::*;
use riscv_transpiler::vm::Counters;
use std::alloc::Global;
use std::collections::BTreeSet;
use worker::Worker;
const NUM_INIT_AND_TEARDOWN_SETS: usize = 16;
const WORD_BITS: u32 = core::mem::size_of::<u32>().trailing_zeros();

// NOTE: these constants must match with ones used in CS crate to produce
// layout and SSA forms, otherwise derived witness-gen functions may write into
// invalid locations
const TRACE_LEN_LOG2: usize = 24;
const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
const BLAKE_NUM_DELEGATION_CYCLES: usize = 1 << 20;
const BIGINT_NUM_DELEGATION_CYCLES: usize = 1 << 22;
const KECCAK_NUM_DELEGATION_CYCLES: usize = 1 << 22;
const BLAKE_G_FUNCTION_NUM_DELEGATION_CYCLES: usize = 1 << 22;
const RAM_BOUND_BYTES: usize = 1 << 30;
const RAM_BOUND_WORDS: usize = RAM_BOUND_BYTES / core::mem::size_of::<u32>();

const CHECK_MEMORY_PERMUTATION_ONLY: bool = false;
const PROVE_EMPTY: bool = true;

pub use crate::definitions::SecurityLevel;

#[test]
fn gkr_run_basic_unrolled_test_sec_80() {
    gkr_run_basic_unrolled_test_impl(SecurityLevel::Sec80, None, None);
}

#[test]
fn gkr_run_basic_unrolled_test_sec_100() {
    gkr_run_basic_unrolled_test_impl(SecurityLevel::Sec100, None, None);
}

pub fn gkr_run_basic_unrolled_test_impl(
    level: SecurityLevel,
    maybe_gpu_unrolled_comparison_hook: Option<Box<dyn Fn()>>,
    maybe_gpu_delegation_comparison_hook: Option<Box<dyn Fn()>>,
) {
    let proof_suffix = level.dir_suffix();
    type CountersT = riscv_transpiler::vm::DelegationsAndFamiliesCounters;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let worker = Worker::new_with_num_threads(8);

    let circuits_filter = super::orchestration::common::parse_circuits_filter();

    let program = std::env::var("GKR_PROGRAM").ok();
    let config = match program.as_deref() {
        Some("hashed_fibonacci_g_function") => {
            super::orchestration::common::ProgramConfig::hashed_fibonacci_blake_g_function()
        }
        Some("hashed_fibonacci_compression") => {
            super::orchestration::common::ProgramConfig::hashed_fibonacci_blake_compression()
        }
        _ => super::orchestration::common::ProgramConfig::keccak_f1600(),
    };

    let vm = super::orchestration::common::run_vm_and_capture::<
        CountersT,
        FullUnsignedMachineDecoderConfig,
    >(&config, &worker);

    assert_eq!(
        (NUM_INIT_AND_TEARDOWN_SETS << TRACE_LEN_LOG2) << WORD_BITS,
        RAM_BOUND_BYTES
    );
    let mut inits_and_teardowns = Vec::with_capacity(NUM_INIT_AND_TEARDOWN_SETS);
    for _ in 0..NUM_INIT_AND_TEARDOWN_SETS {
        let a = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let b = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let c = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        let d = Vec::with_capacity(1 << TRACE_LEN_LOG2);
        inits_and_teardowns.push(([a, b], [c, d]));
    }
    vm.ram
        .collect_inits_and_teardowns_into_columns::<BabyBearField, _>(
            &worker,
            TRACE_LEN_LOG2,
            0,
            &mut inits_and_teardowns,
        );

    println!("Finished at PC = 0x{:08x}", vm.final_pc());
    for (reg_idx, reg) in vm.register_final_state().iter().enumerate() {
        println!("x{} = {}", reg_idx, reg.current_value);
    }

    // Derived accessors first (they borrow all of `vm`), then move the owned fields out.
    let expected_final_state = vm.expected_final_state();
    let final_pc = vm.final_pc();
    let final_timestamp = vm.final_timestamp();
    let register_final_state = vm.register_final_state();
    let counters = vm.counters;
    let total_unique_teardowns = vm.total_unique_teardowns;
    let cycles_bound = vm.cycles_bound;
    let snapshotter = vm.snapshotter;
    let tape = vm.tape;
    let text_section = vm.text_section;
    let binary = vm.binary;

    let flattened_inits_and_teardowns: Vec<_> = vm
        .shuffle_ram_touched_addresses
        .iter()
        .flatten()
        .cloned()
        .collect();

    let external_challenges = super::orchestration::common::hardcoded_external_challenges();

    // evaluate memory witness

    let preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(
        &text_section,
        &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
        ],
    );

    let register_final_state_raw = register_final_state
        .map(|el| (el.current_value, split_timestamp(el.last_access_timestamp)));

    let mut permutation_argument_accumulator =
        produce_initial_permutation_product_contribution::<BabyBearField, BabyBearExt4>(
            &register_final_state_raw,
            INITIAL_PC,
            split_timestamp(INITIAL_TIMESTAMP),
            final_pc,
            split_timestamp(final_timestamp),
            &external_challenges,
        );

    let mut write_set = BTreeSet::<(u32, TimestampScalar)>::new();
    let mut read_set = BTreeSet::<(u32, TimestampScalar)>::new();

    write_set.insert((INITIAL_PC, INITIAL_TIMESTAMP));
    read_set.insert((final_pc, final_timestamp));

    let mut memory_read_set = BTreeSet::new();
    let mut memory_write_set = BTreeSet::new();

    let mut delegation_read_set = BTreeSet::new();
    let mut delegation_write_set = BTreeSet::new();

    for i in 0..32 {
        memory_write_set.insert((true, i as u32, 0, 0));
        memory_read_set.insert((
            true,
            i as u32,
            register_final_state[i].last_access_timestamp,
            register_final_state[i].current_value,
        ));
    }

    assert!(
        counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<SHIFT_BINARY_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<MUL_DIV_CIRCUIT_FAMILY_IDX>() < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );
    assert!(
        counters.get_calls_to_circuit_family::<LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX>()
            < NUM_CYCLES_PER_CHUNK
    );

    {
        const CIRCUIT_TYPE: u8 = ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;
        let out = super::orchestration::per_family::prove_non_mem_family::<CIRCUIT_TYPE, CountersT>(
            &snapshotter,
            &tape,
            &expected_final_state,
            cycles_bound,
            counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>(),
            &preprocessing_data[&CIRCUIT_TYPE],
            cs::gkr_circuits::add_sub_family::add_sub_lui_auipc_mop_table_driver_fn::<BabyBearField>,
            trace_len,
            NUM_CYCLES_PER_CHUNK,
            &external_challenges,
            level,
            PROVE_EMPTY,
            CHECK_MEMORY_PERMUTATION_ONLY,
            &circuits_filter,
            "add_sub_lui_auipc_mop",
            &proof_suffix,
            &worker,
            add_sub_lui_auipc_mop::witness_eval_fn,
        );
        parse_state_permutation_elements_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut write_set,
            &mut read_set,
        );
        parse_shuffle_ram_accesses_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut memory_write_set,
            &mut memory_read_set,
            &mut delegation_write_set,
        );
        if let Some(proof) = &out.proof {
            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);
        }
    }

    {
        const CIRCUIT_TYPE: u8 = JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX;
        let out = super::orchestration::per_family::prove_non_mem_family::<CIRCUIT_TYPE, CountersT>(
            &snapshotter,
            &tape,
            &expected_final_state,
            cycles_bound,
            counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>(),
            &preprocessing_data[&CIRCUIT_TYPE],
            cs::gkr_circuits::jump_branch_slt_family::jump_branch_slt_table_driver_fn::<
                BabyBearField,
            >,
            trace_len,
            NUM_CYCLES_PER_CHUNK,
            &external_challenges,
            level,
            PROVE_EMPTY,
            CHECK_MEMORY_PERMUTATION_ONLY,
            &circuits_filter,
            "jump_branch_slt",
            &proof_suffix,
            &worker,
            jump_branch_slt::witness_eval_fn,
        );
        parse_state_permutation_elements_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut write_set,
            &mut read_set,
        );
        parse_shuffle_ram_accesses_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut memory_write_set,
            &mut memory_read_set,
            &mut delegation_write_set,
        );
        if let Some(proof) = &out.proof {
            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);
        }
    }

    {
        const CIRCUIT_TYPE: u8 = SHIFT_BINARY_CIRCUIT_FAMILY_IDX;
        let out = super::orchestration::per_family::prove_non_mem_family::<CIRCUIT_TYPE, CountersT>(
            &snapshotter,
            &tape,
            &expected_final_state,
            cycles_bound,
            counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>(),
            &preprocessing_data[&CIRCUIT_TYPE],
            cs::gkr_circuits::binary_shifts_family::shift_binop_table_driver_fn::<BabyBearField>,
            trace_len,
            NUM_CYCLES_PER_CHUNK,
            &external_challenges,
            level,
            PROVE_EMPTY,
            CHECK_MEMORY_PERMUTATION_ONLY,
            &circuits_filter,
            "shift_binop",
            &proof_suffix,
            &worker,
            shift_binary_ops::witness_eval_fn,
        );
        parse_state_permutation_elements_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut write_set,
            &mut read_set,
        );
        parse_shuffle_ram_accesses_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut memory_write_set,
            &mut memory_read_set,
            &mut delegation_write_set,
        );
        if let Some(proof) = &out.proof {
            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);
        }
    }

    {
        const CIRCUIT_TYPE: u8 = MUL_DIV_CIRCUIT_FAMILY_IDX;
        let out = super::orchestration::per_family::prove_non_mem_family::<CIRCUIT_TYPE, CountersT>(
            &snapshotter,
            &tape,
            &expected_final_state,
            cycles_bound,
            counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>(),
            &preprocessing_data[&CIRCUIT_TYPE],
            cs::gkr_circuits::mul_div::mul_div_table_driver_fn::<BabyBearField, false>,
            trace_len,
            NUM_CYCLES_PER_CHUNK,
            &external_challenges,
            level,
            PROVE_EMPTY,
            CHECK_MEMORY_PERMUTATION_ONLY,
            &circuits_filter,
            "unsigned_mul_div",
            &proof_suffix,
            &worker,
            unsigned_mul_div::witness_eval_fn,
        );
        parse_state_permutation_elements_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut write_set,
            &mut read_set,
        );
        parse_shuffle_ram_accesses_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut memory_write_set,
            &mut memory_read_set,
            &mut delegation_write_set,
        );
        if let Some(proof) = &out.proof {
            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);
        }
    }

    {
        const CIRCUIT_TYPE: u8 = LOAD_STORE_WORD_ONLY_CIRCUIT_FAMILY_IDX;
        let out = super::orchestration::per_family::prove_mem_family::<CIRCUIT_TYPE, CountersT>(
            &snapshotter,
            &tape,
            &expected_final_state,
            cycles_bound,
            counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>(),
            &preprocessing_data[&CIRCUIT_TYPE],
            |td| {
                cs::gkr_circuits::mem_word_only::mem_word_only_table_driver_fn(td);
                let extra_tables =
                    cs::gkr_circuits::mem_word_only::create_mem_word_only_special_tables::<
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(&binary);
                for (table_type, table) in extra_tables {
                    td.add_table_with_content(table_type, table);
                }
            },
            trace_len,
            NUM_CYCLES_PER_CHUNK,
            &external_challenges,
            level,
            PROVE_EMPTY,
            CHECK_MEMORY_PERMUTATION_ONLY,
            &circuits_filter,
            "mem_word_only",
            &proof_suffix,
            &worker,
            mem_word_only::witness_eval_fn,
        );
        parse_state_permutation_elements_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut write_set,
            &mut read_set,
        );
        parse_shuffle_ram_accesses_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut memory_write_set,
            &mut memory_read_set,
            &mut delegation_write_set,
        );
        if let Some(proof) = &out.proof {
            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);
        }
    }

    {
        const CIRCUIT_TYPE: u8 = LOAD_STORE_SUBWORD_ONLY_CIRCUIT_FAMILY_IDX;
        let out = super::orchestration::per_family::prove_mem_family::<CIRCUIT_TYPE, CountersT>(
            &snapshotter,
            &tape,
            &expected_final_state,
            cycles_bound,
            counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>(),
            &preprocessing_data[&CIRCUIT_TYPE],
            |td| {
                cs::gkr_circuits::mem_subword_only::mem_subword_only_table_driver_fn(td);
                let extra_tables =
                    cs::gkr_circuits::mem_subword_only::create_mem_subword_only_special_tables::<
                        _,
                        { common_constants::ROM_SECOND_WORD_BITS },
                    >(&binary);
                for (table_type, table) in extra_tables {
                    td.add_table_with_content(table_type, table);
                }
            },
            trace_len,
            NUM_CYCLES_PER_CHUNK,
            &external_challenges,
            level,
            PROVE_EMPTY,
            CHECK_MEMORY_PERMUTATION_ONLY,
            &circuits_filter,
            "mem_subword_only",
            &proof_suffix,
            &worker,
            mem_subword_only::witness_eval_fn,
        );
        parse_state_permutation_elements_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut write_set,
            &mut read_set,
        );
        parse_shuffle_ram_accesses_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut memory_write_set,
            &mut memory_read_set,
            &mut delegation_write_set,
        );
        if let Some(proof) = &out.proof {
            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);
        }
    }

    // Machine state permutation ended
    {
        for (pc, ts) in write_set.iter().copied() {
            if read_set.contains(&(pc, ts)) == false {
                panic!("read set doesn't contain a pair {:?}", (pc, ts));
            }
        }

        for (pc, ts) in read_set.iter().copied() {
            if write_set.contains(&(pc, ts)) == false {
                panic!("write set doesn't contain a pair {:?}", (pc, ts));
            }
        }
    }

    {
        let out = super::orchestration::per_family::prove_inits_and_teardowns(
            inits_and_teardowns,
            total_unique_teardowns,
            trace_len,
            &external_challenges,
            level,
            CHECK_MEMORY_PERMUTATION_ONLY,
            &circuits_filter,
            &proof_suffix,
            &worker,
        );
        if let Some(proof) = &out.proof {
            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);
        }
    }

    // now prove delegation circuits
    {
        let out = super::orchestration::delegations::prove_delegation_blake::<CountersT>(
            &snapshotter,
            &tape,
            &expected_final_state,
            cycles_bound,
            counters.blake_calls,
            &external_challenges,
            level,
            PROVE_EMPTY,
            CHECK_MEMORY_PERMUTATION_ONLY,
            &circuits_filter,
            &proof_suffix,
            &worker,
            super::blake2_with_extended_control::witness_eval_fn,
        );
        parse_delegation_ram_accesses_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut memory_write_set,
            &mut memory_read_set,
            &mut delegation_read_set,
            out.delegation_type,
        );
        if let Some(proof) = &out.proof {
            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);
        }
    }

    {
        let out = super::orchestration::delegations::prove_delegation_bigint::<CountersT>(
            &snapshotter,
            &tape,
            &expected_final_state,
            cycles_bound,
            counters.bigint_calls,
            &external_challenges,
            level,
            PROVE_EMPTY,
            CHECK_MEMORY_PERMUTATION_ONLY,
            &circuits_filter,
            &proof_suffix,
            &worker,
            super::bigint_with_extended_control::witness_eval_fn,
        );
        parse_delegation_ram_accesses_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut memory_write_set,
            &mut memory_read_set,
            &mut delegation_read_set,
            out.delegation_type,
        );
        if let Some(proof) = &out.proof {
            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);
        }
    }

    {
        let out = super::orchestration::delegations::prove_delegation_keccak::<CountersT>(
            &snapshotter,
            &tape,
            &expected_final_state,
            cycles_bound,
            counters.keccak_calls,
            &external_challenges,
            level,
            PROVE_EMPTY,
            CHECK_MEMORY_PERMUTATION_ONLY,
            &circuits_filter,
            &proof_suffix,
            &worker,
            super::keccak_special5::witness_eval_fn,
        );
        parse_delegation_ram_accesses_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut memory_write_set,
            &mut memory_read_set,
            &mut delegation_read_set,
            out.delegation_type,
        );
        if let Some(proof) = &out.proof {
            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);
        }
    }

    {
        let out = super::orchestration::delegations::prove_delegation_blake_g_function::<CountersT>(
            &snapshotter,
            &tape,
            &expected_final_state,
            cycles_bound,
            counters.blake_g_function_calls,
            &external_challenges,
            level,
            PROVE_EMPTY,
            CHECK_MEMORY_PERMUTATION_ONLY,
            &circuits_filter,
            &proof_suffix,
            &worker,
            super::blake2_g_function::witness_eval_fn,
        );
        parse_delegation_ram_accesses_from_full_trace(
            &out.compiled_circuit,
            &out.memory_trace,
            &mut memory_write_set,
            &mut memory_read_set,
            &mut delegation_read_set,
            out.delegation_type,
        );
        if let Some(proof) = &out.proof {
            permutation_argument_accumulator.mul_assign(&proof.grand_product_accumulator_computed);
        }
    }

    // delegation registers invocations
    {
        if delegation_read_set != delegation_write_set {
            let delegations_without_invocations: Vec<_> = delegation_read_set
                .difference(&delegation_write_set)
                .collect();
            let delegations_without_processing: Vec<_> = delegation_write_set
                .difference(&delegation_read_set)
                .collect();
            dbg!(delegation_read_set.len());
            dbg!(&delegation_read_set);
            dbg!(delegation_write_set.len());
            dbg!(&delegation_write_set);
            dbg!(&delegations_without_invocations);
            dbg!(&delegations_without_processing);
            panic!("Unprocessed delegations");
        }
    }

    // inits and teardowns
    {
        let expected_init_set: Vec<_> = memory_read_set.difference(&memory_write_set).collect();
        let expected_teardown_set: Vec<_> = memory_write_set.difference(&memory_read_set).collect();
        assert_eq!(expected_init_set.len(), expected_teardown_set.len());
        // assert_eq!(expected_init_set.len(), flattened_inits_and_teardowns.len());

        if flattened_inits_and_teardowns.len() != expected_init_set.len() {
            for (idx, (address, (teardown_ts, teardown_value))) in
                flattened_inits_and_teardowns.iter().enumerate()
            {
                let mut init_set_el = None;
                for (i, (is_reg, addr, ts, init_value)) in expected_init_set.iter().enumerate() {
                    if *addr == *address {
                        init_set_el = Some((*is_reg, *addr, *ts, *init_value));
                    }
                }
                let Some(init_set_el) = init_set_el else {
                    panic!("No expected init set element for address {} of flattened inits or teardowns", *address);
                };

                let mut teardown_set_el = None;
                for (i, (is_reg, addr, ts, teardown_value)) in
                    expected_teardown_set.iter().enumerate()
                {
                    if *addr == *address {
                        teardown_set_el = Some((*is_reg, *addr, *ts, *teardown_value));
                    }
                }
                let Some(teardown_set_el) = teardown_set_el else {
                    panic!("No expected teardown set element for address {} of flattened inits or teardowns", *address);
                };
                let (_, _, expected_teardown_ts, expected_teardown_value) = teardown_set_el;
                assert_eq!(
                    *teardown_ts, expected_teardown_ts,
                    "failed for address {}",
                    address
                );
                assert_eq!(
                    *teardown_value, expected_teardown_value,
                    "failed for address {}",
                    address
                );
            }
        }

        for (idx, (is_register, addr, ts, init_value)) in expected_init_set.iter().enumerate() {
            assert!(
                *is_register == false,
                "found an unexpected init for register {} with value {} at timestamp {}",
                *addr,
                *init_value,
                *ts
            );
            assert_eq!(
                *ts, 0,
                "init timestamp is invalid for memory address {}",
                addr
            );
            assert_eq!(
                *init_value, 0,
                "init value is invalid for memory address {}",
                addr
            );
            assert_eq!(
                flattened_inits_and_teardowns[idx].0, *addr,
                "diverged at expected lazy init {}",
                idx
            );
        }
        for (idx, (is_register, addr, ts, value)) in expected_teardown_set.iter().enumerate() {
            assert!(
                *is_register == false,
                "found an unexpected teardown for register {} with value {} at timestamp {}",
                *addr,
                *value,
                *ts
            );
            assert!(
                *ts > INITIAL_TIMESTAMP,
                "teardown timestamp is invalid for memory address {}",
                addr
            );
            assert_eq!(
                flattened_inits_and_teardowns[idx].1 .0, *ts,
                "diverged at expected lazy init {}",
                idx
            );
            assert_eq!(
                flattened_inits_and_teardowns[idx].1 .1, *value,
                "diverged at expected lazy init {}",
                idx
            );
        }

        for ((_, addr0, _, _), (_, addr1, _, _)) in
            expected_init_set.iter().zip(expected_teardown_set.iter())
        {
            assert_eq!(*addr0, *addr1);
        }

        assert_eq!(total_unique_teardowns, expected_teardown_set.len());
    }

    if CHECK_MEMORY_PERMUTATION_ONLY == false && circuits_filter.is_none() {
        dbg!(permutation_argument_accumulator);
        assert_eq!(permutation_argument_accumulator, BabyBearExt4::ONE);
    }
}

#[test]
fn add_sub_mop_real_program_check_satisfied() {
    use riscv_transpiler::vm::DelegationsAndFamiliesCounters;

    type CountersT = DelegationsAndFamiliesCounters;
    const CIRCUIT_TYPE: u8 = ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;

    let worker = Worker::new_with_num_threads(8);

    let config = super::orchestration::common::ProgramConfig::mop_smoke();
    let vm = super::orchestration::common::run_vm_and_capture::<
        CountersT,
        FullUnsignedMachineDecoderConfig,
    >(&config, &worker);

    let num_calls = vm.counters.get_calls_to_circuit_family::<CIRCUIT_TYPE>();
    assert!(num_calls > 0);

    let preprocessing_data = process_binary_into_separate_tables_ext::<
        BabyBearField,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(
        &vm.text_section,
        &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
            BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16,
        ],
    );
    let decoder_table_data = &preprocessing_data[&CIRCUIT_TYPE];

    let circuit: GKRCircuitArtifact<BabyBearField> = deserialize_from_file(
        &super::orchestration::per_family::circuit_path("add_sub_lui_auipc_mop"),
    );
    let mut table_driver = TableDriver::<BabyBearField>::new();
    cs::gkr_circuits::add_sub_family::add_sub_lui_auipc_mop_table_driver_fn(&mut table_driver);

    // Replay + oracle + witness-gen go through the shared per-family orchestration
    // builder (no memory-consistency check: this test only needs the full trace
    // for `check_satisfied` and the prove below).
    let full_trace =
        super::orchestration::per_family::build_nonmem_family_full_trace::<CIRCUIT_TYPE, _>(
            &vm.snapshotter,
            &vm.tape,
            &vm.expected_final_state(),
            vm.cycles_bound,
            num_calls,
            &circuit,
            &table_driver,
            decoder_table_data,
            add_sub_lui_auipc_mop::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            false,
            &worker,
        );

    assert!(check_satisfied(&circuit, &full_trace));

    let trace_len = 1usize << TRACE_LEN_LOG2;
    let proof = super::orchestration::per_family::prove_built_family_trace(
        &circuit,
        &table_driver,
        decoder_table_data,
        full_trace,
        trace_len,
        &super::orchestration::common::hardcoded_external_challenges(),
        SecurityLevel::Sec80,
        &worker,
    );

    serialize_to_file(&proof, "test_proofs/mop_add_sub_gkr_proof.json");
}
