use super::*;

use crate::tracers::unrolled::tracer::*;
use crate::unrolled::evaluate_witness_for_executor_family;
use crate::unrolled::run_unrolled_machine_for_num_cycles;
use crate::unrolled::MemoryCircuitOracle;
use crate::unrolled::NonMemoryCircuitOracle;
use common_constants::circuit_families::*;
use common_constants::delegation_types::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER;
use common_constants::delegation_types::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER;
use common_constants::delegation_types::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER;
use cs::cs::circuit::Circuit;
use cs::machine::ops::unrolled::*;
use cs::machine::NON_DETERMINISM_CSR;
use risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
use risc_v_simulator::{cycle::*, delegations::DelegationsCSRProcessor};
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use std::alloc::Allocator;
use std::collections::BTreeSet;

use crate::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits;
use crate::witness_evaluator::unrolled::evaluate_memory_witness_for_executor_family;

mod reduced_machine;
pub mod with_transpiler;

pub mod add_sub_lui_auipc_mod {
    use crate::unrolled::NonMemoryCircuitOracle;
    use crate::witness_evaluator::SimpleWitnessProxy;
    use crate::witness_proxy::WitnessProxy;
    use ::cs::cs::placeholder::Placeholder;
    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::Mersenne31Field;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../add_sub_lui_auipc_mop_preprocessed_generated.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, NonMemoryCircuitOracle<'b>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, NonMemoryCircuitOracle<'b>>,
        >;
        (fn_ptr)(proxy);
    }
}

pub mod jump_branch_slt {
    use crate::unrolled::NonMemoryCircuitOracle;
    use crate::witness_evaluator::SimpleWitnessProxy;
    use crate::witness_proxy::WitnessProxy;
    use ::cs::cs::placeholder::Placeholder;
    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::Mersenne31Field;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../jump_branch_slt_preprocessed_generated.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, NonMemoryCircuitOracle<'b>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, NonMemoryCircuitOracle<'b>>,
        >;
        (fn_ptr)(proxy);
    }
}

pub mod shift_binop_csrrw {
    use crate::unrolled::NonMemoryCircuitOracle;
    use crate::witness_evaluator::SimpleWitnessProxy;
    use crate::witness_proxy::WitnessProxy;
    use ::cs::cs::placeholder::Placeholder;
    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::Mersenne31Field;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../shift_binop_csrrw_preprocessed_generated.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, NonMemoryCircuitOracle<'b>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, NonMemoryCircuitOracle<'b>>,
        >;
        (fn_ptr)(proxy);
    }
}

pub mod mul_div {
    use crate::unrolled::NonMemoryCircuitOracle;
    use crate::witness_evaluator::SimpleWitnessProxy;
    use crate::witness_proxy::WitnessProxy;
    use ::cs::cs::placeholder::Placeholder;
    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::Mersenne31Field;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../mul_div_preprocessed_generated.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, NonMemoryCircuitOracle<'b>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, NonMemoryCircuitOracle<'b>>,
        >;
        (fn_ptr)(proxy);
    }
}

pub mod mul_div_unsigned_only {
    use crate::unrolled::NonMemoryCircuitOracle;
    use crate::witness_evaluator::SimpleWitnessProxy;
    use crate::witness_proxy::WitnessProxy;
    use ::cs::cs::placeholder::Placeholder;
    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::Mersenne31Field;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../mul_div_unsigned_preprocessed_generated.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut SimpleWitnessProxy<'a, NonMemoryCircuitOracle<'b>>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, NonMemoryCircuitOracle<'b>>,
        >;
        (fn_ptr)(proxy);
    }
}

pub mod load_store {
    use crate::unrolled::MemoryCircuitOracle;
    use crate::witness_evaluator::SimpleWitnessProxy;
    use crate::witness_proxy::WitnessProxy;
    use ::cs::cs::placeholder::Placeholder;
    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::Mersenne31Field;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../load_store_preprocessed_generated.rs");

    pub fn witness_eval_fn<'a, 'b>(proxy: &'_ mut SimpleWitnessProxy<'a, MemoryCircuitOracle<'b>>) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, MemoryCircuitOracle<'b>>,
        >;
        (fn_ptr)(proxy);
    }
}

pub mod word_load_store {
    use crate::unrolled::MemoryCircuitOracle;
    use crate::witness_evaluator::SimpleWitnessProxy;
    use crate::witness_proxy::WitnessProxy;
    use ::cs::cs::placeholder::Placeholder;
    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::Mersenne31Field;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../word_only_load_store_preprocessed_generated.rs");

    pub fn witness_eval_fn<'a, 'b>(proxy: &'_ mut SimpleWitnessProxy<'a, MemoryCircuitOracle<'b>>) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, MemoryCircuitOracle<'b>>,
        >;
        (fn_ptr)(proxy);
    }
}

pub mod subword_load_store {
    use crate::unrolled::MemoryCircuitOracle;
    use crate::witness_evaluator::SimpleWitnessProxy;
    use crate::witness_proxy::WitnessProxy;
    use ::cs::cs::placeholder::Placeholder;
    use ::cs::cs::witness_placer::WitnessTypeSet;
    use ::cs::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::Mersenne31Field;
    use cs::cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../subword_only_load_store_preprocessed_generated.rs");

    pub fn witness_eval_fn<'a, 'b>(proxy: &'_ mut SimpleWitnessProxy<'a, MemoryCircuitOracle<'b>>) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<Mersenne31Field, true>,
            SimpleWitnessProxy<'a, MemoryCircuitOracle<'b>>,
        >;
        (fn_ptr)(proxy);
    }
}

pub(crate) unsafe fn read_u32(trace_row: &[Mersenne31Field], columns: ColumnSet<2>) -> u32 {
    let low = trace_row[columns.start()].to_reduced_u32();
    let high = trace_row[columns.start() + 1].to_reduced_u32();

    (high << 16) | low
}

pub(crate) unsafe fn read_u16(trace_row: &[Mersenne31Field], columns: ColumnSet<1>) -> u16 {
    let low = trace_row[columns.start()].to_reduced_u32();

    low as u16
}

pub(crate) unsafe fn read_timestamp(
    trace_row: &[Mersenne31Field],
    columns: ColumnSet<2>,
) -> TimestampScalar {
    let low = trace_row[columns.start()].to_reduced_u32();
    let high = trace_row[columns.start() + 1].to_reduced_u32();

    ((high as TimestampScalar) << TIMESTAMP_COLUMNS_NUM_BITS) | (low as TimestampScalar)
}

pub(crate) unsafe fn parse_state_permutation_elements(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    trace_row: &[Mersenne31Field],
    write_set: &mut BTreeSet<(u32, TimestampScalar)>,
    read_set: &mut BTreeSet<(u32, TimestampScalar)>,
) {
    let intermediate_state_layout = compiled_circuit
        .memory_layout
        .intermediate_state_layout
        .unwrap();
    let machine_state_layout = compiled_circuit.memory_layout.machine_state_layout.unwrap();
    // intermediate_state_layout -> machine_state_layout
    let execute = intermediate_state_layout.execute;
    let is_active = trace_row[execute.start()].as_boolean();
    let initial_ts = read_timestamp(trace_row, intermediate_state_layout.timestamp);
    let final_ts = read_timestamp(trace_row, machine_state_layout.timestamp);

    let initial_pc = read_u32(trace_row, intermediate_state_layout.pc);
    let final_pc = read_u32(trace_row, machine_state_layout.pc);

    if is_active {
        let is_unique = write_set.insert((final_pc, final_ts));
        if is_unique == false {
            panic!("Duplicate entry {:?} in write set", (final_pc, final_ts));
        }

        let is_unique = read_set.insert((initial_pc, initial_ts));
        if is_unique == false {
            panic!("Duplicate entry {:?} in read set", (initial_pc, initial_ts));
        }
    }
}

#[track_caller]
pub(crate) unsafe fn parse_shuffle_ram_accesses(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    trace_row: &[Mersenne31Field],
    write_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    read_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    _row: usize,
) {
    let intermediate_state_layout = compiled_circuit
        .memory_layout
        .intermediate_state_layout
        .unwrap();
    let execute = intermediate_state_layout.execute;
    let is_active = trace_row[execute.start()].as_boolean();
    if is_active {
        let base_ts = read_timestamp(trace_row, intermediate_state_layout.timestamp);
        assert!(base_ts >= INITIAL_TIMESTAMP);
        for (access_idx, access) in compiled_circuit
            .memory_layout
            .shuffle_ram_access_sets
            .iter()
            .enumerate()
        {
            let read_ts = read_timestamp(trace_row, access.get_read_timestamp_columns());
            let read_value = read_u32(trace_row, access.get_read_value_columns());
            let mut write_value = read_value;
            if let ShuffleRamQueryColumns::Write(write) = access {
                write_value = read_u32(trace_row, write.write_value);
            }
            let write_ts = base_ts + (access_idx as TimestampScalar);
            let mut is_register = true;
            let address;
            match access.get_address() {
                ShuffleRamAddress::RegisterOnly(reg_idx) => {
                    let reg_idx = read_u16(trace_row, reg_idx.register_index);
                    address = reg_idx as u32;
                }
                ShuffleRamAddress::RegisterOrRam(reg_or_ram) => {
                    is_register = read_u16(trace_row, reg_or_ram.is_register) != 0;
                    address = read_u32(trace_row, reg_or_ram.address);
                }
            }

            if is_register == false && address < common_constants::rom::ROM_BYTE_SIZE as u32 {
                assert_eq!(read_value, 0);
                let ShuffleRamQueryColumns::Readonly(..) = access else {
                    panic!("write access into ROM");
                };
            }

            // if _row < 100 {
            //     println!("Row {}, index {}: read reg = {}, address = {} at ts = {} into value {}", _row, access_idx, is_register, address, read_ts, read_value);
            // }

            // if _row < 100 {
            //     println!("Row {}, index {}: write reg = {}, address = {} at ts = {} into value {}", _row, access_idx, is_register, address, write_ts, write_value);
            // }

            let to_write = (is_register, address, write_ts, write_value);
            let is_unique = write_set.insert(to_write);
            if is_unique == false {
                dbg!(trace_row);
                dbg!(access_idx);
                panic!("Duplicate entry {:?} in write set", to_write);
            }

            let to_read = (is_register, address, read_ts, read_value);
            let is_unique = read_set.insert(to_read);
            if is_unique == false {
                dbg!(trace_row);
                dbg!(access_idx);
                panic!("Duplicate entry {:?} in read set", to_read);
            }
        }
    }
}

pub(crate) unsafe fn parse_delegation_ram_accesses(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    trace_row: &[Mersenne31Field],
    write_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    read_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    _row: usize,
) {
    let delegation_processor_layout = compiled_circuit
        .memory_layout
        .delegation_processor_layout
        .unwrap();
    let execute = delegation_processor_layout.multiplicity;
    let is_active = trace_row[execute.start()].as_boolean();
    if is_active {
        let write_ts = read_timestamp(trace_row, delegation_processor_layout.write_timestamp);
        assert_eq!(write_ts % 4, 3);
        assert!(write_ts >= INITIAL_TIMESTAMP);
        for (access_idx, access) in compiled_circuit
            .memory_layout
            .register_and_indirect_accesses
            .iter()
            .enumerate()
        {
            // register
            let base_offset = {
                let reg_idx = access.register_access.get_register_index();
                let read_ts = read_timestamp(
                    trace_row,
                    access.register_access.get_read_timestamp_columns(),
                );
                let read_value =
                    read_u32(trace_row, access.register_access.get_read_value_columns());
                let mut write_value = read_value;
                if let RegisterAccessColumns::WriteAccess {
                    write_value: write_columns,
                    ..
                } = access.register_access
                {
                    write_value = read_u32(trace_row, write_columns);
                }

                let to_write = (true, reg_idx, write_ts, write_value);
                let is_unique = write_set.insert(to_write);
                if is_unique == false {
                    dbg!(trace_row);
                    dbg!(access_idx);
                    panic!("Duplicate entry {:?} in write set", to_write);
                }

                let to_read = (true, reg_idx, read_ts, read_value);
                let is_unique = read_set.insert(to_read);
                if is_unique == false {
                    dbg!(trace_row);
                    dbg!(access_idx);
                    panic!("Duplicate entry {:?} in read set", to_read);
                }

                read_value
            };

            for indirect in access.indirect_accesses.iter() {
                assert!(base_offset >= common_constants::rom::ROM_BYTE_SIZE as u32);
                let mut offset = indirect.offset_constant();
                assert_eq!(offset % 4, 0);

                if let Some((var_scale, var_column, _var_idx)) = indirect.variable_dependent() {
                    let var_value = read_u16(trace_row, var_column);
                    let var_offset = var_scale.checked_mul(var_value as u32).unwrap();
                    offset = offset.checked_add(var_offset).unwrap();
                }

                let (address, of) = base_offset.overflowing_add(offset);
                assert!(of == false);
                assert!(address as usize >= common_constants::rom::ROM_BYTE_SIZE);
                let read_ts = read_timestamp(trace_row, indirect.get_read_timestamp_columns());
                let read_value = read_u32(trace_row, indirect.get_read_value_columns());
                let mut write_value = read_value;
                if let IndirectAccessColumns::WriteAccess {
                    write_value: write_columns,
                    ..
                } = indirect
                {
                    write_value = read_u32(trace_row, *write_columns);
                }

                let to_write = (false, address, write_ts, write_value);
                let is_unique = write_set.insert(to_write);
                if is_unique == false {
                    dbg!(trace_row);
                    dbg!(access_idx);
                    panic!("Duplicate entry {:?} in write set", to_write);
                }

                let to_read = (false, address, read_ts, read_value);
                let is_unique = read_set.insert(to_read);
                if is_unique == false {
                    dbg!(trace_row);
                    dbg!(access_idx);
                    panic!("Duplicate entry {:?} in read set", to_read);
                }
            }
        }
    } else {
        // check conventions
        let base_ts = read_timestamp(trace_row, delegation_processor_layout.write_timestamp);
        assert_eq!(base_ts, 0);
        for (_access_idx, access) in compiled_circuit
            .memory_layout
            .register_and_indirect_accesses
            .iter()
            .enumerate()
        {
            // register
            {
                let reg_idx = access.register_access.get_register_index();
                let read_ts = read_timestamp(
                    trace_row,
                    access.register_access.get_read_timestamp_columns(),
                );
                let read_value =
                    read_u32(trace_row, access.register_access.get_read_value_columns());
                let mut write_value = read_value;
                if let RegisterAccessColumns::WriteAccess {
                    write_value: write_columns,
                    ..
                } = access.register_access
                {
                    write_value = read_u32(trace_row, write_columns);
                }
                // assert_eq!(reg_idx, 0);
                assert_eq!(read_ts, 0);
                assert_eq!(read_value, 0);
                assert_eq!(write_value, 0);
            }

            for indirect in access.indirect_accesses.iter() {
                if let Some((_var_scale, var_column, _var_idx)) = indirect.variable_dependent() {
                    let var_value = read_u16(trace_row, var_column);
                    assert_eq!(var_value, 0);
                }
                let read_ts = read_timestamp(trace_row, indirect.get_read_timestamp_columns());
                let read_value = read_u32(trace_row, indirect.get_read_value_columns());
                let mut write_value = read_value;
                if let IndirectAccessColumns::WriteAccess {
                    write_value: write_columns,
                    ..
                } = indirect
                {
                    write_value = read_u32(trace_row, *write_columns);
                }
                assert_eq!(read_ts, 0);
                assert_eq!(read_value, 0);
                assert_eq!(write_value, 0);
            }
        }
    }
}

pub(crate) fn parse_state_permutation_elements_from_full_trace<const N: usize>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness: &WitnessEvaluationDataForExecutionFamily<N, Global>,
    write_set: &mut BTreeSet<(u32, TimestampScalar)>,
    read_set: &mut BTreeSet<(u32, TimestampScalar)>,
) {
    let mut trace = witness
        .exec_trace
        .row_view(0..(witness.exec_trace.len() - 1));
    for _row in 0..(witness.exec_trace.len() - 1) {
        // dbg!(_row);
        unsafe {
            let (_, memory) = trace.current_row_split(witness.num_witness_columns);
            parse_state_permutation_elements(compiled_circuit, &*memory, write_set, read_set);
            trace.advance_row();
        }
    }
}

pub(crate) fn parse_shuffle_ram_accesses_from_full_trace<const N: usize>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness: &WitnessEvaluationDataForExecutionFamily<N, Global>,
    write_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    read_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
) {
    let mut trace = witness
        .exec_trace
        .row_view(0..(witness.exec_trace.len() - 1));
    for row in 0..(witness.exec_trace.len() - 1) {
        unsafe {
            let (_, memory) = trace.current_row_split(witness.num_witness_columns);
            parse_shuffle_ram_accesses(compiled_circuit, &*memory, write_set, read_set, row);
            trace.advance_row();
        }
    }
}

pub(crate) fn parse_delegation_ram_accesses_from_full_trace<const N: usize>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    witness: &WitnessEvaluationData<N, Global>,
    write_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    read_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
) {
    let mut trace = witness
        .exec_trace
        .row_view(0..(witness.exec_trace.len() - 1));
    for row in 0..(witness.exec_trace.len() - 1) {
        unsafe {
            let (_, memory) = trace.current_row_split(witness.num_witness_columns);
            parse_delegation_ram_accesses(compiled_circuit, &*memory, write_set, read_set, row);
            trace.advance_row();
        }
    }
}

pub(crate) fn ensure_memory_trace_consistency<const N: usize, const M: usize>(
    memory_trace: &MemoryOnlyWitnessEvaluationDataForExecutionFamily<N, impl Allocator + Clone>,
    witness_trace: &WitnessEvaluationDataForExecutionFamily<M, impl Allocator + Clone>,
) {
    assert_eq!(
        witness_trace.exec_trace.len(),
        witness_trace.exec_trace.len()
    );
    let mut trace = witness_trace
        .exec_trace
        .row_view(0..(witness_trace.exec_trace.len() - 1));
    let mut memory = memory_trace
        .memory_trace
        .row_view(0..(memory_trace.memory_trace.len() - 1));
    for row in 0..(witness_trace.exec_trace.len() - 1) {
        unsafe {
            let (_, memory_in_witness) = trace.current_row_split(witness_trace.num_witness_columns);
            let memory_row = memory.current_row();
            assert_eq!(memory_in_witness, memory_row, "diverged at row {}", row);
            trace.advance_row();
            memory.advance_row();
        }
    }
}

const SUPPORT_SIGNED: bool = false;
const INITIAL_PC: u32 = 0;

// #[ignore = "test has explicit panic inside"]
#[test]
fn run_basic_unrolled_test() {
    run_basic_unrolled_test_impl(None);
}

pub fn run_basic_unrolled_test_impl(
    maybe_gpu_comparison_hook: Option<Box<dyn Fn(&GpuComparisonArgs)>>,
) {
    // NOTE: these constants must match with ones used in CS crate to produce
    // layout and SSA forms, otherwise derived witness-gen functions may write into
    // invalid locations
    const TRACE_LEN_LOG2: usize = 24;
    const NUM_CYCLES_PER_CHUNK: usize = (1 << TRACE_LEN_LOG2) - 1;

    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let lde_factor = 2;
    let tree_cap_size = 32;

    let default_security_config = prover_stages::ProofSecurityConfig::for_queries_only(5, 28, 63);

    let worker = Worker::new_with_num_threads(1);
    // load binary

    // let binary = std::fs::read("../examples/basic_fibonacci/app.bin").unwrap();
    let binary = std::fs::read("../examples/hashed_fibonacci/app.bin").unwrap();
    assert!(binary.len() % 4 == 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    // let text_section = std::fs::read("../examples/basic_fibonacci/app.text").unwrap();
    let text_section = std::fs::read("../examples/hashed_fibonacci/app.text").unwrap();
    assert!(text_section.len() % 4 == 0);
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let mut opcode_family_factories = HashMap::new();
    for family in 1..=4u8 {
        let factory = Box::new(|| NonMemTracingFamilyChunk::new_for_num_cycles((1 << 24) - 1));
        opcode_family_factories.insert(family, factory as _);
    }
    let mem_factory = Box::new(|| MemTracingFamilyChunk::new_for_num_cycles((1 << 24) - 1)) as _;

    let csr_processor = DelegationsCSRProcessor;

    let mut memory = VectorMemoryImplWithRom::new_for_byte_size(1 << 32, 1 << 21 as usize); // use full RAM
    for (idx, insn) in binary.iter().enumerate() {
        memory.populate(INITIAL_PC + idx as u32 * 4, *insn);
    }

    use crate::tracers::delegation::*;

    let mut factories = HashMap::new();
    for delegation_type in [
        BLAKE2S_DELEGATION_CSR_REGISTER,
        BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
    ] {
        if delegation_type == BLAKE2S_DELEGATION_CSR_REGISTER {
            let num_requests_per_circuit = (1 << 20) - 1;
            let delegation_type = delegation_type as u16;
            let factory_fn = move || {
                blake2_with_control_factory_fn(delegation_type, num_requests_per_circuit, Global)
            };
            factories.insert(
                delegation_type,
                Box::new(factory_fn) as Box<dyn Fn() -> DelegationWitness + Send + Sync + 'static>,
            );
        } else if delegation_type == BIGINT_OPS_WITH_CONTROL_CSR_REGISTER {
            let num_requests_per_circuit = (1 << 21) - 1;
            let delegation_type = delegation_type as u16;
            let factory_fn = move || {
                bigint_with_control_factory_fn(delegation_type, num_requests_per_circuit, Global)
            };
            factories.insert(
                delegation_type,
                Box::new(factory_fn) as Box<dyn Fn() -> DelegationWitness + Send + Sync + 'static>,
            );
        } else {
            panic!(
                "delegation type {} is unsupported for tests",
                delegation_type
            )
        }
    }

    let (
        final_pc,
        family_circuits,
        mem_circuits,
        delegation_circuits,
        register_final_state,
        shuffle_ram_touched_addresses,
    ) = if SUPPORT_SIGNED {
        let mut non_determinism = QuasiUARTSource::new_with_reads(vec![15, 1]); // 1000 steps of fibonacci, and 1 round of hashing
        run_unrolled_machine_for_num_cycles::<_, IMStandardIsaConfig, Global>(
            NUM_CYCLES_PER_CHUNK,
            INITIAL_PC,
            csr_processor,
            &mut memory,
            1 << 21,
            &mut non_determinism,
            opcode_family_factories,
            mem_factory,
            factories,
            1 << 32,
            &worker,
        )
    } else {
        let mut non_determinism = QuasiUARTSource::new_with_reads(vec![15, 1]); // 1000 steps of fibonacci, and 1 round of hashing
        run_unrolled_machine_for_num_cycles::<_, IMStandardIsaConfigWithUnsignedMulDiv, Global>(
            NUM_CYCLES_PER_CHUNK,
            INITIAL_PC,
            csr_processor,
            &mut memory,
            1 << 21,
            &mut non_determinism,
            opcode_family_factories,
            mem_factory,
            factories,
            1 << 32,
            &worker,
        )
    };

    println!("Finished at PC = 0x{:08x}", final_pc);
    for (reg_idx, reg) in register_final_state.iter().enumerate() {
        println!("x{} = {}", reg_idx, reg.current_value);
    }

    for (k, v) in family_circuits.iter() {
        println!(
            "Traced {} circuits of type {}, total len: {}",
            v.len(),
            k,
            v.iter().map(|el| el.data.len()).sum::<usize>()
        );
    }

    println!(
        "Traced {} memory circuits, total len {}",
        mem_circuits.len(),
        mem_circuits.iter().map(|el| el.data.len()).sum::<usize>()
    );

    let memory_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(2),
        Mersenne31Field(5),
        Mersenne31Field(42),
        Mersenne31Field(123),
    ]);
    let memory_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(11),
        Mersenne31Field(7),
        Mersenne31Field(1024),
        Mersenne31Field(8000),
    ]);

    let memory_argument_linearization_challenges_powers: [Mersenne31Quartic;
        NUM_MEM_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            memory_argument_alpha,
            NUM_MEM_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let delegation_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(5),
        Mersenne31Field(8),
        Mersenne31Field(32),
        Mersenne31Field(16),
    ]);
    let delegation_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(200),
        Mersenne31Field(100),
        Mersenne31Field(300),
        Mersenne31Field(400),
    ]);

    let state_permutation_argument_alpha = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(41),
        Mersenne31Field(42),
        Mersenne31Field(43),
        Mersenne31Field(44),
    ]);
    let state_permutation_argument_gamma = Mersenne31Quartic::from_array_of_base([
        Mersenne31Field(80),
        Mersenne31Field(90),
        Mersenne31Field(100),
        Mersenne31Field(110),
    ]);

    let delegation_argument_linearization_challenges: [Mersenne31Quartic;
        NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            delegation_argument_alpha,
            NUM_DELEGATION_ARGUMENT_KEY_PARTS - 1,
        )
        .try_into()
        .unwrap();

    let linearization_challenges: [Mersenne31Quartic; NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES] =
        materialize_powers_serial_starting_with_elem::<_, Global>(
            state_permutation_argument_alpha,
            NUM_MACHINE_STATE_LINEARIZATION_CHALLENGES,
        )
        .try_into()
        .unwrap();

    let external_values = ExternalValues {
        challenges: ExternalChallenges {
            memory_argument: ExternalMemoryArgumentChallenges {
                memory_argument_linearization_challenges:
                    memory_argument_linearization_challenges_powers,
                memory_argument_gamma,
            },
            delegation_argument: Some(ExternalDelegationArgumentChallenges {
                delegation_argument_linearization_challenges,
                delegation_argument_gamma,
            }),
            machine_state_permutation_argument: Some(ExternalMachineStateArgumentChallenges {
                linearization_challenges,
                additive_term: state_permutation_argument_gamma,
            }),
        },
        aux_boundary_values: AuxArgumentsBoundaryValues::default(),
    };

    // evaluate memory witness
    use crate::cs::machine::ops::unrolled::process_binary_into_separate_tables;

    let preprocessing_data = if SUPPORT_SIGNED {
        process_binary_into_separate_tables::<Mersenne31Field, Global>(
            &text_section,
            &opcodes_for_full_machine(),
            1 << 20,
            &[
                NON_DETERMINISM_CSR,
                BLAKE2S_DELEGATION_CSR_REGISTER as u16,
                BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            ],
        )
    } else {
        process_binary_into_separate_tables::<Mersenne31Field, Global>(
            &text_section,
            &opcodes_for_full_machine_with_unsigned_mul_div_only(),
            1 << 20,
            &[
                NON_DETERMINISM_CSR,
                BLAKE2S_DELEGATION_CSR_REGISTER as u16,
                BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            ],
        )
    };

    if false {
        println!("Will try to prove ADD/SUB/LUI/AUIPC/MOP circuit");

        let add_sub_circuit = {
            use crate::cs::machine::ops::unrolled::add_sub_lui_auipc_mop::*;
            compile_unrolled_circuit_state_transition::<Mersenne31Field>(
                &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
                &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode(cs),
                1 << 20,
                TRACE_LEN_LOG2,
            )
        };

        let family_data = &family_circuits[&ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX];
        assert_eq!(family_data.len(), 1);
        let (decoder_table_data, witness_gen_data) =
            &preprocessing_data[&ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX];
        let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

        let oracle = NonMemoryCircuitOracle {
            inner: &family_data[0].data,
            decoder_table: witness_gen_data,
            default_pc_value_in_padding: 4,
        };

        // println!(
        //     "Opcode = 0x{:08x}",
        //     family_data[0].data[4].opcode_data.opcode
        // );

        let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
            &add_sub_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
        );

        let full_trace = evaluate_witness_for_executor_family::<_, Global>(
            &add_sub_circuit,
            add_sub_lui_auipc_mod::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &TableDriver::new(),
            &worker,
            Global,
        );

        let is_satisfied = check_satisfied(
            &add_sub_circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &TableDriver::new(),
            &decoder_table_data,
            trace_len,
            &add_sub_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        //     Some(witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &add_sub_circuit,
            &vec![],
            &external_values.challenges,
            full_trace,
            &[],
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            &default_security_config,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());
    }

    if false {
        println!("Will try to prove JUMP/BRANCH/SLT circuit");

        use crate::cs::machine::ops::unrolled::jump_branch_slt::*;

        let jump_branch_circuit = {
            compile_unrolled_circuit_state_transition::<Mersenne31Field>(
                &|cs| jump_branch_slt_table_addition_fn(cs),
                &|cs| jump_branch_slt_circuit_with_preprocessed_bytecode::<_, _, true>(cs),
                1 << 20,
                TRACE_LEN_LOG2,
            )
        };

        let mut table_driver = TableDriver::<Mersenne31Field>::new();
        jump_branch_slt_table_driver_fn(&mut table_driver);

        let family_data = &family_circuits[&JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX];
        assert_eq!(family_data.len(), 1);
        let (decoder_table_data, witness_gen_data) =
            &preprocessing_data[&JUMP_BRANCH_SLT_CIRCUIT_FAMILY_IDX];
        let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

        let oracle = NonMemoryCircuitOracle {
            inner: &family_data[0].data,
            decoder_table: witness_gen_data,
            default_pc_value_in_padding: 0, // we conditionally manupulate PC, and if no opcodes are applied in padding - it would end up in 0
        };

        // println!(
        //     "Opcode = 0x{:08x}",
        //     family_data[0].data[4].opcode_data.opcode
        // );

        let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
            &jump_branch_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
        );

        let full_trace = evaluate_witness_for_executor_family::<_, Global>(
            &jump_branch_circuit,
            jump_branch_slt::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
        );

        let is_satisfied = check_satisfied(
            &jump_branch_circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table_data,
            trace_len,
            &jump_branch_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        //     Some(witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &jump_branch_circuit,
            &vec![],
            &external_values.challenges,
            full_trace,
            &[],
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            &default_security_config,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());
    }

    let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
        true,
        &[BLAKE2S_DELEGATION_CSR_REGISTER],
        TableType::SpecialCSRProperties.to_table_id(),
    );

    if false {
        println!("Will try to prove XOR/AND/OR/SHIFT/CSR circuit");
        use crate::cs::machine::ops::unrolled::shift_binary_csr::*;

        let shift_binop_csrrw_circuit = {
            compile_unrolled_circuit_state_transition::<Mersenne31Field>(
                &|cs| {
                    shift_binop_csrrw_table_addition_fn(cs);
                    // and we need to add CSR table
                    cs.add_table_with_content(
                        TableType::SpecialCSRProperties,
                        LookupWrapper::Dimensional3(csr_table.clone()),
                    );
                },
                &|cs| shift_binop_csrrw_circuit_with_preprocessed_bytecode::<_, _>(cs),
                1 << 20,
                TRACE_LEN_LOG2,
            )
        };

        let mut table_driver = TableDriver::<Mersenne31Field>::new();
        shift_binop_csrrw_table_driver_fn(&mut table_driver);
        table_driver.add_table_with_content(
            TableType::SpecialCSRProperties,
            LookupWrapper::Dimensional3(csr_table),
        );

        let family_data = &family_circuits[&SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX];
        assert_eq!(family_data.len(), 1);
        let (decoder_table_data, witness_gen_data) =
            &preprocessing_data[&SHIFT_BINARY_CSR_CIRCUIT_FAMILY_IDX];
        let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

        let oracle = NonMemoryCircuitOracle {
            inner: &family_data[0].data,
            decoder_table: witness_gen_data,
            default_pc_value_in_padding: 4,
        };

        // println!(
        //     "Opcode = 0x{:08x}",
        //     family_data[0].data[26].opcode_data.opcode
        // );

        let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
            &shift_binop_csrrw_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
        );

        let full_trace = evaluate_witness_for_executor_family::<_, Global>(
            &shift_binop_csrrw_circuit,
            shift_binop_csrrw::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
        );

        let is_satisfied = check_satisfied(
            &shift_binop_csrrw_circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table_data,
            trace_len,
            &shift_binop_csrrw_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        //     Some(witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &shift_binop_csrrw_circuit,
            &vec![],
            &external_values.challenges,
            full_trace,
            &[],
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            &default_security_config,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());
    }

    if false {
        println!("Will try to prove MUL/DIV circuit");

        use crate::cs::machine::ops::unrolled::mul_div::*;

        let witness_fn = if SUPPORT_SIGNED {
            mul_div::witness_eval_fn
        } else {
            mul_div_unsigned_only::witness_eval_fn
        };

        let mul_div_circuit = {
            compile_unrolled_circuit_state_transition::<Mersenne31Field>(
                &|cs| {
                    mul_div_table_addition_fn(cs);
                },
                &|cs| mul_div_circuit_with_preprocessed_bytecode::<_, _, SUPPORT_SIGNED>(cs),
                1 << 20,
                TRACE_LEN_LOG2,
            )
        };

        let mut table_driver = TableDriver::<Mersenne31Field>::new();
        mul_div_table_driver_fn(&mut table_driver);

        let family_data = &family_circuits[&MUL_DIV_CIRCUIT_FAMILY_IDX];
        assert_eq!(family_data.len(), 1);
        let (decoder_table_data, witness_gen_data) =
            &preprocessing_data[&MUL_DIV_CIRCUIT_FAMILY_IDX];
        let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

        let oracle = NonMemoryCircuitOracle {
            inner: &family_data[0].data,
            decoder_table: witness_gen_data,
            default_pc_value_in_padding: 4,
        };

        // println!(
        //     "Opcode = 0x{:08x}",
        //     family_data[0].data[26].opcode_data.opcode
        // );

        let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
            &mul_div_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
        );

        let full_trace = evaluate_witness_for_executor_family::<_, Global>(
            &mul_div_circuit,
            witness_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
        );

        let is_satisfied = check_satisfied(
            &mul_div_circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table_data,
            trace_len,
            &mul_div_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        //     Some(witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &mul_div_circuit,
            &vec![],
            &external_values.challenges,
            full_trace,
            &[],
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            &default_security_config,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());
    }

    if true {
        println!("Will try to prove LOAD/STORE circuit");

        use cs::machine::ops::unrolled::load_store::*;
        const SECOND_WORD_BITS: usize = 4;

        let extra_tables = create_load_store_special_tables::<_, SECOND_WORD_BITS>(&binary);
        let load_store_circuit = {
            compile_unrolled_circuit_state_transition::<Mersenne31Field>(
                &|cs| {
                    load_store_table_addition_fn(cs);
                    for (table_type, table) in extra_tables.clone() {
                        cs.add_table_with_content(table_type, table);
                    }
                },
                &|cs| load_store_circuit_with_preprocessed_bytecode::<_, _, SECOND_WORD_BITS>(cs),
                1 << 20,
                TRACE_LEN_LOG2,
            )
        };

        let mut table_driver = TableDriver::<Mersenne31Field>::new();
        load_store_table_driver_fn(&mut table_driver);
        for (table_type, table) in extra_tables.clone() {
            table_driver.add_table_with_content(table_type, table);
        }

        let family_data = &mem_circuits;
        assert_eq!(family_data.len(), 1);
        let (decoder_table_data, witness_gen_data) =
            &preprocessing_data[&LOAD_STORE_CIRCUIT_FAMILY_IDX];
        let decoder_table_data = materialize_flattened_decoder_table(decoder_table_data);

        let oracle = MemoryCircuitOracle {
            inner: &family_data[0].data,
            decoder_table: witness_gen_data,
        };

        // println!(
        //     "Opcode = 0x{:08x}",
        //     family_data[0].data[29].opcode_data.opcode
        // );

        let memory_trace = evaluate_memory_witness_for_executor_family::<_, Global>(
            &load_store_circuit,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &worker,
            Global,
        );

        let full_trace = evaluate_witness_for_executor_family::<_, Global>(
            &load_store_circuit,
            load_store::witness_eval_fn,
            NUM_CYCLES_PER_CHUNK,
            &oracle,
            &table_driver,
            &worker,
            Global,
        );

        let is_satisfied = check_satisfied(
            &load_store_circuit,
            &full_trace.exec_trace,
            full_trace.num_witness_columns,
        );
        assert!(is_satisfied);

        let twiddles: Twiddles<_, Global> = Twiddles::new(trace_len, &worker);
        let lde_precomputations = LdePrecomputations::new(trace_len, lde_factor, &[0, 1], &worker);
        let setup = SetupPrecomputations::from_tables_and_trace_len_with_decoder_table(
            &table_driver,
            &decoder_table_data,
            trace_len,
            &load_store_circuit.setup_layout,
            &twiddles,
            &lde_precomputations,
            lde_factor,
            tree_cap_size,
            &worker,
        );

        // let lookup_mapping_for_gpu = if maybe_delegator_gpu_comparison_hook.is_some() {
        //     Some(witness.lookup_mapping.clone())
        // } else {
        //     None
        // };

        println!("Trying to prove");

        let now = std::time::Instant::now();
        let (prover_data, proof) = prove_configured_for_unrolled_circuits::<
            DEFAULT_TRACE_PADDING_MULTIPLE,
            _,
            DefaultTreeConstructor,
        >(
            &load_store_circuit,
            &vec![],
            &external_values.challenges,
            full_trace,
            &[],
            &setup,
            &twiddles,
            &lde_precomputations,
            None,
            lde_factor,
            tree_cap_size,
            &default_security_config,
            &worker,
        );
        println!("Proving time is {:?}", now.elapsed());
    }

    // if !for_gpu_comparison {
    //     serialize_to_file(&proof, "delegation_proof");
    // }

    // if let Some(ref gpu_comparison_hook) = maybe_delegator_gpu_comparison_hook {
    //     let log_n = (NUM_PROC_CYCLES + 1).trailing_zeros();
    //     assert_eq!(log_n, 20);
    //     let gpu_comparison_args = GpuComparisonArgs {
    //         circuit: &compiled_machine,
    //         setup: &setup,
    //         external_values: &external_values,
    //         public_inputs: &public_inputs,
    //         twiddles: &twiddles,
    //         lde_precomputations: &lde_precomputations,
    //         table_driver: &table_driver,
    //         lookup_mapping: lookup_mapping_for_gpu.unwrap(),
    //         log_n: log_n as usize,
    //         circuit_sequence: 0,
    //         delegation_processing_type: None,
    //         prover_data: &prover_data,
    //     };
    //     gpu_comparison_hook(&gpu_comparison_args);
    // }

    // let register_contribution_in_memory_argument =
    //     produce_register_contribution_into_memory_accumulator(
    //         &register_final_values,
    //         memory_argument_linearization_challenges_powers,
    //         memory_argument_gamma,
    //     );

    // dbg!(&prover_data.stage_2_result.grand_product_accumulator);
    // dbg!(&prover_data.stage_2_result.sum_over_delegation_poly);
    // dbg!(register_contribution_in_memory_argument);

    // let mut memory_accumulator = prover_data.stage_2_result.grand_product_accumulator;
    // memory_accumulator.mul_assign(&register_contribution_in_memory_argument);

    // let mut sum_over_delegation_poly = prover_data.stage_2_result.sum_over_delegation_poly;

    // // now prove delegation circuits
    // let mut external_values = external_values;
    // external_values.aux_boundary_values = Default::default();
    // for work_type in delegation_circuits.into_iter() {
    //     dbg!(work_type.delegation_type);
    //     dbg!(work_type.trace_len);
    //     dbg!(work_type.work_units.len());

    //     let delegation_type = work_type.delegation_type;
    //     // create setup
    //     let twiddles: Twiddles<_, Global> = Twiddles::new(work_type.trace_len, &worker);
    //     let lde_precomputations =
    //         LdePrecomputations::new(work_type.trace_len, lde_factor, &[0, 1], &worker);

    //     let setup = SetupPrecomputations::from_tables_and_trace_len(
    //         &work_type.table_driver,
    //         work_type.trace_len,
    //         &work_type.compiled_circuit.setup_layout,
    //         &twiddles,
    //         &lde_precomputations,
    //         lde_factor,
    //         tree_cap_size,
    //         &worker,
    //     );

    //     for witness in work_type.work_units.into_iter() {
    //         println!(
    //             "Checking if delegation type {} circuit is satisfied",
    //             delegation_type
    //         );
    //         let is_satisfied = check_satisfied(
    //             &work_type.compiled_circuit,
    //             &witness.witness.exec_trace,
    //             witness.witness.num_witness_columns,
    //         );
    //         assert!(is_satisfied);

    //         let lookup_mapping_for_gpu = if maybe_delegated_gpu_comparison_hook.is_some() {
    //             Some(witness.witness.lookup_mapping.clone())
    //         } else {
    //             None
    //         };

    //         dbg!(witness.witness.exec_trace.len());
    //         let now = std::time::Instant::now();
    //         let (prover_data, proof) = prove::<DEFAULT_TRACE_PADDING_MULTIPLE, _>(
    //             &work_type.compiled_circuit,
    //             &[],
    //             &external_values,
    //             witness.witness,
    //             &setup,
    //             &twiddles,
    //             &lde_precomputations,
    //             0,
    //             Some(delegation_type),
    //             lde_factor,
    //             tree_cap_size,
    //             53,
    //             28,
    //             &worker,
    //         );
    //         println!(
    //             "Delegation circuit type {} proving time is {:?}",
    //             delegation_type,
    //             now.elapsed()
    //         );

    //         if let Some(ref gpu_comparison_hook) = maybe_delegated_gpu_comparison_hook {
    //             let log_n = work_type.trace_len.trailing_zeros();
    //             assert_eq!(work_type.trace_len, 1 << log_n);
    //             let dummy_public_inputs = Vec::<Mersenne31Field>::new();
    //             let gpu_comparison_args = GpuComparisonArgs {
    //                 circuit: &work_type.compiled_circuit,
    //                 setup: &setup,
    //                 external_values: &external_values,
    //                 public_inputs: &dummy_public_inputs,
    //                 twiddles: &twiddles,
    //                 lde_precomputations: &lde_precomputations,
    //                 table_driver: &work_type.table_driver,
    //                 lookup_mapping: lookup_mapping_for_gpu.unwrap(),
    //                 log_n: log_n as usize,
    //                 circuit_sequence: 0,
    //                 delegation_processing_type: Some(delegation_type),
    //                 prover_data: &prover_data,
    //             };
    //             gpu_comparison_hook(&gpu_comparison_args);
    //         }

    //         if !for_gpu_comparison {
    //             serialize_to_file(&proof, "blake2s_delegator_proof");
    //         }

    //         dbg!(prover_data.stage_2_result.grand_product_accumulator);
    //         dbg!(prover_data.stage_2_result.sum_over_delegation_poly);

    //         memory_accumulator.mul_assign(&prover_data.stage_2_result.grand_product_accumulator);
    //         sum_over_delegation_poly
    //             .sub_assign(&prover_data.stage_2_result.sum_over_delegation_poly);
    //     }
    // }

    // assert_eq!(memory_accumulator, Mersenne31Quartic::ONE);
    // assert_eq!(sum_over_delegation_poly, Mersenne31Quartic::ZERO);
}

#[test]
fn test_single_non_mem_circuit() {
    use crate::cs::cs::cs_reference::BasicAssembly;
    use cs::cs::circuit::Circuit;
    use cs::machine::ops::unrolled::add_sub_lui_auipc_mop::*;
    use cs::machine::ops::unrolled::shift_binary_csr::*;
    use std::path::Path;

    let family_idx = ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX;

    println!("Reading and preprocessing binary");
    // let (_, text_section) = read_binary(Path::new("../../zksync-os/zksync_os/app.text"));
    let (_, text_section) = read_binary(Path::new("../tools/verifier/unrolled_base_layer.text"));
    dbg!(text_section.len());
    let pc = 1434836;
    dbg!(text_section[pc / 4]);

    let mut t = process_binary_into_separate_tables_ext::<Mersenne31Field, true, Global>(
        &text_section,
        &[Box::new(AddSubLuiAuipcMopDecoder)],
        1 << 20,
        &[1984, 1991],
    );
    let (_, decoder_data) = t.remove(&family_idx).expect("decoder data");

    let oracle_input =
        fast_deserialize_from_file::<NonMemTracingFamilyChunk<Global>>("tmp_wit.bin");

    // {
    //     println!("Deserializing witness");
    //     let oracle_input = fast_deserialize_from_file::<NonMemTracingFamilyChunk<Global>>(
    //         "../../zksync-os/tests/instances/eth_runner/family_1_circuit_0_oracle_witness.bin",
    //     );
    //     let round = 288655;
    //     let t = NonMemTracingFamilyChunk {
    //         data: oracle_input.data[round..][..1].to_vec(),
    //         num_cycles: oracle_input.num_cycles,
    //     };
    //     fast_serialize_to_file(&t, "tmp_wit.bin");
    //     panic!();
    // }

    // for round in 0..oracle_input.len() {
    {
        // println!("Round = {}", round);

        let oracle = NonMemoryCircuitOracle {
            // inner: &oracle_input.data[round..][..1],
            inner: &oracle_input.data,
            decoder_table: &decoder_data,
            default_pc_value_in_padding: 4,
        };

        dbg!(oracle.inner[0]);

        let oracle: NonMemoryCircuitOracle<'static> = unsafe { core::mem::transmute(oracle) };
        let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle_and_preprocessed_decoder(
            oracle,
            decoder_data.clone(),
        );

        add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode(&mut cs);

        // shift_binop_csrrw_table_addition_fn(&mut cs);
        // let csr_table = create_csr_table_for_delegation(
        //     true,
        //     &[1984, 1991, 1994, 1995],
        //     TableType::SpecialCSRProperties.to_table_id(),
        // );
        // cs.add_table_with_content(
        //     TableType::SpecialCSRProperties,
        //     LookupWrapper::Dimensional3(csr_table.clone()),
        // );
        // shift_binop_csrrw_circuit_with_preprocessed_bytecode(&mut cs);

        assert!(cs.is_satisfied());
    }
}

#[test]
fn test_bigint_with_replayer_oracle() {
    use crate::cs::cs::cs_reference::BasicAssembly;
    use crate::cs::delegation::bigint_with_control::*;
    use crate::tracers::oracles::transpiler_oracles::delegation::*;
    use cs::cs::circuit::Circuit;
    println!("Deserializing witness");
    let oracle_input = fast_deserialize_from_file::<Vec<BigintDelegationWitness>>(
        "../../zksync-os/tests/instances/eth_runner/delegation_1994_circuit_0_oracle_witness.bin",
    );

    let round = 0;

    // for round in 0..oracle_input.len() {
    {
        println!("Round = {}", round);

        let oracle = BigintDelegationOracle {
            cycle_data: &oracle_input[round..][..1],
            marker: core::marker::PhantomData,
        };

        dbg!(oracle.cycle_data[0]);

        let oracle: BigintDelegationOracle<'static> = unsafe { core::mem::transmute(oracle) };
        let mut cs = BasicAssembly::<Mersenne31Field>::new_with_oracle(oracle);
        let (output_state_vars, output_extended_state_vars) =
            define_u256_ops_extended_control_delegation_circuit(&mut cs);

        assert!(cs.is_satisfied());

        let mut produced_state_outputs = vec![];

        use cs::types::Num;
        use cs::types::Register;

        for (_, input) in output_state_vars.iter().enumerate() {
            let register = Register(input.map(|el| Num::Var(el)));
            let value = register.get_value_unsigned(&cs).unwrap();
            produced_state_outputs.push(value);
        }

        let register = Register(output_extended_state_vars.map(|el| Num::Var(el)));
        let result_x12 = register.get_value_unsigned(&cs).unwrap();

        // assert_eq!(expected_x12, result_x12, "x12 diverged for round {}", round);

        // assert_eq!(
        //     expected_state, produced_state_outputs,
        //     "state diverged for round {}",
        //     round
        // );
    }
}

#[test]
fn test_reference_block_exec() {
    use risc_v_simulator::abstractions::non_determinism::QuasiUARTSource;
    use riscv_transpiler::ir::*;
    use riscv_transpiler::vm::*;
    use std::path::Path;

    let (_, binary) = read_binary(&Path::new("../riscv_transpiler/examples/zksync_os/app.bin"));
    let (_, text) = read_binary(&Path::new(
        "../riscv_transpiler/examples/zksync_os/app.text",
    ));

    let (witness, _) = read_binary(&Path::new(
        "../riscv_transpiler/examples/zksync_os/23620012_witness",
    ));
    let witness = hex::decode(core::str::from_utf8(&witness).unwrap()).unwrap();
    let witness: Vec<_> = witness
        .as_chunks::<4>()
        .0
        .iter()
        .map(|el| u32::from_be_bytes(*el))
        .collect();
    let mut source = QuasiUARTSource::new_with_reads(witness);

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig>(&text);
    let tape = SimpleTape::new(&instructions);
    let mut ram =
        RamWithRomRegion::<{ common_constants::rom::ROM_SECOND_WORD_BITS }>::from_rom_content(
            &binary,
            1 << 30,
        );

    let cycles_bound = 1 << 30;

    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
    let mut snapshotter = SimpleSnapshotter::new_with_cycle_limit(cycles_bound, state);

    let now = std::time::Instant::now();
    VM::run_basic_unrolled::<_, _, _>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut source,
    );
    let elapsed = now.elapsed();

    let final_timestamp = state.timestamp;
    assert_eq!(final_timestamp % TIMESTAMP_STEP, 0);
    let num_instructions = (final_timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP;
    println!(
        "Frequency is {} MHz over {} instructions",
        (num_instructions as f64) * 1000f64 / (elapsed.as_nanos() as f64),
        num_instructions,
    );

    println!("PC = 0x{:08x}", state.pc);
    dbg!(state.registers.map(|el| el.value));

    {
        let worker = Worker::new_with_num_threads(8);
        use crate::unrolled::replay_non_mem;
        let cycles_per_circuit = (1 << 24) - 1;
        let now = std::time::Instant::now();
        let t = replay_non_mem::<
            ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX,
            Global,
            { common_constants::rom::ROM_SECOND_WORD_BITS },
        >(&tape, &snapshotter, cycles_per_circuit, &worker);
        let elapsed = now.elapsed();

        println!(
            "Replay frequency is {} MHz over {} instructions into {} circuits",
            (num_instructions as f64) * 1000f64 / (elapsed.as_nanos() as f64),
            num_instructions,
            t.len(),
        );
    }
}
