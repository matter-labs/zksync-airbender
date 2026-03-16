use super::*;

#[cfg(test)]
use crate::tracers::unrolled::tracer::*;
use crate::unrolled::evaluate_witness_for_executor_family;
use crate::unrolled::MemoryCircuitOracle;
use crate::unrolled::NonMemoryCircuitOracle;
use common_constants::delegation_types::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER;
use cs::cs::circuit::Circuit;
use cs::machine::ops::unrolled::*;
#[cfg(test)]
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use std::alloc::Allocator;
use std::collections::BTreeSet;

use crate::prover_stages::unrolled_prover::prove_configured_for_unrolled_circuits;
use crate::witness_evaluator::unrolled::evaluate_memory_witness_for_executor_family;

#[cfg(test)]
use test_utils::skip_if_ci;

#[cfg(test)]
mod reduced_machine;
pub mod with_transpiler;

#[allow(unused_imports)]
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

#[allow(unused_imports)]
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

#[allow(unused_imports)]
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

#[allow(unused_imports)]
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

#[allow(unused_imports)]
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

#[allow(unused_imports)]
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

#[allow(unused_imports)]
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
                let _reg_idx = access.register_access.get_register_index();
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

#[cfg(test)]
#[ignore = "requires local witness fixture (tmp_wit.bin)"]
#[test]
fn test_single_non_mem_circuit() {
    skip_if_ci!();
    use crate::cs::cs::cs_reference::BasicAssembly;
    use cs::cs::circuit::Circuit;
    use cs::machine::ops::unrolled::add_sub_lui_auipc_mop::*;
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

#[cfg(test)]
#[ignore = "requires external zksync-os witness fixtures"]
#[test]
fn test_bigint_with_replayer_oracle() {
    skip_if_ci!();
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
        let _result_x12 = register.get_value_unsigned(&cs).unwrap();

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
    use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
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
