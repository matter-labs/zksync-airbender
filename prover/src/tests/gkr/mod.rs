use super::*;
use crate::gkr::witness_gen::family_circuits::{GKRFullWitnessTrace, GKRMemoryOnlyWitnessTrace};
use common_constants::*;
use cs::definitions::gkr::*;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRCircuitArtifact;
use fft::GoodAllocator;
use field::PrimeField;
use std::alloc::Allocator;
use std::collections::BTreeSet;

pub(crate) fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

pub(crate) fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    serde_json::from_reader(src).unwrap()
}

pub(crate) mod codegen_ir_crossval;
pub(crate) mod dag_ir_oracle;
pub(crate) mod evaluators;

mod family_circuits;
mod malicious_proofs;

pub(crate) fn ensure_memory_trace_consistency<F: PrimeField>(
    memory_trace: &GKRMemoryOnlyWitnessTrace<F, impl Allocator + Clone, impl Allocator + Clone>,
    witness_trace: &GKRFullWitnessTrace<F, impl Allocator + Clone, impl Allocator + Clone>,
) {
    assert_eq!(
        memory_trace.column_major_trace.len(),
        witness_trace.column_major_memory_trace.len()
    );
    for column in 0..memory_trace.column_major_trace.len() {
        let from_mem = &memory_trace.column_major_trace[column];
        let from_wit = &witness_trace.column_major_memory_trace[column];

        assert_eq!(from_mem.len(), from_wit.len());
        assert!(from_mem.len().is_power_of_two());
        for row in 0..from_mem.len() {
            assert_eq!(
                from_mem[row], from_wit[row],
                "diverged for column {}, row {}",
                column, row
            );
        }
    }
}

pub fn check_satisfied<F: PrimeField, A: GoodAllocator, B: GoodAllocator>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    full_trace: &GKRFullWitnessTrace<F, A, B>,
) -> bool {
    let trace_len = full_trace.column_major_memory_trace[0].len();
    assert!(trace_len.is_power_of_two());
    for p in full_trace.column_major_memory_trace.iter() {
        assert_eq!(p.len(), trace_len);
    }
    for p in full_trace.column_major_witness_trace.iter() {
        assert_eq!(p.len(), trace_len);
    }
    for row in 0..trace_len {
        let row_satisfied = check_satisfied_row(compiled_circuit, full_trace, row);
        if row_satisfied == false {
            println!("Unsatisfied at row {}", row);
            return false;
        }
    }

    true
}

fn evaluate_linear_constraint<F: PrimeField, A: GoodAllocator, B: GoodAllocator>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    full_trace: &GKRFullWitnessTrace<F, A, B>,
    absolute_row_idx: usize,
    constraint_idx: usize,
) -> F {
    let constraint = &compiled_circuit.degree_1_constraints[constraint_idx];
    let mut result = constraint.constant_term;
    for (c, a) in constraint.linear_terms.iter() {
        let mut t = *c;
        let a = match compiled_circuit.placement_data[a] {
            GKRAddress::BaseLayerMemory(offset) => {
                full_trace.column_major_memory_trace[offset][absolute_row_idx]
            }
            GKRAddress::BaseLayerWitness(offset) => {
                full_trace.column_major_witness_trace[offset][absolute_row_idx]
            }
            _ => {
                return F::ZERO;
            }
        };
        t.mul_assign(&a);
        result.add_assign(&t);
    }

    result
}

fn evaluate_quadratic_constraint<F: PrimeField, A: GoodAllocator, B: GoodAllocator>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    full_trace: &GKRFullWitnessTrace<F, A, B>,
    absolute_row_idx: usize,
    constraint_idx: usize,
) -> F {
    let constraint = &compiled_circuit.degree_2_constraints[constraint_idx];
    let mut result = constraint.constant_term;
    for (c, a, b) in constraint.quadratic_terms.iter() {
        let mut t = *c;
        let a = match compiled_circuit.placement_data[a] {
            GKRAddress::BaseLayerMemory(offset) => {
                full_trace.column_major_memory_trace[offset][absolute_row_idx]
            }
            GKRAddress::BaseLayerWitness(offset) => {
                full_trace.column_major_witness_trace[offset][absolute_row_idx]
            }
            _ => {
                return F::ZERO;
            }
        };
        let b = match compiled_circuit.placement_data[b] {
            GKRAddress::BaseLayerMemory(offset) => {
                full_trace.column_major_memory_trace[offset][absolute_row_idx]
            }
            GKRAddress::BaseLayerWitness(offset) => {
                full_trace.column_major_witness_trace[offset][absolute_row_idx]
            }
            _ => {
                return F::ZERO;
            }
        };
        t.mul_assign(&a);
        t.mul_assign(&b);
        result.add_assign(&t);
    }

    for (c, a) in constraint.linear_terms.iter() {
        let mut t = *c;
        let a = match compiled_circuit.placement_data[a] {
            GKRAddress::BaseLayerMemory(offset) => {
                full_trace.column_major_memory_trace[offset][absolute_row_idx]
            }
            GKRAddress::BaseLayerWitness(offset) => {
                full_trace.column_major_witness_trace[offset][absolute_row_idx]
            }
            _ => {
                return F::ZERO;
            }
        };
        t.mul_assign(&a);
        result.add_assign(&t);
    }

    result
}

fn read_value<F: PrimeField, A: GoodAllocator, B: GoodAllocator>(
    full_trace: &GKRFullWitnessTrace<F, A, B>,
    absolute_row_idx: usize,
    pos: GKRAddress,
) -> F {
    match pos {
        GKRAddress::BaseLayerMemory(offset) => {
            full_trace.column_major_memory_trace[offset][absolute_row_idx]
        }
        GKRAddress::BaseLayerWitness(offset) => {
            full_trace.column_major_witness_trace[offset][absolute_row_idx]
        }
        _ => {
            return F::ZERO;
        }
    }
}

pub fn check_satisfied_row<F: PrimeField, A: GoodAllocator, B: GoodAllocator>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    full_trace: &GKRFullWitnessTrace<F, A, B>,
    absolute_row_idx: usize,
) -> bool {
    // we only check constraints and not tables
    for idx in 0..compiled_circuit.degree_1_constraints.len() {
        let eval_result =
            evaluate_linear_constraint(compiled_circuit, full_trace, absolute_row_idx, idx);
        if eval_result != F::ZERO {
            println!(
                "Unsatisfied at row {}, linear constraint {:?}",
                absolute_row_idx, &compiled_circuit.degree_1_constraints[idx]
            );
            let constraint = &compiled_circuit.degree_1_constraints[idx];
            let mut all_vars = BTreeSet::new();
            for (_, a) in constraint.linear_terms.iter() {
                all_vars.insert(*a);
            }
            for var in all_vars.into_iter() {
                let pos = compiled_circuit.placement_data[&var];
                if let Some(name) = compiled_circuit.variable_names.get(&var) {
                    println!(
                        "Variable {:?} `{}` (position {:?}) = {:?}",
                        var,
                        name,
                        pos,
                        read_value(full_trace, absolute_row_idx, pos)
                    );
                } else {
                    println!(
                        "Variable {:?} (position {:?}) = {:?}",
                        var,
                        pos,
                        read_value(full_trace, absolute_row_idx, pos)
                    );
                }
            }
            return false;
        }
    }
    for idx in 0..compiled_circuit.degree_2_constraints.len() {
        let eval_result =
            evaluate_quadratic_constraint(compiled_circuit, full_trace, absolute_row_idx, idx);
        if eval_result != F::ZERO {
            println!(
                "Unsatisfied at row {}, quadratic constraint {:?}",
                absolute_row_idx, &compiled_circuit.degree_2_constraints[idx]
            );
            let mut all_vars = BTreeSet::new();
            let constraint = &compiled_circuit.degree_2_constraints[idx];
            for (_, a, b) in constraint.quadratic_terms.iter() {
                all_vars.insert(*a);
                all_vars.insert(*b);
            }
            for (_, a) in constraint.linear_terms.iter() {
                all_vars.insert(*a);
            }
            for var in all_vars.into_iter() {
                let pos = compiled_circuit.placement_data[&var];
                if let Some(name) = compiled_circuit.variable_names.get(&var) {
                    println!(
                        "Variable {:?} `{}` (position {:?}) = {:?}",
                        var,
                        name,
                        pos,
                        read_value(full_trace, absolute_row_idx, pos)
                    );
                } else {
                    println!(
                        "Variable {:?} (position {:?}) = {:?}",
                        var,
                        pos,
                        read_value(full_trace, absolute_row_idx, pos)
                    );
                }
            }
            return false;
        }
    }

    true
}

mod add_sub_lui_auipc_mop {
    use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use crate::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
    use crate::gkr::witness_gen::witness_proxy::WitnessProxy;
    use ::cs::oracle::Placeholder;
    use ::cs::witness_placer::WitnessTypeSet;
    use ::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::baby_bear::base::BabyBearField;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../compiled_circuits/add_sub_lui_auipc_mop_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BabyBearField>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BabyBearField, true>,
            ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BabyBearField>,
        >;
        (fn_ptr)(proxy);
    }
}

mod jump_branch_slt {
    use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use crate::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
    use crate::gkr::witness_gen::witness_proxy::WitnessProxy;
    use ::cs::oracle::Placeholder;
    use ::cs::witness_placer::WitnessTypeSet;
    use ::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::baby_bear::base::BabyBearField;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../compiled_circuits/jump_branch_slt_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BabyBearField>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BabyBearField, true>,
            ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BabyBearField>,
        >;
        (fn_ptr)(proxy);
    }
}

mod shift_binary_ops {
    use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use crate::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
    use crate::gkr::witness_gen::witness_proxy::WitnessProxy;
    use ::cs::oracle::Placeholder;
    use ::cs::witness_placer::WitnessTypeSet;
    use ::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::baby_bear::base::BabyBearField;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../compiled_circuits/shift_binop_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BabyBearField>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BabyBearField, true>,
            ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BabyBearField>,
        >;
        (fn_ptr)(proxy);
    }
}

mod unsigned_mul_div {
    use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use crate::gkr::witness_gen::oracles::NonMemoryCircuitOracle;
    use crate::gkr::witness_gen::witness_proxy::WitnessProxy;
    use ::cs::oracle::Placeholder;
    use ::cs::witness_placer::WitnessTypeSet;
    use ::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::baby_bear::base::BabyBearField;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../compiled_circuits/unsigned_mul_div_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BabyBearField>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BabyBearField, true>,
            ColumnMajorWitnessProxy<'a, NonMemoryCircuitOracle<'b>, BabyBearField>,
        >;
        (fn_ptr)(proxy);
    }
}

mod mem_word_only {
    use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use crate::gkr::witness_gen::oracles::MemoryCircuitOracle;
    use crate::gkr::witness_gen::witness_proxy::WitnessProxy;
    use ::cs::oracle::Placeholder;
    use ::cs::witness_placer::WitnessTypeSet;
    use ::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::baby_bear::base::BabyBearField;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../compiled_circuits/mem_word_only_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, MemoryCircuitOracle<'b>, BabyBearField>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BabyBearField, true>,
            ColumnMajorWitnessProxy<'a, MemoryCircuitOracle<'b>, BabyBearField>,
        >;
        (fn_ptr)(proxy);
    }
}

mod mem_subword_only {
    use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use crate::gkr::witness_gen::oracles::MemoryCircuitOracle;
    use crate::gkr::witness_gen::witness_proxy::WitnessProxy;
    use ::cs::oracle::Placeholder;
    use ::cs::witness_placer::WitnessTypeSet;
    use ::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::baby_bear::base::BabyBearField;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../compiled_circuits/mem_subword_only_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, MemoryCircuitOracle<'b>, BabyBearField>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BabyBearField, true>,
            ColumnMajorWitnessProxy<'a, MemoryCircuitOracle<'b>, BabyBearField>,
        >;
        (fn_ptr)(proxy);
    }
}

mod blake2_with_extended_control {
    use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use crate::gkr::witness_gen::witness_proxy::WitnessProxy;
    use crate::tracers::oracles::transpiler_oracles::delegation::Blake2sDelegationOracle;
    use ::cs::oracle::Placeholder;
    use ::cs::witness_placer::WitnessTypeSet;
    use ::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::baby_bear::base::BabyBearField;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../compiled_circuits/blake2_with_extended_control_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, Blake2sDelegationOracle<'b>, BabyBearField>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BabyBearField, true>,
            ColumnMajorWitnessProxy<'a, Blake2sDelegationOracle<'b>, BabyBearField>,
        >;
        (fn_ptr)(proxy);
    }
}

mod bigint_with_extended_control {
    use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use crate::gkr::witness_gen::witness_proxy::WitnessProxy;
    use crate::tracers::oracles::transpiler_oracles::delegation::BigintDelegationOracle;
    use ::cs::oracle::Placeholder;
    use ::cs::witness_placer::WitnessTypeSet;
    use ::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::baby_bear::base::BabyBearField;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../compiled_circuits/bigint_with_extended_control_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, BigintDelegationOracle<'b>, BabyBearField>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BabyBearField, true>,
            ColumnMajorWitnessProxy<'a, BigintDelegationOracle<'b>, BabyBearField>,
        >;
        (fn_ptr)(proxy);
    }
}

mod keccak_special5 {
    use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use crate::gkr::witness_gen::witness_proxy::WitnessProxy;
    use crate::tracers::oracles::transpiler_oracles::delegation::KeccakDelegationOracle;
    use ::cs::oracle::Placeholder;
    use ::cs::witness_placer::WitnessTypeSet;
    use ::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::baby_bear::base::BabyBearField;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../compiled_circuits/keccak_special5_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<'a, KeccakDelegationOracle<'b>, BabyBearField>,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BabyBearField, true>,
            ColumnMajorWitnessProxy<'a, KeccakDelegationOracle<'b>, BabyBearField>,
        >;
        (fn_ptr)(proxy);
    }
}

mod blake2_g_function {
    use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
    use crate::gkr::witness_gen::witness_proxy::WitnessProxy;
    use crate::tracers::oracles::transpiler_oracles::delegation::Blake2sGFunctionDelegationOracle;
    use ::cs::oracle::Placeholder;
    use ::cs::witness_placer::WitnessTypeSet;
    use ::cs::witness_placer::{
        WitnessComputationCore, WitnessComputationalField, WitnessComputationalI32,
        WitnessComputationalInteger, WitnessComputationalU16, WitnessComputationalU32,
        WitnessComputationalU8, WitnessMask,
    };
    use ::field::baby_bear::base::BabyBearField;
    use cs::witness_placer::scalar_witness_type_set::ScalarWitnessTypeSet;

    include!("../../../compiled_circuits/blake2_g_function_generated_gkr.rs");

    pub fn witness_eval_fn<'a, 'b>(
        proxy: &'_ mut ColumnMajorWitnessProxy<
            'a,
            Blake2sGFunctionDelegationOracle<'b>,
            BabyBearField,
        >,
    ) {
        let fn_ptr = evaluate_witness_fn::<
            ScalarWitnessTypeSet<BabyBearField, true>,
            ColumnMajorWitnessProxy<'a, Blake2sGFunctionDelegationOracle<'b>, BabyBearField>,
        >;
        (fn_ptr)(proxy);
    }
}

pub(crate) fn read_u32<F: PrimeField>(trace_row: &[F], columns: [usize; 2]) -> u32 {
    let low = trace_row[columns[0]].as_u32_reduced();
    let high = trace_row[columns[1]].as_u32_reduced();

    (high << 16) | low
}

pub(crate) fn read_u32_from_u8x4<F: PrimeField>(trace_row: &[F], columns: [usize; 4]) -> u32 {
    let a = trace_row[columns[0]].as_u32_reduced();
    let b = trace_row[columns[1]].as_u32_reduced();
    let c = trace_row[columns[2]].as_u32_reduced();
    let d = trace_row[columns[3]].as_u32_reduced();

    a | (b << 8) | (c << 16) | (d << 24)
}

pub(crate) fn read_u16<F: PrimeField>(trace_row: &[F], column: usize) -> u16 {
    let low = trace_row[column].as_u32_reduced();

    low as u16
}

pub(crate) fn read_timestamp<F: PrimeField>(
    trace_row: &[F],
    columns: [usize; 2],
) -> TimestampScalar {
    let low = trace_row[columns[0]].as_u32_reduced();
    let high = trace_row[columns[1]].as_u32_reduced();

    ((high as TimestampScalar) << TIMESTAMP_COLUMNS_NUM_BITS) | (low as TimestampScalar)
}

pub(crate) fn parse_state_permutation_elements<F: PrimeField>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    trace_row: &[F],
    write_set: &mut BTreeSet<(u32, TimestampScalar)>,
    read_set: &mut BTreeSet<(u32, TimestampScalar)>,
) {
    let machine_state_layout = compiled_circuit.memory_layout.machine_state.unwrap();
    let execute = machine_state_layout.execute;
    let is_active = trace_row[execute].as_boolean();
    let initial_ts = read_timestamp(trace_row, machine_state_layout.initial_state.timestamp);
    let final_ts = read_timestamp(trace_row, machine_state_layout.final_state.timestamp);

    let initial_pc = read_u32(trace_row, machine_state_layout.initial_state.pc);
    let final_pc = read_u32(trace_row, machine_state_layout.final_state.pc);

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
pub(crate) fn parse_shuffle_ram_accesses<F: PrimeField>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    trace_row: &[F],
    write_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    read_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    delegation_write_set: &mut BTreeSet<(bool, u32, TimestampScalar)>,
    _row: usize,
) {
    let machine_state_layout = compiled_circuit.memory_layout.machine_state.unwrap();
    let execute = machine_state_layout.execute;
    let is_active = trace_row[execute].as_boolean();
    if is_active {
        let base_ts = read_timestamp(trace_row, machine_state_layout.initial_state.timestamp);
        assert!(base_ts >= INITIAL_TIMESTAMP);
        for (access_idx, access) in compiled_circuit
            .memory_layout
            .ram_access_sets
            .iter()
            .enumerate()
        {
            let read_ts = read_timestamp(trace_row, access.get_read_timestamp_columns());
            let read_value = match access.get_read_value_columns() {
                RamWordRepresentation::U16Limbs(words) => read_u32(trace_row, words),
                RamWordRepresentation::U8Limbs(bytes) => read_u32_from_u8x4(trace_row, bytes),
                RamWordRepresentation::Zero => 0u32,
            };
            let mut write_value = read_value;
            if let RamQuery::Write(write) = access {
                write_value = match write.write_value {
                    RamWordRepresentation::U16Limbs(words) => read_u32(trace_row, words),
                    RamWordRepresentation::U8Limbs(bytes) => read_u32_from_u8x4(trace_row, bytes),
                    RamWordRepresentation::Zero => 0u32,
                };
            }
            let write_ts = base_ts + (access.local_timestamp_in_cycle() as TimestampScalar);
            let mut is_register = true;
            let address;
            match access.get_address() {
                RamAddress::ConstantRegister(reg_idx) => {
                    address = reg_idx as u32;
                }
                RamAddress::RegisterOnly(reg_idx) => {
                    let reg_idx = read_u16(trace_row, reg_idx.register_index);
                    address = reg_idx as u32;
                }
                RamAddress::RegisterOrRam(addr) => {
                    match addr.address_space {
                        RegisterOrRamAddressSpace::RamAddressSpace(column) => {
                            let flag = read_u16(trace_row, column) == 1;
                            if flag {
                                is_register = false;
                            }
                        }
                        RegisterOrRamAddressSpace::RegisterAddressSpace(column) => {
                            let flag = read_u16(trace_row, column) == 1;
                            if flag == false {
                                is_register = false;
                            }
                        }
                    }
                    address = read_u32(trace_row, addr.address);
                }
                RamAddress::IndirectRam(..) => {
                    unreachable!()
                }
            }

            if is_register == false && address < common_constants::rom::ROM_BYTE_SIZE as u32 {
                assert_eq!(read_value, 0);
                let RamQuery::Readonly(..) = access else {
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
            if is_register && address >= 32 {
                assert_eq!(write_value, 0);
                assert_eq!(read_value, 0);
                assert!((read_ts == 0 && write_ts != 0) | (read_ts != 0 && write_ts == 0));
                if read_ts == 0 {
                    let is_unique = delegation_write_set.insert((is_register, address, write_ts));
                    if is_unique == false {
                        dbg!(trace_row);
                        dbg!(access_idx);
                        panic!(
                            "Duplicate delegation entry {:?} in write set",
                            (is_register, address, write_ts)
                        );
                    }
                } else {
                    dbg!(trace_row);
                    dbg!(access_idx);
                    panic!(
                        "Delegation entry {:?} in with zero write ts",
                        (is_register, address, read_ts)
                    );
                }
            } else {
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

            // if is_register == false && address == 71302656 {
            //     // dbg!(trace_row);
            //     dbg!(access_idx);
            //     dbg!(read_ts);
            // }
        }
    }
}

pub(crate) fn parse_delegation_ram_accesses<F: PrimeField>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    trace_row: &[F],
    write_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    read_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    delegation_read_set: &mut BTreeSet<(bool, u32, TimestampScalar)>,
    delegation_type: u16,
    _row: usize,
) {
    let delegation_processor_layout = compiled_circuit
        .memory_layout
        .delegation_state
        .as_ref()
        .unwrap();
    let execute = delegation_processor_layout.execute;
    let is_active = trace_row[execute].as_boolean();
    if is_active {
        const WRITE_TS_OFFSET: TimestampScalar = 2;
        let invocation_ts =
            read_timestamp(trace_row, delegation_processor_layout.invocation_timestamp);
        assert_eq!(
            invocation_ts % 4,
            1,
            "invocation timestamp must be 1 mod 4 in delegations, got {}",
            invocation_ts
        );
        assert!(invocation_ts >= INITIAL_TIMESTAMP);
        let write_ts = invocation_ts + WRITE_TS_OFFSET;

        // mark delegation itself
        let is_unique = delegation_read_set.insert((true, delegation_type as u32, invocation_ts));
        if is_unique == false {
            dbg!(trace_row);
            panic!(
                "Duplicate delegation entry {:?} in read set",
                (true, delegation_type, invocation_ts)
            );
        }

        for (access_idx, access) in compiled_circuit
            .memory_layout
            .ram_access_sets
            .iter()
            .enumerate()
        {
            // otherwise it's registers and corresponding indirects
            let is_register;
            let address;
            let read_value;
            let write_value;
            let read_ts;

            match access {
                RamQuery::Readonly(readonly_access) => {
                    assert_eq!(readonly_access.in_cycle_write_index, WRITE_TS_OFFSET as u32);
                    let RamWordRepresentation::U16Limbs(read_value_columns) =
                        readonly_access.read_value
                    else {
                        unreachable!()
                    };
                    let value = read_u32(trace_row, read_value_columns);
                    read_value = value;
                    write_value = value;
                    read_ts = read_timestamp(trace_row, readonly_access.read_timestamp);
                    match readonly_access.address {
                        RamAddress::ConstantRegister(reg) => {
                            assert!(reg < 32);
                            assert!(reg > 0);
                            is_register = true;
                            address = reg as u32;
                        }
                        RamAddress::IndirectRam(indirect) => {
                            is_register = false;
                            let mut computed_address =
                                read_u32(trace_row, indirect.base_register_value);
                            computed_address += indirect.constant_offset as u32;
                            if let Some((c, v)) = indirect.variable_offset {
                                let mut t = read_u16(trace_row, v) as u32;
                                t *= c as u32;
                                computed_address += t;
                            }
                            address = computed_address;
                        }
                        a @ _ => {
                            panic!("{:?} access is not allowed in delegations", a);
                        }
                    }
                }
                RamQuery::Write(read_write_access) => {
                    assert_eq!(
                        read_write_access.in_cycle_write_index,
                        WRITE_TS_OFFSET as u32
                    );
                    let RamWordRepresentation::U16Limbs(read_value_columns) =
                        read_write_access.read_value
                    else {
                        unreachable!()
                    };
                    read_value = read_u32(trace_row, read_value_columns);
                    let RamWordRepresentation::U16Limbs(write_value_columns) =
                        read_write_access.write_value
                    else {
                        unreachable!()
                    };
                    write_value = read_u32(trace_row, write_value_columns);
                    read_ts = read_timestamp(trace_row, read_write_access.read_timestamp);
                    match read_write_access.address {
                        RamAddress::ConstantRegister(reg) => {
                            assert!(reg < 32);
                            assert!(reg > 0);
                            is_register = true;
                            address = reg as u32;
                        }
                        RamAddress::IndirectRam(indirect) => {
                            is_register = false;
                            let mut computed_address =
                                read_u32(trace_row, indirect.base_register_value);
                            computed_address += indirect.constant_offset as u32;
                            if let Some((c, v)) = indirect.variable_offset {
                                let mut t = read_u16(trace_row, v) as u32;
                                t *= c as u32;
                                computed_address += t;
                            }
                            address = computed_address;
                        }
                        a @ _ => {
                            panic!("{:?} access is not allowed in delegations", a);
                        }
                    }
                }
            }

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

            // if is_register == false && address == 71302656 {
            //     dbg!(_row);
            //     // dbg!(trace_row);
            //     dbg!(access_idx);
            //     dbg!(read_ts);
            // }
        }
    }
}

pub(crate) fn read_memory_trace_row<F: PrimeField>(
    witness: &GKRMemoryOnlyWitnessTrace<F, impl Allocator + Clone, impl Allocator + Clone>,
    row: usize,
    buffer: &mut Vec<F>,
) {
    buffer.clear();
    for column in witness.column_major_trace.iter() {
        let value = column[row];
        buffer.push(value);
    }
}

pub(crate) fn parse_state_permutation_elements_from_full_trace<F: PrimeField>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    witness: &GKRMemoryOnlyWitnessTrace<F, impl Allocator + Clone, impl Allocator + Clone>,
    write_set: &mut BTreeSet<(u32, TimestampScalar)>,
    read_set: &mut BTreeSet<(u32, TimestampScalar)>,
) {
    let mut buffer = Vec::new();
    for row in 0..compiled_circuit.trace_len {
        // dbg!(_row);
        read_memory_trace_row(witness, row, &mut buffer);
        parse_state_permutation_elements(compiled_circuit, &buffer, write_set, read_set);
    }
}

pub(crate) fn parse_shuffle_ram_accesses_from_full_trace<F: PrimeField>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    witness: &GKRMemoryOnlyWitnessTrace<F, impl Allocator + Clone, impl Allocator + Clone>,
    write_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    read_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    delegation_write_set: &mut BTreeSet<(bool, u32, TimestampScalar)>,
) {
    let mut buffer = Vec::new();
    for row in 0..compiled_circuit.trace_len {
        read_memory_trace_row(witness, row, &mut buffer);
        parse_shuffle_ram_accesses(
            compiled_circuit,
            &buffer,
            write_set,
            read_set,
            delegation_write_set,
            row,
        );
    }
}

pub(crate) fn parse_delegation_ram_accesses_from_full_trace<F: PrimeField>(
    compiled_circuit: &GKRCircuitArtifact<F>,
    witness: &GKRMemoryOnlyWitnessTrace<F, impl Allocator + Clone, impl Allocator + Clone>,
    write_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    read_set: &mut BTreeSet<(bool, u32, TimestampScalar, u32)>,
    delegation_read_set: &mut BTreeSet<(bool, u32, TimestampScalar)>,
    delegation_type: u16,
) {
    let mut buffer = Vec::new();
    for row in 0..compiled_circuit.trace_len {
        read_memory_trace_row(witness, row, &mut buffer);
        parse_delegation_ram_accesses(
            compiled_circuit,
            &buffer,
            write_set,
            read_set,
            delegation_read_set,
            delegation_type,
            row,
        );
    }
}
