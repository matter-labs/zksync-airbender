use super::*;
use crate::gkr::witness_gen::family_circuits::{GKRFullWitnessTrace, GKRMemoryOnlyWitnessTrace};
use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRCircuitArtifact;
use fft::GoodAllocator;
use field::PrimeField;

use std::alloc::Allocator;
use std::collections::BTreeSet;

fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    serde_json::from_reader(src).unwrap()
}

mod family_circuits;

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

    include!("../../../compiled_circuits/add_sub_lui_auipc_mop_preprocessed_generated_gkr.rs");

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

    include!("../../../compiled_circuits/jump_branch_slt_preprocessed_generated_gkr.rs");

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

    include!("../../../compiled_circuits/shift_binop_preprocessed_generated_gkr.rs");

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

    include!("../../../compiled_circuits/mem_word_only_preprocessed_generated_gkr.rs");

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

    include!("../../../compiled_circuits/mem_subword_only_preprocessed_generated_gkr.rs");

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
