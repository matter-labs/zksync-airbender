use super::*;
use crate::upstream::UnrolledCircuitWitnessEvalFn;
use execution_prover_model::circuit_type::{
    UnrolledCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType,
};
use execution_prover_model::MachineType;
use worker::Worker;

/// A padded ROM image large enough for decoder preprocessing.
fn test_binary() -> Vec<u32> {
    let words = (1usize << (16 + common_constants::ROM_SECOND_WORD_BITS)) / 4;
    vec![0u32; words]
}

fn eval_fn_of(setup: &CanonicalCircuitSetup) -> Option<&UnrolledCircuitWitnessEvalFn<Global>> {
    match setup {
        CanonicalCircuitSetup::Riscv(setup) => setup.witness_eval_fn.as_ref(),
        CanonicalCircuitSetup::Delegation(_) => None,
    }
}

#[test]
fn cpu_non_memory_setup_retains_evaluator_decoder_and_padding_pc() {
    let worker = Worker::new();
    let binary = test_binary();
    let circuit_type = UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop;
    let canonical = build_unrolled_setup(
        MachineType::FullUnsigned,
        UnrolledCircuitType::NonMemory(circuit_type),
        &binary,
        &binary,
        &worker,
    );

    let (decoder_table, default_pc_value_in_padding) = match eval_fn_of(&canonical) {
        Some(UnrolledCircuitWitnessEvalFn::NonMemory {
            decoder_table,
            default_pc_value_in_padding,
            ..
        }) => (decoder_table, *default_pc_value_in_padding),
        other => panic!("expected a NonMemory evaluator, got {:?}", other.is_some()),
    };
    assert!(!decoder_table.is_empty());
    assert_eq!(
        default_pc_value_in_padding,
        circuit_type.get_default_pc_value_in_padding(),
        "padding PC disagrees with the circuit-type accessor the GPU oracle uses"
    );

    // Absent decoder entries must occupy a defaulted row in the dense table.
    let dense = canonical.decoder_data().expect("non-memory decoder rows");
    assert_eq!(dense.len(), decoder_table.len());
    let absent = decoder_table.iter().filter(|e| e.is_none()).count();
    assert!(
        absent > 0,
        "an all-zero ROM should leave undecodable words absent, exercising the default"
    );
    for (dense_row, table_entry) in dense.iter().zip(decoder_table.iter()) {
        let expected = table_entry.as_ref().copied().unwrap_or_default();
        assert_eq!(dense_row.imm, expected.imm);
        assert_eq!(dense_row.rd_index, expected.rd_index);
        assert_eq!(dense_row.opcode_family_bits, expected.opcode_family_bits);
    }
}

#[test]
fn cpu_every_unrolled_family_of_every_machine_type_builds() {
    let worker = Worker::new();
    let binary = test_binary();
    for machine in [MachineType::FullUnsigned, MachineType::Reduced] {
        for circuit in UnrolledMemoryCircuitType::get_circuit_types_for_machine_type(machine) {
            let circuit_type = UnrolledCircuitType::Memory(*circuit);
            let canonical = build_unrolled_setup(machine, circuit_type, &binary, &binary, &worker);
            assert_eq!(canonical.trace_len(), circuit_type.get_domain_size());
        }
        for circuit in UnrolledNonMemoryCircuitType::get_circuit_types_for_machine_type(machine) {
            let circuit_type = UnrolledCircuitType::NonMemory(*circuit);
            let canonical = build_unrolled_setup(machine, circuit_type, &binary, &binary, &worker);
            assert_eq!(canonical.trace_len(), circuit_type.get_domain_size());
        }
    }
}

#[test]
fn cpu_unified_setup_matches_the_previous_gpu_table_driver() {
    // Compare the canonical constructor with the former GPU table driver.
    use crate::upstream::{build_unified_table_driver, CpuGKRSetup};

    let worker = Worker::new();
    let binary = test_binary();
    let canonical = build_unified_setup(&binary, &binary, &worker);
    let decoder_table = match eval_fn_of(&canonical) {
        Some(UnrolledCircuitWitnessEvalFn::Unified { decoder_table, .. }) => decoder_table.clone(),
        _ => panic!("expected a Unified evaluator"),
    };

    let previous = CpuGKRSetup::construct(
        &build_unified_table_driver::<crate::upstream::BF>(&binary),
        &decoder_table,
        UnrolledCircuitType::Unified.get_domain_size(),
        canonical.compiled_circuit(),
    );

    let canonical_evals = &canonical.setup().hypercube_evals;
    assert_eq!(
        canonical_evals.len(),
        previous.hypercube_evals.len(),
        "unified setup column count changed"
    );
    for (index, (a, b)) in canonical_evals
        .iter()
        .zip(previous.hypercube_evals.iter())
        .enumerate()
    {
        assert_eq!(&a[..], &b[..], "unified setup column {index} differs");
    }
}
