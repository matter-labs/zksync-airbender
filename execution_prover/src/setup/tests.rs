use super::*;
use crate::upstream::UnrolledCircuitWitnessEvalFn;
use execution_prover_model::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
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
fn cpu_delegation_setups_match_the_upstream_constructors() {
    let worker = Worker::new();
    for delegation_type in DelegationCircuitType::get_all_delegation_types()
        .iter()
        .copied()
    {
        let canonical = build_delegation_setup(delegation_type, &worker);

        assert_eq!(
            canonical.trace_len(),
            delegation_type.get_domain_size(),
            "{delegation_type:?} trace_len disagrees with its circuit geometry"
        );
        assert_eq!(
            canonical.compiled_circuit().trace_len,
            delegation_type.get_domain_size(),
            "{delegation_type:?} compiled circuit disagrees with its circuit geometry"
        );
        // Delegation circuits carry no per-family decoder table.
        assert!(canonical.decoder_data().is_none());
    }
}

#[test]
fn cpu_inits_and_teardowns_setup_has_no_decoder_table() {
    let worker = Worker::new();
    let canonical = build_inits_and_teardowns_setup(&worker);

    assert_eq!(
        canonical.trace_len(),
        UnrolledCircuitType::InitsAndTeardowns.get_domain_size()
    );
    // The standalone i&t circuit decodes nothing, so it has neither an
    // evaluator with a decoder table nor dense decoder rows.
    assert!(eval_fn_of(&canonical).is_none());
    assert!(canonical.decoder_data().is_none());
}

#[test]
fn cpu_common_setups_cover_every_binary_independent_circuit() {
    let worker = Worker::new();
    let setups = build_common_setups(&worker);

    let mut expected: Vec<CircuitType> = DelegationCircuitType::get_all_delegation_types()
        .iter()
        .map(|d| CircuitType::Delegation(*d))
        .collect();
    expected.push(CircuitType::Unrolled(
        UnrolledCircuitType::InitsAndTeardowns,
    ));
    expected.sort();

    let mut actual: Vec<CircuitType> = setups.keys().copied().collect();
    actual.sort();

    assert_eq!(actual, expected);
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

    // This is the data the previous GPU-only path discarded at construction.
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

    // The dense rows a backend's decoder table needs are the same table, with
    // absent entries defaulted — one entry per ROM word, not one per present
    // entry.
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
fn cpu_memory_setup_retains_its_evaluator_and_decoder() {
    let worker = Worker::new();
    let binary = test_binary();
    let canonical = build_unrolled_setup(
        MachineType::FullUnsigned,
        UnrolledCircuitType::Memory(UnrolledMemoryCircuitType::LoadStoreWordOnly),
        &binary,
        &binary,
        &worker,
    );

    match eval_fn_of(&canonical) {
        Some(UnrolledCircuitWitnessEvalFn::Memory { decoder_table, .. }) => {
            assert!(!decoder_table.is_empty())
        }
        _ => panic!("expected a Memory evaluator"),
    }
    assert!(canonical.decoder_data().is_some());
}

#[test]
fn cpu_unified_setup_retains_the_unified_evaluator() {
    let worker = Worker::new();
    let binary = test_binary();
    let canonical = build_unified_setup(&binary, &binary, &worker);

    // The previous GPU path produced a stripped tuple here, losing exactly this.
    match eval_fn_of(&canonical) {
        Some(UnrolledCircuitWitnessEvalFn::Unified { decoder_table, .. }) => {
            assert!(!decoder_table.is_empty())
        }
        _ => panic!("expected a Unified evaluator"),
    }
    assert_eq!(
        canonical.trace_len(),
        UnrolledCircuitType::Unified.get_domain_size()
    );
    assert!(canonical.decoder_data().is_some());

    // Structural checks carried over from the GPU-local unified builder this
    // replaces: the unified circuit folds its inits-and-teardowns inline, so it
    // must expose both global outputs and a non-empty teardown-set list.
    use cs::gkr_compiler::OutputType;
    let compiled = canonical.compiled_circuit();
    assert!(compiled
        .global_output_map
        .contains_key(&OutputType::PermutationProduct));
    assert!(compiled
        .global_output_map
        .contains_key(&OutputType::InitsAndTeardownsProduct));
    assert!(!compiled.memory_layout.teardown_sets.is_empty());
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
fn cpu_backend_inputs_preserve_the_decoder_rows() {
    let worker = Worker::new();
    let binary = test_binary();
    let canonical = build_unrolled_setup(
        MachineType::FullUnsigned,
        UnrolledCircuitType::NonMemory(UnrolledNonMemoryCircuitType::ShiftBinary),
        &binary,
        &binary,
        &worker,
    );
    let before = canonical.decoder_data().expect("decoder rows");
    let trace_len = canonical.trace_len();

    let inputs = canonical.into_backend_inputs();

    assert_eq!(inputs.trace_len, trace_len);
    assert_eq!(inputs.compiled_circuit.trace_len, trace_len);
    let after = inputs.decoder_data.expect("decoder rows survive the move");
    assert_eq!(after.len(), before.len());
}

#[test]
fn cpu_unified_setup_matches_the_previous_gpu_table_driver() {
    // The canonical constructor builds its table driver through
    // `unified_reduced_machine::get_table_driver`, while the GPU-only path it
    // replaces used `prover::…::build_unified_table_driver`. Those are two
    // different code paths, and the setup they produce is what every unified
    // proof binds, so the equivalence is asserted rather than assumed.
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
