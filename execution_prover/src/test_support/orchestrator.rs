use super::*;
use crate::{CommitmentMode, ExecutionKind, ExecutionProver, MachineType};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;

/// Three batches on a prover sized for one: the extra callers wait for a
/// cached memory holder and trace chunk set.
#[test]
fn concurrent_batches_wait_for_cached_resources() {
    REQUESTS.store(0, Ordering::SeqCst);
    // One memory access every two cycles fills two JIT trace chunks.
    let program = vec![0x0001_2083, 0xffdf_f06f]; // lw x1, 0(x2); jal x0, -4
    let cycles = 4 * riscv_transpiler::jit::TRACE_CHUNK_LEN as u32;
    let mut prover = ExecutionProver::<TestBackend>::new();
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        program.clone(),
        program,
        Some(cycles),
        &[crate::ProofProfile::Standard],
    );
    let expected_final_timestamp =
        common_constants::INITIAL_TIMESTAMP + u64::from(cycles) * common_constants::TIMESTAMP_STEP;
    std::thread::scope(|scope| {
        for batch_id in 1..=3 {
            let prover = &prover;
            let handle = &handle;
            scope.spawn(move || {
                let commitment = prover.commit_memory(
                    batch_id,
                    handle,
                    QuasiUARTSource::new_with_reads(vec![]),
                    CommitmentMode::SeparateMemoryAndWitness,
                    crate::ProofProfile::Standard,
                );
                assert_eq!(commitment.final_timestamp, expected_final_timestamp);
            });
        }
    });
    assert!(REQUESTS.load(Ordering::SeqCst) > 0);
}

fn unified_prover(
    profiles: &[crate::ProofProfile],
) -> (ExecutionProver<TestBackend>, crate::BinaryHandle) {
    let mut prover = ExecutionProver::<TestBackend>::new();
    let program = vec![0x0001_2083, 0xffdf_f06f];
    let handle = prover.add_binary(
        ExecutionKind::Unified,
        MachineType::Reduced,
        program.clone(),
        program,
        Some(32),
        profiles,
    );
    (prover, handle)
}

#[test]
fn commit_then_prove_carries_the_ticket_profile() {
    use crate::ProofProfile::{L1Feeder, Standard};
    use execution_prover_model::circuit_type::UnrolledCircuitType;
    const BATCH: u64 = 8009;
    let (prover, handle) = unified_prover(&[L1Feeder, Standard, L1Feeder]);
    let reads = || QuasiUARTSource::new_with_reads(vec![]);
    let ticket = prover.commit_memory(
        BATCH,
        &handle,
        reads(),
        CommitmentMode::MergedMemoryAndWitness,
        L1Feeder,
    );
    assert_eq!(ticket.profile, L1Feeder);
    let result = prover.prove(BATCH, ticket, reads());
    assert!(result
        .circuit_families_proofs
        .values()
        .any(|proofs| !proofs.is_empty()));
    let recorded = PROFILES.lock().unwrap();
    let requests: Vec<_> = recorded
        .iter()
        .filter(|(batch, ..)| *batch == BATCH)
        .collect();
    let unified = CircuitType::Unrolled(UnrolledCircuitType::Unified);
    for proving in [false, true] {
        assert!(requests
            .iter()
            .any(|(_, circuit, is_proof, _)| *circuit == unified && *is_proof == proving));
    }
    for (_, circuit, _, profile) in requests {
        assert_eq!(
            *profile,
            if *circuit == unified {
                L1Feeder
            } else {
                Standard
            }
        );
    }
}

#[test]
#[should_panic(expected = "ProofProfile::L1Feeder requires CommitmentMode::MergedMemoryAndWitness")]
fn l1_feeder_with_separate_mode_is_rejected() {
    let (prover, handle) = unified_prover(&[crate::ProofProfile::L1Feeder]);
    prover.commit_memory(
        1,
        &handle,
        QuasiUARTSource::new_with_reads(vec![]),
        CommitmentMode::SeparateMemoryAndWitness,
        crate::ProofProfile::L1Feeder,
    );
}

#[test]
#[should_panic(expected = "ProofProfile::L1Feeder was not declared for this binary")]
fn undeclared_profile_is_rejected() {
    let (prover, handle) = unified_prover(&[crate::ProofProfile::Standard]);
    prover.commit_memory(
        1,
        &handle,
        QuasiUARTSource::new_with_reads(vec![]),
        CommitmentMode::MergedMemoryAndWitness,
        crate::ProofProfile::L1Feeder,
    );
}
