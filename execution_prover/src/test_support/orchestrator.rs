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
    execution_kind: ExecutionKind,
    profiles: &[crate::ProofProfile],
) -> (ExecutionProver<TestBackend>, crate::BinaryHandle) {
    let mut prover = ExecutionProver::<TestBackend>::new();
    let program = vec![0x0001_2083, 0xffdf_f06f];
    let handle = prover.add_binary(
        execution_kind,
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
    let (prover, handle) = unified_prover(ExecutionKind::Unified22, &[L1Feeder, L1Feeder]);
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
    let unified = CircuitType::Unrolled(UnrolledCircuitType::Unified22);
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

/// The same program registered as the 2^23 final layer and as the 2^22
/// feeder: two handles, two circuits, no shared precomputations.
#[test]
fn unified22_registration_is_distinct() {
    use crate::ProofProfile::{L1Feeder, Standard};
    use execution_prover_model::circuit_type::UnrolledCircuitType;
    const STANDARD_BATCH: u64 = 8010;
    const FEEDER_BATCH: u64 = 8011;
    let mut prover = ExecutionProver::<TestBackend>::new();
    let program = vec![0x0001_2083, 0xffdf_f06f];
    let standard = prover.add_binary(
        ExecutionKind::Unified,
        MachineType::Reduced,
        program.clone(),
        program.clone(),
        Some(32),
        &[Standard],
    );
    let feeder = prover.add_binary(
        ExecutionKind::Unified22,
        MachineType::Reduced,
        program.clone(),
        program,
        Some(32),
        &[L1Feeder],
    );
    assert_ne!(standard, feeder);
    let reads = || QuasiUARTSource::new_with_reads(vec![]);
    for (batch, handle, mode, profile) in [
        (
            STANDARD_BATCH,
            &standard,
            CommitmentMode::SeparateMemoryAndWitness,
            Standard,
        ),
        (
            FEEDER_BATCH,
            &feeder,
            CommitmentMode::MergedMemoryAndWitness,
            L1Feeder,
        ),
    ] {
        let ticket = prover.commit_memory(batch, handle, reads(), mode, profile);
        assert_eq!(ticket.profile, profile);
        let result = prover.prove(batch, ticket, reads());
        assert!(result
            .circuit_families_proofs
            .values()
            .any(|proofs| !proofs.is_empty()));
    }
    let recorded = PROFILES.lock().unwrap();
    for (batch, circuit_type, profile) in [
        (
            STANDARD_BATCH,
            CircuitType::Unrolled(UnrolledCircuitType::Unified),
            Standard,
        ),
        (
            FEEDER_BATCH,
            CircuitType::Unrolled(UnrolledCircuitType::Unified22),
            L1Feeder,
        ),
    ] {
        let requests: Vec<_> = recorded
            .iter()
            .filter(|(request_batch, ..)| *request_batch == batch)
            .collect();
        for proving in [false, true] {
            assert!(requests
                .iter()
                .any(|(_, circuit, is_proof, _)| *circuit == circuit_type && *is_proof == proving));
        }
        for (_, circuit, _, request_profile) in requests {
            if *circuit == circuit_type {
                assert_eq!(*request_profile, profile);
            } else {
                assert!(matches!(circuit, CircuitType::Delegation(_)), "{circuit:?}");
            }
        }
    }
}

#[test]
#[should_panic(expected = "ExecutionKind::Unified22 requires exactly ProofProfile::L1Feeder")]
fn unified22_invalid_profile_is_rejected() {
    unified_prover(
        ExecutionKind::Unified22,
        &[crate::ProofProfile::L1Feeder, crate::ProofProfile::Standard],
    );
}

#[test]
#[should_panic(expected = "ProofProfile::L1Feeder requires ExecutionKind::Unified22")]
fn unified_rejects_the_l1_feeder_profile() {
    unified_prover(
        ExecutionKind::Unified,
        &[crate::ProofProfile::Standard, crate::ProofProfile::L1Feeder],
    );
}

#[test]
#[should_panic(expected = "ProofProfile::L1Feeder requires CommitmentMode::MergedMemoryAndWitness")]
fn l1_feeder_with_separate_mode_is_rejected() {
    let (prover, handle) =
        unified_prover(ExecutionKind::Unified22, &[crate::ProofProfile::L1Feeder]);
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
    let (prover, handle) = unified_prover(ExecutionKind::Unified, &[crate::ProofProfile::Standard]);
    prover.commit_memory(
        1,
        &handle,
        QuasiUARTSource::new_with_reads(vec![]),
        CommitmentMode::MergedMemoryAndWitness,
        crate::ProofProfile::L1Feeder,
    );
}

/// The same program registered as the 2^22 and the 2^21 L1 wrap: two handles,
/// two setups, each proof request carrying its own circuit and packing.
#[test]
fn l1_wrap21_registration_is_distinct() {
    const WRAP22_BATCH: u64 = 8020;
    const WRAP21_BATCH: u64 = 8021;
    let mut prover = ExecutionProver::<TestBackend>::new();
    let program = vec![0x0001_2083, 0xffdf_f06f];
    let handles = [ExecutionKind::L1Wrap, ExecutionKind::L1Wrap21].map(|kind| {
        prover.add_binary(
            kind,
            MachineType::Reduced,
            program.clone(),
            program.clone(),
            Some(32),
            &[crate::ProofProfile::L1Wrap],
        )
    });
    assert_ne!(handles[0], handles[1]);
    for (batch, handle, circuit_type) in [
        (WRAP22_BATCH, &handles[0], CircuitType::L1Wrap),
        (WRAP21_BATCH, &handles[1], CircuitType::L1Wrap21),
    ] {
        let result = prover.prove_l1_wrap(batch, handle, QuasiUARTSource::new_with_reads(vec![]));
        let CommitmentMode::MergedAndPackedMemoryAndWitness {
            pack_log2,
            external_challenges_pow_bits,
            ..
        } = result.commitment_mode
        else {
            panic!("wrong mode")
        };
        assert_eq!(
            (pack_log2, external_challenges_pow_bits),
            crate::l1_wrap_packing(circuit_type)
        );
        let recorded = PROFILES.lock().unwrap();
        let requests: Vec<_> = recorded
            .iter()
            .filter(|(request_batch, ..)| *request_batch == batch)
            .collect();
        assert_eq!(requests.len(), 1);
        assert_eq!(requests[0].1, circuit_type);
    }
}

#[test]
#[should_panic(expected = "ExecutionKind::L1Wrap21 requires exactly ProofProfile::L1Wrap")]
fn l1_wrap21_rejects_mismatched_profile() {
    let program = vec![0x0001_2083, 0xffdf_f06f];
    ExecutionProver::<TestBackend>::new().add_binary(
        ExecutionKind::L1Wrap21,
        MachineType::Reduced,
        program.clone(),
        program,
        Some(32),
        &[crate::ProofProfile::Standard],
    );
}

#[test]
#[should_panic(
    expected = "ProofProfile::L1Wrap requires ExecutionKind::L1Wrap or ExecutionKind::L1Wrap21"
)]
fn l1_wrap_profile_requires_a_wrap_kind() {
    unified_prover(ExecutionKind::Unified, &[crate::ProofProfile::L1Wrap]);
}

/// The 2^21 wrap's ROM holds 2^17 words: a larger image, including one
/// already padded to the regular 4 MiB ROM, is rejected at registration.
#[test]
fn wrap_image_over_512kib_is_rejected() {
    for words in [(1 << 17) + 1, 1 << 20] {
        let mut image = vec![0u32; words];
        image[..2].copy_from_slice(&[0x0001_2083, 0xffdf_f06f]);
        let panic = std::panic::catch_unwind(|| {
            ExecutionProver::<TestBackend>::new().add_binary(
                ExecutionKind::L1Wrap21,
                MachineType::Reduced,
                image.clone(),
                image.clone(),
                Some(32),
                &[crate::ProofProfile::L1Wrap],
            )
        })
        .err()
        .unwrap_or_else(|| panic!("a {words}-word image was accepted"));
        assert_eq!(
            panic.downcast_ref::<&str>(),
            Some(&"bytecode exceeds selected ROM"),
            "{words} words"
        );
    }
}
