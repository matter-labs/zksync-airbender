use super::*;
use crate::{ExecutionKind, ExecutionProver, MachineType};
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

/// Standard and A share a 2^23 handle; C uses its own 2^22 circuit.
#[test]
fn unified_profiles_reach_commitment_and_proof_requests() {
    use crate::ProofProfile::{L1Feeder, L1FeederA, Standard};
    use execution_prover_model::circuit_type::UnrolledCircuitType;
    let (mut prover, handle) = unified_prover(ExecutionKind::Unified, &[L1FeederA, Standard]);
    let program = vec![0x0001_2083, 0xffdf_f06f];
    let feeder = prover.add_binary(
        ExecutionKind::Unified22,
        MachineType::Reduced,
        program.clone(),
        program,
        Some(32),
        &[L1Feeder],
    );
    for (batch, handle, profile, circuit) in [
        (8012, handle, Standard, UnrolledCircuitType::Unified),
        (8013, handle, L1FeederA, UnrolledCircuitType::Unified),
        (8014, feeder, L1Feeder, UnrolledCircuitType::Unified22),
    ] {
        let reads = || QuasiUARTSource::new_with_reads(vec![]);
        let ticket = prover.commit_memory(batch, &handle, reads(), profile);
        assert_eq!(ticket.profile, profile);
        prover.prove(batch, ticket, reads());
        let recorded = PROFILES.lock().unwrap();
        for proving in [false, true] {
            assert!(recorded.iter().any(|&(b, c, p, f)| b == batch
                && c == CircuitType::Unrolled(circuit)
                && p == proving
                && f == profile));
        }
        assert!(recorded
            .iter()
            .filter(|&&(b, ..)| b == batch)
            .all(|&(_, c, _, f)| match c {
                c if c == CircuitType::Unrolled(circuit) => f == profile,
                CircuitType::Delegation(_) => f == Standard,
                _ => false,
            }));
    }
}

#[test]
fn unsupported_registration_profiles_are_rejected() {
    use crate::ProofProfile::{L1Feeder, L1FeederA, L1Wrap, Standard};
    for (kind, profiles) in [
        (ExecutionKind::Unified22, vec![L1Feeder, Standard]),
        (ExecutionKind::Unified, vec![Standard, L1Feeder]),
        (ExecutionKind::Unified22, vec![L1Feeder, L1FeederA]),
        (ExecutionKind::L1Wrap21, vec![Standard]),
        (ExecutionKind::Unified, vec![L1Wrap]),
        (ExecutionKind::Unrolled, vec![L1Feeder]),
        (ExecutionKind::Unrolled, vec![L1FeederA]),
    ] {
        assert!(
            std::panic::catch_unwind(|| unified_prover(kind, &profiles)).is_err(),
            "{kind:?} {profiles:?}"
        );
    }
}

#[test]
#[should_panic(expected = "ProofProfile::L1Feeder was not declared for this binary")]
fn undeclared_profile_is_rejected() {
    let (prover, handle) = unified_prover(ExecutionKind::Unified, &[crate::ProofProfile::Standard]);
    prover.commit_memory(
        1,
        &handle,
        QuasiUARTSource::new_with_reads(vec![]),
        crate::ProofProfile::L1Feeder,
    );
}

/// A regular-ROM-padded image cannot be registered for the 512 KiB wrap ROM.
#[test]
#[should_panic(expected = "bytecode exceeds selected ROM")]
fn wrap_image_over_512kib_is_rejected() {
    ExecutionProver::<TestBackend>::new().add_binary(
        ExecutionKind::L1Wrap21,
        MachineType::Reduced,
        vec![0; 1 << 20],
        vec![0; 1 << 20],
        Some(32),
        &[crate::ProofProfile::L1Wrap],
    );
}
