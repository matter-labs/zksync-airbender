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
    let handle = prover.add_binary_variants(
        program.clone(),
        program,
        &[(
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            &[crate::ProofProfile::Standard],
        )],
        Some(cycles),
    )[0];
    prover.finalize_setup();
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
    let handle = prover.add_binary_variants(
        program.clone(),
        program,
        &[(execution_kind, MachineType::Reduced, profiles)],
        Some(32),
    )[0];
    (prover, handle)
}

#[test]
fn unsupported_registration_profiles_are_rejected() {
    use crate::ProofProfile::{Compression, CompressionFinal, L1Wrap, Standard};
    for (kind, profiles) in [
        (ExecutionKind::Unified22, vec![CompressionFinal, Standard]),
        (ExecutionKind::Unified, vec![Standard, CompressionFinal]),
        (
            ExecutionKind::Unified22,
            vec![CompressionFinal, Compression],
        ),
        (ExecutionKind::L1Wrap, vec![Standard]),
        (ExecutionKind::Unified, vec![L1Wrap]),
        (ExecutionKind::Unrolled, vec![CompressionFinal]),
        (ExecutionKind::Unrolled, vec![Compression]),
    ] {
        assert!(
            std::panic::catch_unwind(|| unified_prover(kind, &profiles)).is_err(),
            "{kind:?} {profiles:?}"
        );
    }
}

#[test]
#[should_panic(expected = "ProofProfile::CompressionFinal was not declared for this binary")]
fn undeclared_profile_is_rejected() {
    let (mut prover, handle) =
        unified_prover(ExecutionKind::Unified, &[crate::ProofProfile::Standard]);
    prover.finalize_setup();
    prover.commit_memory(
        1,
        &handle,
        QuasiUARTSource::new_with_reads(vec![]),
        crate::ProofProfile::CompressionFinal,
    );
}

/// A regular-ROM-padded image cannot be registered for the 512 KiB wrap ROM.
#[test]
#[should_panic(expected = "bytecode exceeds selected ROM")]
fn wrap_image_over_512kib_is_rejected() {
    ExecutionProver::<TestBackend>::new().add_binary_variants(
        vec![0; 1 << 20],
        vec![0; 1 << 20],
        &[(
            ExecutionKind::L1Wrap,
            MachineType::Reduced,
            &[crate::ProofProfile::L1Wrap],
        )],
        Some(32),
    );
}
