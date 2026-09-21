use super::*;
use crate::{ExecutionKind, ExecutionProver, MachineType};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use std::panic::AssertUnwindSafe;

// Both tests inspect the allocator's process-wide counters.
static SERIAL: Mutex<()> = Mutex::new(());

#[test]
fn multiple_snapshots_complete_and_return_every_block() {
    let _serial = SERIAL.lock().unwrap();
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
    );
    let commitment = prover.commit_memory(1, &handle, QuasiUARTSource::new_with_reads(vec![]));
    assert_eq!(
        commitment.final_timestamp,
        common_constants::INITIAL_TIMESTAMP + u64::from(cycles) * common_constants::TIMESTAMP_STEP
    );
    assert!(REQUESTS.load(Ordering::SeqCst) > 0);
    assert_eq!(LIVE_BLOCKS.load(Ordering::SeqCst), 0);
}

#[test]
fn backend_failure_drains_a_bounded_guest_and_rejects_later_use() {
    let _serial = SERIAL.lock().unwrap();
    let mut config = ExecutionProverConfiguration::<TestConfiguration>::default();
    config.backend.fail_after_requests = Some(1);
    let mut prover = ExecutionProver::<TestBackend>::with_configuration(config).unwrap();
    // Cancellation stops producing snapshots; the guest finishes at its cycle bound.
    let program = vec![0x0001_2083, 0xffdf_f06f];
    let handle = prover.add_binary(
        ExecutionKind::Unified,
        MachineType::Reduced,
        program.clone(),
        program,
        Some(32 << 20),
    );
    let panic = std::panic::catch_unwind(AssertUnwindSafe(|| {
        prover.commit_memory(1, &handle, QuasiUARTSource::new_with_reads(vec![]));
    }))
    .expect_err("backend failure must terminate the batch");
    assert!(panic_text(&panic).contains("test backend failed"));

    // Repeated rejection must preserve the cause without poisoning the saved-error lock.
    for batch_id in 2..4 {
        let panic = std::panic::catch_unwind(AssertUnwindSafe(|| {
            prover.commit_memory(batch_id, &handle, QuasiUARTSource::new_with_reads(vec![]));
        }))
        .expect_err("terminal prover must refuse further work");
        let reason = panic_text(&panic);
        assert!(reason.contains("unusable after a backend failure"));
        assert!(reason.contains("test backend failed"));
    }
    drop(prover);
    assert_eq!(LIVE_BLOCKS.load(Ordering::SeqCst), 0);
}

fn panic_text(panic: &Box<dyn std::any::Any + Send>) -> &str {
    panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .expect("unexpected panic payload")
}
