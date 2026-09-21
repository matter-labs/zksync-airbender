use super::*;
use crate::{ExecutionKind, ExecutionProver, MachineType};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use std::panic::AssertUnwindSafe;

// Both tests inspect the allocator's process-wide counters.
static SERIAL: Mutex<()> = Mutex::new(());

#[test]
fn multiple_snapshots_complete_on_the_minimum_pool_and_return_every_block() {
    let _serial = SERIAL.lock().unwrap();
    REQUESTS.store(0, Ordering::SeqCst);
    // The fixture's stack top is about 68 MiB, within the default Medium RAM.
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let (_, bin) = setups::read_binary(&root.join("examples/hashed_fibonacci/app.bin"));
    let (_, text) = setups::read_binary(&root.join("examples/hashed_fibonacci/app.text"));
    let mut prover = ExecutionProver::<TestBackend>::new();
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        bin,
        text,
        Some(4 << 20),
    );
    let commitment = prover.commit_memory(
        1,
        &handle,
        QuasiUARTSource::new_with_reads(vec![100, 30_000]),
    );
    assert!(
        commitment.final_timestamp
            > 2 * u64::from(riscv_transpiler::jit::DEFAULT_MAX_CYCLES_PER_SNAPSHOT)
                * common_constants::TIMESTAMP_STEP
    );
    assert!(REQUESTS.load(Ordering::SeqCst) > 0);
    assert_eq!(LIVE_BLOCKS.load(Ordering::SeqCst), 0);
}

#[test]
fn backend_failure_stops_an_endless_guest_and_rejects_later_use() {
    let _serial = SERIAL.lock().unwrap();
    let mut config = ExecutionProverConfiguration::<TestConfiguration>::default();
    config.backend.fail_after_requests = Some(1);
    let mut prover = ExecutionProver::<TestBackend>::with_configuration(config).unwrap();
    // lw x1, 0(x2); jal x0, -4. With no cycle bound, only cancellation can stop it.
    let program = vec![0x0001_2083, 0xffdf_f06f];
    let handle = prover.add_binary(
        ExecutionKind::Unified,
        MachineType::Reduced,
        program.clone(),
        program,
        None,
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
