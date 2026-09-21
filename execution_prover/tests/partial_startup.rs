//! Replay-thread spawn failure after simulation starts. The snapshot free-list
//! sender must close before joining the simulator, whose final drain waits for
//! that closure without consulting cancellation.
//!
//! Separate target because spawn-failure injection is process-global.

use execution_prover::test_support::{
    clear_spawn_injection, fail_replay_spawn_after, FakeBackend, FakeBackendConfiguration,
};
use execution_prover::{ExecutionKind, ExecutionProver, ExecutionProverConfiguration, MachineType};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use std::panic::AssertUnwindSafe;

type Prover = ExecutionProver<FakeBackend>;

/// See `failure_drain.rs`: `memory.x` puts RAM at 4 MiB and `link.x` gives the
/// guest a 64 MiB stack, so the fixture's stack top is around 68 MiB and a
/// smaller holder lets the JIT write past the allocation.
const FIXTURE_RAM: riscv_transpiler::jit::JitRunnerRam =
    riscv_transpiler::jit::JitRunnerRam::Medium;

fn workload() -> (Vec<u32>, Vec<u32>) {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let (_, bin) = setups::read_binary(&root.join("examples/hashed_fibonacci/app.bin"));
    let (_, text) = setups::read_binary(&root.join("examples/hashed_fibonacci/app.text"));
    (bin, text)
}

fn non_determinism() -> QuasiUARTSource {
    QuasiUARTSource::new_with_reads(vec![100, 5])
}

fn prover() -> Prover {
    let mut config = ExecutionProverConfiguration::<FakeBackendConfiguration>::default();
    config.replay_worker_threads_count = 1;
    config.ram_config = FIXTURE_RAM;
    // After the RAM is chosen: the reserve is derived from it.
    config.host_allocators_per_job_count = config.minimum_host_allocators_per_job().unwrap();
    Prover::with_configuration(config).expect("fake backend construction must succeed")
}

fn panic_reason(panic: &(dyn std::any::Any + Send)) -> String {
    panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap_or("")
        .to_string()
}

#[test]
fn a_failed_replay_spawn_neither_hangs_nor_detaches_the_simulator() {
    let mut prover = prover();
    let (bin, text) = workload();
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        bin,
        text,
        Some(1 << 20),
    );
    let before = prover.available_trace_blocks();
    assert!(before > 0, "the pool must start with blocks to account for");

    // The simulator spawns first and is already running; the very next spawn —
    // the first replay thread — reports failure.
    fail_replay_spawn_after(0);
    let started = std::time::Instant::now();
    let panic = std::panic::catch_unwind(AssertUnwindSafe(|| {
        prover.commit_memory(1, &handle, non_determinism());
    }))
    .expect_err("a failed replay spawn must surface, not be swallowed");
    let elapsed = started.elapsed();
    clear_spawn_injection();

    let reason = panic_reason(panic.as_ref());
    assert!(
        reason.contains("failed to start a replay thread"),
        "the spawn failure must be the reported cause; got: {reason}"
    );
    // Without the ordering fix this never returns at all; the bound is loose
    // because it is distinguishing "finished" from "deadlocked", not timing.
    assert!(
        elapsed < std::time::Duration::from_secs(300),
        "partial startup deadlocked, took {elapsed:?}"
    );

    // The simulator was joined, not detached: it returned its memory holder and
    // its whole chunk set to the caches, so the next batch can take them. A
    // detached or still-blocked simulator makes this second batch hang or panic
    // on an empty cache.
    let second = prover.commit_memory(2, &handle, non_determinism());
    drop(second);
    assert_eq!(
        prover.available_trace_blocks(),
        before,
        "the pool did not come back whole after a partial startup"
    );
    assert!(
        !prover.is_terminal(),
        "a producer spawn failure is not a backend failure and must not terminate the instance"
    );
}
