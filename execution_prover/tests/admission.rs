//! Execution admission: the pool is sized for `J` concurrent executions, so at
//! most `J` may draw on it at once.
//!
//! These drive the real orchestrator. The interesting case is not the happy
//! path but the one where a caller waits: waiting is unbounded, and the
//! execution it waits behind may be the one that kills the backend.

use execution_prover::test_support::{result_gate, FakeBackend, FakeBackendConfiguration};
use execution_prover::{ExecutionKind, ExecutionProver, ExecutionProverConfiguration, MachineType};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use std::panic::AssertUnwindSafe;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};
use std::time::{Duration, Instant};

type Prover = ExecutionProver<FakeBackend>;

/// See `failure_drain.rs`: the fixture's guest stack top is around 68 MiB.
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

fn configuration(jobs: usize) -> ExecutionProverConfiguration<FakeBackendConfiguration> {
    let mut config = ExecutionProverConfiguration::<FakeBackendConfiguration>::default();
    config.expected_concurrent_jobs = jobs;
    config.replay_worker_threads_count = 1;
    config.ram_config = FIXTURE_RAM;
    // AFTER the RAM is chosen, never before: the producer reserve is computed
    // from it, so a pool sized against the default RAM is rejected the moment
    // the RAM changes.
    config.host_allocators_per_job_count = config.minimum_host_allocators_per_job().unwrap();
    config
}

/// Spin until `condition` holds, failing loudly rather than hanging.
///
/// Not a sleep standing in for synchronization: the condition is an observable
/// state transition, and the deadline exists so a regression reports a failure
/// instead of wedging the suite.
fn await_condition(what: &str, mut condition: impl FnMut() -> bool) {
    let deadline = Instant::now() + Duration::from_secs(120);
    while !condition() {
        assert!(Instant::now() < deadline, "timed out waiting for {what}");
        std::thread::yield_now();
    }
}

/// Serializes the whole target.
///
/// `result_gate` and the admission counters are process-global, so two tests
/// running concurrently would clear or open each other's gate — and setup
/// requests are gated too, so a stray `open()` can let another test's
/// construction race ahead. Passing `--test-threads=1` at the call site is not
/// enough: a runner that forgets the flag would produce confusing, intermittent
/// failures rather than a clear one.
///
/// Poisoning is ignored deliberately: one failing test should not cascade into
/// every later one reporting a poisoned mutex instead of its own result.
static SERIAL: Mutex<()> = Mutex::new(());

fn serial() -> MutexGuard<'static, ()> {
    SERIAL.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Joins every spawned execution, including when an assertion has already
/// failed.
///
/// A bare `join()` after the assertions detaches them on the failure path,
/// leaving threads running against a prover the test is dropping.
///
/// DECLARATION ORDER MATTERS: declare this BEFORE the `GateGuard`, so the gate
/// is released first and the threads it was holding can actually finish. The
/// other order joins threads that are still blocked waiting for a permit.
#[derive(Default)]
struct Joiner(Vec<std::thread::JoinHandle<()>>);

impl Joiner {
    fn push(&mut self, handle: std::thread::JoinHandle<()>) {
        self.0.push(handle);
    }
}

impl Drop for Joiner {
    fn drop(&mut self) {
        for handle in std::mem::take(&mut self.0) {
            let _ = handle.join();
        }
    }
}

/// Restores the completion gate however a test ends, including on a panic.
/// A gate left armed would hang every later test in this process.
struct GateGuard;

impl Drop for GateGuard {
    fn drop(&mut self) {
        result_gate::clear();
    }
}

fn panic_reason(panic: &(dyn std::any::Any + Send)) -> String {
    panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap_or("")
        .to_string()
}

/// The declared limit is real: a second execution does not start until the
/// first has finished.
#[test]
fn concurrent_executions_are_held_to_the_declared_limit() {
    let _serial = serial();
    let mut joiner = Joiner::default();
    let mut prover = Prover::with_configuration(configuration(1)).unwrap();
    assert_eq!(
        prover.available_execution_slots(),
        Some(1),
        "the fake backend declares a limit, so a semaphore must exist"
    );

    let (bin, text) = workload();
    // Registered before sharing: `add_binary` needs `&mut self`, while the
    // executions below only need `&self`.
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        bin,
        text,
        Some(1 << 20),
    );
    let prover = Arc::new(prover);

    let _guard = GateGuard;
    result_gate::arm();
    {
        let prover = prover.clone();
        joiner.push(std::thread::spawn(move || {
            let _ = prover.commit_memory(1, &handle, non_determinism());
        }));
    }
    // The gate holds the first execution in flight: with completions withheld
    // it cannot finish, so it cannot release its slot. That is what makes the
    // observation below a fact rather than a race — the waiter is inside
    // `acquire` and STAYS there until this test says otherwise.
    await_condition("the first execution to take the slot", || {
        prover.available_execution_slots() == Some(0)
    });
    await_condition("the first execution to start simulating", || {
        prover.simulations_started() >= 1
    });

    {
        let prover = prover.clone();
        joiner.push(std::thread::spawn(move || {
            let _ = prover.commit_memory(2, &handle, non_determinism());
        }));
    }

    // Observed INSIDE the blocking wait, not merely started.
    await_condition("the second execution to block on admission", || {
        prover.execution_slot_wait_entries() >= 1
    });
    assert_eq!(
        prover.simulations_started(),
        1,
        "a blocked execution must not have spawned producers or taken buffers"
    );
    assert_eq!(
        prover.execution_slot_acquisitions(),
        1,
        "the waiter must not have been admitted while the first still holds"
    );

    // Only now let the first finish and free the slot.
    result_gate::open();
    drop(joiner);
    assert_eq!(
        prover.simulations_started(),
        2,
        "the waiter must run once the slot frees, not be dropped"
    );
    assert_eq!(
        prover.available_execution_slots(),
        Some(1),
        "every execution must return its slot"
    );
}

/// A caller that waited for a slot is rejected if the backend died while it
/// waited — before it allocates buffers or spawns producers.
///
/// This is the case a single pre-wait check misses. The first execution holds
/// the slot, fails, marks the instance terminal and only then releases; the
/// waiter's pre-wait check happened long before any of that, so without a
/// recheck after acquisition it would go on to build a whole execution against
/// a backend that can never serve it.
#[test]
fn a_waiting_execution_rechecks_terminal_state_after_acquiring_its_slot() {
    let _serial = serial();
    let mut config = configuration(1);
    config.backend.fail_after_requests = Some(0);
    let mut prover = Prover::with_configuration(config).unwrap();

    let (bin, text) = workload();
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        bin,
        text,
        Some(1 << 20),
    );
    let prover = Arc::new(prover);

    // The gate covers the injected failure too, so the failing execution is
    // held right before it reports — slot still taken, instance not yet
    // terminal. Without that hold, it could fail and release before the waiter
    // ever blocks, and the test would silently stop testing the recheck.
    let mut joiner = Joiner::default();
    let _guard = GateGuard;
    result_gate::arm();
    {
        let prover = prover.clone();
        joiner.push(std::thread::spawn(move || {
            let _ = std::panic::catch_unwind(AssertUnwindSafe(|| {
                prover.commit_memory(1, &handle, non_determinism());
            }));
        }));
    }
    await_condition("the failing execution to take the slot", || {
        prover.available_execution_slots() == Some(0)
    });
    await_condition("the failing execution to start simulating", || {
        prover.simulations_started() >= 1
    });
    let simulations_before_waiter = prover.simulations_started();

    let waiter = {
        let prover = prover.clone();
        std::thread::spawn(move || {
            let started = Instant::now();
            let panic = std::panic::catch_unwind(AssertUnwindSafe(|| {
                prover.commit_memory(2, &handle, non_determinism());
            }))
            .expect_err("a waiter must not be admitted to a terminal instance");
            (panic_reason(panic.as_ref()), started.elapsed())
        })
    };

    // The waiter is blocked and the failing execution is still held. Releasing
    // now is what orders "instance becomes terminal" strictly before "waiter
    // acquires", which is the sequence under test.
    await_condition("the waiter to block on admission", || {
        prover.execution_slot_wait_entries() >= 1
    });
    assert!(
        !prover.is_terminal(),
        "the failing execution must still be in flight, so the waiter cannot \
         have been rejected by a pre-wait check"
    );
    result_gate::open();

    drop(joiner);
    let (reason, waited) = waiter.join().expect("the waiter thread must not be lost");

    assert!(
        prover.is_terminal(),
        "the first execution's failure must have terminated the instance"
    );
    assert!(
        reason.contains("unusable after a backend failure"),
        "the waiter must be rejected for the terminal state; got: {reason}"
    );
    assert!(
        reason.contains("fake backend failed"),
        "the rejection must carry the ORIGINAL failure reason; got: {reason}"
    );
    assert!(
        waited < Duration::from_secs(300),
        "the waiter must be released when the slot frees, not hang; took {waited:?}"
    );
    assert_eq!(
        prover.available_execution_slots(),
        Some(1),
        "a rejected waiter must still return the slot it acquired"
    );
    assert!(
        prover.execution_slot_wait_entries() >= 1,
        "the waiter must have actually blocked; otherwise this test proves \
         nothing about rechecking AFTER acquisition"
    );
    assert_eq!(
        prover.simulations_started(),
        simulations_before_waiter,
        "a waiter rejected on the terminal recheck must not have spawned \
         producers or taken buffers"
    );
}

/// The combined pass holds ONE slot, not one per phase.
///
/// Its cache carries trace blocks from the commit pass into the prove pass, so
/// it draws on the pool continuously; a second acquisition would admit more
/// executions than the pool is sized for.
#[test]
fn the_combined_pass_holds_a_single_slot() {
    let _serial = serial();
    let _guard = GateGuard;
    result_gate::clear();
    let mut prover = Prover::with_configuration(configuration(2)).unwrap();
    let (bin, text) = workload();
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        bin,
        text,
        Some(1 << 20),
    );
    assert_eq!(prover.available_execution_slots(), Some(2));

    // The fake backend serves no proofs, so the prove pass is expected to fail;
    // what matters is how many slots were taken on the way.
    let _ = std::panic::catch_unwind(AssertUnwindSafe(|| {
        prover.commit_memory_and_prove(1, &handle, non_determinism())
    }));

    // The cumulative count, not the final free count: a pass that acquired,
    // released and acquired again would leave two slots free at the end and
    // look identical. Only this distinguishes one permit across both phases
    // from one per phase.
    assert_eq!(
        prover.execution_slot_acquisitions(),
        1,
        "the combined pass must take ONE slot across both phases"
    );
    assert_eq!(
        prover.available_execution_slots(),
        Some(2),
        "and must return it"
    );
}
