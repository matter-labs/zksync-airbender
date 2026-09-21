//! Backend-failure drain and shutdown, driven through the real collector.
//!
//! These run the actual orchestrator — real simulation, real replay, the real
//! collector loop — against a backend that fails mid-batch. Inspecting the
//! failure branch by eye is not enough: the defects these cover were all cases
//! where the branch looked right but some other path ran first.

use execution_prover::test_support::{FakeBackend, FakeBackendConfiguration};
use execution_prover::{ExecutionKind, ExecutionProver, ExecutionProverConfiguration, MachineType};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use std::panic::AssertUnwindSafe;

type Prover = ExecutionProver<FakeBackend>;

/// Guest RAM for the `hashed_fibonacci` fixture.
///
/// Not a tuning choice. `examples/scripts/lds/memory.x` puts RAM at origin 4 MiB
/// with length 1022 MiB, and `link.x` sets `_hart_stack_size = 64M` with the
/// stack at the base of RAM — so the guest's stack top is around 68 MiB. A
/// smaller holder lets the JIT write past the end of the allocation into
/// neighbouring heap, which shows up as an intermittent SIGSEGV rather than a
/// clean failure: a run that happens to pass under an undersized holder has
/// corrupted something, not proved anything.
const FIXTURE_RAM: riscv_transpiler::jit::JitRunnerRam =
    riscv_transpiler::jit::JitRunnerRam::Medium;

fn workload() -> (Vec<u32>, Vec<u32>) {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    // `read_binary` returns `(raw_bytes, words)`; only the words are wanted.
    let (_, bin) = setups::read_binary(&root.join("examples/hashed_fibonacci/app.bin"));
    let (_, text) = setups::read_binary(&root.join("examples/hashed_fibonacci/app.text"));
    (bin, text)
}

/// Non-determinism for `hashed_fibonacci`: `n` register-only iterations then
/// `h` blake hashes. Starving the source panics inside the JIT trace callback,
/// which aborts the process under its non-unwinding ABI instead of failing.
fn non_determinism() -> QuasiUARTSource {
    QuasiUARTSource::new_with_reads(vec![100, 5])
}

/// Size the block pool from the RAM setting, which must already be chosen.
///
/// The producer reserve is derived from the RAM, so the default pool — sized
/// for the default RAM — is rejected as soon as a test picks a different one.
fn size_pool_for_ram(config: &mut ExecutionProverConfiguration<FakeBackendConfiguration>) {
    config.host_allocators_per_job_count = config.minimum_host_allocators_per_job().unwrap();
}

fn prover_succeeding() -> Prover {
    let mut config = ExecutionProverConfiguration::<FakeBackendConfiguration> {
        replay_worker_threads_count: 1,
        ram_config: FIXTURE_RAM,
        ..Default::default()
    };
    size_pool_for_ram(&mut config);
    Prover::with_configuration(config).expect("fake backend construction must succeed")
}

fn prover_failing_after(requests: usize) -> Prover {
    let mut config = ExecutionProverConfiguration::<FakeBackendConfiguration>::default();
    config.backend.fail_after_requests = Some(requests);
    // One replayer: the point is to observe credits. The pool stays at the
    // default, which is now the derived minimum — shrinking it below that is
    // rejected, and a leak still shows because the assertions compare the
    // count before and after rather than against a small absolute number.
    config.replay_worker_threads_count = 1;
    config.ram_config = FIXTURE_RAM;
    size_pool_for_ram(&mut config);
    Prover::with_configuration(config).expect("fake backend construction must succeed")
}

/// A failing backend surfaces promptly with the ORIGINAL error, and does not
/// hang.
///
/// Covers the ordering defects found by review: late producer events arriving
/// after the failure must be released rather than dispatched through a closed
/// sender, the abandoned in-flight requests must not trip the pending-count
/// assertion in place of the real error, and parked/cached owners must be
/// released before the failure is raised so the unwind cannot skip it.
///
/// Note what is deliberately NOT asserted: that the pool is made whole. A
/// backend that abandons consumed requests takes their input owners with it,
/// and the failure event carries none, so full credit recovery is not
/// achievable — nor needed, since the instance is terminal.
#[test]
fn failed_batch_reports_the_original_error_without_hanging() {
    let mut prover = prover_failing_after(0);
    let (bin, text) = workload();
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        bin,
        text,
        Some(1 << 20),
    );

    let started = std::time::Instant::now();
    let panic = std::panic::catch_unwind(AssertUnwindSafe(|| {
        prover.commit_memory(1, &handle, non_determinism());
    }))
    .expect_err("a failing backend must surface as an error, not a silent result");

    let reason = panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap_or("");
    assert!(
        reason.contains("fake backend failed"),
        "the ORIGINAL backend failure must be reported, not a downstream \
         assertion or unwrap panic; got: {reason}"
    );
    // Producers were cancelled and joined rather than left blocked; without
    // that this call does not return at all.
    assert!(
        started.elapsed() < std::time::Duration::from_secs(300),
        "the failed batch must not hang"
    );
    // Positive coverage check: without it this test could pass while never
    // reaching the post-failure release branch it exists to exercise.
    assert!(
        prover.released_work_requests() > 0,
        "no request was released after the failure, so the late-event branch \
         was never exercised and this test proves nothing about it"
    );
}

/// A terminated instance refuses further work promptly, before it allocates or
/// spawns anything.
///
/// A dead backend cannot serve another batch, so the honest behaviour is to say
/// so immediately and name the original failure, rather than let a caller
/// rediscover it by blocking against a backend that will never answer.
#[test]
fn a_terminated_prover_rejects_further_work_fast() {
    let mut prover = prover_failing_after(1);
    let (bin, text) = workload();
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        bin,
        text,
        Some(1 << 20),
    );

    let _ = std::panic::catch_unwind(AssertUnwindSafe(|| {
        prover.commit_memory(1, &handle, non_determinism());
    }));
    assert!(
        prover.is_terminal(),
        "a backend failure must mark the instance terminal"
    );

    // Two subsequent attempts, not one. The rejection panics while the saved
    // reason is read; taking a copy and releasing the lock first is what keeps
    // the second rejection informative — unwinding out with the guard alive
    // poisons the mutex, and attempt 3 would report the poison instead of the
    // original backend failure.
    for attempt in 2..=3u64 {
        let started = std::time::Instant::now();
        let panic = std::panic::catch_unwind(AssertUnwindSafe(|| {
            prover.commit_memory(attempt, &handle, non_determinism());
        }))
        .expect_err("a terminated prover must refuse further work");
        let elapsed = started.elapsed();

        let reason = panic
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| panic.downcast_ref::<&str>().copied())
            .unwrap_or("");
        assert!(
            reason.contains("unusable after a backend failure"),
            "attempt {attempt}: the rejection must name the terminal state; got: {reason}"
        );
        assert!(
            reason.contains("fake backend failed"),
            "attempt {attempt}: the rejection must carry the ORIGINAL failure \
             reason; got: {reason}"
        );
        assert!(
            prover.is_terminal(),
            "attempt {attempt}: the terminal flag must stay readable"
        );
        // Fast enough to prove nothing was allocated or spawned: a real batch on
        // this fixture takes seconds.
        assert!(
            elapsed < std::time::Duration::from_millis(500),
            "attempt {attempt}: rejection must happen before any allocation or \
             spawn, took {elapsed:?}"
        );
    }
}

/// The normal path still returns every owner and every credit.
///
/// The terminal-failure contract must not weaken the success contract: repeated
/// successful batches leave the pool exactly as they found it.
#[test]
fn successful_batches_return_every_credit() {
    let mut prover = prover_succeeding();
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

    for batch_id in 1..=3 {
        let _ = prover.commit_memory(batch_id, &handle, non_determinism());
        assert_eq!(
            prover.available_trace_blocks(),
            before,
            "successful batch {batch_id} did not return every block"
        );
        assert!(!prover.is_terminal());
    }
}

/// A backend that stops reading requests before it reports why must still
/// surface the ORIGINAL reason.
///
/// The ordering is the whole test: the collector meets the closed request
/// channel while dispatching work rebuilt from a late producer event, i.e.
/// before the explaining failure arrives. Sending into that channel used to be
/// an `unwrap`, which panicked there — ahead of consuming the real error and
/// ahead of marking the instance terminal, so a caller saw a closed-channel
/// unwrap and the dead instance still looked reusable.
///
/// No sleeps: the fake backend queues the event, closes the channel and sends
/// the failure on the same sender, so FIFO fixes the order.
#[test]
fn a_backend_that_closes_requests_before_failing_reports_the_original_reason() {
    let mut config = ExecutionProverConfiguration::<FakeBackendConfiguration>::default();
    // Serve a few commitments first so the trace cache holds entries when the
    // disconnect happens: the failure branch then has to drop cached owners as
    // well as the refused request, which is the combination that used to risk
    // a uniqueness panic in place of the real error.
    config.backend.close_requests_before_failure_after = Some(2);
    config.replay_worker_threads_count = 1;
    config.ram_config = FIXTURE_RAM;
    // Room above the producer reserve so the cache can actually hold entries.
    // At the default pool the quota is zero and every entry is evicted on
    // insertion, which would make the "cache enabled" part of this test
    // vacuous — the peak assertion below is what proves it is not.
    config.host_allocators_per_job_count = config.minimum_host_allocators_per_job().unwrap() + 64;
    let mut prover = Prover::with_configuration(config).expect("construction must succeed");
    assert!(prover.cache_quota_blocks() > 0);

    let (bin, text) = workload();
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        bin,
        text,
        Some(1 << 20),
    );

    let started = std::time::Instant::now();
    // `commit_memory_and_prove` is the entry point that enables the trace
    // cache; the failure lands in its commit phase, before any proof request.
    let panic = std::panic::catch_unwind(AssertUnwindSafe(|| {
        prover.commit_memory_and_prove(1, &handle, non_determinism());
    }))
    .expect_err("a backend that stopped serving must surface as an error");

    let reason = panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap_or("");
    assert!(
        reason.contains("fake backend failed"),
        "the ORIGINAL backend reason must survive the closed request channel; \
         got: {reason}"
    );
    assert!(
        !reason.contains("without reporting a failure"),
        "the fallback reason must not replace a reported one; got: {reason}"
    );
    assert!(
        prover.is_terminal(),
        "the instance must be marked terminal through the normal failure path"
    );
    assert!(
        prover.peak_cached_blocks() > 0,
        "the cache never held a block, so this did not exercise the \
         cache-enabled path it claims to"
    );
    assert!(
        started.elapsed() < std::time::Duration::from_secs(300),
        "the closed request channel must not hang the collector"
    );
}

/// A backend that stops accepting while CACHED proof requests are being seeded
/// still surfaces the original reason, and spawns no producers.
///
/// `seed_from_cache` runs before the producers exist, so its dispatch used to
/// `expect`-panic on a closed channel — ahead of consuming the backend's own
/// failure and ahead of marking the instance terminal. That is the same defect
/// the normal dispatch path had, on a path the normal-dispatch test cannot
/// reach: this one disconnects during the PROVE pass's seeding, not during
/// collection.
///
/// The spawn assertion is the second half of the fix. Handling this branch by
/// spawning producers and immediately cancelling them would risk a spawn
/// failure of its own, and that panic would mask the queued original failure —
/// exactly what the fix exists to prevent.
#[test]
fn a_backend_that_closes_requests_during_cached_seeding_reports_the_original_reason() {
    let mut config = ExecutionProverConfiguration::<FakeBackendConfiguration>::default();
    // Per-backend ordinal, and the census includes setup: 0 is the
    // constructor's setup initialization, 1 is `add_binary`'s, 2 is the commit
    // pass (which must succeed so the cache is populated), and 3 is the prove
    // pass, whose cached seeding is the subject. A smaller value would fire
    // during registration, before the `catch_unwind` below — the simulation
    // assertion at the end is what would catch that mistake.
    config.backend.close_requests_on_submit = Some(3);
    config.replay_worker_threads_count = 1;
    config.ram_config = FIXTURE_RAM;
    config.host_allocators_per_job_count = config.minimum_host_allocators_per_job().unwrap() + 64;
    let mut prover = Prover::with_configuration(config).expect("construction must succeed");
    assert!(
        prover.cache_quota_blocks() > 0,
        "the cache must be able to hold entries"
    );

    let (bin, text) = workload();
    let handle = prover.add_binary(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        bin,
        text,
        Some(1 << 20),
    );

    let simulations_before = prover.simulations_started();
    let started = std::time::Instant::now();
    let panic = std::panic::catch_unwind(AssertUnwindSafe(|| {
        prover.commit_memory_and_prove(1, &handle, non_determinism());
    }))
    .expect_err("a backend that stopped accepting must surface as an error");

    let reason = panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap_or("");
    assert!(
        reason.contains("fake backend refused batch at submit"),
        "the ORIGINAL backend reason must survive a disconnect during cached \
         seeding — and this reason is unique to the submit-time refusal, so it \
         cannot be confused with the mid-batch failure the other tests inject; \
         got: {reason}"
    );
    assert!(
        !reason.contains("without reporting a failure"),
        "the fallback reason must not replace a reported one; got: {reason}"
    );
    assert!(
        prover.is_terminal(),
        "the instance must be marked terminal through the normal failure path"
    );
    assert!(
        prover.peak_cached_blocks() > 0,
        "the commit pass must have cached something, or the prove pass would \
         have nothing to seed and this test would not reach the disconnect"
    );
    assert_eq!(
        prover.simulations_started(),
        simulations_before + 1,
        "only the commit pass may simulate: the prove pass disconnected before \
         its producers were spawned, and spawning-then-cancelling is what this \
         fix removed"
    );
    assert!(
        started.elapsed() < std::time::Duration::from_secs(300),
        "the disconnect must not hang the collector"
    );
}
