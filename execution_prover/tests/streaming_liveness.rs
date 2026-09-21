//! Finite-pool progress through the real orchestrator.
//!
//! Reserve validation uses real 64 MiB blocks. Starvation tests report larger
//! blocks than they allocate so small fixtures can exhaust the pool; those
//! tests establish wakeup behavior, not reserve sufficiency. The fixture must
//! publish before exhaustion so a backend completion can return credits.
//!
//! Gates and counters are process-global. Tests serialize and join producers
//! on failure; bounded counter waits establish progress without sleeps.

use execution_prover::test_support::finite_pool::{
    replay_gate, stats, FiniteBackend, FiniteBackendConfiguration,
};
use execution_prover::test_support::{result_gate, waits};
use execution_prover::{ExecutionKind, ExecutionProver, ExecutionProverConfiguration, MachineType};
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use std::sync::{Arc, MutexGuard};
use std::time::{Duration, Instant};

type Prover = ExecutionProver<FiniteBackend>;

const DEADLINE: Duration = Duration::from_secs(300);

/// The unified tail's fixture. `hashed_fibonacci` computes `(a + b) % MODULUS`,
/// which lowers to a multiply/divide the Reduced machine does not have, and
/// `ExecutionKind::Unified` is Reduced-only — so it cannot serve here. This one
/// is Reduced-compatible and is what the CPU unified smoke uses. Padded, as
/// that path pads it.
fn unified_workload() -> (Vec<u32>, Vec<u32>) {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let base = root.join("examples/multi_family_smoke/app_blake2_with_compression");
    let (_, bin) = setups::read_and_pad_binary(&base.with_extension("bin"));
    let (_, text) = setups::read_and_pad_binary(&base.with_extension("text"));
    (bin, text)
}

/// Cycles one iteration of the `multi_family_smoke` loop costs, as that
/// fixture's own source documents it ("~50 cycles/iter"). Approximate by
/// nature, which is why the gate below asserts structure rather than counts.
const CYCLES_PER_ITERATION: u32 = 50;

/// Cycles one unified instance covers.
///
/// This restates `UnifiedReducedMachineCircuit::DOMAIN_SIZE_LOG2 = 23`
/// (`circuit_defs/unrolled_circuits/unified_reduced_machine`), which is what
/// `UnrolledCircuitType::Unified.get_domain_size()` reads. It is a literal here
/// only because an integration test cannot reach `execution_prover_model`: the
/// crate is not a dev-dependency and `execution_prover` re-exports only
/// `MachineType`. Adding it as one would make this a real derivation.
const UNIFIED_DOMAIN_CYCLES: u32 = 1 << 23;

/// Iterations needed to span `instances` unified circuits.
fn unified_iterations(instances: u32) -> u32 {
    // `+ 1` puts the run strictly past the boundary rather than on it.
    instances * (UNIFIED_DOMAIN_CYCLES / CYCLES_PER_ITERATION) + 1
}

fn workload() -> (Vec<u32>, Vec<u32>) {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let (_, bin) = setups::read_binary(&root.join("examples/hashed_fibonacci/app.bin"));
    let (_, text) = setups::read_binary(&root.join("examples/hashed_fibonacci/app.text"));
    (bin, text)
}

/// `hashed_fibonacci` reads `n` register-only iterations then `h` blake hashes.
/// `h` is what sizes the trace: enough rows to fill a small pool many times,
/// but far short of a delegation circuit's `2^20` rows, so no circuit boundary
/// is crossed and every block stays held until the run finalizes.
fn non_determinism(hashes: u32) -> QuasiUARTSource {
    QuasiUARTSource::new_with_reads(vec![100, hashes])
}

const HASHES: u32 = 2000;

/// Cycle bound for the mechanism harness.
///
/// Bounded on purpose. Those blocks are 8 KiB, so an unbounded run would hold
/// more of them than even the generous pool phase one measures against, and
/// phase one would then be measuring the pool rather than the fixture. This run
/// is a few MiB of rows, on the order of a thousand blocks against a 16k-block
/// pool. Cutting the run short is safe; over-running the non-determinism source
/// is not, and this cannot.
const MECHANISM_CYCLES: u32 = 100_000;

/// The snapshot-pool test needs the run to publish more than two snapshots, so
/// that a pool of two chunks with one held can actually run out. Publication is
/// now bounded by `SimulationRunner`'s `MAX_CYCLES_PER_SNAPSHOT`
/// (`DEFAULT_MAX_CYCLES_PER_SNAPSHOT`, 2^20 cycles), so cycles are what sizes
/// this workload; the hashes only keep the program from finishing first.
const SNAPSHOT_CYCLES: u32 = 4 << 20;
const HASHES_FOR_SNAPSHOTS: u32 = 30_000;

/// Held for a whole test: serializes on the global seams and restores them.
///
/// The lock taken is the one that lives with the wait counters, not a
/// file-local one. Anything else in this process that reaches
/// `Cancellation::recv` moves the same globals, so a private mutex would let a
/// "producer blocked" observation false-positive on somebody else's wait — and
/// that observation is what every gate here rests on. It is taken before
/// construction and held for the whole test, so `--test-threads=1` at the call
/// site is not what makes these correct.
struct Serial(#[allow(dead_code)] MutexGuard<'static, ()>);

impl Serial {
    fn acquire() -> Self {
        let guard = waits::observation_guard();
        result_gate::clear();
        replay_gate::clear();
        waits::reset();
        stats::reset();
        Serial(guard)
    }
}

impl Drop for Serial {
    fn drop(&mut self) {
        result_gate::clear();
        replay_gate::clear();
    }
}

/// An execution running on its own thread.
///
/// `Drop` opens the gate and joins. Without that, a failed assertion would
/// leave a gated producer parked forever, and every later test in this process
/// would meet a pool with blocks missing from it.
struct Execution<T> {
    handle: Option<std::thread::JoinHandle<T>>,
}

impl<T: Send + 'static> Execution<T> {
    fn spawn(body: impl FnOnce() -> T + Send + 'static) -> Self {
        Self {
            handle: Some(std::thread::spawn(body)),
        }
    }

    fn join(mut self) -> T {
        self.handle
            .take()
            .expect("an execution is joined once")
            .join()
            .expect("the execution thread must not panic")
    }
}

impl<T> Drop for Execution<T> {
    fn drop(&mut self) {
        if let Some(handle) = self.handle.take() {
            result_gate::open();
            replay_gate::release();
            let _ = handle.join();
        }
    }
}

/// Spin until `condition` holds, failing loudly rather than hanging.
fn await_condition(what: &str, mut condition: impl FnMut() -> bool) {
    let deadline = Instant::now() + DEADLINE;
    while !condition() {
        assert!(Instant::now() < deadline, "timed out waiting for {what}");
        std::thread::yield_now();
    }
}

/// Block size for the acceptance gate: reported to the budget and owned by the
/// allocator. 64 MiB is the shipping GPU default, so the numbers this gate
/// accepts are the production ones.
const HONEST_BLOCK_BYTES: usize = 64 << 20;

/// A configuration whose reported and real block sizes agree.
///
/// Everything derived from the block size is therefore real here. The pool is
/// `N * 64 MiB` of genuinely owned memory; it costs no resident memory until
/// rows are written into it, because a block's region is untouched zero pages
/// until a producer fills it.
fn honest_configuration(
    pool: Option<usize>,
) -> ExecutionProverConfiguration<FiniteBackendConfiguration> {
    let mut config = ExecutionProverConfiguration::<FiniteBackendConfiguration> {
        host_allocator_backing_allocation_size: HONEST_BLOCK_BYTES,
        backend: FiniteBackendConfiguration {
            real_block_capacity_bytes: HONEST_BLOCK_BYTES,
        },
        ..Default::default()
    };
    config.host_allocators_per_job_count =
        pool.unwrap_or_else(|| config.minimum_host_allocators_per_job().unwrap());
    config
}

fn honest_minimum() -> usize {
    honest_configuration(Some(1))
        .minimum_host_allocators_per_job()
        .unwrap()
}

/// A configuration whose blocks are smaller than the budget was told.
///
/// Mechanism only. Its `N` is computed from a size the allocator does not
/// honour, so no conclusion about the reserve, the minimum or the cache quota
/// may be drawn from a test that uses it — those are gated by
/// [`honest_configuration`].
fn mechanism_configuration(
    blocks: usize,
) -> ExecutionProverConfiguration<FiniteBackendConfiguration> {
    ExecutionProverConfiguration {
        host_allocators_per_job_count: blocks,
        ..Default::default()
    }
}

fn mechanism_minimum() -> usize {
    ExecutionProverConfiguration::<FiniteBackendConfiguration>::default()
        .minimum_host_allocators_per_job()
        .unwrap()
}

fn register(
    prover: &mut Prover,
    kind: ExecutionKind,
    machine: MachineType,
    cycles: Option<u32>,
) -> execution_prover::BinaryHandle {
    let (bin, text) = workload();
    prover.add_binary(kind, machine, bin, text, cycles)
}

/// ACCEPTANCE GATE, honest sizes: the derived minimum is `R_effective + 1`, one
/// block below it is rejected before any backend resource exists, and an
/// execution at exactly the minimum completes and returns every credit.
///
/// The pool here is real memory of the size the budget was given, so the number
/// this accepts is the production number rather than a scaled stand-in.
#[test]
fn the_derived_minimum_pool_is_accepted_and_one_block_below_is_rejected() {
    let _serial = Serial::acquire();
    let minimum = honest_minimum();
    let config = honest_configuration(None);
    println!(
        "honest gate: block bytes {}, RAM {:?}, R_effective = {}, minimum pool = {minimum} \
         ({} GiB of owned backing)",
        config.host_allocator_backing_allocation_size,
        config.ram_config,
        minimum - 1,
        (minimum * HONEST_BLOCK_BYTES) >> 30,
    );

    let rejected = Prover::with_configuration(honest_configuration(Some(minimum - 1)))
        .err()
        .expect("one block below the minimum must be rejected");
    let message = rejected.to_string();
    assert!(
        message.contains("producer progress") && message.contains(&minimum.to_string()),
        "the rejection must name the reserve it could not meet: {message}"
    );

    let mut prover = Prover::with_configuration(config).expect("the minimum must be accepted");
    assert_eq!(
        prover.cache_quota_blocks(),
        0,
        "at the minimum pool nothing is left for the cache"
    );
    assert_eq!(prover.available_trace_blocks(), minimum);
    let handle = register(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        None,
    );

    let _ = prover.commit_memory(1, &handle, non_determinism(HASHES));

    println!(
        "honest gate: peak blocks in use {} of {minimum}",
        stats::peak_live_blocks()
    );
    assert!(
        stats::peak_live_blocks() > 0,
        "no block was used, so the pool was never exercised"
    );
    assert_eq!(
        prover.available_trace_blocks(),
        minimum,
        "the minimum pool must be returned whole after an execution"
    );
    assert_eq!(
        stats::live_blocks(),
        0,
        "a block region is still handed out"
    );
    assert_eq!(stats::double_use_errors(), 0);
    assert_eq!(stats::over_capacity_errors(), 0);
    assert_eq!(waits::trace_block_waits(), 0, "the minimum pool starved");
    assert!(!prover.is_terminal());
}

/// A producer with no free block blocks, and a completion is what resumes it.
///
/// Two phases, because the regime has to be established rather than hoped for.
/// Phase one measures how many blocks this fixture holds at the moment its
/// producers finalize and publish — nothing is published before that, since no
/// circuit boundary is crossed, so that is the pool's high-water mark for the
/// simulation itself. Phase two then runs with exactly one block more than
/// that: the simulation completes, its publications sit with the gated backend
/// holding every credit, and the inits-and-teardowns chunking that follows
/// needs at least three more blocks (one per series) and cannot get them.
///
/// That ordering is what makes the resumption meaningful. The producer is
/// observed blocked while work is already sitting with the backend, so
/// releasing a permit is demonstrably what returns the credits.
#[test]
fn a_starved_producer_blocks_and_resumes_when_a_completion_returns_credits() {
    let _serial = Serial::acquire();
    let minimum = mechanism_minimum();

    let held_at_publication = {
        // Generous enough that phase one cannot itself starve; if it did, the
        // measurement below would be of the pool rather than of the fixture.
        let generous = minimum + 16384;
        let mut prover = Prover::with_configuration(mechanism_configuration(generous)).unwrap();
        let handle = register(
            &mut prover,
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            Some(MECHANISM_CYCLES),
        );
        let prover = Arc::new(prover);
        // After construction and registration: see phase two.
        result_gate::arm();
        let execution = {
            let prover = Arc::clone(&prover);
            Execution::spawn(move || prover.commit_memory(1, &handle, non_determinism(HASHES)))
        };
        await_condition("the producers to finalize and publish", || {
            stats::requests_received() >= 1
        });
        let held = stats::live_blocks();
        result_gate::open();
        execution.join();
        assert_eq!(
            waits::trace_block_waits(),
            0,
            "phase one starved, so its measurement is of the pool, not the fixture"
        );
        assert_eq!(prover.available_trace_blocks(), generous);
        held
    };
    println!("blocks held when the fixture publishes: {held_at_publication}");
    assert!(
        held_at_publication > 3,
        "this fixture holds almost nothing, so phase two would not starve"
    );

    let pool = std::cmp::max(minimum, held_at_publication + 1);
    assert_eq!(
        pool,
        held_at_publication + 1,
        "the fixture must out-hold the derived minimum for this to bite"
    );
    println!("phase two pool: {pool} blocks");

    let mut prover = Prover::with_configuration(mechanism_configuration(pool)).unwrap();
    let handle = register(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        Some(MECHANISM_CYCLES),
    );
    let prover = Arc::new(prover);
    // Armed only now. Construction and `add_binary` both issue setup
    // initialization requests and wait for them, and those completions pass
    // through the same gate — arming earlier stops the prover from being built
    // at all.
    waits::reset();
    stats::reset();
    result_gate::arm();
    let execution = {
        let prover = Arc::clone(&prover);
        Execution::spawn(move || prover.commit_memory(1, &handle, non_determinism(HASHES)))
    };

    await_condition("a producer to block on an empty trace-block pool", || {
        waits::trace_block_waits() > 0
    });
    // Observed BEFORE anything is released: work is with the backend, no
    // completion has been served, and the pool is empty. That is the circular
    // wait, reproduced rather than inferred.
    assert!(
        stats::requests_received() > 0,
        "the producer blocked before publishing anything, so no completion \
         could ever return a credit and this configuration cannot recover"
    );
    assert_eq!(
        result_gate::served(),
        0,
        "a completion slipped through, so the block was not caused by the gate"
    );
    assert_eq!(
        prover.available_trace_blocks(),
        0,
        "the producer is waiting on a pool that is not actually empty"
    );
    let blocked_waits = waits::trace_block_waits();

    result_gate::open();
    execution.join();

    assert!(
        result_gate::served() > 0,
        "nothing was completed after the gate opened, so nothing shows the \
         producer resumed"
    );
    assert!(
        waits::trace_block_waits() >= blocked_waits,
        "the wait counter must be monotonic"
    );
    assert_eq!(
        prover.available_trace_blocks(),
        pool,
        "a resumed execution must return every credit it held"
    );
    assert_eq!(
        stats::live_blocks(),
        0,
        "a block region is still handed out"
    );
    assert_eq!(stats::double_use_errors(), 0);
    assert_eq!(stats::over_capacity_errors(), 0);
    assert!(
        !prover.is_terminal(),
        "starvation is backpressure, not failure"
    );
}

/// Repeated executions at the same pool recycle every block, and no block is
/// ever held by two owners.
///
/// `into_allocators` asserts unique `Arc` ownership, so a reader that outlived
/// a trace panics rather than leaking a credit; the finite blocks add the other
/// half, since handing the same region out twice is counted rather than
/// silently aliased.
#[test]
fn repeated_executions_recycle_every_block_without_aliasing() {
    let _serial = Serial::acquire();
    let minimum = mechanism_minimum();
    let mut prover = Prover::with_configuration(mechanism_configuration(minimum + 4096)).unwrap();
    let handle = register(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        Some(MECHANISM_CYCLES),
    );
    let pool = prover.available_trace_blocks();

    for batch_id in 1..=3 {
        let _ = prover.commit_memory(batch_id, &handle, non_determinism(HASHES));
        assert_eq!(
            prover.available_trace_blocks(),
            pool,
            "execution {batch_id} did not return every block"
        );
        assert_eq!(
            stats::live_blocks(),
            0,
            "execution {batch_id} left a block region handed out"
        );
    }
    assert_eq!(
        prover.simulations_started(),
        3,
        "each call must run its own simulation, or the accounting above is vacuous"
    );
    assert!(
        stats::peak_live_blocks() > 0,
        "no block was ever used, so nothing was recycled"
    );
    assert_eq!(stats::double_use_errors(), 0);
    assert_eq!(stats::over_capacity_errors(), 0);
}

/// A replayer held inside its chunk drains the snapshot pool, and releasing it
/// replenishes it.
///
/// This is a different finite pool from the trace blocks: it holds
/// `2 * replay_worker_threads_count` chunks and is replenished by the
/// replayers, so the result gate cannot reach it at all. The exhaustion is
/// forced rather than observed incidentally — a wait that depends on the
/// replayer merely being slower than the simulator can stop being true without
/// anyone touching the pool, and would gate nothing. `FiniteSnapshot` parks a
/// replay thread the first time it touches a chunk it has taken, so the
/// simulator provably runs the pool down to nothing.
#[test]
fn a_held_replayer_drains_the_snapshot_pool_and_releasing_it_replenishes() {
    let _serial = Serial::acquire();
    // Honest sizing, and not because the block size matters here: with the
    // trace-block pool far from being the constraint, a snapshot-chunk wait is
    // unambiguously about the snapshot pool.
    let mut config = honest_configuration(None);
    // One replayer is two chunks for the whole execution: the tightest the pool
    // can legally be.
    config.replay_worker_threads_count = 1;
    let mut prover = Prover::with_configuration(config).unwrap();
    let handle = register(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        Some(SNAPSHOT_CYCLES),
    );
    let prover = Arc::new(prover);

    replay_gate::arm();
    let execution = {
        let prover = Arc::clone(&prover);
        Execution::spawn(move || {
            prover.commit_memory(1, &handle, non_determinism(HASHES_FOR_SNAPSHOTS))
        })
    };
    await_condition("a replayer to be held inside its chunk", || {
        replay_gate::parked() >= 1
    });
    await_condition("the simulator to run out of snapshot chunks", || {
        waits::snapshot_chunk_waits() > 0
    });
    let blocked = waits::snapshot_chunk_waits();
    assert_eq!(
        waits::trace_block_waits(),
        0,
        "a trace block was also short, so the wait above is not unambiguously \
         about the snapshot pool"
    );

    replay_gate::release();
    execution.join();

    assert!(
        waits::snapshot_chunk_waits() >= blocked,
        "the wait counter must be monotonic"
    );
    assert_eq!(
        stats::live_blocks(),
        0,
        "a block region is still handed out"
    );
    assert!(
        !prover.is_terminal(),
        "waiting for a snapshot chunk is backpressure, not failure"
    );
}

/// A second caller waits for an execution slot and is admitted the moment the
/// first finishes.
///
/// The waiter is observed inside the blocking wait, with the first execution
/// still gated, so this cannot pass with an unenforced limit.
#[test]
fn a_second_caller_waits_for_a_slot_and_is_admitted_when_the_first_finishes() {
    let _serial = Serial::acquire();
    let minimum = mechanism_minimum();
    let mut prover = Prover::with_configuration(mechanism_configuration(minimum + 16384)).unwrap();
    let handle = register(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        Some(MECHANISM_CYCLES),
    );
    let prover = Arc::new(prover);
    assert_eq!(prover.available_execution_slots(), Some(1));

    result_gate::arm();
    let first = {
        let prover = Arc::clone(&prover);
        Execution::spawn(move || prover.commit_memory(1, &handle, non_determinism(HASHES)))
    };
    await_condition("the first execution to reach the backend", || {
        stats::requests_received() >= 1
    });

    let second = {
        let prover = Arc::clone(&prover);
        Execution::spawn(move || prover.commit_memory(2, &handle, non_determinism(HASHES)))
    };
    await_condition("the second caller to block on admission", || {
        prover.execution_slot_wait_entries() >= 1
    });
    assert_eq!(prover.available_execution_slots(), Some(0));
    assert_eq!(
        prover.simulations_started(),
        1,
        "a blocked caller must not have started a simulation or taken buffers"
    );

    result_gate::open();
    first.join();
    second.join();
    assert_eq!(prover.available_execution_slots(), Some(1));
    assert_eq!(prover.simulations_started(), 2);
    assert_eq!(stats::live_blocks(), 0);
}

/// Two executions are admitted at once when the backend declares room for two,
/// and the pool is sized for both.
///
/// Both are observed in flight simultaneously — the gate holds them there — so
/// this cannot pass with a limit that silently serializes them.
#[test]
fn two_executions_run_concurrently_when_the_backend_admits_two() {
    let _serial = Serial::acquire();
    let mut config = mechanism_configuration(mechanism_minimum() + 16384);
    config.expected_concurrent_jobs = 2;
    let mut prover = Prover::with_configuration(config).unwrap();
    let handle = register(
        &mut prover,
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        Some(MECHANISM_CYCLES),
    );
    let prover = Arc::new(prover);
    let pool = prover.available_trace_blocks();
    assert_eq!(prover.available_execution_slots(), Some(2));

    result_gate::arm();
    let executions: Vec<_> = (1..=2)
        .map(|batch_id| {
            let prover = Arc::clone(&prover);
            Execution::spawn(move || {
                prover.commit_memory(batch_id, &handle, non_determinism(HASHES))
            })
        })
        .collect();
    await_condition("both executions to be admitted and simulating", || {
        prover.simulations_started() >= 2
    });
    assert_eq!(
        prover.available_execution_slots(),
        Some(0),
        "both slots must be taken while both executions are in flight"
    );
    assert_eq!(
        prover.execution_slot_wait_entries(),
        0,
        "neither caller should have had to wait for a slot"
    );

    result_gate::open();
    for execution in executions {
        execution.join();
    }
    assert_eq!(prover.available_execution_slots(), Some(2));
    assert_eq!(prover.available_trace_blocks(), pool);
    assert_eq!(stats::live_blocks(), 0);
    assert_eq!(stats::double_use_errors(), 0);
}

/// ACCEPTANCE GATE, honest sizes: the trace cache never retains more than
/// `N - R_effective - 1` blocks, retains none when that is zero, and retains
/// strictly less as the quota tightens.
///
/// What this establishes and nothing more. It is a bound on how many credits
/// caching may keep out of the pool, which is the only part of the cache the
/// producer-progress guarantee depends on: at the minimum pool the quota is
/// zero and every entry must be evicted, or the reserve the constructor
/// accepted would not actually be available to producers.
///
/// It says nothing about cache HITS or about the prove pass. The backend here
/// serves no proof requests, so `commit_memory_and_prove` always ends in a
/// reported backend failure; hit counts, all-cached skipping and
/// replay/cached deduplication need a backend that really proves, and are
/// covered against real proofs elsewhere. Asserting them here would pass on a
/// path that never produced a proof.
#[test]
fn the_trace_cache_never_retains_more_than_its_quota() {
    let _serial = Serial::acquire();
    let minimum = honest_minimum();

    // Quota, peak blocks the cache held.
    let mut observed = Vec::new();
    for spare in [32usize, 2, 0] {
        result_gate::clear();
        let mut prover =
            Prover::with_configuration(honest_configuration(Some(minimum + spare))).unwrap();
        let handle = register(
            &mut prover,
            ExecutionKind::Unrolled,
            MachineType::FullUnsigned,
            None,
        );
        assert_eq!(prover.cache_quota_blocks(), spare);
        // Expected to end in the backend's "serves no proof requests" failure;
        // the commit pass and the cache behaviour before it are what matter.
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prover.commit_memory_and_prove(1, &handle, non_determinism(HASHES))
        }));
        observed.push((spare, prover.peak_cached_blocks()));
    }

    for (quota, peak) in &observed {
        println!("honest gate: quota {quota}, peak cached {peak}");
    }
    let (_, with_room) = observed[0];
    let (_, tight) = observed[1];
    let (_, at_minimum) = observed[2];

    // A zero quota is the minimum-pool case, and the one where the reserve the
    // constructor accepted depends on the cache keeping nothing at all.
    assert_eq!(
        at_minimum, 0,
        "a zero quota must evict every entry, or the reserve is not really free"
    );
    // A quota with room to spare evicts nothing, so what was sampled is what
    // the cache actually retained.
    assert!(
        with_room > 0 && with_room <= 32,
        "with a quota of 32 the cache retained {with_room} blocks"
    );
    // `peak_cached_blocks` is sampled after `evict_to_fit`, so it means
    // "largest retained" and the quota is a true, deterministic bound. It was
    // not always: sampled before eviction it measured the post-insert,
    // pre-eviction high-water mark, which exceeded the quota by up to one whole
    // entry and varied run to run (5 then 2 against a quota of 2).
    for (quota, peak) in &observed {
        assert!(
            peak <= quota,
            "the cache retained {peak} blocks against a quota of {quota}"
        );
    }
    assert!(
        tight < with_room,
        "a quota of 2 held {tight} blocks, no less than a quota of 32 held \
         ({with_room}), so the quota is not shaping the cache at all"
    );
}

/// ACCEPTANCE GATE, honest sizes: unified execution partitions its instances
/// into leading trivial markers and a trailing run of inits-and-teardowns
/// carriers, with no gap and no overlap.
///
/// In unified mode the i&t sets ride inline in TRAILING unified instances, so
/// the leading ones are trivial markers carrying no data. An earlier version of
/// this gate ran a workload short enough to produce ONE instance, which made
/// `num_trivial_unified_circuits == 0` and any "carriers come after the markers"
/// assertion vacuously true — it checked nothing, because one side was empty.
///
/// WHY THE WORKLOAD IS THIS LONG, derived rather than tuned. A unified instance
/// covers [`UNIFIED_DOMAIN_CYCLES`] = `2^23` cycles, and
/// the instance count is `ceil(total_cycles / 2^23)`. This fixture's i&t data
/// fits a single carrier, so markers exist only once the run spans more than
/// one instance, i.e. strictly more than `2^23` cycles. Its first
/// non-determinism word is the cycle target at roughly
/// [`CYCLES_PER_ITERATION`] cycles per iteration — documented in
/// `examples/multi_family_smoke/src/main.rs`, whose loop is written so `n` can
/// grow unbounded while the stack array stays bounded by modulo indexing. So
/// the iteration count for `k` instances is `k * 2^23 / 50`, and `k = 2` is the
/// cheapest that produces a marker at all.
///
/// The counts themselves are deliberately NOT asserted: `~50` is the fixture's
/// own approximation, so pinning an instance count would make this a test of
/// that constant. What is asserted is the structure, which is exact.
#[test]
fn unified_execution_partitions_markers_and_inits_and_teardowns_carriers() {
    let _serial = Serial::acquire();
    let mut prover = Prover::with_configuration(honest_configuration(None)).unwrap();
    let (bin, text) = unified_workload();
    let handle = prover.add_binary(
        ExecutionKind::Unified,
        MachineType::Reduced,
        bin,
        text,
        None,
    );
    let pool = prover.available_trace_blocks();

    let result = prover.commit_memory(
        1,
        &handle,
        QuasiUARTSource::new_with_reads(vec![unified_iterations(2), 0xDEAD_BEEF]),
    );

    let markers = result.num_trivial_unified_circuits;
    let carriers = &result.inits_and_teardowns_top_bits;
    // An instance count the test did NOT compute. The caps map is keyed by
    // circuit family and unified execution registers exactly one, so the length
    // of its per-sequence cap list is how many instances the result itself saw.
    // Checking `markers + carriers` against a "total" defined as their sum
    // could only agree with itself — an instance belonging to neither group
    // would be invisible to it.
    assert_eq!(
        result.circuit_families_memory_caps.len(),
        1,
        "unified execution must register exactly one circuit family, found {:?}",
        result
            .circuit_families_memory_caps
            .keys()
            .collect::<Vec<_>>()
    );
    let instances = result
        .circuit_families_memory_caps
        .values()
        .next()
        .expect("just asserted one family")
        .len();
    println!(
        "unified: {markers} trivial markers, {} i&t-carrying instances, {instances} \
         unified instances by cap count",
        carriers.len()
    );

    // The half that was vacuous before.
    assert!(
        markers > 0,
        "the run produced no trivial markers, so the leading half of the pairing is \
         untested — the workload did not span more than one unified instance"
    );
    assert!(
        !carriers.is_empty(),
        "no unified instance carried inits-and-teardowns, so there is no tail to pair"
    );

    // The real statement: markers and carriers partition the instance range.
    // Carriers are the TRAILING instances, so their sequence IDs are exactly
    // `markers .. markers + carriers.len()` — contiguous, starting where the
    // markers stop. A gap or an overlap would mean an instance that is neither
    // or both, which is what "paired" has to exclude.
    let expected: Vec<usize> = (markers..markers + carriers.len()).collect();
    let actual: Vec<usize> = carriers.keys().copied().collect();
    assert_eq!(
        actual, expected,
        "i&t carriers are not the contiguous trailing run after {markers} markers"
    );
    // And the two groups account for every instance the result reports, with
    // none left over.
    assert_eq!(
        markers + carriers.len(),
        instances,
        "{markers} markers plus {} carriers do not account for the {instances} \
         unified instances the caps report",
        carriers.len()
    );

    for (sequence_id, top_bits) in carriers {
        assert!(
            !top_bits.is_empty(),
            "instance {sequence_id} is listed as carrying i&t data but names no window"
        );
        assert!(
            top_bits.windows(2).all(|pair| pair[0] < pair[1]),
            "instance {sequence_id} has non-ascending i&t windows {top_bits:?}"
        );
    }

    assert!(!prover.is_terminal());
    assert_eq!(
        prover.available_trace_blocks(),
        pool,
        "the unified tail did not return every credit"
    );
    assert_eq!(stats::live_blocks(), 0);
    assert_eq!(stats::double_use_errors(), 0);
}
