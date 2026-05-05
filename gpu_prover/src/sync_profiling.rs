use std::fmt;
use std::sync::{Mutex, MutexGuard};
use std::time::Duration;

#[cfg(feature = "sync_profiling")]
use std::cell::RefCell;
#[cfg(feature = "sync_profiling")]
use std::ops::{Deref, DerefMut};
#[cfg(feature = "sync_profiling")]
use std::sync::atomic::{AtomicU64, Ordering};
#[cfg(feature = "sync_profiling")]
use std::time::Instant;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(usize)]
pub enum SyncMetric {
    ConcurrentAllocatorLockWait,
    ConcurrentAllocatorLockHold,
    JitCacheLockWait,
    JitCacheLockHold,
    CpuModelMemoryHoldersCacheLockWait,
    CpuModelMemoryHoldersCacheLockHold,
    CpuModelTraceChunksCacheLockWait,
    CpuModelTraceChunksCacheLockHold,
    CpuModelTraceChunksCacheRestoreRecv,
    CpuModelTimingsLockWait,
    CpuModelTimingsLockHold,
    CpuWorkerNonDeterminismLockWait,
    CpuWorkerNonDeterminismLockHold,
    SimulatorExecuteTraceChunk,
    SimulatorPrepareSnapshot,
    SimulatorFinalizeTracingData,
    ReplayerProcessSnapshot,
    ReplayerRecycleSnapshot,
    SnapshotRecyclerProcessSnapshot,
    CpuModelCollectInitsAndTeardowns,
    CpuModelPartitionInitsAndTeardowns,
    CpuModelHandleInitsAndTeardowns,
    CpuModelHandleTracingData,
    CpuModelHandleSimulationResult,
    CpuModelHandleSnapshotReplayed,
    FreeAllocatorsSend,
    FreeAllocatorsRecv,
    FreeTraceChunksSend,
    FreeTraceChunksRecv,
    SnapshotsSend,
    SnapshotsRecv,
    WorkResultsSend,
    WorkResultsRecv,
}

impl SyncMetric {
    #[cfg(feature = "sync_profiling")]
    const ALL: [Self; 33] = [
        Self::ConcurrentAllocatorLockWait,
        Self::ConcurrentAllocatorLockHold,
        Self::JitCacheLockWait,
        Self::JitCacheLockHold,
        Self::CpuModelMemoryHoldersCacheLockWait,
        Self::CpuModelMemoryHoldersCacheLockHold,
        Self::CpuModelTraceChunksCacheLockWait,
        Self::CpuModelTraceChunksCacheLockHold,
        Self::CpuModelTraceChunksCacheRestoreRecv,
        Self::CpuModelTimingsLockWait,
        Self::CpuModelTimingsLockHold,
        Self::CpuWorkerNonDeterminismLockWait,
        Self::CpuWorkerNonDeterminismLockHold,
        Self::SimulatorExecuteTraceChunk,
        Self::SimulatorPrepareSnapshot,
        Self::SimulatorFinalizeTracingData,
        Self::ReplayerProcessSnapshot,
        Self::ReplayerRecycleSnapshot,
        Self::SnapshotRecyclerProcessSnapshot,
        Self::CpuModelCollectInitsAndTeardowns,
        Self::CpuModelPartitionInitsAndTeardowns,
        Self::CpuModelHandleInitsAndTeardowns,
        Self::CpuModelHandleTracingData,
        Self::CpuModelHandleSimulationResult,
        Self::CpuModelHandleSnapshotReplayed,
        Self::FreeAllocatorsSend,
        Self::FreeAllocatorsRecv,
        Self::FreeTraceChunksSend,
        Self::FreeTraceChunksRecv,
        Self::SnapshotsSend,
        Self::SnapshotsRecv,
        Self::WorkResultsSend,
        Self::WorkResultsRecv,
    ];

    #[cfg(feature = "sync_profiling")]
    fn as_index(self) -> usize {
        self as usize
    }

    pub fn name(self) -> &'static str {
        match self {
            Self::ConcurrentAllocatorLockWait => "allocator.concurrent.lock.wait",
            Self::ConcurrentAllocatorLockHold => "allocator.concurrent.lock.hold",
            Self::JitCacheLockWait => "jit_cache.lock.wait",
            Self::JitCacheLockHold => "jit_cache.lock.hold",
            Self::CpuModelMemoryHoldersCacheLockWait => "cpu_model.memory_holders_cache.lock.wait",
            Self::CpuModelMemoryHoldersCacheLockHold => "cpu_model.memory_holders_cache.lock.hold",
            Self::CpuModelTraceChunksCacheLockWait => "cpu_model.trace_chunks_cache.lock.wait",
            Self::CpuModelTraceChunksCacheLockHold => "cpu_model.trace_chunks_cache.lock.hold",
            Self::CpuModelTraceChunksCacheRestoreRecv => {
                "cpu_model.trace_chunks_cache.restore.recv"
            }
            Self::CpuModelTimingsLockWait => "cpu_model.timings.lock.wait",
            Self::CpuModelTimingsLockHold => "cpu_model.timings.lock.hold",
            Self::CpuWorkerNonDeterminismLockWait => "cpu_worker.nondeterminism.lock.wait",
            Self::CpuWorkerNonDeterminismLockHold => "cpu_worker.nondeterminism.lock.hold",
            Self::SimulatorExecuteTraceChunk => "phase.simulator.execute_trace_chunk",
            Self::SimulatorPrepareSnapshot => "phase.simulator.prepare_snapshot",
            Self::SimulatorFinalizeTracingData => "phase.simulator.finalize_tracing_data",
            Self::ReplayerProcessSnapshot => "phase.replayer.process_snapshot",
            Self::ReplayerRecycleSnapshot => "phase.replayer.recycle_snapshot",
            Self::SnapshotRecyclerProcessSnapshot => "phase.snapshot_recycler.process_snapshot",
            Self::CpuModelCollectInitsAndTeardowns => "phase.cpu_model.collect_inits_and_teardowns",
            Self::CpuModelPartitionInitsAndTeardowns => {
                "phase.cpu_model.partition_inits_and_teardowns"
            }
            Self::CpuModelHandleInitsAndTeardowns => "phase.cpu_model.handle_inits_and_teardowns",
            Self::CpuModelHandleTracingData => "phase.cpu_model.handle_tracing_data",
            Self::CpuModelHandleSimulationResult => "phase.cpu_model.handle_simulation_result",
            Self::CpuModelHandleSnapshotReplayed => "phase.cpu_model.handle_snapshot_replayed",
            Self::FreeAllocatorsSend => "channel.free_allocators.send",
            Self::FreeAllocatorsRecv => "channel.free_allocators.recv",
            Self::FreeTraceChunksSend => "channel.free_trace_chunks.send",
            Self::FreeTraceChunksRecv => "channel.free_trace_chunks.recv",
            Self::SnapshotsSend => "channel.snapshots.send",
            Self::SnapshotsRecv => "channel.snapshots.recv",
            Self::WorkResultsSend => "channel.work_results.send",
            Self::WorkResultsRecv => "channel.work_results.recv",
        }
    }
}

#[derive(Clone, Debug)]
pub struct SyncMetricSnapshot {
    pub metric: SyncMetric,
    pub count: u64,
    pub total: Duration,
    pub min: Duration,
    pub median: Duration,
    pub max: Duration,
}

impl SyncMetricSnapshot {
    pub fn average(&self) -> Duration {
        if self.count == 0 {
            Duration::ZERO
        } else {
            Duration::from_nanos((self.total.as_nanos() / self.count as u128) as u64)
        }
    }
}

impl fmt::Display for SyncMetricSnapshot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:<42} count={:<8} total={:>10.3}ms avg={:>9.3}us min={:>9.3}us median={:>9.3}us max={:>10.3}ms",
            self.metric.name(),
            self.count,
            self.total.as_secs_f64() * 1000.0,
            self.average().as_secs_f64() * 1_000_000.0,
            self.min.as_secs_f64() * 1_000_000.0,
            self.median.as_secs_f64() * 1_000_000.0,
            self.max.as_secs_f64() * 1000.0,
        )
    }
}

#[cfg(feature = "sync_profiling")]
struct MetricCounters {
    count: AtomicU64,
    total_ns: AtomicU64,
    max_ns: AtomicU64,
    samples_ns: Mutex<Vec<u64>>,
}

#[cfg(feature = "sync_profiling")]
impl MetricCounters {
    const fn new() -> Self {
        Self {
            count: AtomicU64::new(0),
            total_ns: AtomicU64::new(0),
            max_ns: AtomicU64::new(0),
            samples_ns: Mutex::new(Vec::new()),
        }
    }

    fn reset(&self) {
        self.count.store(0, Ordering::Relaxed);
        self.total_ns.store(0, Ordering::Relaxed);
        self.max_ns.store(0, Ordering::Relaxed);
        self.samples_ns
            .lock()
            .expect("sync profile samples lock should not be poisoned")
            .clear();
    }
}

#[cfg(feature = "sync_profiling")]
static COUNTERS: [MetricCounters; SyncMetric::ALL.len()] =
    [const { MetricCounters::new() }; SyncMetric::ALL.len()];

#[cfg(feature = "sync_profiling")]
thread_local! {
    static ACTIVE_EXCLUSIVE_PHASES: RefCell<Vec<u64>> = RefCell::new(Vec::new());
}

#[cfg(feature = "sync_profiling")]
fn duration_to_nanos(duration: Duration) -> u64 {
    duration.as_nanos().min(u64::MAX as u128) as u64
}

#[cfg(feature = "sync_profiling")]
fn update_max(atomic: &AtomicU64, value: u64) {
    let mut observed = atomic.load(Ordering::Relaxed);
    while observed < value {
        match atomic.compare_exchange_weak(observed, value, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => return,
            Err(next) => observed = next,
        }
    }
}

#[cfg(feature = "sync_profiling")]
fn account_nested_measurement(elapsed_ns: u64) {
    ACTIVE_EXCLUSIVE_PHASES.with(|phases| {
        if let Some(nested_ns) = phases.borrow_mut().last_mut() {
            *nested_ns = nested_ns.saturating_add(elapsed_ns);
        }
    });
}

#[cfg(feature = "sync_profiling")]
fn record_raw(metric: SyncMetric, elapsed_ns: u64) {
    let counter = &COUNTERS[metric.as_index()];
    counter.count.fetch_add(1, Ordering::Relaxed);
    counter.total_ns.fetch_add(elapsed_ns, Ordering::Relaxed);
    update_max(&counter.max_ns, elapsed_ns);
    counter
        .samples_ns
        .lock()
        .expect("sync profile samples lock should not be poisoned")
        .push(elapsed_ns);
}

#[cfg(feature = "sync_profiling")]
pub fn reset() {
    for counter in &COUNTERS {
        counter.reset();
    }
}

#[cfg(not(feature = "sync_profiling"))]
pub fn reset() {}

#[cfg(feature = "sync_profiling")]
pub fn snapshot() -> Vec<SyncMetricSnapshot> {
    SyncMetric::ALL
        .into_iter()
        .filter_map(|metric| {
            let counter = &COUNTERS[metric.as_index()];
            let count = counter.count.load(Ordering::Relaxed);
            if count == 0 {
                return None;
            }

            let mut samples = counter
                .samples_ns
                .lock()
                .expect("sync profile samples lock should not be poisoned")
                .clone();
            samples.sort_unstable();
            let min = samples.first().copied().unwrap_or_default();
            let median = median_ns(&samples);

            Some(SyncMetricSnapshot {
                metric,
                count,
                total: Duration::from_nanos(counter.total_ns.load(Ordering::Relaxed)),
                min: Duration::from_nanos(min),
                median: Duration::from_nanos(median),
                max: Duration::from_nanos(counter.max_ns.load(Ordering::Relaxed)),
            })
        })
        .collect()
}

#[cfg(not(feature = "sync_profiling"))]
pub fn snapshot() -> Vec<SyncMetricSnapshot> {
    Vec::new()
}

#[cfg(feature = "sync_profiling")]
pub fn record(metric: SyncMetric, elapsed: Duration) {
    let elapsed_ns = duration_to_nanos(elapsed);
    account_nested_measurement(elapsed_ns);
    record_raw(metric, elapsed_ns);
}

#[cfg(not(feature = "sync_profiling"))]
#[inline(always)]
pub fn record(_metric: SyncMetric, _elapsed: Duration) {}

#[cfg(feature = "sync_profiling")]
pub struct ProfiledMutexGuard<'a, T> {
    guard: Option<MutexGuard<'a, T>>,
    wait_metric: SyncMetric,
    wait_elapsed: Duration,
    hold_metric: SyncMetric,
    acquired_at: Instant,
}

#[cfg(feature = "sync_profiling")]
impl<T> Deref for ProfiledMutexGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.guard
            .as_ref()
            .expect("profiled mutex guard should be present")
    }
}

#[cfg(feature = "sync_profiling")]
impl<T> DerefMut for ProfiledMutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.guard
            .as_mut()
            .expect("profiled mutex guard should be present")
    }
}

#[cfg(feature = "sync_profiling")]
impl<T> Drop for ProfiledMutexGuard<'_, T> {
    fn drop(&mut self) {
        let hold_elapsed = self.acquired_at.elapsed();

        // Profiling should not extend the measured critical section. Release
        // the real mutex before writing the samples used for min/median.
        drop(
            self.guard
                .take()
                .expect("profiled mutex guard should be present"),
        );

        record(self.wait_metric, self.wait_elapsed);
        record(self.hold_metric, hold_elapsed);
    }
}

#[cfg(not(feature = "sync_profiling"))]
pub type ProfiledMutexGuard<'a, T> = MutexGuard<'a, T>;

#[cfg(feature = "sync_profiling")]
pub fn lock<'a, T>(
    mutex: &'a Mutex<T>,
    wait_metric: SyncMetric,
    hold_metric: SyncMetric,
) -> ProfiledMutexGuard<'a, T> {
    let wait_started_at = Instant::now();
    let guard = mutex.lock().unwrap();
    let wait_elapsed = wait_started_at.elapsed();
    ProfiledMutexGuard {
        guard: Some(guard),
        wait_metric,
        wait_elapsed,
        hold_metric,
        acquired_at: Instant::now(),
    }
}

#[cfg(feature = "sync_profiling")]
fn median_ns(sorted_samples: &[u64]) -> u64 {
    match sorted_samples.len() {
        0 => 0,
        len if len % 2 == 1 => sorted_samples[len / 2],
        len => {
            let lower = sorted_samples[len / 2 - 1] as u128;
            let upper = sorted_samples[len / 2] as u128;
            ((lower + upper) / 2).min(u64::MAX as u128) as u64
        }
    }
}

#[cfg(not(feature = "sync_profiling"))]
#[inline(always)]
pub fn lock<'a, T>(
    mutex: &'a Mutex<T>,
    _wait_metric: SyncMetric,
    _hold_metric: SyncMetric,
) -> ProfiledMutexGuard<'a, T> {
    mutex.lock().unwrap()
}

#[cfg(feature = "sync_profiling")]
pub fn measure<R>(metric: SyncMetric, f: impl FnOnce() -> R) -> R {
    let started_at = Instant::now();
    let result = f();
    record(metric, started_at.elapsed());
    result
}

#[cfg(not(feature = "sync_profiling"))]
#[inline(always)]
pub fn measure<R>(_metric: SyncMetric, f: impl FnOnce() -> R) -> R {
    f()
}

#[cfg(feature = "sync_profiling")]
pub fn measure_exclusive<R>(metric: SyncMetric, f: impl FnOnce() -> R) -> R {
    let started_at = Instant::now();
    ACTIVE_EXCLUSIVE_PHASES.with(|phases| phases.borrow_mut().push(0));

    let result = f();

    let nested_ns = ACTIVE_EXCLUSIVE_PHASES.with(|phases| {
        phases
            .borrow_mut()
            .pop()
            .expect("exclusive phase stack should contain the current phase")
    });
    let total_ns = duration_to_nanos(started_at.elapsed());
    let exclusive_ns = total_ns.saturating_sub(nested_ns);
    account_nested_measurement(total_ns);
    record_raw(metric, exclusive_ns);

    result
}

#[cfg(not(feature = "sync_profiling"))]
#[inline(always)]
pub fn measure_exclusive<R>(_metric: SyncMetric, f: impl FnOnce() -> R) -> R {
    f()
}
