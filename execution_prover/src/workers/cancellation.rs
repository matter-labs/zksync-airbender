//! Coordinated cancellation for the blocking producer loops.
//!
//! The producers spend most of their life blocked on a channel, and dropping a
//! result sender wakes none of them — a producer blocked on the free-buffer
//! channel is not waiting on that sender at all. So a failure has to reach
//! them explicitly, before any join, or shutdown deadlocks.
//!
//! Any holder can trigger it, not just the orchestrator: a replay worker that
//! unwinds while the simulator waits for the chunk it held is the only thing
//! that will ever wake that simulator.

use crate::messages::{ProducerFailure, WorkerResult};
use crossbeam_channel::{unbounded, Receiver, Sender};
use execution_prover_model::allocator::HostTraceAllocator;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

struct Inner {
    flag: AtomicBool,
    /// Dropped to wake every registered waiter. Behind a mutex so any holder
    /// can trigger cancellation, not only a unique owner.
    sender: Mutex<Option<Sender<()>>>,
}

impl Inner {
    fn cancel(&self) {
        self.flag.store(true, Ordering::Relaxed);
        // Cannot be poisoned: the guard is only ever held across this `take`.
        self.sender
            .lock()
            .expect("cancellation sender mutex poisoned")
            .take();
    }
}

/// Orchestrator-side handle.
pub(crate) struct Cancellation {
    inner: Arc<Inner>,
    receiver: Receiver<()>,
}

/// Clone handed to each blocking loop.
#[derive(Clone)]
pub(crate) struct CancellationToken {
    inner: Arc<Inner>,
    receiver: Receiver<()>,
}

impl Cancellation {
    pub(crate) fn new() -> Self {
        let (sender, receiver) = unbounded();
        Self {
            inner: Arc::new(Inner {
                flag: AtomicBool::new(false),
                sender: Mutex::new(Some(sender)),
            }),
            receiver,
        }
    }

    pub(crate) fn token(&self) -> CancellationToken {
        CancellationToken {
            inner: Arc::clone(&self.inner),
            receiver: self.receiver.clone(),
        }
    }

    pub(crate) fn cancel(&self) {
        self.inner.cancel();
    }
}

impl CancellationToken {
    pub(crate) fn is_cancelled(&self) -> bool {
        self.inner.flag.load(Ordering::Relaxed)
    }

    /// Trigger cancellation from inside a producer.
    pub(crate) fn cancel(&self) {
        self.inner.cancel();
    }

    /// Receive from `channel`, giving up if cancellation fires first.
    ///
    /// The only way a producer may block on a pool channel: a bare `recv()`
    /// cannot be interrupted, and turns a failure elsewhere into a hang.
    /// `pool` names which finite pool the wait is against, so a liveness test
    /// can tell trace-block starvation from snapshot-chunk starvation.
    pub(crate) fn recv<T>(&self, pool: Pool, channel: &Receiver<T>) -> Option<T> {
        if self.is_cancelled() {
            return None;
        }
        // A non-blocking attempt first, so the wait counters mean "had to
        // wait" rather than "asked". This biases towards draining a queued
        // value over an in-flight cancellation; the producer then stops at its
        // next `recv` and returns the block either way.
        match channel.try_recv() {
            Ok(value) => return Some(value),
            Err(crossbeam_channel::TryRecvError::Empty) => {
                #[cfg(any(test, feature = "test_utils"))]
                waits::record(pool);
            }
            Err(crossbeam_channel::TryRecvError::Disconnected) => {}
        }
        let _ = pool;
        let mut select = crossbeam_channel::Select::new();
        let work = select.recv(channel);
        let cancel = select.recv(&self.receiver);
        let op = select.select();
        match op.index() {
            index if index == work => op.recv(channel).ok(),
            index if index == cancel => {
                // The sender is dropped rather than used, so a completed
                // operation here means cancellation.
                let _ = op.recv(&self.receiver);
                None
            }
            _ => unreachable!(),
        }
    }
}

/// Reports and cancels on an abnormal exit from a producer thread.
///
/// Cancelling peers alone would not unblock shutdown: a cancelled simulator
/// publishes no `SimulationResult`, so the collector never closes its request
/// sender, the backend holds the batch's result sender until it does, and the
/// collector's loop never ends to reach the join.
///
/// Order is load-bearing: notify, then cancel. A collector blocked on `recv`
/// wakes on the event; cancelling first would only wake the producers.
pub(crate) struct CancelOnPanic<A: HostTraceAllocator> {
    token: CancellationToken,
    results: Sender<WorkerResult<A>>,
    batch_id: u64,
    thread: &'static str,
    armed: bool,
}

impl<A: HostTraceAllocator> CancelOnPanic<A> {
    pub(crate) fn new(
        token: CancellationToken,
        results: Sender<WorkerResult<A>>,
        batch_id: u64,
        thread: &'static str,
    ) -> Self {
        Self {
            token,
            results,
            batch_id,
            thread,
            armed: true,
        }
    }

    pub(crate) fn disarm(mut self) {
        self.armed = false;
    }
}

impl<A: HostTraceAllocator> Drop for CancelOnPanic<A> {
    fn drop(&mut self) {
        if !self.armed || !std::thread::panicking() {
            return;
        }
        // Best effort: if the collector has already gone there is no one to
        // tell, and cancelling peers is still worth doing.
        let _ = self
            .results
            .send(WorkerResult::ProducerFailure(ProducerFailure {
                batch_id: self.batch_id,
                reason: format!("the {} thread panicked", self.thread),
            }));
        self.token.cancel();
    }
}

/// What a blocked `recv` is waiting for.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Pool {
    /// Host trace blocks, returned when a consumer finishes with a trace.
    TraceBlock,
    /// Snapshot chunks, `2 * replay_worker_threads_count` per execution,
    /// returned by the replayers. A separate finite pool with its own
    /// exhaustion behaviour, so it is counted separately.
    SnapshotChunk,
    /// A replayer waiting for the simulator to hand it a snapshot. NOT a
    /// finite pool — an idle replayer is normal and says nothing about
    /// exhaustion, so this is deliberately not counted.
    Handoff,
}

/// Cumulative counts of genuine waits on each finite pool.
///
/// Test seam, process-global because the choke point is a free function on the
/// path every producer takes. Monotonic, so a test can wait for a count to
/// rise without racing a reset.
#[cfg(any(test, feature = "test_utils"))]
pub mod waits {
    use super::Pool;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Mutex, MutexGuard};

    /// Anything else in the binary reaching `Cancellation::recv` keeps bumping
    /// these counters, so a reader that does not hold this can false-positive
    /// on somebody else's wait.
    static OBSERVATION: Mutex<()> = Mutex::new(());

    /// Serialize against every other counter-reading test in this binary.
    pub fn observation_guard() -> MutexGuard<'static, ()> {
        OBSERVATION
            .lock()
            .expect("a counter-reading test panicked while holding the observation guard")
    }

    static TRACE_BLOCK_WAITS: AtomicUsize = AtomicUsize::new(0);
    static SNAPSHOT_CHUNK_WAITS: AtomicUsize = AtomicUsize::new(0);

    pub(super) fn record(pool: Pool) {
        let counter = match pool {
            Pool::TraceBlock => &TRACE_BLOCK_WAITS,
            Pool::SnapshotChunk => &SNAPSHOT_CHUNK_WAITS,
            Pool::Handoff => return,
        };
        counter.fetch_add(1, Ordering::SeqCst);
    }

    /// Times a producer had to wait for a host trace block.
    pub fn trace_block_waits() -> usize {
        TRACE_BLOCK_WAITS.load(Ordering::SeqCst)
    }

    /// Times a producer had to wait for a snapshot chunk.
    pub fn snapshot_chunk_waits() -> usize {
        SNAPSHOT_CHUNK_WAITS.load(Ordering::SeqCst)
    }

    pub fn reset() {
        TRACE_BLOCK_WAITS.store(0, Ordering::SeqCst);
        SNAPSHOT_CHUNK_WAITS.store(0, Ordering::SeqCst);
    }
}
