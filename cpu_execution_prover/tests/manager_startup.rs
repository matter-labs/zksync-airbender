//! Manager startup failure, in its own process: the spawn injection is
//! process-global, so a failure injected here would otherwise land on
//! whichever manager the liveness tests happened to start next.

use cpu_execution_prover::test_support::{spawn_injection, CpuManager, RequestExecutor};
use cpu_execution_prover::CpuTraceAllocator;
use crossbeam_channel::{bounded, RecvTimeoutError};
use execution_prover::messages::{WorkRequest, WorkResult};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;
use worker::Worker;

const TIMEOUT: Duration = Duration::from_secs(20);

type Alloc = CpuTraceAllocator;

struct IdleExecutor {
    dropped: Arc<AtomicBool>,
}

impl Drop for IdleExecutor {
    fn drop(&mut self) {
        self.dropped.store(true, Ordering::SeqCst);
    }
}

impl RequestExecutor<Alloc, ()> for IdleExecutor {
    fn execute(
        &self,
        _request: WorkRequest<Alloc, ()>,
        _worker: &Worker,
    ) -> Result<WorkResult<Alloc>, String> {
        unreachable!("this test dispatches no requests")
    }
}

fn with_timeout<T: Send + 'static>(
    label: &'static str,
    body: impl FnOnce() -> T + Send + 'static,
) -> T {
    let (done, wait) = bounded(1);
    let handle = thread::spawn(move || {
        let _ = done.send(body());
    });
    match wait.recv_timeout(TIMEOUT) {
        Ok(value) => {
            let _ = handle.join();
            value
        }
        Err(RecvTimeoutError::Timeout) => panic!("{label} did not finish within {TIMEOUT:?}"),
        Err(RecvTimeoutError::Disconnected) => match handle.join() {
            Err(payload) => std::panic::resume_unwind(payload),
            Ok(()) => unreachable!(),
        },
    }
}

/// An injected coordinator-spawn failure comes back as `Err`, and the driver
/// that already started is joined rather than detached.
///
/// One test, not two: the injection is a process-global countdown, so a second
/// concurrent test would race it for the failing spawn.
#[test]
fn a_failed_coordinator_spawn_is_reported_and_joins_the_driver() {
    let worker = Arc::new(Worker::new_with_num_threads(1));
    let dropped = Arc::new(AtomicBool::new(false));
    let executor = IdleExecutor {
        dropped: dropped.clone(),
    };

    // The driver spawns first and must succeed; the coordinator must not.
    spawn_injection::fail_spawn_after(1);
    let observed = dropped.clone();
    let outcome = with_timeout("manager construction", move || {
        CpuManager::<Alloc, ()>::try_new(worker, executor).map(|_| ())
    });
    spawn_injection::clear();

    let error = outcome.expect_err("the second spawn was injected to fail");
    assert!(error.to_string().contains("coordinator"), "{error}");
    // The driver owned the executor, so the executor being dropped is how we
    // know that thread finished instead of being left running.
    assert!(
        observed.load(Ordering::SeqCst),
        "the already-started driver must be joined before the error returns"
    );

    // And construction works again with the injection cleared.
    let worker = Arc::new(Worker::new_with_num_threads(1));
    let dropped = Arc::new(AtomicBool::new(false));
    let manager = CpuManager::<Alloc, ()>::try_new(worker, IdleExecutor { dropped })
        .expect("construction must succeed without injection");
    with_timeout("shutdown", move || drop(manager));
}
