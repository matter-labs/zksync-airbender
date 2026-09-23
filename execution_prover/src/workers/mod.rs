pub(crate) mod simulation;
pub(crate) mod simulation_runner;

use std::thread::JoinHandle;

/// Threads whose channels the collector waits on: a panic aborts the process
/// (like a panic on the worker pool) instead of leaving the collector waiting.
pub fn spawn_abort_on_panic(name: String, f: impl FnOnce() + Send + 'static) -> JoinHandle<()> {
    std::thread::Builder::new()
        .name(name)
        .stack_size(worker::REQUIRED_STACK_SIZE)
        .spawn(move || {
            if std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).is_err() {
                std::process::abort();
            }
        })
        .expect("failed to start a thread")
}
