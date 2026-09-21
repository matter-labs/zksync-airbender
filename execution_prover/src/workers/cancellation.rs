//! Cancellation disconnects a channel to wake producers blocked on finite pools.

use crate::messages::{ProducerFailure, WorkerResult};
use crossbeam_channel::{unbounded, Receiver, Sender, TryRecvError};
use execution_prover_model::allocator::HostTraceAllocator;
use std::sync::{Arc, Mutex};

#[derive(Clone)]
pub(crate) struct Cancellation {
    sender: Arc<Mutex<Option<Sender<()>>>>,
    receiver: Receiver<()>,
}

impl Cancellation {
    pub(crate) fn new() -> Self {
        let (sender, receiver) = unbounded();
        Self {
            sender: Arc::new(Mutex::new(Some(sender))),
            receiver,
        }
    }

    pub(crate) fn cancel(&self) {
        self.sender
            .lock()
            .expect("cancellation sender mutex poisoned")
            .take();
    }

    pub(crate) fn is_cancelled(&self) -> bool {
        matches!(self.receiver.try_recv(), Err(TryRecvError::Disconnected))
    }

    pub(crate) fn recv<T>(&self, channel: &Receiver<T>) -> Option<T> {
        if self.is_cancelled() {
            return None;
        }
        crossbeam_channel::select! {
            recv(channel) -> value => value.ok(),
            recv(self.receiver) -> _ => None,
        }
    }
}

/// Notify the collector before cancelling peers, so both can finish draining.
pub(crate) struct CancelOnPanic<A: HostTraceAllocator> {
    cancellation: Cancellation,
    results: Sender<WorkerResult<A>>,
    batch_id: u64,
    thread: &'static str,
}

impl<A: HostTraceAllocator> CancelOnPanic<A> {
    pub(crate) fn new(
        cancellation: Cancellation,
        results: Sender<WorkerResult<A>>,
        batch_id: u64,
        thread: &'static str,
    ) -> Self {
        Self {
            cancellation,
            results,
            batch_id,
            thread,
        }
    }
}

impl<A: HostTraceAllocator> Drop for CancelOnPanic<A> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            let _ = self
                .results
                .send(WorkerResult::ProducerFailure(ProducerFailure {
                    batch_id: self.batch_id,
                    reason: format!("the {} thread panicked", self.thread),
                }));
            self.cancellation.cancel();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn cancellation_releases_an_empty_connected_channel() {
        let cancellation = Cancellation::new();
        let (sender, receiver) = unbounded::<()>();
        let (done_sender, done_receiver) = unbounded();
        let peer = cancellation.clone();
        let thread = std::thread::spawn(move || {
            assert!(peer.recv(&receiver).is_none());
            done_sender.send(()).unwrap();
        });
        cancellation.cancel();
        done_receiver.recv_timeout(Duration::from_secs(5)).unwrap();
        thread.join().unwrap();
        drop(sender);
    }
}
