//! Execution admission: at most `expected_concurrent_jobs` calls in flight.
//!
//! The pool is sized for `J` executions, each guaranteed `R_effective + 1`
//! blocks, and that only holds if no more than `J` draw on it at once. A
//! backend that declares no limit gets no semaphore and never waits.

#[cfg(any(test, feature = "test_utils"))]
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex};

/// A counting semaphore over execution slots.
pub(super) struct Admission {
    available: Mutex<usize>,
    released: Condvar,
    /// Callers that have entered the blocking wait, cumulative. Test seam,
    /// incremented while holding the mutex and immediately before parking, so
    /// an observer knows the waiter is committed and cannot miss the notify.
    #[cfg(any(test, feature = "test_utils"))]
    entered_wait: AtomicUsize,
    /// Slots taken since construction, cumulative. Test seam.
    #[cfg(any(test, feature = "test_utils"))]
    acquired: AtomicUsize,
}

impl Admission {
    pub(super) fn new(limit: usize) -> Self {
        Self {
            available: Mutex::new(limit),
            released: Condvar::new(),
            #[cfg(any(test, feature = "test_utils"))]
            entered_wait: AtomicUsize::new(0),
            #[cfg(any(test, feature = "test_utils"))]
            acquired: AtomicUsize::new(0),
        }
    }

    /// Block the CALLING thread until a slot is free — never a pooled worker,
    /// which a running execution may need to release the slot being waited on.
    pub(super) fn acquire(&self) -> AdmissionPermit<'_> {
        let mut available = self
            .available
            .lock()
            .expect("execution admission mutex poisoned");
        if *available == 0 {
            #[cfg(any(test, feature = "test_utils"))]
            self.entered_wait.fetch_add(1, Ordering::SeqCst);
            while *available == 0 {
                available = self
                    .released
                    .wait(available)
                    .expect("execution admission mutex poisoned");
            }
        }
        *available -= 1;
        #[cfg(any(test, feature = "test_utils"))]
        self.acquired.fetch_add(1, Ordering::SeqCst);
        AdmissionPermit { admission: self }
    }

    fn release(&self) {
        let mut available = self
            .available
            .lock()
            .expect("execution admission mutex poisoned");
        *available += 1;
        self.released.notify_one();
    }

    #[cfg(any(test, feature = "test_utils"))]
    pub(super) fn available(&self) -> usize {
        *self
            .available
            .lock()
            .expect("execution admission mutex poisoned")
    }

    /// Callers that have entered the blocking wait since construction.
    #[cfg(any(test, feature = "test_utils"))]
    pub(super) fn entered_wait(&self) -> usize {
        self.entered_wait.load(Ordering::SeqCst)
    }

    /// Slots taken since construction, cumulative.
    #[cfg(any(test, feature = "test_utils"))]
    pub(super) fn acquisitions(&self) -> usize {
        self.acquired.load(Ordering::SeqCst)
    }
}

/// Held for as long as an execution is drawing on the pool, and released on
/// drop — including on an unwind, by which point the execution has already
/// joined its producers and released its ownership.
pub(super) struct AdmissionPermit<'a> {
    admission: &'a Admission,
}

impl Drop for AdmissionPermit<'_> {
    fn drop(&mut self) {
        self.admission.release();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    #[test]
    fn cpu_a_permit_is_returned_on_drop_including_on_unwind() {
        let admission = Admission::new(1);
        {
            let _permit = admission.acquire();
            assert_eq!(admission.available(), 0);
        }
        assert_eq!(admission.available(), 1);

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _permit = admission.acquire();
            panic!("execution failed");
        }));
        assert!(result.is_err());
        assert_eq!(
            admission.available(),
            1,
            "an unwinding execution must still return its slot"
        );
    }

    /// The waiter is observed INSIDE the blocking wait before the first
    /// permit is released; a barrier before `acquire` would prove only that
    /// the thread reached the barrier.
    #[test]
    fn cpu_a_second_execution_waits_for_the_first_to_finish() {
        let admission = Arc::new(Admission::new(1));
        let admitted = Arc::new(AtomicUsize::new(0));

        let permit = admission.acquire();
        admitted.fetch_add(1, Ordering::SeqCst);

        let waiter = {
            let admission = admission.clone();
            let admitted = admitted.clone();
            std::thread::spawn(move || {
                let _permit = admission.acquire();
                admitted.fetch_add(1, Ordering::SeqCst);
            })
        };

        await_wait_entry(&admission, 1);
        assert_eq!(admission.available(), 0);
        assert_eq!(
            admitted.load(Ordering::SeqCst),
            1,
            "the waiter must still be blocked, not admitted"
        );

        drop(permit);
        waiter.join().unwrap();
        assert_eq!(admitted.load(Ordering::SeqCst), 2);
        assert_eq!(admission.available(), 1);
    }

    /// Spin until `count` callers have entered the blocking wait, bounded so
    /// a regression fails instead of wedging the suite.
    fn await_wait_entry(admission: &Admission, count: usize) {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
        while admission.entered_wait() < count {
            assert!(
                std::time::Instant::now() < deadline,
                "timed out waiting for {count} caller(s) to block on admission"
            );
            std::thread::yield_now();
        }
    }

    #[test]
    fn cpu_a_larger_limit_admits_that_many_at_once() {
        let admission = Admission::new(3);
        let first = admission.acquire();
        let second = admission.acquire();
        let third = admission.acquire();
        assert_eq!(admission.available(), 0);
        assert_eq!(admission.acquisitions(), 3);
        drop((first, second, third));
        assert_eq!(admission.available(), 3);
    }
}
