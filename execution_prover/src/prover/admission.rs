//! The finite trace pool funds at most `expected_concurrent_jobs` executions.

use std::sync::{Condvar, Mutex};

pub(super) struct Admission {
    available: Mutex<usize>,
    released: Condvar,
}

impl Admission {
    pub(super) fn new(limit: usize) -> Self {
        Self {
            available: Mutex::new(limit),
            released: Condvar::new(),
        }
    }

    // Block the caller, never a pooled worker needed by an admitted execution.
    pub(super) fn acquire(&self) -> AdmissionPermit<'_> {
        let mut available = self
            .available
            .lock()
            .expect("execution admission mutex poisoned");
        while *available == 0 {
            available = self
                .released
                .wait(available)
                .expect("execution admission mutex poisoned");
        }
        *available -= 1;
        AdmissionPermit { admission: self }
    }
}

pub(super) struct AdmissionPermit<'a> {
    admission: &'a Admission,
}

impl Drop for AdmissionPermit<'_> {
    fn drop(&mut self) {
        let mut available = self
            .admission
            .available
            .lock()
            .expect("execution admission mutex poisoned");
        *available += 1;
        self.admission.released.notify_one();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_permit_is_returned_on_unwind() {
        let admission = Admission::new(1);
        let result = std::panic::catch_unwind(|| {
            let _permit = admission.acquire();
            assert_eq!(*admission.available.lock().unwrap(), 0);
            panic!("execution failed");
        });
        assert!(result.is_err());
        assert_eq!(*admission.available.lock().unwrap(), 1);
    }
}
