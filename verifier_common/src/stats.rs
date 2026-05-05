#[cfg(feature = "verifier_stats")]
extern crate std;

use crate::lazy_vec::LazyVec;
use core::cell::RefCell;

pub const MAX_LOG_ENTRIES: usize = 128;

pub type Snapshot = (
    &'static str,
    field::stats::Stats,
    non_determinism_source::stats::Stats,
    common_constants::stats::Stats,
);

#[cfg(feature = "verifier_stats")]
std::thread_local! {
    pub static STATS_LOG: RefCell<LazyVec<Snapshot, MAX_LOG_ENTRIES>> =
        const { RefCell::new(LazyVec::new()) };
}

#[cfg(feature = "verifier_stats")]
#[inline]
pub fn log(label: &'static str) {
    let snapshot = (
        label,
        field::stats::FIELD_STATS.with_borrow(|s| *s),
        non_determinism_source::stats::NDS_STATS.with_borrow(|s| *s),
        common_constants::stats::GKR_VERIFY_STATS.with_borrow(|s| *s),
    );
    STATS_LOG.with_borrow_mut(|log| {
        // Runtime assert (not debug_assert) so release/test-release also panics
        // instead of silently overrunning the LazyVec backing storage.
        assert!(
            log.len() < MAX_LOG_ENTRIES,
            "verifier_common::stats::STATS_LOG overflow; raise MAX_LOG_ENTRIES"
        );
        log.push(snapshot);
    });
}
