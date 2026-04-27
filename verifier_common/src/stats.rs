use crate::lazy_vec::LazyVec;
use core::cell::RefCell;

pub const MAX_LOG_ENTRIES: usize = 128;

pub type Snapshot = (
    &'static str,
    field::stats::Stats,
    non_determinism_source::stats::Stats,
    common_constants::stats::Stats,
);

#[thread_local]
pub static STATS_LOG: RefCell<LazyVec<Snapshot, MAX_LOG_ENTRIES>> = RefCell::new(LazyVec::new());

#[inline]
pub fn log(label: &'static str) {
    let snapshot = (
        label,
        *field::stats::FIELD_STATS.borrow(),
        *non_determinism_source::stats::NDS_STATS.borrow(),
        *common_constants::stats::GKR_VERIFY_STATS.borrow(),
    );
    let mut log = STATS_LOG.borrow_mut();
    // Runtime assert (not debug_assert) so release/test-release also panics
    // instead of silently overrunning the LazyVec backing storage.
    assert!(
        log.len() < MAX_LOG_ENTRIES,
        "verifier_common::stats::STATS_LOG overflow; raise MAX_LOG_ENTRIES"
    );
    log.push(snapshot);
}
