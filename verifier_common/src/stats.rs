use crate::lazy_vec::LazyVec;

pub const MAX_LOG_ENTRIES: usize = 128;

pub type Snapshot = (
    &'static str,
    field::stats::Stats,
    non_determinism_source::stats::Stats,
    common_constants::stats::Stats,
);

pub static mut STATS_LOG: LazyVec<Snapshot, MAX_LOG_ENTRIES> = LazyVec::new();

#[inline]
pub fn log(label: &'static str) {
    unsafe {
        // Runtime assert (not debug_assert) so release/test-release also panics
        // instead of silently overrunning the LazyVec backing storage.
        assert!(
            STATS_LOG.len() < MAX_LOG_ENTRIES,
            "verifier_common::stats::STATS_LOG overflow; raise MAX_LOG_ENTRIES"
        );
        STATS_LOG.push((
            label,
            field::stats::FIELD_STATS,
            non_determinism_source::stats::NDS_STATS,
            common_constants::stats::GKR_VERIFY_STATS,
        ));
    }
}

/// Clears the log and zeroes every counter static. Stats are scoped to a
/// single verifier run; tests should call this before the run to avoid
/// inheriting state from anything that ran earlier in the process.
pub fn reset() {
    unsafe {
        STATS_LOG.clear();
        field::stats::FIELD_STATS = field::stats::Stats::default();
        non_determinism_source::stats::NDS_STATS = non_determinism_source::stats::Stats::default();
        common_constants::stats::GKR_VERIFY_STATS = common_constants::stats::Stats::default();
    }
}
