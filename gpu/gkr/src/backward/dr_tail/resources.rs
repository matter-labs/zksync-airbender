//! Device limits asserted while scheduling the DR tail.

pub(crate) const DR_TAIL_OCCUPANCY_THREADS: u32 = super::kernels::DR_TAIL_BLOCK_THREADS;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrTailRawAttributes {
    pub static_smem_bytes: usize,
    pub local_bytes: usize,
    pub max_dynamic_smem_bytes: usize,
}

pub(crate) fn dr_continuation_window_count(entry_round: usize) -> usize {
    if entry_round == 0 {
        return 0;
    }
    debug_assert!(entry_round >= 3 && entry_round.is_multiple_of(3));
    (entry_round - 3) / 3
}
