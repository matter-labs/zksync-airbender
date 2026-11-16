use super::kernels::DR_TAIL_MAX_REMAINING_ROUNDS;
use crate::backward::kernels::{GKR_EQ_GROUP_SIZE, GKR_EQ_GROUP_TABLE_LEN};

const _: () = assert!(GKR_EQ_GROUP_TABLE_LEN == 1 << 8);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrTailCapacityRequest {
    pub(crate) folding_steps: usize,
    pub(crate) canonical_sources: usize,
    pub(crate) static_smem_bytes: usize,
    pub(crate) device_cap_bytes: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrTailCapacityDecision {
    pub(crate) entry_round: usize,
    pub(crate) global_state_bytes: usize,
    pub(crate) dynamic_smem_bytes: usize,
}

pub(crate) fn dr_tail_entry_round(folding_steps: usize) -> usize {
    3 * folding_steps
        .saturating_sub(DR_TAIL_MAX_REMAINING_ROUNDS)
        .div_ceil(3)
}

pub(crate) fn capacity_sizes<F>(
    canonical_sources: usize,
    remaining_rounds: usize,
) -> (usize, usize) {
    let global_state_bytes = 2 * canonical_sources * (1 << (remaining_rounds + 1)) * size_of::<F>();
    let dynamic_smem_bytes = (remaining_rounds - 1).div_ceil(GKR_EQ_GROUP_SIZE)
        * GKR_EQ_GROUP_TABLE_LEN
        * size_of::<F>();
    (global_state_bytes, dynamic_smem_bytes)
}
