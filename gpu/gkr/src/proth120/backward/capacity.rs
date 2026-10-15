use crate::backward::GKR_EQ_GROUP_TABLE_LEN;
use crate::proth120::backward::dr_tail::{PR_DR_TAIL_MAX_REMAINING_ROUNDS, PR_DR_TAIL_MAX_SOURCES};
use crate::upstream::PR;

const PR_BYTES: usize = 16;
const EQ_GROUP_BITS: usize = 8;

const _: () = assert!(GKR_EQ_GROUP_TABLE_LEN == 1 << EQ_GROUP_BITS);
const _: () = assert!(size_of::<PR>() == PR_BYTES);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrTailCapacityRequestPr {
    pub(crate) folding_steps: usize,
    pub(crate) canonical_sources: usize,
    pub(crate) static_smem_bytes: usize,
    pub(crate) device_cap_bytes: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrTailCapacityDecisionPr {
    pub(crate) entry_round: usize,
    pub(crate) global_state_bytes: usize,
    pub(crate) dynamic_smem_bytes: usize,
}

pub(crate) fn dr_tail_entry_round_pr(folding_steps: usize) -> usize {
    3 * folding_steps
        .saturating_sub(PR_DR_TAIL_MAX_REMAINING_ROUNDS)
        .div_ceil(3)
}

pub(crate) fn select_capacity_pr(request: DrTailCapacityRequestPr) -> DrTailCapacityDecisionPr {
    assert!(
        request.folding_steps > 0,
        "Proth120 DR tail needs at least one folding step"
    );
    let entry_round = dr_tail_entry_round_pr(request.folding_steps);
    assert!(
        (1..=PR_DR_TAIL_MAX_SOURCES).contains(&request.canonical_sources),
        "Proth120 DR tail supports 1..={PR_DR_TAIL_MAX_SOURCES} canonical sources, got {}",
        request.canonical_sources
    );
    let remaining_rounds = request.folding_steps - entry_round;
    assert!(
        (1..=PR_DR_TAIL_MAX_REMAINING_ROUNDS).contains(&remaining_rounds),
        "Proth120 DR tail remaining rounds out of range"
    );
    let global_state_bytes =
        2 * request.canonical_sources * (1 << (remaining_rounds + 1)) * PR_BYTES;
    let dynamic_smem_bytes =
        (remaining_rounds - 1).div_ceil(EQ_GROUP_BITS) * GKR_EQ_GROUP_TABLE_LEN * PR_BYTES;
    let total_smem_bytes = dynamic_smem_bytes
        .checked_add(request.static_smem_bytes)
        .expect("Proth120 DR-tail shared-memory size overflowed");
    assert!(
        total_smem_bytes <= request.device_cap_bytes,
        "Proth120 DR-tail shared-memory capacity exceeded"
    );
    DrTailCapacityDecisionPr {
        entry_round,
        global_state_bytes,
        dynamic_smem_bytes,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(width: usize, sources: usize) -> DrTailCapacityRequestPr {
        DrTailCapacityRequestPr {
            folding_steps: width,
            canonical_sources: sources,
            static_smem_bytes: 1024,
            device_cap_bytes: 99 * 1024,
        }
    }

    #[test]
    fn cpu_pr_dr_tail_capacity_covers_proth120_widths() {
        for width in 4..=21 {
            for sources in [1, 4, 10] {
                let plan = select_capacity_pr(request(width, sources));
                let expected_entry = match width {
                    4..=8 => 0,
                    9..=11 => 3,
                    12..=14 => 6,
                    15..=17 => 9,
                    18..=20 => 12,
                    _ => 15,
                };
                assert_eq!(plan.entry_round, expected_entry);
                let remaining = width - plan.entry_round;
                assert_eq!(
                    plan.global_state_bytes,
                    2 * sources * (1 << (remaining + 1)) * PR_BYTES
                );
                assert_eq!(plan.dynamic_smem_bytes, GKR_EQ_GROUP_TABLE_LEN * PR_BYTES);
            }
        }
    }

    #[test]
    fn cpu_pr_dr_tail_capacity_rejects_unsupported_requests() {
        let exact = select_capacity_pr(request(8, 10));
        let mut boundary = request(8, 10);
        boundary.device_cap_bytes = exact.dynamic_smem_bytes + boundary.static_smem_bytes;
        assert_eq!(select_capacity_pr(boundary).entry_round, 0);
        boundary.device_cap_bytes -= 1;
        assert!(std::panic::catch_unwind(|| select_capacity_pr(boundary)).is_err());
        assert!(std::panic::catch_unwind(|| select_capacity_pr(request(8, 11))).is_err());
        assert!(std::panic::catch_unwind(|| select_capacity_pr(request(8, 0))).is_err());
    }
}
