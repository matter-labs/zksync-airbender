use super::super::kernels::GKR_EQ_GROUP_TABLE_LEN;

const E4_BYTES: usize = 16;
const EQ_GROUP_BITS: usize = 8;
const MAX_CANONICAL_SOURCES: usize = 10;

const _: () = assert!(GKR_EQ_GROUP_TABLE_LEN == 1 << EQ_GROUP_BITS);

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

impl DrTailCapacityDecision {
    pub(crate) const fn entry_round(&self) -> usize {
        self.entry_round
    }

    pub(crate) const fn dynamic_smem_bytes(&self) -> usize {
        self.dynamic_smem_bytes
    }
}

pub(crate) fn select_capacity(request: DrTailCapacityRequest) -> DrTailCapacityDecision {
    assert!(request.folding_steps > 0);
    let entry_round = 3 * request
        .folding_steps
        .saturating_sub(super::kernels::DR_TAIL_MAX_REMAINING_ROUNDS)
        .div_ceil(3);
    assert!((1..=MAX_CANONICAL_SOURCES).contains(&request.canonical_sources));

    let remaining_rounds = request.folding_steps.checked_sub(entry_round).unwrap();
    assert!((1..=super::kernels::DR_TAIL_MAX_REMAINING_ROUNDS).contains(&remaining_rounds));
    let global_state_bytes =
        2 * request.canonical_sources * (1 << (remaining_rounds + 1)) * E4_BYTES;
    let dynamic_smem_bytes =
        (remaining_rounds - 1).div_ceil(EQ_GROUP_BITS) * GKR_EQ_GROUP_TABLE_LEN * E4_BYTES;
    let total_smem_bytes = dynamic_smem_bytes
        .checked_add(request.static_smem_bytes)
        .expect("DR-tail shared-memory size overflowed");
    assert!(
        total_smem_bytes <= request.device_cap_bytes,
        "DR-tail shared-memory capacity exceeded"
    );

    DrTailCapacityDecision {
        entry_round,
        global_state_bytes,
        dynamic_smem_bytes,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(width: usize, sources: usize) -> DrTailCapacityRequest {
        DrTailCapacityRequest {
            folding_steps: width,
            canonical_sources: sources,
            static_smem_bytes: 768,
            device_cap_bytes: 99 * 1024,
        }
    }

    #[test]
    fn cpu_direct_tail_covers_all_small_corpus_shapes() {
        for width in 4..=8 {
            for sources in [2, 6, 8, 10] {
                let plan = select_capacity(request(width, sources));
                assert_eq!(plan.entry_round, 0);
                assert_eq!(
                    plan.global_state_bytes,
                    2 * sources * (1 << (width + 1)) * 16
                );
                assert_eq!(plan.dynamic_smem_bytes, GKR_EQ_GROUP_TABLE_LEN * E4_BYTES);
            }
        }
    }

    #[test]
    fn cpu_direct_tail_respects_exact_capacity_boundary() {
        let mut req = request(8, 10);
        let direct = select_capacity(req);
        req.device_cap_bytes = direct.dynamic_smem_bytes + req.static_smem_bytes;
        assert_eq!(select_capacity(req).entry_round, 0);
        req.device_cap_bytes -= 1;
        assert!(std::panic::catch_unwind(|| select_capacity(req)).is_err());
    }

    #[test]
    fn cpu_early_tail_uses_only_necessary_windows() {
        for width in 4..=23 {
            for sources in [2, 6, 8, 10] {
                let req = request(width, sources);
                let plan = select_capacity(req);
                assert_eq!(plan.entry_round % 3, 0);
                assert!((1..=8).contains(&(width - plan.entry_round)));
                if plan.entry_round > 0 {
                    assert!(width - (plan.entry_round - 3) > 8);
                }
            }
        }
    }
}
