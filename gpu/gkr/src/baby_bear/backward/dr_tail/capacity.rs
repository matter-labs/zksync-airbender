use crate::backward::dr_tail::capacity::{
    capacity_sizes, dr_tail_entry_round, DrTailCapacityDecision, DrTailCapacityRequest,
};
use gpu_core::primitives::field::E4;

pub(crate) fn select_capacity(request: DrTailCapacityRequest) -> DrTailCapacityDecision {
    assert!(request.folding_steps > 0);
    let entry_round = dr_tail_entry_round(request.folding_steps);
    assert!((1..=crate::backward::dr_tail::kernels::DR_TAIL_MAX_SOURCES)
        .contains(&request.canonical_sources));

    let remaining_rounds = request.folding_steps.checked_sub(entry_round).unwrap();
    assert!(
        (1..=crate::backward::dr_tail::kernels::DR_TAIL_MAX_REMAINING_ROUNDS)
            .contains(&remaining_rounds)
    );
    let (global_state_bytes, dynamic_smem_bytes) =
        capacity_sizes::<E4>(request.canonical_sources, remaining_rounds);
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
    use crate::backward::kernels::GKR_EQ_GROUP_TABLE_LEN;

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
                assert_eq!(plan.dynamic_smem_bytes, GKR_EQ_GROUP_TABLE_LEN * 16);
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
