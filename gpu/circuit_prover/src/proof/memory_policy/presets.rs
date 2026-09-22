use super::ProofMemoryPolicy;
use gpu_trace::witness::circuit_type::CircuitType;

mod generated;

pub fn select_arena_bytes(available: usize) -> usize {
    let budget = select_policy_budget(available);
    // Give the 29 GiB policy an extra GiB for allocation placement, leaving
    // at least another GiB free beyond the context's reserved slack. Keep
    // the calibrated policy and smaller-device fallbacks unchanged.
    if budget == 29 << 30 && available >= 31 << 30 {
        30 << 30
    } else {
        budget
    }
}

fn select_policy_budget(available: usize) -> usize {
    generated::PRESET_ARENA_BYTES
        .iter()
        .rev()
        .copied()
        .find(|&bytes| bytes <= available)
        .unwrap_or_else(|| panic!("no memory preset fits in {available} available arena bytes"))
}

pub fn policy(circuit: CircuitType, arena_bytes: usize) -> ProofMemoryPolicy {
    generated::policy(circuit, select_policy_budget(arena_bytes))
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    #[test]
    fn preset_budget_boundaries() {
        assert_eq!(generated::PRESET_ARENA_BYTES, &[21 << 30, 29 << 30]);
        assert!(std::panic::catch_unwind(|| select_arena_bytes((21 << 30) - 1)).is_err());
        for (available, expected) in [
            (21 << 30, 21 << 30),
            ((29 << 30) - 1, 21 << 30),
            (29 << 30, 29 << 30),
            ((30 << 30) - 1, 29 << 30),
            (30 << 30, 29 << 30),
            ((31 << 30) - 1, 29 << 30),
            (31 << 30, 30 << 30),
            (usize::MAX, 30 << 30),
        ] {
            assert_eq!(select_arena_bytes(available), expected);
            assert!(expected <= available);
        }
    }

    #[test]
    fn extra_arena_space_keeps_calibrated_policy_budget() {
        assert_eq!(select_policy_budget(select_arena_bytes(31 << 30)), 29 << 30);
        assert_eq!(select_policy_budget(29 << 30), 29 << 30);
        assert_eq!(select_policy_budget(21 << 30), 21 << 30);
    }
}
