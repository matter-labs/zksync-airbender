use super::ProofMemoryPolicy;
use gpu_trace::witness::circuit_type::CircuitType;

mod generated;

/// Arena bytes kept free for the next request's inputs while a proof runs:
/// the largest full-capacity input bundle of any supported circuit, rounded up.
pub const INPUTS_RESERVE_BYTES: usize = 1537 << 20;

pub fn select_arena_bytes(available: usize) -> usize {
    generated::PRESET_ARENA_BYTES
        .iter()
        .rev()
        .copied()
        .find(|&bytes| bytes <= available)
        .unwrap_or_else(|| panic!("no memory preset fits in {available} available arena bytes"))
}

pub fn policy(circuit: CircuitType, arena_bytes: usize) -> ProofMemoryPolicy {
    generated::policy(circuit, select_arena_bytes(arena_bytes))
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    #[test]
    fn preset_budget_boundaries() {
        assert_eq!(generated::PRESET_ARENA_BYTES, &[21 << 30, 30 << 30]);
        assert!(std::panic::catch_unwind(|| select_arena_bytes((21 << 30) - 1)).is_err());
        for (available, expected) in [
            (21 << 30, 21 << 30),
            ((30 << 30) - 1, 21 << 30),
            (30 << 30, 30 << 30),
            (usize::MAX, 30 << 30),
        ] {
            assert_eq!(select_arena_bytes(available), expected);
        }
    }
}
