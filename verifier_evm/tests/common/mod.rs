//! Shared test fixture: the prover config the committed `unified_circuit_proof_proth120.json`
//! proof was produced with. This is the single source of truth the WHIR verifier generation and
//! the WHIR calldata flattening are both driven from, so the two can't drift in the tests.

use prover::definitions::SecurityLevel;
use prover::gkr::prover::WhirSchedule;
use prover::gkr::prover_config::ProverConfig;

/// Base-layer packing factor from the prover's `CommitmentMode` (2^22 base trace -> 2^26 message).
pub const PACK_LOG2: usize = 4;

/// Mirrors `prover/src/tests/gkr/large_field.rs` (Sec100, 2^22, 5 WHIR rounds
/// with the 2^8 plain-text tail).
pub fn production_prover_config() -> ProverConfig {
    ProverConfig {
        // circuit trace length; the WHIR message is 2^(22 + PACK_LOG2) = 2^26
        trace_len_log2: 22,
        // gkr.sol consumes monomial [c0..c3] rounds: plain naive
        // sumcheck steps only (empty schedule = naive for every round)
        same_size_sumcheck_schedule: prover::gkr::prover_config::naive_same_size_schedule(),
        dimension_reducing_sumcheck_schedule: Default::default(),
        lde_factor: 1 << 5,
        cap_size: 8,
        base_oracles_values_per_leaf: 1 << 2,
        sumcheck_explicit_output_size_log_2: 4,
        security_level: SecurityLevel::Sec100,
        whir_schedule: WhirSchedule {
            base_lde_factor: 1 << 5,
            cap_size: 8,
            whir_steps_schedule: vec![2, 4, 4, 4, 4],
            whir_queries_schedule: vec![17, 12, 8, 6, 5],
            whir_steps_lde_factors: vec![1 << 7, 1 << 11, 1 << 15, 1 << 19],
            whir_pow_schedule: vec![30, 30, 27, 25, 21],
        },
    }
}
