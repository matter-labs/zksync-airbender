//! Shared test fixture: the prover config the committed `unified_circuit_proof_proth120.json`
//! proof was produced with. This is the single source of truth the WHIR verifier generation and
//! the WHIR calldata flattening are both driven from, so the two can't drift in the tests.

use prover::definitions::SecurityLevel;
use prover::gkr::prover::WhirSchedule;
use prover::gkr::prover_config::ProverConfig;

/// Base-layer packing factor from the prover's `CommitmentMode` (2^22 base trace -> 2^26 message).
pub const PACK_LOG2: usize = 4;

/// Mirrors `prover/src/tests/gkr/large_field.rs` (Sec100, 2^22, 6 WHIR rounds).
pub fn production_prover_config() -> ProverConfig {
    ProverConfig {
            // gkr.sol consumes monomial [c0..c3] rounds; keep the windowed
            // schedule (transcript-identical to naive), NOT the uniskip default
            wide_same_size_sumcheck_schedule: prover::gkr::prover_config::windowed_same_size_schedule(),
            narrow_same_size_sumcheck_schedule: prover::gkr::prover_config::windowed_same_size_schedule(),
            dimension_reducing_sumcheck_schedule: Default::default(),
        lde_factor: 1 << 5,
        cap_size: 8,
        base_oracles_values_per_leaf: 1 << 2,
        sumcheck_explicit_output_size_log_2: 4,
        security_level: SecurityLevel::Sec100,
        whir_schedule: WhirSchedule {
            base_lde_factor: 1 << 5,
            cap_size: 8,
            whir_steps_schedule: vec![2, 4, 4, 4, 4, 4],
            whir_queries_schedule: vec![17, 12, 8, 6, 5, 4],
            whir_steps_lde_factors: vec![1 << 7, 1 << 11, 1 << 15, 1 << 19, 1 << 23],
            whir_pow_schedule: vec![30, 30, 27, 25, 21, 24],
        },
    }
}
