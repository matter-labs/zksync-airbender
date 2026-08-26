//! Shared test fixture: the prover config the committed `unified_circuit_proof_proth120.json`
//! proof was produced with. This is the single source of truth the WHIR verifier generation and
//! the WHIR calldata flattening are both driven from, so the two can't drift in the tests.

use prover::definitions::SecurityLevel;
use prover::gkr::prover_config::example_configs::{
    evm_production_packed_prover_config, EVM_PRODUCTION_PACK_LOG2,
};
use prover::gkr::prover_config::ProverConfig;

/// Base-layer packing factor from the prover's `CommitmentMode` (2^22 base trace -> 2^26 message).
pub const PACK_LOG2: usize = EVM_PRODUCTION_PACK_LOG2;

/// The production packed config, straight from the prover crate (single
/// source of truth — no schedule mirror to drift), with one difference:
/// gkr.sol consumes monomial [c0..c3] rounds, so the sumcheck schedule here
/// is plain naive for every round (transcript-identical to the prover's
/// windowed schedule).
pub fn production_prover_config() -> ProverConfig {
    let mut config = evm_production_packed_prover_config(SecurityLevel::Sec100);
    config.same_size_sumcheck_schedule = prover::gkr::prover_config::naive_same_size_schedule();
    config
}
