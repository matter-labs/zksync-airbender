use crate::lazy_vec::LazyVec;
use cs::definitions::GKRAddress;
use field::Field;
use transcript::Seed;

/// Oracle indices in eval/query ordering (used by flattener NDS data and verifier).
/// The prover's `oracle_refs` array uses this order.
pub const MEMORY_ORACLE_IDX: usize = 0;
pub const WITNESS_ORACLE_IDX: usize = 1;
pub const SETUP_ORACLE_IDX: usize = 2;
pub const NUM_BASE_ORACLES: usize = 3;

/// Transcript cap ordering: [setup, memory, witness].
/// This is the order caps appear in the transcript (from `commit_initial`).
pub const CAP_TRANSCRIPT_ORDER: [usize; NUM_BASE_ORACLES] =
    [SETUP_ORACLE_IDX, MEMORY_ORACLE_IDX, WITNESS_ORACLE_IDX];

#[cfg(any(test, feature = "proof_utils"))]
pub mod flatten;

#[derive(Clone, Debug)]
pub struct LayerState<E: Field, const ROUNDS: usize, const ADDRS: usize> {
    pub prev_point: [E; ROUNDS],
    pub prev_point_len: usize,
    pub prev_claims: LazyVec<E, ADDRS>,
    pub batching_challenge: E,
}

pub struct GKRVerifierOutput<
    'a,
    E: Field,
    const ROUNDS: usize,
    const ADDRS: usize,
    const TOTAL_CAP_WORDS: usize,
> {
    pub base_layer_addrs: &'a [GKRAddress],
    pub evaluation_point: [E; ROUNDS],
    pub evaluation_point_len: usize,
    pub grand_product_accumulator: E,
    pub additional_base_layer_openings: &'a [GKRAddress],
    pub whir_batching_challenge: E,
    pub whir_transcript_seed: Seed,
    pub base_layer_claims: LazyVec<E, ADDRS>,
    pub oracle_caps: [u32; TOTAL_CAP_WORDS],
}
