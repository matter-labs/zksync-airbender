use cs::definitions::GKRAddress;
use field::Field;
use transcript::Seed;

pub use crate::lazy_vec::LazyVec;

#[cfg(any(test, feature = "proof_utils"))]
pub mod flatten;

#[derive(Clone, Debug)]
pub struct LayerState<E: Field, const ROUNDS: usize, const ADDRS: usize> {
    pub prev_point: [E; ROUNDS],
    pub prev_point_len: usize,
    pub prev_claims: LazyVec<E, ADDRS>,
    pub batching_challenge: E,
}

#[derive(Clone, Debug)]
pub enum GKRVerificationError {
    SumcheckRoundFailed { layer: usize, round: usize },
    FinalStepCheckFailed { layer: usize },
    CacheRelationFailed { layer: usize },
}

pub struct GKRVerifierOutput<
    'a,
    E: Field,
    const ROUNDS: usize,
    const ADDRS: usize,
    const SETUP_CAP: usize,
    const MEM_CAP: usize,
    const WIT_CAP: usize,
> {
    pub base_layer_addrs: &'a [GKRAddress],
    pub evaluation_point: [E; ROUNDS],
    pub evaluation_point_len: usize,
    pub grand_product_accumulator: E,
    pub additional_base_layer_openings: &'a [GKRAddress],
    pub whir_batching_challenge: E,
    pub whir_transcript_seed: Seed,
    pub base_layer_claims: LazyVec<E, ADDRS>,
    pub setup_cap: [u32; SETUP_CAP],
    pub memory_cap: [u32; MEM_CAP],
    pub witness_cap: [u32; WIT_CAP],
}
