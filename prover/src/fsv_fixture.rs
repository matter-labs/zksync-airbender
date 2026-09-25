use crate::definitions::{FinalRegisterValue, MerkleTreeCap, DEFAULT_CAP_SIZE};
use crate::gkr::prover::GKRProof;
use crate::merkle_trees::DefaultTreeConstructor;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};

type Proof = GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>;

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct DelegationComponents {
    pub delegation_csr: u32,
    pub proof: Proof,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct UnifiedBaseLayerComponents {
    pub unified_proof: Proof,
    pub delegations: Vec<DelegationComponents>,
    pub register_final_values: Vec<FinalRegisterValue>,
    pub final_pc: u32,
    pub final_timestamp: crate::cs::definitions::TimestampScalar,
    pub unified_setup_cap: MerkleTreeCap<DEFAULT_CAP_SIZE>,
    /// Memory/delegation proof-of-work the external challenges were drawn with: the bits
    /// (the FSV asserts they equal `MEMORY_DELEGATION_POW_BITS`) and the ground nonce.
    pub pow_bits: u32,
    pub pow_challenge: u64,
}
