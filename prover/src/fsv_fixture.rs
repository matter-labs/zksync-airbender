use crate::cs::gkr_compiler::GKRCircuitArtifact;
use crate::definitions::{FinalRegisterValue, MerkleTreeCap, DEFAULT_CAP_SIZE};
use crate::gkr::prover::GKRProof;
use crate::merkle_trees::DefaultTreeConstructor;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};

type Proof = GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>;
type Circuit = GKRCircuitArtifact<BabyBearField>;

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct DelegationComponents {
    pub delegation_csr: u32,
    pub proof: Proof,
    pub compiled_circuit: Circuit,
}


#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct UnifiedBaseLayerComponents {
    pub unified_proof: Proof,
    pub compiled_unified_circuit: Circuit,
    pub delegations: Vec<DelegationComponents>,
    pub register_final_values: Vec<FinalRegisterValue>,
    pub final_pc: u32,
    pub final_timestamp: crate::cs::definitions::TimestampScalar,
    pub unified_setup_cap: MerkleTreeCap<DEFAULT_CAP_SIZE>,
}
