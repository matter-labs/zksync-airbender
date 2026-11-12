mod geometry;
mod inputs;
mod orchestration;

pub use geometry::L1WrapGeometry;
pub use inputs::L1WrapInputs;
pub use orchestration::{assemble_l1_proof, GpuL1WrapProofJob, L1WrapProofRequest};

use std::sync::Arc;

use gpu_core::primitives::field::PR;
use gpu_gkr::proth120::base_layer_claims::BaseClaimGatherPr;
use gpu_gkr::proth120::programs::GkrProgramsPr;
use gpu_gkr::proth120::proof_layout::ProofLayoutPr;
use gpu_trace::witness::proth120::LookupRelationsPr;

use crate::upstream::{
    GKRCircuitArtifact, GKRProof, Keccak256MerkleTreeWithCap, Proth120, ProverConfig,
};

pub type L1Proof = GKRProof<Proth120, Proth120, Keccak256MerkleTreeWithCap>;

/// Largest log2 Proth120 evaluation domain used by the wrap NTT.
pub const L1_WRAP_NTT_LOG_MAX_DOMAIN: u32 = gpu_ntt::proth120::LOG_MAX_DOMAIN;

/// Per-circuit wrap constants, built once; relations and claim indices are passed by value.
pub struct L1WrapConstantsHost {
    pub(crate) relations: LookupRelationsPr,
    pub(crate) base_claim_indices: BaseClaimGatherPr,
}

impl L1WrapConstantsHost {
    pub fn new(
        programs: &Arc<GkrProgramsPr>,
        circuit: &GKRCircuitArtifact<PR>,
        config: &ProverConfig,
        geometry: &L1WrapGeometry,
    ) -> Self {
        let layout = ProofLayoutPr::new(programs, config);
        Self {
            relations: LookupRelationsPr::new(circuit),
            base_claim_indices: BaseClaimGatherPr::new(
                programs,
                &layout,
                geometry.memory_columns,
                geometry.witness_columns,
                geometry.setup_columns,
            ),
        }
    }
}
