mod geometry;
mod inputs;
mod orchestration;
#[cfg(test)]
mod tests;

pub use geometry::L1WrapGeometry;
pub use inputs::L1WrapInputs;
#[doc(hidden)]
pub use orchestration::prove_stagewise;
pub use orchestration::{assemble_l1_proof, prove, GpuL1WrapProofJob};

use std::sync::Arc;

use era_cudart::result::CudaResult;
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
pub const L1_WRAP_NTT_LOG_MAX_DOMAIN: u32 =
    gpu_prover_context::ProverContext::PROTH120_NTT_LOG_MAX_DOMAIN;

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
    ) -> CudaResult<Self> {
        let layout = ProofLayoutPr::new(programs, config);
        Ok(Self {
            relations: LookupRelationsPr::new(circuit),
            base_claim_indices: BaseClaimGatherPr::new(
                programs,
                &layout,
                geometry.memory_columns,
                geometry.witness_columns,
                geometry.setup_columns,
            ),
        })
    }
}
