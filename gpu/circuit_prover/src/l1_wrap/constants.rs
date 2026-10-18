use era_cudart::result::CudaResult;
use gpu_core::primitives::field::PR;
use gpu_gkr::proth120::base_layer_claims::BaseClaimIndicesHostPr;
use gpu_gkr::proth120::programs::GkrProgramsPr;
use gpu_gkr::proth120::proof_layout::ProofLayoutPr;
use gpu_trace::witness::proth120::Proth120LookupRelationsHost;

use super::L1WrapGeometry;
use crate::upstream::{GKRCircuitArtifact, ProverConfig};

/// Per-circuit constants every wrap proof uploads with its phase-one inputs.
pub struct L1WrapConstantsHost {
    pub(crate) relations: Proth120LookupRelationsHost,
    pub(crate) base_claim_indices: BaseClaimIndicesHostPr,
}

impl L1WrapConstantsHost {
    pub fn new(
        programs: &GkrProgramsPr,
        circuit: &GKRCircuitArtifact<PR>,
        config: &ProverConfig,
        geometry: &L1WrapGeometry,
    ) -> CudaResult<Self> {
        let layout = ProofLayoutPr::new(programs, config, geometry.pack_log2 as usize);
        Ok(Self {
            relations: Proth120LookupRelationsHost::new(circuit)?,
            base_claim_indices: BaseClaimIndicesHostPr::new(
                programs,
                &layout,
                geometry.memory_columns,
                geometry.witness_columns,
                geometry.setup_columns,
            )?,
        })
    }
}
