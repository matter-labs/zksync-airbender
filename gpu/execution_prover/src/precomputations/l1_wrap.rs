use std::sync::{Arc, Mutex, OnceLock};

use era_cudart::result::CudaResult;
use gpu_circuit_prover::l1_wrap::{L1WrapConstantsHost, L1WrapGeometry};
use gpu_core::primitives::field::PR;
use gpu_core::primitives::static_host::StaticPinnedBox;
use gpu_gkr::proth120::programs::GkrProgramsPr;
use gpu_gkr::setup::L1WrapSetupHost;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::packed::PackedCommitConfig;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::ExecutorFamilyDecoderData;

use super::decoder_host;
use crate::upstream::{
    CpuGKRSetup, GKRCircuitArtifact, L1WrapSetup, MerkleTreeCapVarLength, ProofProfile,
    ProverConfig,
};
use execution_prover::config::SoundnessMode;

pub struct L1WrapPrecomputed {
    pub circuit_type: CircuitType,
    source: Mutex<Option<CpuGKRSetup<PR>>>,
    pub circuit: Arc<GKRCircuitArtifact<PR>>,
    pub programs: Arc<GkrProgramsPr>,
    pub decoder_host: Option<Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>>,
    pub config: ProverConfig,
    pub geometry: L1WrapGeometry,
    host: OnceLock<Arc<L1WrapSetupHost>>,
    constants: Arc<L1WrapConstantsHost>,
}

impl L1WrapPrecomputed {
    pub fn new(
        circuit_type: CircuitType,
        setup: L1WrapSetup,
        soundness_mode: SoundnessMode,
    ) -> CudaResult<Self> {
        let config = ProofProfile::L1Wrap
            .prover_config(circuit_type.get_domain_size_log2() as usize, soundness_mode);
        let geometry = L1WrapGeometry::new(circuit_type, &config, &setup.circuit, &setup);
        let decoder_host = decoder_host(&setup.decoder_table)?;
        let circuit = Arc::new(setup.circuit);
        let programs = Arc::new(GkrProgramsPr::compile(circuit_type, Arc::clone(&circuit)));
        let constants = Arc::new(L1WrapConstantsHost::new(
            &programs, &circuit, &config, &geometry,
        ));
        Ok(Self {
            circuit_type,
            source: Mutex::new(Some(setup.setup)),
            circuit,
            programs,
            decoder_host,
            config,
            geometry,
            host: OnceLock::new(),
            constants,
        })
    }

    pub fn initialize(&self, context: &ProverContext) -> CudaResult<()> {
        self.host
            .get_or_try_init(|| {
                let source = self
                    .source
                    .lock()
                    .unwrap()
                    .take()
                    .expect("L1Wrap CPU setup is consumed once during initialization");
                let cfg = PackedCommitConfig::from_prover_config(
                    &self.config,
                    L1WrapSetupHost::PARTIAL_TREE_REDUCTION_LAYERS,
                );
                L1WrapSetupHost::precompute(&source, self.geometry.pack_log2, cfg, context)
                    .map(Arc::new)
            })
            .map(|_| ())
    }

    pub fn host(&self) -> Arc<L1WrapSetupHost> {
        Arc::clone(
            self.host
                .get()
                .expect("L1Wrap setup initialization must run before proving"),
        )
    }

    pub fn constants(&self) -> Arc<L1WrapConstantsHost> {
        Arc::clone(&self.constants)
    }

    pub fn setup_cap(&self) -> MerkleTreeCapVarLength {
        self.host().cap()
    }
}
