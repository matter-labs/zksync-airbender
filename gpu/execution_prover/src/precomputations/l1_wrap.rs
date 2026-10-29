use std::sync::{Arc, OnceLock};

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
    GKRCircuitArtifact, L1WrapSetup, MerkleTreeCapVarLength, ProofProfile, ProverConfig,
    SecurityLevel,
};

pub struct L1WrapPrecomputed {
    pub circuit_type: CircuitType,
    pub setup: L1WrapSetup,
    pub circuit: Arc<GKRCircuitArtifact<PR>>,
    pub programs: Arc<GkrProgramsPr>,
    pub decoder_host: Option<Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>>,
    pub security: SecurityLevel,
    pub config: ProverConfig,
    pub geometry: L1WrapGeometry,
    host: OnceLock<Arc<L1WrapSetupHost>>,
    constants: OnceLock<Arc<L1WrapConstantsHost>>,
}

impl L1WrapPrecomputed {
    pub fn new(
        circuit_type: CircuitType,
        setup: L1WrapSetup,
        security: SecurityLevel,
    ) -> CudaResult<Self> {
        let config =
            gpu_circuit_prover::config::prover_config(circuit_type, ProofProfile::L1Wrap, security)
                .expect("unsupported GPU security level");
        let geometry = L1WrapGeometry::new(circuit_type, &config, &setup.circuit, &setup);
        let circuit = Arc::new(setup.circuit.clone());
        let programs = Arc::new(
            GkrProgramsPr::compile(circuit_type, Arc::clone(&circuit))
                .unwrap_or_else(|error| panic!("{circuit_type:?} GKR programs: {error}")),
        );
        let decoder_host = decoder_host(&setup.decoder_table)?;
        Ok(Self {
            circuit_type,
            setup,
            circuit,
            programs,
            decoder_host,
            security,
            config,
            geometry,
            host: OnceLock::new(),
            constants: OnceLock::new(),
        })
    }

    pub fn initialize(&self, security: SecurityLevel, context: &ProverContext) -> CudaResult<()> {
        let circuit_type = self.circuit_type;
        assert_eq!(
            security, self.security,
            "{circuit_type:?} setup initialization security level differs from the precomputation"
        );
        assert_eq!(
            self.setup.rom,
            circuit_type.rom(),
            "{circuit_type:?} setup ROM mismatch"
        );
        assert_eq!(
            self.setup.trace_len,
            circuit_type.get_domain_size(),
            "{circuit_type:?} setup trace length mismatch"
        );
        self.host.get_or_try_init(|| {
            let cfg = PackedCommitConfig::from_prover_config(
                &self.config,
                gpu_trace::trace::holder::PARTIAL_TREE_REDUCTION_LAYERS,
            );
            L1WrapSetupHost::precompute(&self.setup.setup, self.geometry.pack_log2, cfg, context)
                .map(Arc::new)
        })?;
        self.constants
            .get_or_try_init(|| {
                L1WrapConstantsHost::new(
                    &self.programs,
                    &self.circuit,
                    &self.config,
                    &self.geometry,
                )
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
        Arc::clone(
            self.constants
                .get()
                .expect("L1Wrap setup initialization must run before proving"),
        )
    }

    pub fn setup_cap(&self) -> MerkleTreeCapVarLength {
        self.host().cap()
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;

    #[test]
    #[should_panic(expected = "L1Wrap setup initialization must run before proving")]
    fn host_before_initialize_panics() {
        let circuit = serde_json::from_str(include_str!(
            "../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json"
        ))
        .expect("committed Proth120 layout");
        let setup = L1WrapSetup {
            circuit,
            rom: prover::common_constants::rom::L1_WRAP_ROM,
            table_driver: cs::tables::TableDriver::new(),
            decoder_table: vec![None; common_constants::rom::L1_WRAP_ROM.word_size()],
            setup: prover::gkr::prover::setup::GKRSetup {
                hypercube_evals: Vec::new(),
            },
            trace_len: 1 << 21,
        };
        let circuit_type = CircuitType::L1Wrap21;
        let security = SecurityLevel::Sec100;
        let config =
            gpu_circuit_prover::config::prover_config(circuit_type, ProofProfile::L1Wrap, security)
                .expect("supported L1Wrap config");
        let geometry = L1WrapGeometry::new(circuit_type, &config, &setup.circuit, &setup);
        let circuit = Arc::new(setup.circuit.clone());
        let programs =
            Arc::new(GkrProgramsPr::compile(circuit_type, Arc::clone(&circuit)).unwrap());
        // The host initialization guard does not need a pinned decoder allocation.
        let precomputed = L1WrapPrecomputed {
            circuit_type,
            setup,
            circuit,
            programs,
            decoder_host: None,
            security,
            config,
            geometry,
            host: OnceLock::new(),
            constants: OnceLock::new(),
        };
        precomputed.host();
    }
}
