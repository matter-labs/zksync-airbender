use std::sync::{Arc, Mutex, OnceLock};

use era_cudart::result::CudaResult;
use gpu_circuit_prover::proth120::{L1WrapConstantsHost, L1WrapGeometry};
use gpu_core::primitives::field::PR;
use gpu_core::primitives::static_host::StaticPinnedBox;
use gpu_gkr::proth120::programs::GkrProgramsPr;
use gpu_gkr::proth120::setup::L1WrapSetupHost;
use gpu_prover_context::ProverContext;
use gpu_trace::proth120::trace::packed::PackedCommitConfig;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::ExecutorFamilyDecoderData;

use crate::precomputations::decoder_host;
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

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use crate::precomputations::CircuitPrecomputations;
    use execution_prover::setup::CanonicalCircuitSetup;
    use std::panic::{catch_unwind, AssertUnwindSafe};
    use ProofProfile::L1Wrap;

    fn panic_message(f: impl FnOnce()) -> String {
        let payload = catch_unwind(AssertUnwindSafe(f)).expect_err("expected a named panic");
        payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| {
                payload
                    .downcast_ref::<&str>()
                    .map(|message| message.to_string())
            })
            .expect("panic payload is a message")
    }

    /// The GPU L1 wrap precomputation refuses ethproofs with the profile's mode assert before its
    /// pinned allocations: under the CUDA stubs (or without a device) any allocation would panic
    /// with another message, so the assert's message also pins the order. The setup is the committed layout with empty tables,
    /// so the test needs no `memory_sweep` feature.
    #[test]
    fn cpu_ethproofs_l1_wrap_precomputation_is_rejected_before_allocation() {
        use execution_prover::config::SoundnessMode;
        let setup = crate::upstream::L1WrapSetup {
            circuit: serde_json::from_str(include_str!(
                "../../../../circuit_defs/unrolled_circuits/unified_reduced_machine_proth120/generated/layout.json"
            ))
            .expect("committed Proth120 layout"),
            rom: prover::common_constants::rom::L1_WRAP_ROM,
            table_driver: cs::tables::TableDriver::new(),
            decoder_table: vec![None; prover::common_constants::rom::L1_WRAP_ROM.word_size()],
            setup: prover::gkr::prover::setup::GKRSetup {
                hypercube_evals: Vec::new(),
            },
            trace_len: 1 << 21,
        };
        let soundness_mode = SoundnessMode::EthproofsSoundnessCalc;
        let message = panic_message(|| {
            CircuitPrecomputations::from_canonical(
                CircuitType::L1Wrap,
                CanonicalCircuitSetup::L1Wrap(setup),
                soundness_mode,
                &[L1Wrap],
            );
        });
        assert!(
            message.contains("supports only the pessimistic-conjecture soundness mode"),
            "{message}"
        );
    }
}
