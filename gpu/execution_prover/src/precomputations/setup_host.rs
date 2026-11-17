use gpu_core::primitives::field::BF;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use gpu_gkr::setup::GpuGKRSetupHost;
use gpu_gkr::GkrPrograms;
use gpu_prover_context::ProverContext;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::ExecutorFamilyDecoderData;

use era_cudart::result::CudaResult;

use crate::upstream::{
    BaseColumns, BaseCommitmentGeometry, CpuGKRSetup, ProverConfig, UnrolledCircuitWitnessEvalFn,
};
use execution_prover::config::SoundnessMode;
use execution_prover::setup::CanonicalCircuitSetup;
use std::sync::{Arc, Mutex, OnceLock};

pub struct LazyGpuGKRSetupHost {
    inner: OnceLock<Option<Arc<GpuGKRSetupHost>>>,
    /// Consumed by the first `get_or_init`: once the pinned copy exists the
    /// heap copy has no reader.
    cpu_setup: Mutex<Option<CpuGKRSetup<BF>>>,
    geometry: BaseCommitmentGeometry,
}

impl LazyGpuGKRSetupHost {
    pub fn new(cpu_setup: CpuGKRSetup<BF>, geometry: BaseCommitmentGeometry) -> Self {
        assert_eq!(
            cpu_setup.hypercube_evals.len(),
            geometry.logical_columns().setup,
            "setup cache column geometry mismatch"
        );
        for column in &cpu_setup.hypercube_evals {
            assert_eq!(
                column.len(),
                1usize << geometry.trace_len_log2(),
                "setup cache trace geometry mismatch"
            );
        }
        Self {
            inner: OnceLock::new(),
            cpu_setup: Mutex::new(Some(cpu_setup)),
            geometry,
        }
    }

    pub fn base_commitment_geometry(&self) -> BaseCommitmentGeometry {
        self.geometry
    }

    pub fn get_or_init(&self, context: &ProverContext) -> CudaResult<()> {
        self.inner
            .get_or_try_init(|| {
                let cpu_setup = self
                    .cpu_setup
                    .lock()
                    .unwrap()
                    .take()
                    .expect("the CPU setup is consumed exactly once");
                if cpu_setup.hypercube_evals.is_empty() {
                    return Ok(None);
                }
                let host =
                    GpuGKRSetupHost::precompute_for_geometry(&cpu_setup, self.geometry, context)?;
                Ok(Some(Arc::new(host)))
            })
            .map(|_| ())
    }

    pub fn get_initialized(&self) -> Option<Arc<GpuGKRSetupHost>> {
        self.inner
            .get()
            .expect(
                "setup host must be initialized by a constructor/add_binary setup batch before use",
            )
            .clone()
    }
}

#[derive(Clone)]
pub struct CircuitPrecomputations {
    pub gkr_programs: Arc<GkrPrograms>,
    pub setup_host: Arc<LazyGpuGKRSetupHost>,
    pub decoder_host: Option<Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>>,
    pub(crate) config: ProverConfig,
    pub(crate) geometry: BaseCommitmentGeometry,
}

impl CircuitPrecomputations {
    pub fn from_canonical(
        circuit_type: CircuitType,
        setup: CanonicalCircuitSetup,
        soundness_mode: SoundnessMode,
    ) -> Self {
        let (compiled_circuit, cpu_setup, decoder_table) = match setup {
            CanonicalCircuitSetup::Riscv(setup) => {
                let decoder_table = setup.witness_eval_fn.map(|evaluator| match evaluator {
                    UnrolledCircuitWitnessEvalFn::NonMemory { decoder_table, .. }
                    | UnrolledCircuitWitnessEvalFn::Memory { decoder_table, .. }
                    | UnrolledCircuitWitnessEvalFn::Unified { decoder_table, .. } => decoder_table,
                });
                (setup.compiled_circuit, setup.setup, decoder_table)
            }
            CanonicalCircuitSetup::Delegation(setup) => (setup.compiled_circuit, setup.setup, None),
            CanonicalCircuitSetup::L1Wrap(_) => {
                unimplemented!("L1 wrap GPU setup preparation")
            }
        };
        assert_eq!(
            compiled_circuit.trace_len,
            circuit_type.get_domain_size(),
            "compiled circuit trace_len disagrees with CircuitType geometry for {circuit_type:?}"
        );
        let config = circuit_type.prover_config_in_mode(&compiled_circuit, soundness_mode);
        let compiled_circuit = Arc::new(compiled_circuit);
        let geometry =
            BaseCommitmentGeometry::from_config(&config, BaseColumns::of(&compiled_circuit));
        let gkr_programs = Arc::new(
            GkrPrograms::compile(circuit_type, Arc::clone(&compiled_circuit))
                .unwrap_or_else(|error| panic!("{circuit_type:?} GKR programs: {error}")),
        );
        let setup_host = Arc::new(LazyGpuGKRSetupHost::new(cpu_setup, geometry));
        let decoder_host = match decoder_table.as_deref() {
            Some(rows) if !rows.is_empty() => {
                let mut buf =
                    alloc_static_pinned_box_uninit::<ExecutorFamilyDecoderData>(rows.len())
                        .expect("pinned decoder table allocation failed");
                for (slot, src) in buf.iter_mut().zip(rows.iter().copied()) {
                    *slot = src.unwrap_or_default().into();
                }
                Some(Arc::new(buf))
            }
            _ => None,
        };
        Self {
            gkr_programs,
            setup_host,
            decoder_host,
            config,
            geometry,
        }
    }
}
