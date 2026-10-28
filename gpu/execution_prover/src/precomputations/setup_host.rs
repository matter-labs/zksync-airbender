use gpu_core::primitives::field::BF;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use gpu_gkr::setup::GpuGKRSetupHost;
use gpu_gkr::GkrPrograms;
use gpu_prover_context::ProverContext;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::ExecutorFamilyDecoderData;

use era_cudart::result::CudaResult;

use crate::upstream::{
    BaseColumns, BaseCommitmentGeometry, CpuGKRSetup, ProverConfig, SecurityLevel,
    UnrolledCircuitWitnessEvalFn,
};
use execution_prover::setup::CanonicalCircuitSetup;
use std::sync::{Arc, Mutex, OnceLock};

#[cfg(test)]
mod tests;

pub struct LazyGpuGKRSetupHost {
    inner: OnceLock<Option<Arc<GpuGKRSetupHost>>>,
    /// Consumed by the first `get_or_init`: once the pinned copy exists the
    /// heap copy has no reader.
    cpu_setup: Mutex<Option<CpuGKRSetup<BF>>>,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
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
            log_lde_factor: geometry.lde_factor().trailing_zeros(),
            log_rows_per_leaf: geometry.values_per_leaf().trailing_zeros(),
            log_tree_cap_size: geometry.cap_size().trailing_zeros(),
            geometry,
        }
    }

    pub fn base_commitment_geometry(&self) -> BaseCommitmentGeometry {
        self.geometry
    }

    /// Divergence guard for the config selecting this cache. Eager warmup is
    /// still legacy until packed/virtual execution admission is qualified.
    pub fn validate_config(&self, config: &ProverConfig, columns: BaseColumns) {
        let requested = BaseCommitmentGeometry::from_config(config, columns)
            .expect("invalid requested setup cache geometry");
        assert_eq!(
            requested, self.geometry,
            "setup cache commitment geometry mismatch"
        );
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
                Ok(Some(Arc::new(GpuGKRSetupHost::precompute_from_cpu_setup(
                    &cpu_setup,
                    self.log_lde_factor,
                    self.log_rows_per_leaf,
                    self.log_tree_cap_size,
                    context,
                )?)))
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
}

impl CircuitPrecomputations {
    pub fn from_canonical(
        circuit_type: CircuitType,
        setup: CanonicalCircuitSetup,
        security_level: SecurityLevel,
    ) -> CudaResult<Self> {
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
        };
        assert_eq!(
            compiled_circuit.trace_len,
            circuit_type.get_domain_size(),
            "compiled circuit trace_len disagrees with CircuitType geometry for {circuit_type:?}"
        );
        let config = gpu_circuit_prover::config::prover_config(circuit_type, security_level)
            .expect("unsupported GPU security level");
        let geometry =
            BaseCommitmentGeometry::from_config(&config, BaseColumns::of(&compiled_circuit))
                .expect("invalid canonical setup cache geometry");
        let compiled_circuit = Arc::new(compiled_circuit);
        let gkr_programs = Arc::new(
            GkrPrograms::compile(circuit_type, Arc::clone(&compiled_circuit))
                .unwrap_or_else(|error| panic!("{circuit_type:?} GKR programs: {error}")),
        );
        let setup_host = Arc::new(LazyGpuGKRSetupHost::new(cpu_setup, geometry));
        let decoder_host = match decoder_table.as_deref() {
            Some(rows) if !rows.is_empty() => {
                let mut buf =
                    alloc_static_pinned_box_uninit::<ExecutorFamilyDecoderData>(rows.len())?;
                for (slot, src) in buf.iter_mut().zip(rows.iter().copied()) {
                    *slot = src.unwrap_or_default().into();
                }
                Some(Arc::new(buf))
            }
            _ => None,
        };
        Ok(Self {
            gkr_programs,
            setup_host,
            decoder_host,
        })
    }
}
