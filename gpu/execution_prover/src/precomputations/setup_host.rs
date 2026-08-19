use gpu_core::primitives::field::BF;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use gpu_gkr::setup::GpuGKRSetupHost;
use gpu_gkr::GkrPrograms;
use gpu_prover_context::ProverContext;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::ExecutorFamilyDecoderData;

use era_cudart::result::CudaResult;

use crate::upstream::{CSExecutorFamilyDecoderData, CpuGKRSetup, GKRCircuitArtifact};
use std::sync::{Arc, OnceLock};

/// Lazy GPU-side setup host: the CPU setup and the geometry needed to
/// produce a `GpuGKRSetupHost` are stored here, and the actual
/// `GpuGKRSetupHost::precompute_from_cpu_setup` call (which does GPU LDE +
/// commit + D2H of partial trees and the unified cap) runs on first use
/// inside the GPU worker, against that worker's already-initialized
/// `ProverContext`.
///
/// The `Arc` wrapper around `GpuGKRSetupHost` is what subsequent workers
/// clone — every prove() that uses this circuit picks up the same cached
/// pinned-host buffers.
pub(crate) struct LazyGpuGKRSetupHost {
    inner: OnceLock<Option<Arc<GpuGKRSetupHost>>>,
    cpu_setup: Arc<CpuGKRSetup<BF>>,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
}

impl LazyGpuGKRSetupHost {
    pub fn new(
        cpu_setup: Arc<CpuGKRSetup<BF>>,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
    ) -> Self {
        Self {
            inner: OnceLock::new(),
            cpu_setup,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
        }
    }

    /// The CPU-side setup this lazy host wraps. Exposed for program-level
    /// consumers (`gpu_program_prover`) that recompute setup merkle caps on the
    /// CPU via `GKRSetup::commit` when assembling a `ProgramProof`.
    pub fn cpu_setup(&self) -> &Arc<CpuGKRSetup<BF>> {
        &self.cpu_setup
    }

    /// First call: builds the host on `context` (one-shot stream sync inside
    /// `precompute_from_cpu_setup`) and fills the lock — with `None` when the
    /// CPU setup has no columns (e.g. InitsAndTeardowns), so "initialized as
    /// absent" is distinguishable from "never initialized". Subsequent calls
    /// return the cached value.
    pub fn get_or_init(&self, context: &ProverContext) -> CudaResult<Option<Arc<GpuGKRSetupHost>>> {
        self.inner
            .get_or_try_init(|| {
                if self.cpu_setup.hypercube_evals.is_empty() {
                    return Ok(None);
                }
                Ok(Some(Arc::new(GpuGKRSetupHost::precompute_from_cpu_setup(
                    &self.cpu_setup,
                    self.log_lde_factor,
                    self.log_rows_per_leaf,
                    self.log_tree_cap_size,
                    context,
                )?)))
            })
            .map(|opt| opt.clone())
    }

    pub fn get_initialized(&self) -> Option<Arc<GpuGKRSetupHost>> {
        self.inner
            .get()
            .expect("setup host must be initialized by a constructor/add_binary setup batch before use")
            .clone()
    }

    pub fn is_initialized(&self) -> bool {
        self.inner.get().is_some()
    }
}

/// Per-circuit precomputations cached across `prove()` invocations.
/// `setup_host` is a `LazyGpuGKRSetupHost` populated on first GPU-worker
/// use; the decoder table is host-only and built eagerly in this
/// constructor.
#[derive(Clone)]
pub(crate) struct CircuitPrecomputations {
    pub gkr_programs: Arc<GkrPrograms>,
    pub setup_host: Arc<LazyGpuGKRSetupHost>,
    pub decoder_host: Option<Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>>,
}

impl CircuitPrecomputations {
    /// Build the per-circuit precomputations. The GPU-side `GpuGKRSetupHost`
    /// is *not* materialized here — `setup_host.get_or_init(context)` does
    /// that on first use inside a GPU worker.
    pub fn new(
        circuit_type: CircuitType,
        compiled_circuit: GKRCircuitArtifact<BF>,
        cpu_setup: CpuGKRSetup<BF>,
        decoder_table_data: Option<&[CSExecutorFamilyDecoderData]>,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_tree_cap_size: u32,
    ) -> CudaResult<Self> {
        assert_eq!(
            compiled_circuit.trace_len,
            circuit_type.get_domain_size(),
            "compiled circuit trace_len disagrees with CircuitType geometry for {circuit_type:?}"
        );
        let compiled_circuit = Arc::new(compiled_circuit);
        let gkr_programs = Arc::new(
            GkrPrograms::compile(circuit_type, Arc::clone(&compiled_circuit))
                .unwrap_or_else(|error| panic!("{circuit_type:?} GKR programs: {error}")),
        );
        let setup_host = Arc::new(LazyGpuGKRSetupHost::new(
            Arc::new(cpu_setup),
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
        ));
        let decoder_host = match decoder_table_data {
            Some(rows) if !rows.is_empty() => {
                let mut buf =
                    alloc_static_pinned_box_uninit::<ExecutorFamilyDecoderData>(rows.len())?;
                for (slot, src) in buf.iter_mut().zip(rows.iter().copied()) {
                    *slot = src.into();
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
