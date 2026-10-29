use gpu_core::primitives::field::BF;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use gpu_gkr::setup::GpuGKRSetupHost;
use gpu_gkr::GkrPrograms;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::memory::uses_base_commitment_geometry;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::ExecutorFamilyDecoderData;

use era_cudart::result::CudaResult;

use crate::upstream::{
    BaseColumns, BaseCommitmentGeometry, CommitmentMode, CpuGKRSetup, GKRCircuitArtifact,
    MerkleTreeCapVarLength, PrimeField, ProverConfig, SecurityLevel, UnrolledCircuitWitnessEvalFn,
};
use execution_prover::setup::CanonicalCircuitSetup;
use std::sync::{Arc, Mutex, OnceLock};

#[cfg(test)]
mod tests;

/// Immutable CPU-selected configuration shared by setup and both worker phases.
pub(crate) struct ResolvedProverConfig<F: PrimeField> {
    circuit_type: CircuitType,
    circuit: Arc<GKRCircuitArtifact<F>>,
    config: ProverConfig,
    geometry: BaseCommitmentGeometry,
}

impl<F: PrimeField> ResolvedProverConfig<F> {
    fn new(
        circuit_type: CircuitType,
        circuit: Arc<GKRCircuitArtifact<F>>,
        config: ProverConfig,
    ) -> Self {
        let geometry = BaseCommitmentGeometry::from_config(&config, BaseColumns::of(&circuit))
            .expect("invalid canonical commitment geometry");
        Self {
            circuit_type,
            circuit,
            config,
            geometry,
        }
    }

    pub(crate) fn config(&self) -> &ProverConfig {
        &self.config
    }

    pub(crate) fn geometry(&self) -> BaseCommitmentGeometry {
        self.geometry
    }

    pub(crate) fn validate_request(
        &self,
        circuit_type: CircuitType,
        security_level: SecurityLevel,
        circuit: &Arc<GKRCircuitArtifact<F>>,
    ) {
        assert_eq!(
            circuit_type, self.circuit_type,
            "request circuit differs from resolved config"
        );
        assert_eq!(
            security_level, self.config.security_level,
            "request security level differs from resolved config"
        );
        assert!(
            Arc::ptr_eq(circuit, &self.circuit),
            "request artifact differs from resolved config"
        );
        if self.config.commitment_mode == CommitmentMode::MergedMemoryAndWitness {
            gpu_circuit_prover::proof::merged_commitment::validate_merged_packed_geometry(
                &self.geometry,
            );
            gpu_circuit_prover::proof::merged_commitment::validate_merged_circuit_type(
                circuit_type,
                &self.geometry,
            );
        }
    }
}

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

    /// Divergence guard for the config selecting this cache.
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
                let host = if uses_base_commitment_geometry(&self.geometry) {
                    if self.geometry.commitment_mode() == CommitmentMode::MergedMemoryAndWitness {
                        gpu_circuit_prover::proof::merged_commitment::validate_merged_packed_geometry(
                            &self.geometry,
                        );
                    } else {
                        gpu_trace::trace::memory::validate_separate_base_commitment_geometry(
                            &self.geometry,
                        );
                    }
                    GpuGKRSetupHost::precompute_for_geometry(&cpu_setup, self.geometry, context)?
                } else {
                    // Unpacked nonvirtual setup retains its legacy producer.
                    GpuGKRSetupHost::precompute_from_cpu_setup(
                        &cpu_setup,
                        self.log_lde_factor,
                        self.log_rows_per_leaf,
                        self.log_tree_cap_size,
                        context,
                    )?
                };
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
    pub(crate) resolved_config: Arc<ResolvedProverConfig<BF>>,
}

impl CircuitPrecomputations {
    /// Validate host-only request metadata before any transfer constructor.
    /// `caps` distinguishes a proof request from its memory precommit.
    pub(crate) fn admit_inputs_before_transfers(
        &self,
        circuit_type: CircuitType,
        security_level: SecurityLevel,
        caps: Option<&[MerkleTreeCapVarLength]>,
        twiddle_domain_log2: u32,
    ) -> (
        Option<Arc<GpuGKRSetupHost>>,
        Option<Arc<gpu_trace::trace::memory_transfer::GpuGKRMemoryTransferHost>>,
    ) {
        use gpu_trace::trace::memory_transfer::GpuGKRMemoryTransferHost;
        let circuit = self.gkr_programs.compiled_circuit();
        let resolved = &self.resolved_config;
        resolved.validate_request(circuit_type, security_level, circuit);
        assert_eq!(self.gkr_programs.circuit_type(), circuit_type);
        let config = resolved.config();
        let geometry = resolved.geometry();
        self.setup_host
            .validate_config(config, BaseColumns::of(circuit));
        if config.commitment_mode == CommitmentMode::MergedMemoryAndWitness {
            use gpu_circuit_prover::proof::merged_commitment::{
                validate_merged_circuit_type, validate_merged_commitment_geometry,
                validate_merged_packed_geometry,
            };
            validate_merged_packed_geometry(&geometry);
            validate_merged_circuit_type(circuit_type, &geometry);
            validate_merged_commitment_geometry(config, &geometry, circuit);
        } else {
            gpu_trace::trace::memory::validate_memory_commitment_config(config, &geometry, circuit);
        }
        // Proof requests receive the BF transform check in proof preflight.
        if caps.is_none() && uses_base_commitment_geometry(&geometry) {
            gpu_trace::trace::holder::validate_baby_bear_base_geometry(
                &geometry,
                twiddle_domain_log2,
            );
        }
        // Setup batches drain before constructor/add_binary returns, including
        // for memory requests. This accessor allocates nothing.
        let setup = self.setup_host.get_initialized();
        if let Some(host) = setup.as_ref() {
            host.validate_for_geometry(&geometry);
        } else {
            assert_eq!(
                geometry.logical_columns().setup,
                0,
                "missing setup producer"
            );
        }
        if config.commitment_mode == CommitmentMode::MergedMemoryAndWitness {
            assert!(
                setup.is_some(),
                "merged memory producer requires initialized setup"
            );
        }
        // Cap packing uses the ordinary heap, never pinned/device allocations.
        let memory = caps.map(|caps| {
            let host = if !uses_base_commitment_geometry(&geometry) {
                GpuGKRMemoryTransferHost::from_per_coset_caps(
                    caps,
                    config.lde_factor().trailing_zeros(),
                    config.cap_size.trailing_zeros(),
                )
            } else {
                GpuGKRMemoryTransferHost::from_per_coset_caps_for_geometry(caps, geometry)
            };
            host.validate_for_geometry(&geometry);
            Arc::new(host)
        });
        (setup, memory)
    }

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
        let compiled_circuit = Arc::new(compiled_circuit);
        let resolved_config = Arc::new(ResolvedProverConfig::new(
            circuit_type,
            Arc::clone(&compiled_circuit),
            config,
        ));
        let gkr_programs = Arc::new(
            GkrPrograms::compile(circuit_type, Arc::clone(&compiled_circuit))
                .unwrap_or_else(|error| panic!("{circuit_type:?} GKR programs: {error}")),
        );
        let setup_host = Arc::new(LazyGpuGKRSetupHost::new(
            cpu_setup,
            resolved_config.geometry(),
        ));
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
            resolved_config,
        })
    }
}
