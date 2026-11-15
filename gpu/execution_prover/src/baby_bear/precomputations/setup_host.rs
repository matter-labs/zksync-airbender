use crate::precomputations::decoder_host;
use crate::upstream::{
    BaseColumns, BaseCommitmentGeometry, CSExecutorFamilyDecoderData, CpuGKRSetup,
    GKRCircuitArtifact, ProofProfile, ProverConfig,
};
use era_cudart::result::CudaResult;
use execution_prover::config::SoundnessMode;
use gpu_core::primitives::field::BF;
use gpu_core::primitives::static_host::StaticPinnedBox;
use gpu_gkr::baby_bear::setup::GpuGKRSetupHost;
use gpu_gkr::baby_bear::GkrPrograms;
use gpu_prover_context::ProverContext;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::ExecutorFamilyDecoderData;
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, OnceLock};

pub struct LazyGpuGKRSetupHost {
    published: OnceLock<BTreeMap<ProofProfile, Option<Arc<GpuGKRSetupHost>>>>,
    /// Consumed by the explicit setup batch after all declared profiles are built.
    source: Mutex<Option<CpuGKRSetup<BF>>>,
    geometries: BTreeMap<ProofProfile, BaseCommitmentGeometry>,
}

impl LazyGpuGKRSetupHost {
    pub fn new(
        cpu_setup: CpuGKRSetup<BF>,
        geometries: BTreeMap<ProofProfile, BaseCommitmentGeometry>,
    ) -> Self {
        assert!(
            !geometries.is_empty(),
            "setup cache requires a declared profile"
        );
        for geometry in geometries.values() {
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
        }
        Self {
            published: OnceLock::new(),
            source: Mutex::new(Some(cpu_setup)),
            geometries,
        }
    }

    pub fn base_commitment_geometry(&self, profile: ProofProfile) -> BaseCommitmentGeometry {
        *self
            .geometries
            .get(&profile)
            .unwrap_or_else(|| panic!("ProofProfile::{profile:?} was not declared for this binary"))
    }

    pub fn get_or_init(&self, context: &ProverContext) -> CudaResult<()> {
        self.published
            .get_or_try_init(|| {
                let source = self
                    .source
                    .lock()
                    .unwrap()
                    .take()
                    .expect("the CPU setup is consumed exactly once");
                self.geometries
                    .iter()
                    .map(|(&profile, &geometry)| {
                        let host = if source.hypercube_evals.is_empty() {
                            None
                        } else {
                            Some(Arc::new(GpuGKRSetupHost::precompute_for_geometry(
                                &source, geometry, context,
                            )?))
                        };
                        Ok((profile, host))
                    })
                    .collect::<CudaResult<BTreeMap<_, _>>>()
            })
            .map(|_| ())
    }

    pub fn get_initialized(&self, profile: ProofProfile) -> Option<Arc<GpuGKRSetupHost>> {
        self.published
            .get()
            .expect("setup host must be initialized by a setup batch before use")
            .get(&profile)
            .unwrap_or_else(|| panic!("ProofProfile::{profile:?} was not declared for this binary"))
            .clone()
    }
}

#[derive(Clone)]
pub struct BabyBearPrecomputations {
    pub gkr_programs: Arc<GkrPrograms>,
    pub setup_host: Arc<LazyGpuGKRSetupHost>,
    pub decoder_host: Option<Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>>,
    profile_configs: BTreeMap<ProofProfile, (ProverConfig, BaseCommitmentGeometry)>,
}

impl BabyBearPrecomputations {
    pub(crate) fn profile_config(
        &self,
        profile: ProofProfile,
    ) -> &(ProverConfig, BaseCommitmentGeometry) {
        self.profile_configs
            .get(&profile)
            .unwrap_or_else(|| panic!("ProofProfile::{profile:?} was not declared for this binary"))
    }
    pub(crate) fn from_setup(
        circuit_type: CircuitType,
        compiled_circuit: GKRCircuitArtifact<BF>,
        cpu_setup: CpuGKRSetup<BF>,
        decoder_table: Option<Vec<Option<CSExecutorFamilyDecoderData>>>,
        soundness_mode: SoundnessMode,
        profiles: &[ProofProfile],
    ) -> Self {
        assert_eq!(
            compiled_circuit.trace_len,
            circuit_type.get_domain_size(),
            "compiled circuit trace_len disagrees with CircuitType geometry for {circuit_type:?}"
        );
        let compiled_circuit = Arc::new(compiled_circuit);
        let profile_configs = profiles
            .iter()
            .map(|&profile| {
                let config = execution_prover::config::prover_config_in_mode(
                    circuit_type,
                    &compiled_circuit,
                    profile,
                    soundness_mode,
                );
                let geometry = BaseCommitmentGeometry::from_config(
                    &config,
                    BaseColumns::of(&compiled_circuit),
                );
                (profile, (config, geometry))
            })
            .collect::<BTreeMap<_, _>>();
        let gkr_programs = Arc::new(
            GkrPrograms::compile(circuit_type, Arc::clone(&compiled_circuit))
                .unwrap_or_else(|error| panic!("{circuit_type:?} GKR programs: {error}")),
        );
        let setup_host = Arc::new(LazyGpuGKRSetupHost::new(
            cpu_setup,
            profile_configs
                .iter()
                .map(|(&profile, resolved)| (profile, resolved.1))
                .collect(),
        ));
        let decoder_host = match decoder_table.as_deref() {
            Some(rows) => decoder_host(rows).expect("pinned decoder table allocation failed"),
            None => None,
        };
        Self {
            gkr_programs,
            setup_host,
            decoder_host,
            profile_configs,
        }
    }
}
