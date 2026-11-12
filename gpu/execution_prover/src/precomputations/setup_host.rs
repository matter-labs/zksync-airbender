use gpu_core::primitives::field::BF;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use gpu_gkr::setup::GpuGKRSetupHost;
use gpu_gkr::GkrPrograms;
use gpu_prover_context::ProverContext;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::ExecutorFamilyDecoderData;

use era_cudart::result::CudaResult;

use super::l1_wrap::L1WrapPrecomputed;
use crate::upstream::{
    BaseColumns, BaseCommitmentGeometry, CpuGKRSetup, ProofProfile, ProverConfig,
    UnrolledCircuitWitnessEvalFn,
};
use execution_prover::config::{assert_profiles_for_circuit, SoundnessMode};
use execution_prover::setup::CanonicalCircuitSetup;
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

pub(crate) fn decoder_host<D: Copy + Default + Into<ExecutorFamilyDecoderData>>(
    rows: &[Option<D>],
) -> CudaResult<Option<Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>>> {
    if rows.is_empty() {
        return Ok(None);
    }
    let mut buf = alloc_static_pinned_box_uninit::<ExecutorFamilyDecoderData>(rows.len())?;
    for (slot, src) in buf.iter_mut().zip(rows.iter().copied()) {
        *slot = src.unwrap_or_default().into();
    }
    Ok(Some(Arc::new(buf)))
}

#[derive(Clone)]
pub struct BabyBearPrecomputations {
    pub gkr_programs: Arc<GkrPrograms>,
    pub setup_host: Arc<LazyGpuGKRSetupHost>,
    pub decoder_host: Option<Arc<StaticPinnedBox<ExecutorFamilyDecoderData>>>,
    profile_configs: BTreeMap<ProofProfile, (ProverConfig, BaseCommitmentGeometry)>,
}

#[derive(Clone)]
pub enum CircuitPrecomputations {
    BabyBear(BabyBearPrecomputations),
    L1Wrap(Arc<L1WrapPrecomputed>),
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
}

impl CircuitPrecomputations {
    pub fn baby_bear(&self) -> &BabyBearPrecomputations {
        match self {
            Self::BabyBear(precomputations) => precomputations,
            Self::L1Wrap(_) => panic!("BabyBear precomputations are not defined for L1Wrap"),
        }
    }

    pub fn l1_wrap(&self) -> &Arc<L1WrapPrecomputed> {
        match self {
            Self::L1Wrap(precomputed) => precomputed,
            Self::BabyBear(_) => panic!("L1Wrap requires Proth precomputations"),
        }
    }

    pub fn from_canonical(
        circuit_type: CircuitType,
        setup: CanonicalCircuitSetup,
        soundness_mode: SoundnessMode,
        profiles: &[ProofProfile],
    ) -> Self {
        assert_profiles_for_circuit(circuit_type, profiles);
        assert_eq!(
            matches!(setup, CanonicalCircuitSetup::L1Wrap(_)),
            circuit_type == CircuitType::L1Wrap,
            "canonical setup variant disagrees with {circuit_type:?}"
        );
        let (compiled_circuit, cpu_setup, decoder_table) = match setup {
            CanonicalCircuitSetup::L1Wrap(setup) => {
                return Self::L1Wrap(Arc::new(
                    L1WrapPrecomputed::new(circuit_type, setup, soundness_mode)
                        .expect("L1 wrap precomputation allocation failed"),
                ));
            }
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
        Self::BabyBear(BabyBearPrecomputations {
            gkr_programs,
            setup_host,
            decoder_host,
            profile_configs,
        })
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
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
    /// as in `l1_wrap::cpu_tests`, so the test needs no `memory_sweep` feature.
    #[test]
    fn cpu_ethproofs_l1_wrap_precomputation_is_rejected_before_allocation() {
        use execution_prover::config::SoundnessMode;
        let setup = crate::upstream::L1WrapSetup {
            circuit: serde_json::from_str(include_str!(
                "../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"
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
