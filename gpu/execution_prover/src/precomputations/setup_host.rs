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
use execution_prover::config::SoundnessMode;
use execution_prover::setup::CanonicalCircuitSetup;
use gpu_trace::witness::circuit_type::UnrolledCircuitType;
use std::collections::{BTreeMap, BTreeSet};
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

fn validate_profiles(
    circuit_type: CircuitType,
    setup: &CanonicalCircuitSetup,
    profiles: &[ProofProfile],
) -> BTreeSet<ProofProfile> {
    validate_profile_set(
        circuit_type,
        matches!(setup, CanonicalCircuitSetup::L1Wrap(_)),
        profiles,
    )
}

fn validate_profile_set(
    circuit_type: CircuitType,
    is_l1_wrap_setup: bool,
    profiles: &[ProofProfile],
) -> BTreeSet<ProofProfile> {
    let profiles: BTreeSet<ProofProfile> = profiles.iter().copied().collect();
    assert!(
        !profiles.is_empty(),
        "prepare needs at least one ProofProfile"
    );
    assert!(
        !is_l1_wrap_setup || circuit_type == CircuitType::L1Wrap,
        "CanonicalCircuitSetup::L1Wrap requires CircuitType::L1Wrap, got {circuit_type:?}"
    );
    if circuit_type == CircuitType::L1Wrap {
        assert!(
            is_l1_wrap_setup,
            "CircuitType::L1Wrap requires CanonicalCircuitSetup::L1Wrap"
        );
        assert!(
            profiles.iter().eq([ProofProfile::L1Wrap].iter()),
            "CircuitType::L1Wrap requires exactly ProofProfile::L1Wrap, got {profiles:?}"
        );
        return profiles;
    }
    assert!(
        !profiles.contains(&ProofProfile::L1Wrap),
        "ProofProfile::L1Wrap requires CircuitType::L1Wrap, got {circuit_type:?}"
    );
    const UNIFIED22: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::Unified22);
    assert!(
        !profiles.contains(&ProofProfile::CompressionFinal) || circuit_type == UNIFIED22,
        "ProofProfile::CompressionFinal requires CircuitType::Unrolled(UnrolledCircuitType::Unified22), got {circuit_type:?}"
    );
    assert!(
        circuit_type != UNIFIED22 || profiles.iter().eq([ProofProfile::CompressionFinal].iter()),
        "CircuitType::Unrolled(UnrolledCircuitType::Unified22) requires exactly ProofProfile::CompressionFinal, got {profiles:?}"
    );
    assert!(
        !profiles.contains(&ProofProfile::Compression)
            || circuit_type == CircuitType::Unrolled(UnrolledCircuitType::Unified),
        "ProofProfile::Compression requires CircuitType::Unrolled(UnrolledCircuitType::Unified), got {circuit_type:?}"
    );
    profiles
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
        let profiles = validate_profiles(circuit_type, &setup, profiles);
        let (compiled_circuit, cpu_setup, decoder_table) = match setup {
            CanonicalCircuitSetup::L1Wrap(setup) => {
                // The wrap exists only under PessimisticConjecture (deferred product scope):
                // refuse any other soundness_mode before its pinned allocations.
                ProofProfile::L1Wrap
                    .config_profile()
                    .assert_supports(soundness_mode);
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
    use gpu_trace::witness::circuit_type::{DelegationCircuitType, UnrolledMemoryCircuitType};
    use std::panic::{catch_unwind, AssertUnwindSafe};
    use ProofProfile::{Compression, L1Wrap, Standard};

    const UNIFIED: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::Unified);
    const UNIFIED22: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::Unified22);

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

    fn set(profiles: &[ProofProfile]) -> BTreeSet<ProofProfile> {
        profiles.iter().copied().collect()
    }

    #[test]
    fn cpu_l1_validate_profiles() {
        let inits_and_teardowns = CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns);
        let memory = CircuitType::Unrolled(UnrolledCircuitType::Memory(
            UnrolledMemoryCircuitType::LoadStoreWordOnly,
        ));
        let delegation = CircuitType::Delegation(DelegationCircuitType::Blake2WithCompression);
        assert_eq!(
            validate_profile_set(UNIFIED, false, &[Standard, Standard]),
            set(&[Standard])
        );
        assert_eq!(
            validate_profile_set(UNIFIED, false, &[Standard]),
            set(&[Standard])
        );
        assert_eq!(
            validate_profile_set(UNIFIED, false, &[Compression, Standard, Compression]),
            set(&[Standard, Compression])
        );
        for circuit in [inits_and_teardowns, memory, delegation, UNIFIED22] {
            assert!(catch_unwind(|| validate_profile_set(circuit, false, &[Compression])).is_err());
        }
        for circuit in [inits_and_teardowns, memory, delegation] {
            assert_eq!(
                validate_profile_set(circuit, false, &[Standard, Standard]),
                set(&[Standard])
            );
        }
        assert_eq!(
            validate_profile_set(CircuitType::L1Wrap, true, &[L1Wrap, L1Wrap]),
            set(&[L1Wrap])
        );
        assert_eq!(
            validate_profile_set(UNIFIED22, false, &[Compression, Compression]),
            set(&[Compression])
        );
        let compression_message = |circuit: CircuitType| {
            format!("ProofProfile::CompressionFinal requires CircuitType::Unrolled(UnrolledCircuitType::Unified22), got {circuit:?}")
        };
        let unified22_message = |profiles: &[ProofProfile]| {
            format!(
                "CircuitType::Unrolled(UnrolledCircuitType::Unified22) requires exactly ProofProfile::CompressionFinal, got {:?}",
                set(profiles)
            )
        };
        let cases: [(CircuitType, bool, &[ProofProfile], String); 14] = [
            (
                UNIFIED,
                false,
                &[],
                "prepare needs at least one ProofProfile".to_string(),
            ),
            (
                CircuitType::L1Wrap,
                true,
                &[],
                "prepare needs at least one ProofProfile".to_string(),
            ),
            (
                UNIFIED,
                true,
                &[Standard],
                format!(
                    "CanonicalCircuitSetup::L1Wrap requires CircuitType::L1Wrap, got {UNIFIED:?}"
                ),
            ),
            (
                CircuitType::L1Wrap,
                false,
                &[L1Wrap],
                "CircuitType::L1Wrap requires CanonicalCircuitSetup::L1Wrap".to_string(),
            ),
            (
                CircuitType::L1Wrap,
                true,
                &[Standard],
                format!(
                    "CircuitType::L1Wrap requires exactly ProofProfile::L1Wrap, got {:?}",
                    set(&[Standard])
                ),
            ),
            (
                CircuitType::L1Wrap,
                true,
                &[L1Wrap, Compression],
                format!(
                    "CircuitType::L1Wrap requires exactly ProofProfile::L1Wrap, got {:?}",
                    set(&[Compression, L1Wrap])
                ),
            ),
            (
                UNIFIED,
                false,
                &[Standard, L1Wrap],
                format!("ProofProfile::L1Wrap requires CircuitType::L1Wrap, got {UNIFIED:?}"),
            ),
            (
                inits_and_teardowns,
                false,
                &[Compression],
                compression_message(inits_and_teardowns),
            ),
            (
                memory,
                false,
                &[Standard, Compression],
                compression_message(memory),
            ),
            (
                delegation,
                false,
                &[Compression],
                compression_message(delegation),
            ),
            (
                UNIFIED,
                false,
                &[Compression, Standard, Compression],
                compression_message(UNIFIED),
            ),
            (UNIFIED, false, &[Compression], compression_message(UNIFIED)),
            (
                UNIFIED22,
                false,
                &[Standard],
                unified22_message(&[Standard]),
            ),
            (
                UNIFIED22,
                false,
                &[Standard, Compression],
                unified22_message(&[Standard, Compression]),
            ),
        ];
        for (circuit, is_l1_wrap_setup, profiles, expected) in cases {
            assert_eq!(
                panic_message(|| {
                    validate_profile_set(circuit, is_l1_wrap_setup, profiles);
                }),
                expected
            );
        }
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
