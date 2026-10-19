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
    CpuGKRSetup, ProofProfile, ProverConfig, SecurityLevel, UnrolledCircuitWitnessEvalFn,
};
use execution_prover::setup::CanonicalCircuitSetup;
use gpu_trace::witness::circuit_type::UnrolledCircuitType;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex, OnceLock};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SetupGeometry {
    pub log_lde_factor: u32,
    pub log_rows_per_leaf: u32,
    pub log_tree_cap_size: u32,
}

impl SetupGeometry {
    fn from_config(config: &ProverConfig) -> Self {
        Self {
            log_lde_factor: config.lde_factor.trailing_zeros(),
            log_rows_per_leaf: config.base_oracles_values_per_leaf.trailing_zeros(),
            log_tree_cap_size: config.cap_size.trailing_zeros(),
        }
    }
}

pub(crate) fn setup_geometries(
    circuit_type: CircuitType,
    profiles: &[ProofProfile],
    security_level: SecurityLevel,
) -> BTreeMap<ProofProfile, SetupGeometry> {
    profiles
        .iter()
        .map(|&profile| {
            let config =
                gpu_circuit_prover::config::prover_config(circuit_type, profile, security_level)
                    .expect("unsupported GPU security level");
            (profile, SetupGeometry::from_config(&config))
        })
        .collect()
}

struct ProfileSetupCache<S, T> {
    published: OnceLock<BTreeMap<ProofProfile, T>>,
    /// Consumed once every declared profile is built: once the pinned copies
    /// exist the heap copy has no reader.
    source: Mutex<Option<S>>,
    geometries: BTreeMap<ProofProfile, SetupGeometry>,
}

impl<S, T: Clone> ProfileSetupCache<S, T> {
    fn new(source: S, geometries: BTreeMap<ProofProfile, SetupGeometry>) -> Self {
        Self {
            published: OnceLock::new(),
            source: Mutex::new(Some(source)),
            geometries,
        }
    }

    fn get_or_try_init<E>(
        &self,
        mut build: impl FnMut(&S, SetupGeometry) -> Result<T, E>,
    ) -> Result<(), E> {
        self.published
            .get_or_try_init(|| {
                let mut source = self.source.lock().unwrap();
                let borrowed = source
                    .as_ref()
                    .expect("the CPU setup is consumed exactly once");
                let built = self
                    .geometries
                    .iter()
                    .map(|(&profile, &geometry)| Ok((profile, build(borrowed, geometry)?)))
                    .collect::<Result<BTreeMap<_, _>, E>>()?;
                *source = None;
                Ok(built)
            })
            .map(|_| ())
    }

    fn get(&self, profile: ProofProfile) -> T {
        self.published
            .get()
            .expect(
                "setup host must be initialized by a constructor/add_binary setup batch before use",
            )
            .get(&profile)
            .unwrap_or_else(|| panic!("ProofProfile::{profile:?} was not declared for this binary"))
            .clone()
    }
}

pub struct LazyGpuGKRSetupHost {
    cache: ProfileSetupCache<CpuGKRSetup<BF>, Option<Arc<GpuGKRSetupHost>>>,
}

impl LazyGpuGKRSetupHost {
    pub fn new(
        cpu_setup: CpuGKRSetup<BF>,
        geometries: BTreeMap<ProofProfile, SetupGeometry>,
    ) -> Self {
        Self {
            cache: ProfileSetupCache::new(cpu_setup, geometries),
        }
    }

    pub fn get_or_init(&self, context: &ProverContext) -> CudaResult<()> {
        self.cache.get_or_try_init(|cpu_setup, geometry| {
            if cpu_setup.hypercube_evals.is_empty() {
                return Ok(None);
            }
            GpuGKRSetupHost::precompute_from_cpu_setup(
                cpu_setup,
                geometry.log_lde_factor,
                geometry.log_rows_per_leaf,
                geometry.log_tree_cap_size,
                context,
            )
            .map(|host| Some(Arc::new(host)))
        })
    }

    pub fn get_initialized(&self, profile: ProofProfile) -> Option<Arc<GpuGKRSetupHost>> {
        self.cache.get(profile)
    }
}

pub(crate) fn validate_profiles(
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
        !is_l1_wrap_setup || circuit_type == CircuitType::L1Wrap21,
        "CanonicalCircuitSetup::L1Wrap requires CircuitType::L1Wrap21, got {circuit_type:?}"
    );
    if circuit_type == CircuitType::L1Wrap21 {
        assert!(
            is_l1_wrap_setup,
            "CircuitType::L1Wrap21 requires CanonicalCircuitSetup::L1Wrap"
        );
        assert!(
            profiles.iter().eq([ProofProfile::L1Wrap].iter()),
            "CircuitType::L1Wrap21 requires exactly ProofProfile::L1Wrap, got {profiles:?}"
        );
        return profiles;
    }
    assert!(
        !profiles.contains(&ProofProfile::L1Wrap),
        "ProofProfile::L1Wrap requires CircuitType::L1Wrap21, got {circuit_type:?}"
    );
    const UNIFIED22: CircuitType = CircuitType::Unrolled(UnrolledCircuitType::Unified22);
    assert!(
        !profiles.contains(&ProofProfile::L1Feeder) || circuit_type == UNIFIED22,
        "ProofProfile::L1Feeder requires CircuitType::Unrolled(UnrolledCircuitType::Unified22), got {circuit_type:?}"
    );
    assert!(
        circuit_type != UNIFIED22 || profiles.iter().eq([ProofProfile::L1Feeder].iter()),
        "CircuitType::Unrolled(UnrolledCircuitType::Unified22) requires exactly ProofProfile::L1Feeder, got {profiles:?}"
    );
    assert!(
        !profiles.contains(&ProofProfile::L1FeederA)
            || circuit_type == CircuitType::Unrolled(UnrolledCircuitType::Unified),
        "ProofProfile::L1FeederA requires CircuitType::Unrolled(UnrolledCircuitType::Unified), got {circuit_type:?}"
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
}

#[derive(Clone)]
pub enum CircuitPrecomputations {
    BabyBear(BabyBearPrecomputations),
    L1Wrap(Arc<L1WrapPrecomputed>),
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
        security_level: SecurityLevel,
        profiles: &[ProofProfile],
    ) -> CudaResult<Self> {
        let (compiled_circuit, cpu_setup, decoder_table) = match setup {
            CanonicalCircuitSetup::L1Wrap(setup) => {
                return Ok(Self::L1Wrap(Arc::new(L1WrapPrecomputed::new(
                    circuit_type,
                    setup,
                    security_level,
                )?)));
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
        let gkr_programs = Arc::new(
            GkrPrograms::compile(circuit_type, Arc::clone(&compiled_circuit))
                .unwrap_or_else(|error| panic!("{circuit_type:?} GKR programs: {error}")),
        );
        let setup_host = Arc::new(LazyGpuGKRSetupHost::new(
            cpu_setup,
            setup_geometries(circuit_type, profiles, security_level),
        ));
        let decoder_host = match decoder_table.as_deref() {
            Some(rows) => decoder_host(rows)?,
            None => None,
        };
        Ok(Self::BabyBear(BabyBearPrecomputations {
            gkr_programs,
            setup_host,
            decoder_host,
        }))
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use gpu_trace::witness::circuit_type::{DelegationCircuitType, UnrolledMemoryCircuitType};
    use std::panic::{catch_unwind, AssertUnwindSafe};
    use ProofProfile::{L1Feeder, L1FeederA, L1Wrap, Standard};

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
    fn cpu_m8_validate_profiles() {
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
            validate_profile_set(UNIFIED, false, &[L1FeederA, Standard, L1FeederA]),
            set(&[Standard, L1FeederA])
        );
        for circuit in [inits_and_teardowns, memory, delegation, UNIFIED22] {
            assert!(catch_unwind(|| validate_profile_set(circuit, false, &[L1FeederA])).is_err());
        }
        for circuit in [inits_and_teardowns, memory, delegation] {
            assert_eq!(
                validate_profile_set(circuit, false, &[Standard, Standard]),
                set(&[Standard])
            );
        }
        assert_eq!(
            validate_profile_set(CircuitType::L1Wrap21, true, &[L1Wrap, L1Wrap]),
            set(&[L1Wrap])
        );
        assert_eq!(
            validate_profile_set(UNIFIED22, false, &[L1Feeder, L1Feeder]),
            set(&[L1Feeder])
        );
        let feeder_message = |circuit: CircuitType| {
            format!("ProofProfile::L1Feeder requires CircuitType::Unrolled(UnrolledCircuitType::Unified22), got {circuit:?}")
        };
        let unified22_message = |profiles: &[ProofProfile]| {
            format!(
                "CircuitType::Unrolled(UnrolledCircuitType::Unified22) requires exactly ProofProfile::L1Feeder, got {:?}",
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
                CircuitType::L1Wrap21,
                true,
                &[],
                "prepare needs at least one ProofProfile".to_string(),
            ),
            (
                UNIFIED,
                true,
                &[Standard],
                format!(
                    "CanonicalCircuitSetup::L1Wrap requires CircuitType::L1Wrap21, got {UNIFIED:?}"
                ),
            ),
            (
                CircuitType::L1Wrap21,
                false,
                &[L1Wrap],
                "CircuitType::L1Wrap21 requires CanonicalCircuitSetup::L1Wrap".to_string(),
            ),
            (
                CircuitType::L1Wrap21,
                true,
                &[Standard],
                format!(
                    "CircuitType::L1Wrap21 requires exactly ProofProfile::L1Wrap, got {:?}",
                    set(&[Standard])
                ),
            ),
            (
                CircuitType::L1Wrap21,
                true,
                &[L1Wrap, L1Feeder],
                format!(
                    "CircuitType::L1Wrap21 requires exactly ProofProfile::L1Wrap, got {:?}",
                    set(&[L1Feeder, L1Wrap])
                ),
            ),
            (
                UNIFIED,
                false,
                &[Standard, L1Wrap],
                format!("ProofProfile::L1Wrap requires CircuitType::L1Wrap21, got {UNIFIED:?}"),
            ),
            (
                inits_and_teardowns,
                false,
                &[L1Feeder],
                feeder_message(inits_and_teardowns),
            ),
            (memory, false, &[Standard, L1Feeder], feeder_message(memory)),
            (delegation, false, &[L1Feeder], feeder_message(delegation)),
            (
                UNIFIED,
                false,
                &[L1Feeder, Standard, L1Feeder],
                feeder_message(UNIFIED),
            ),
            (UNIFIED, false, &[L1Feeder], feeder_message(UNIFIED)),
            (
                UNIFIED22,
                false,
                &[Standard],
                unified22_message(&[Standard]),
            ),
            (
                UNIFIED22,
                false,
                &[Standard, L1Feeder],
                unified22_message(&[Standard, L1Feeder]),
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

    #[test]
    fn cpu_m8_setup_cache_publication() {
        let mut geometries = setup_geometries(UNIFIED, &[Standard], SecurityLevel::Sec100);
        geometries.extend(setup_geometries(
            UNIFIED22,
            &[L1Feeder],
            SecurityLevel::Sec100,
        ));
        let feeder = geometries[&L1Feeder];
        assert_ne!(geometries[&Standard], feeder);
        let cache =
            ProfileSetupCache::<Vec<u32>, (u32, SetupGeometry)>::new(vec![7], geometries.clone());
        let mut built = Vec::new();
        let error = cache
            .get_or_try_init(|source, geometry| {
                built.push(geometry);
                if geometry == feeder {
                    Err("feeder setup build failed")
                } else {
                    Ok((source[0], geometry))
                }
            })
            .unwrap_err();
        assert_eq!(error, "feeder setup build failed");
        assert_eq!(built, [geometries[&Standard], feeder]);
        assert!(cache.published.get().is_none());
        assert!(cache.source.lock().unwrap().is_some());
        cache
            .get_or_try_init(|source, geometry| Ok::<_, &str>((source[0], geometry)))
            .unwrap();
        assert!(cache.source.lock().unwrap().is_none());
        assert_eq!(cache.get(Standard), (7, geometries[&Standard]));
        assert_eq!(cache.get(L1Feeder), (7, feeder));
        cache
            .get_or_try_init(|_, _| -> Result<(u32, SetupGeometry), &str> {
                panic!("a published setup cache is never rebuilt")
            })
            .unwrap();
        assert_eq!(
            panic_message(|| {
                cache.get(L1Wrap);
            }),
            "ProofProfile::L1Wrap was not declared for this binary"
        );
        let uninitialized = ProfileSetupCache::<(), ()>::new((), geometries);
        assert_eq!(
            panic_message(|| uninitialized.get(Standard)),
            "setup host must be initialized by a constructor/add_binary setup batch before use"
        );
    }

    #[test]
    fn cpu_m8_feeder_geometry() {
        let mut geometries =
            setup_geometries(UNIFIED, &[Standard, L1FeederA], SecurityLevel::Sec100);
        geometries.extend(setup_geometries(
            UNIFIED22,
            &[L1Feeder],
            SecurityLevel::Sec100,
        ));
        assert!(geometries.keys().eq([Standard, L1Feeder, L1FeederA].iter()));
        assert_ne!(geometries[&L1Feeder], geometries[&Standard]);
        assert_ne!(geometries[&L1FeederA], geometries[&Standard]);
        assert_ne!(geometries[&L1FeederA], geometries[&L1Feeder]);
        let cache = ProfileSetupCache::<(), SetupGeometry>::new((), geometries.clone());
        cache
            .get_or_try_init(|_, geometry| Ok::<_, &str>(geometry))
            .unwrap();
        assert_eq!(cache.get(Standard), geometries[&Standard]);
        assert_eq!(cache.get(L1FeederA), geometries[&L1FeederA]);
        assert_eq!(cache.get(L1Feeder), geometries[&L1Feeder]);
        for (&profile, geometry) in &geometries {
            let circuit = if profile == L1Feeder {
                UNIFIED22
            } else {
                UNIFIED
            };
            let config =
                gpu_circuit_prover::config::prover_config(circuit, profile, SecurityLevel::Sec100)
                    .unwrap();
            assert_eq!(1usize << geometry.log_lde_factor, config.lde_factor);
            assert_eq!(1usize << geometry.log_tree_cap_size, config.cap_size);
            assert_eq!(
                geometry.log_rows_per_leaf as usize,
                config.whir_schedule.whir_steps_schedule[0]
            );
        }
    }
}
