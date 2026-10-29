use gpu_core::primitives::field::BF;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_uninit, StaticPinnedBox};
use gpu_gkr::setup::GpuGKRSetupHost;
use gpu_gkr::GkrPrograms;
use gpu_prover_context::ProverContext;
use gpu_trace::trace::memory::uses_base_commitment_geometry;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::trace_unrolled::ExecutorFamilyDecoderData;

use era_cudart::result::CudaResult;

use super::l1_wrap::L1WrapPrecomputed;
use crate::upstream::{
    BaseColumns, BaseCommitmentGeometry, CommitmentMode, CpuGKRSetup, GKRCircuitArtifact,
    MerkleTreeCapVarLength, PrimeField, ProofProfile, ProverConfig, SecurityLevel,
    UnrolledCircuitWitnessEvalFn,
};
use execution_prover::config::{ProvingSelection, SelectionError};
use execution_prover::setup::CanonicalCircuitSetup;
use gpu_trace::witness::circuit_type::UnrolledCircuitType;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex, OnceLock};

#[cfg(test)]
mod tests;

/// Immutable CPU-selected configuration shared by setup and both worker phases.
pub(crate) struct ResolvedProverConfig<F: PrimeField> {
    circuit_type: CircuitType,
    circuit: Arc<GKRCircuitArtifact<F>>,
    selection: ProvingSelection,
    config: ProverConfig,
    geometry: BaseCommitmentGeometry,
}

impl<F: PrimeField> ResolvedProverConfig<F> {
    /// Pessimistic-conjecture compatibility constructor.
    #[cfg(test)]
    fn new(
        circuit_type: CircuitType,
        circuit: Arc<GKRCircuitArtifact<F>>,
        config: ProverConfig,
    ) -> Self {
        let selection = ProvingSelection {
            security_level: config.security_level,
            soundness_mode: execution_prover::config::SoundnessMode::PessimisticConjecture,
        };
        Self::for_selection(circuit_type, circuit, selection, config)
    }

    fn for_selection(
        circuit_type: CircuitType,
        circuit: Arc<GKRCircuitArtifact<F>>,
        selection: ProvingSelection,
        config: ProverConfig,
    ) -> Self {
        assert_eq!(
            selection.security_level, config.security_level,
            "selection security level differs from its config"
        );
        let geometry = BaseCommitmentGeometry::from_config(&config, BaseColumns::of(&circuit))
            .expect("invalid canonical commitment geometry");
        Self {
            circuit_type,
            circuit,
            selection,
            config,
            geometry,
        }
    }

    /// Divergence guard: a request is served only under the selection its
    /// precomputations were resolved for.
    pub(crate) fn validate_selection(&self, selection: ProvingSelection) {
        assert_eq!(
            selection, self.selection,
            "request selection differs from resolved config"
        );
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
        }
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SetupGeometry {
    pub log_lde_factor: u32,
    pub log_rows_per_leaf: u32,
    pub log_tree_cap_size: u32,
}

#[cfg(test)]
impl SetupGeometry {
    fn from_config(config: &ProverConfig) -> Self {
        Self {
            log_lde_factor: config.lde_factor().trailing_zeros(),
            log_rows_per_leaf: config.base_oracles_values_per_leaf().trailing_zeros(),
            log_tree_cap_size: config.cap_size.trailing_zeros(),
        }
    }
}

#[cfg(test)]
fn setup_geometries(
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

struct ProfileSetupCache<S, T, G> {
    published: OnceLock<BTreeMap<ProofProfile, T>>,
    /// Consumed once every declared profile is built: once the pinned copies
    /// exist the heap copy has no reader.
    source: Mutex<Option<S>>,
    geometries: BTreeMap<ProofProfile, G>,
}

impl<S, T: Clone, G: Copy> ProfileSetupCache<S, T, G> {
    fn new(source: S, geometries: BTreeMap<ProofProfile, G>) -> Self {
        Self {
            published: OnceLock::new(),
            source: Mutex::new(Some(source)),
            geometries,
        }
    }

    fn get_or_try_init<E>(&self, mut build: impl FnMut(&S, G) -> Result<T, E>) -> Result<(), E> {
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
    cache: ProfileSetupCache<CpuGKRSetup<BF>, Option<Arc<GpuGKRSetupHost>>, BaseCommitmentGeometry>,
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
            cache: ProfileSetupCache::new(cpu_setup, geometries),
        }
    }

    pub fn base_commitment_geometry(&self, profile: ProofProfile) -> BaseCommitmentGeometry {
        *self
            .cache
            .geometries
            .get(&profile)
            .unwrap_or_else(|| panic!("ProofProfile::{profile:?} was not declared for this binary"))
    }

    pub fn validate_config(
        &self,
        profile: ProofProfile,
        config: &ProverConfig,
        columns: BaseColumns,
    ) {
        let requested = BaseCommitmentGeometry::from_config(config, columns)
            .expect("invalid requested setup cache geometry");
        assert_eq!(
            requested,
            self.base_commitment_geometry(profile),
            "setup cache commitment geometry mismatch"
        );
    }

    pub fn get_or_init(&self, context: &ProverContext) -> CudaResult<()> {
        self.cache.get_or_try_init(|cpu_setup, geometry| {
            if cpu_setup.hypercube_evals.is_empty() {
                return Ok(None);
            }
            let host = if uses_base_commitment_geometry(&geometry) {
                if geometry.commitment_mode() == CommitmentMode::MergedMemoryAndWitness {
                    gpu_circuit_prover::proof::merged_commitment::validate_merged_packed_geometry(
                        &geometry,
                    );
                } else {
                    gpu_trace::trace::memory::validate_separate_base_commitment_geometry(&geometry);
                }
                GpuGKRSetupHost::precompute_for_geometry(cpu_setup, geometry, context)?
            } else {
                GpuGKRSetupHost::precompute_from_cpu_setup(
                    cpu_setup,
                    geometry.lde_factor().trailing_zeros(),
                    geometry.values_per_leaf().trailing_zeros(),
                    geometry.cap_size().trailing_zeros(),
                    context,
                )?
            };
            Ok(Some(Arc::new(host)))
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
    resolved_configs: BTreeMap<ProofProfile, Arc<ResolvedProverConfig<BF>>>,
}

#[derive(Clone)]
pub enum CircuitPrecomputations {
    BabyBear(BabyBearPrecomputations),
    L1Wrap(Arc<L1WrapPrecomputed>),
}

impl BabyBearPrecomputations {
    /// Validate host-only request metadata before any transfer constructor.
    /// `caps` distinguishes a proof request from its memory precommit.
    pub(crate) fn admit_inputs_before_transfers(
        &self,
        circuit_type: CircuitType,
        security_level: SecurityLevel,
        profile: ProofProfile,
        caps: Option<&[MerkleTreeCapVarLength]>,
        twiddle_domain_log2: u32,
    ) -> (
        Option<Arc<GpuGKRSetupHost>>,
        Option<Arc<gpu_trace::trace::memory_transfer::GpuGKRMemoryTransferHost>>,
    ) {
        use gpu_trace::trace::memory_transfer::GpuGKRMemoryTransferHost;
        let baby_bear = self;
        let circuit = baby_bear.gkr_programs.compiled_circuit();
        let resolved = baby_bear.resolved_config(profile);
        resolved.validate_request(circuit_type, security_level, circuit);
        assert_eq!(
            baby_bear.gkr_programs.circuit_type(),
            circuit_type,
            "request circuit differs from GKR programs"
        );
        let config = resolved.config();
        let geometry = resolved.geometry();
        baby_bear
            .setup_host
            .validate_config(profile, config, BaseColumns::of(circuit));
        if config.commitment_mode == CommitmentMode::MergedMemoryAndWitness {
            use gpu_circuit_prover::proof::merged_commitment::{
                validate_merged_commitment_geometry, validate_merged_packed_geometry,
            };
            validate_merged_packed_geometry(&geometry);
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
        let setup = baby_bear.setup_host.get_initialized(profile);
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

    pub(crate) fn resolved_configs(
        &self,
    ) -> &BTreeMap<ProofProfile, Arc<ResolvedProverConfig<BF>>> {
        &self.resolved_configs
    }

    pub(crate) fn resolved_config(&self, profile: ProofProfile) -> &ResolvedProverConfig<BF> {
        self.resolved_configs
            .get(&profile)
            .unwrap_or_else(|| panic!("ProofProfile::{profile:?} was not declared for this binary"))
    }
}

impl CircuitPrecomputations {
    pub(crate) fn admit_inputs_before_transfers(
        &self,
        circuit_type: CircuitType,
        security_level: SecurityLevel,
        profile: ProofProfile,
        caps: Option<&[MerkleTreeCapVarLength]>,
        twiddle_domain_log2: u32,
    ) -> (
        Option<Arc<GpuGKRSetupHost>>,
        Option<Arc<gpu_trace::trace::memory_transfer::GpuGKRMemoryTransferHost>>,
    ) {
        self.baby_bear().admit_inputs_before_transfers(
            circuit_type,
            security_level,
            profile,
            caps,
            twiddle_domain_log2,
        )
    }

    /// Divergence guard: a request is served only under the selection its precomputations
    /// were resolved for. The L1 wrap is resolved only under `PessimisticConjecture`.
    pub(crate) fn validate_selection(&self, selection: ProvingSelection) {
        match self {
            Self::BabyBear(precomputations) => {
                for resolved in precomputations.resolved_configs().values() {
                    resolved.validate_selection(selection);
                }
            }
            Self::L1Wrap(_) => assert_eq!(
                selection.soundness_mode,
                execution_prover::config::SoundnessMode::PessimisticConjecture,
                "the L1 wrap is resolved only under PessimisticConjecture"
            ),
        }
    }

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
        selection: ProvingSelection,
        profiles: &[ProofProfile],
    ) -> Result<Self, SelectionError> {
        let (compiled_circuit, cpu_setup, decoder_table) = match setup {
            CanonicalCircuitSetup::L1Wrap(setup) => {
                // The wrap exists only under PessimisticConjecture (deferred product scope):
                // reject any other selection before its pinned allocations.
                ProofProfile::L1Wrap
                    .try_prover_config(circuit_type.get_domain_size_log2() as usize, selection)?;
                return Ok(Self::L1Wrap(Arc::new(
                    L1WrapPrecomputed::new(circuit_type, setup, selection.security_level)
                        .expect("L1 wrap precomputation allocation failed"),
                )));
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
        let resolved_configs = profiles
            .iter()
            .map(|&profile| {
                let config = gpu_circuit_prover::config::prover_config_for_profile_selection(
                    circuit_type,
                    &compiled_circuit,
                    profile,
                    selection,
                )?;
                Ok((
                    profile,
                    Arc::new(ResolvedProverConfig::for_selection(
                        circuit_type,
                        Arc::clone(&compiled_circuit),
                        selection,
                        config,
                    )),
                ))
            })
            .collect::<Result<BTreeMap<_, _>, SelectionError>>()?;
        let gkr_programs = Arc::new(
            GkrPrograms::compile(circuit_type, Arc::clone(&compiled_circuit))
                .unwrap_or_else(|error| panic!("{circuit_type:?} GKR programs: {error}")),
        );
        let setup_host = Arc::new(LazyGpuGKRSetupHost::new(
            cpu_setup,
            resolved_configs
                .iter()
                .map(|(&profile, resolved)| (profile, resolved.geometry()))
                .collect(),
        ));
        let decoder_host = match decoder_table.as_deref() {
            Some(rows) => decoder_host(rows).expect("pinned decoder table allocation failed"),
            None => None,
        };
        Ok(Self::BabyBear(BabyBearPrecomputations {
            gkr_programs,
            setup_host,
            decoder_host,
            resolved_configs,
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
    fn cpu_l1_setup_cache_publication() {
        let mut geometries = setup_geometries(UNIFIED, &[Standard], SecurityLevel::Sec100);
        geometries.extend(setup_geometries(
            UNIFIED22,
            &[L1Feeder],
            SecurityLevel::Sec100,
        ));
        let feeder = geometries[&L1Feeder];
        assert_ne!(geometries[&Standard], feeder);
        let cache = ProfileSetupCache::<Vec<u32>, (u32, SetupGeometry), SetupGeometry>::new(
            vec![7],
            geometries.clone(),
        );
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
        let uninitialized = ProfileSetupCache::<(), (), SetupGeometry>::new((), geometries);
        assert_eq!(
            panic_message(|| uninitialized.get(Standard)),
            "setup host must be initialized by a constructor/add_binary setup batch before use"
        );
    }

    #[test]
    fn cpu_l1_feeder_geometry() {
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
        let cache =
            ProfileSetupCache::<(), SetupGeometry, SetupGeometry>::new((), geometries.clone());
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
            assert_eq!(1usize << geometry.log_lde_factor, config.lde_factor());
            assert_eq!(1usize << geometry.log_tree_cap_size, config.cap_size);
            assert_eq!(
                geometry.log_rows_per_leaf as usize,
                config.whir_schedule.base_folding_log2()
            );
        }
    }

    /// The GPU L1 wrap precomputation refuses ethproofs with the deferred-scope error before its
    /// pinned allocations: under the CUDA stubs (or without a device) any allocation would fail,
    /// so the `Err` also pins the order. The setup is the committed layout with empty tables,
    /// as in `l1_wrap::cpu_tests`, so the test needs no `memory_sweep` feature.
    #[test]
    fn cpu_ethproofs_l1_wrap_precomputation_is_rejected_before_allocation() {
        use execution_prover::config::SoundnessMode;
        use prover::definitions::ProverConfigProfile;
        use prover::gkr::prover_config::example_configs::ConfigSelectionError;
        let setup = crate::upstream::L1WrapSetup {
            circuit: serde_json::from_str(include_str!(
                "../../../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120_2p21.json"
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
        let selection = ProvingSelection {
            security_level: SecurityLevel::Sec100,
            soundness_mode: SoundnessMode::EthproofsSoundnessCalc,
        };
        match CircuitPrecomputations::from_canonical(
            CircuitType::L1Wrap21,
            CanonicalCircuitSetup::L1Wrap(setup),
            selection,
            &[L1Wrap],
        ) {
            Err(SelectionError::ConfigSelection(error)) => {
                assert_eq!(
                    error,
                    ConfigSelectionError::UnsupportedSpecialConfigMode {
                        profile: ProverConfigProfile::EvmProductionPacked,
                        mode: SoundnessMode::EthproofsSoundnessCalc,
                    }
                );
                assert_eq!(
                    error.to_string(),
                    "UnsupportedSpecialConfigMode: ethproofs soundness mode is not implemented for \
                     the L1 feeder/wrap/EVM profile (deferred product scope); requested \
                     EvmProductionPacked"
                );
            }
            Err(other) => panic!("unexpected error: {other}"),
            Ok(_) => panic!("ethproofs L1 wrap precomputations were built"),
        }
    }
}
