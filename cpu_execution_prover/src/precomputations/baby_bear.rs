use super::{CpuCircuitPrecomputations, CpuPrecomputed};
use crate::upstream::{
    CircuitSetup, CpuGKRSetup, DefaultTreeConstructor, GKRCircuitArtifact, MerkleTreeCapVarLength,
    ProverConfig, SetupCommitment, TableDriver, TwiddleSetOps, UnrolledCircuitWitnessEvalFn, BF,
};
use execution_prover::backend::CircuitPrecomputation;
use execution_prover::config::SoundnessMode;
use execution_prover::setup::CanonicalCircuitSetup;
use execution_prover::ProofProfile;
use execution_prover_model::circuit_type::CircuitType;
use std::alloc::Global;
use std::collections::BTreeMap;
use std::ops::Deref;
use std::sync::{Arc, OnceLock};
use worker::Worker;

pub struct Precomputed {
    /// The config of every declared profile: `Standard` from the selected mode and the
    /// compiled columns, the L1 profiles from their special configs.
    configs: BTreeMap<ProofProfile, ProverConfig>,
    pub(crate) compiled_circuit: Arc<GKRCircuitArtifact<BF>>,
    pub(crate) setup: CpuGKRSetup<BF>,
    pub(crate) table_driver: TableDriver<BF>,
    /// `None` for delegation circuits and standalone inits-and-teardowns.
    pub(crate) witness_eval_fn: Option<UnrolledCircuitWitnessEvalFn<Global>>,
    pub(crate) trace_len: usize,
    setup_commitments:
        OnceLock<BTreeMap<ProofProfile, SetupCommitment<BF, DefaultTreeConstructor>>>,
}

impl Deref for CpuCircuitPrecomputations {
    type Target = Precomputed;

    fn deref(&self) -> &Self::Target {
        match &*self.0 {
            CpuPrecomputed::BabyBear(precomputed) => precomputed,
            CpuPrecomputed::L1Wrap(_) => {
                panic!("BabyBear precomputations are not defined for L1Wrap")
            }
        }
    }
}

impl CpuCircuitPrecomputations {
    /// The config of a declared profile. The soundness mode is bound when these immutable
    /// configs are prepared.
    pub(crate) fn config(&self, profile: ProofProfile) -> &ProverConfig {
        self.configs
            .get(&profile)
            .unwrap_or_else(|| panic!("ProofProfile::{profile:?} was not declared for this binary"))
    }

    /// The largest WHIR message among the declared profiles: the twiddle size setup
    /// initialization needs.
    pub(crate) fn max_whir_message_size_log2(&self) -> usize {
        self.configs
            .values()
            .map(ProverConfig::whir_message_size_log2)
            .max()
            .expect("a prepared circuit declares at least one profile")
    }

    pub(crate) fn initialize_setup<T: TwiddleSetOps<BF>>(
        &self,
        twiddles: &T,
        worker: &Worker,
    ) -> &BTreeMap<ProofProfile, SetupCommitment<BF, DefaultTreeConstructor>> {
        self.setup_commitments.get_or_init(|| {
            self.configs
                .iter()
                .map(|(&profile, config)| {
                    let commitment = self.setup.commit_for_config::<DefaultTreeConstructor>(
                        twiddles.plain(),
                        config,
                        worker,
                    );
                    (profile, commitment)
                })
                .collect()
        })
    }

    pub(crate) fn setup_commitment(
        &self,
        profile: ProofProfile,
    ) -> &SetupCommitment<BF, DefaultTreeConstructor> {
        self.setup_commitments
            .get()
            .expect("setup initialization must run before a setup commitment is read")
            .get(&profile)
            .unwrap_or_else(|| panic!("ProofProfile::{profile:?} was not declared for this binary"))
    }
}

/// `Standard` resolves the selected mode from the compiled columns; the L1 profiles use
/// their special configs.
fn profile_configs(
    circuit_type: CircuitType,
    compiled: &GKRCircuitArtifact<BF>,
    soundness_mode: SoundnessMode,
    profiles: &[ProofProfile],
) -> BTreeMap<ProofProfile, ProverConfig> {
    profiles
        .iter()
        .map(|&profile| {
            let config = execution_prover::config::prover_config_in_mode(
                circuit_type,
                compiled,
                profile,
                soundness_mode,
            );
            (profile, config)
        })
        .collect()
}

impl Precomputed {
    pub(super) fn new(
        circuit_type: CircuitType,
        setup: CanonicalCircuitSetup,
        soundness_mode: SoundnessMode,
        profiles: &[ProofProfile],
    ) -> Self {
        let precomputed = match setup {
            CanonicalCircuitSetup::Riscv(CircuitSetup {
                family_idx: _,
                geometry: _,
                trace_len,
                compiled_circuit,
                table_driver,
                setup,
                witness_eval_fn,
            }) => Self {
                configs: profile_configs(circuit_type, &compiled_circuit, soundness_mode, profiles),
                compiled_circuit: Arc::new(compiled_circuit),
                setup,
                table_driver,
                witness_eval_fn,
                trace_len,
                setup_commitments: OnceLock::new(),
            },
            CanonicalCircuitSetup::Delegation(setup) => Self {
                configs: profile_configs(
                    circuit_type,
                    &setup.compiled_circuit,
                    soundness_mode,
                    profiles,
                ),
                compiled_circuit: Arc::new(setup.compiled_circuit),
                setup: setup.setup,
                table_driver: setup.table_driver,
                witness_eval_fn: None,
                trace_len: setup.trace_len,
                setup_commitments: OnceLock::new(),
            },
            CanonicalCircuitSetup::L1Wrap(_) => {
                panic!("an L1 wrap setup has no BabyBear precomputations")
            }
        };
        assert_eq!(
            precomputed.trace_len,
            circuit_type.get_domain_size(),
            "setup trace length disagrees with CircuitType geometry for {circuit_type:?}"
        );
        precomputed
    }

    pub(crate) fn trace_len_log2(&self) -> usize {
        self.trace_len.trailing_zeros() as usize
    }
}

impl CircuitPrecomputation for CpuCircuitPrecomputations {
    fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>> {
        &self.compiled_circuit
    }

    fn setup_cap(&self, profile: ProofProfile) -> Option<MerkleTreeCapVarLength> {
        if self.setup.hypercube_evals.is_empty() {
            return None;
        }
        let commitment = self.setup_commitment(profile);
        Some(commitment.get_cap())
    }
}
