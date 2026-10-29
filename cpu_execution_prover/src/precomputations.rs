use crate::upstream::{
    CircuitSetup, ColumnMajorBaseOracleForLDE, CosetByCosetBaseCommitment, CpuGKRSetup,
    DefaultTreeConstructor, GKRCircuitArtifact, Keccak256MerkleTreeWithCap, L1WrapSetup,
    MerkleTreeCapVarLength, Proth120, ProverConfig, SecurityLevel, SetupCommitment, TableDriver,
    TwiddleSetOps, Twiddles, UnrolledCircuitWitnessEvalFn, BF,
};
use execution_prover::backend::CircuitPrecomputation;
use execution_prover::config::{ProvingSelection, SelectionError};
use execution_prover::setup::CanonicalCircuitSetup;
use execution_prover::{prover_config, ProofProfile};
use execution_prover_model::circuit_type::CircuitType;
use std::alloc::Global;
use std::collections::BTreeMap;
use std::ops::Deref;
use std::sync::{Arc, OnceLock};
use worker::Worker;

#[derive(Clone)]
pub struct CpuCircuitPrecomputations(Arc<CpuPrecomputed>);

enum CpuPrecomputed {
    BabyBear(Box<Precomputed>),
    L1Wrap(Box<L1WrapPrecomputed>),
}

pub(crate) struct L1WrapPrecomputed {
    pub(crate) circuit_type: CircuitType,
    pub(crate) setup: L1WrapSetup,
    committed: OnceLock<L1WrapCommittedSetup>,
}

pub(crate) struct L1WrapCommittedSetup {
    pub(crate) commitment: SetupCommitment<Proth120, Keccak256MerkleTreeWithCap>,
    pub(crate) twiddles: Twiddles<Proth120, Global>,
    pub(crate) config: ProverConfig,
}

impl L1WrapPrecomputed {
    pub(crate) fn initialize_setup(&self, security_level: SecurityLevel, worker: &Worker) {
        let config = prover_config(self.circuit_type, ProofProfile::L1Wrap, security_level);
        self.committed
            .get_or_init(|| L1WrapCommittedSetup::new(&self.setup.setup, config, worker));
    }

    pub(crate) fn committed(&self) -> &L1WrapCommittedSetup {
        self.committed
            .get()
            .expect("L1Wrap setup initialization must run before proving")
    }
}

impl L1WrapCommittedSetup {
    fn new(setup: &CpuGKRSetup<Proth120>, config: ProverConfig, worker: &Worker) -> Self {
        let pack_log2 = config.pack_log2();
        let twiddles = Twiddles::new(1 << config.whir_message_size_log2(), worker);
        let inputs: Vec<&[Proth120]> = setup
            .hypercube_evals
            .iter()
            .map(|column| &column[..])
            .collect();
        let oracle =
            ColumnMajorBaseOracleForLDE::CosetRecompute(CosetByCosetBaseCommitment::commit_packed(
                &inputs,
                &twiddles,
                config.lde_factor(),
                config.base_oracles_values_per_leaf().trailing_zeros() as usize,
                config.cap_size,
                config.trace_len_log2,
                pack_log2,
                worker,
            ));
        Self {
            commitment: SetupCommitment::InMemory(oracle),
            twiddles,
            config,
        }
    }
}

pub struct Precomputed {
    circuit_type: CircuitType,
    selection: ProvingSelection,
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
    pub(crate) fn from_canonical(
        circuit_type: CircuitType,
        setup: CanonicalCircuitSetup,
        selection: ProvingSelection,
        profiles: &[ProofProfile],
    ) -> Result<Self, SelectionError> {
        let configs = match &setup {
            CanonicalCircuitSetup::L1Wrap(_) => BTreeMap::new(),
            CanonicalCircuitSetup::Riscv(CircuitSetup {
                compiled_circuit, ..
            }) => profile_configs(circuit_type, compiled_circuit, selection, profiles)?,
            CanonicalCircuitSetup::Delegation(setup) => {
                profile_configs(circuit_type, &setup.compiled_circuit, selection, profiles)?
            }
        };
        let precomputed = match setup {
            CanonicalCircuitSetup::L1Wrap(setup) => {
                assert!(
                    circuit_type.is_l1_wrap(),
                    "an L1 wrap setup needs an L1 wrap circuit, got {circuit_type:?}"
                );
                assert!(
                    setup.trace_len == circuit_type.get_domain_size()
                        && setup.rom == circuit_type.rom(),
                    "L1 wrap setup (trace {}, {:?}) disagrees with {circuit_type:?}",
                    setup.trace_len,
                    setup.rom
                );
                return Ok(Self(Arc::new(CpuPrecomputed::L1Wrap(Box::new(
                    L1WrapPrecomputed {
                        circuit_type,
                        setup,
                        committed: OnceLock::new(),
                    },
                )))));
            }
            CanonicalCircuitSetup::Riscv(CircuitSetup {
                family_idx: _,
                geometry: _,
                trace_len,
                compiled_circuit,
                table_driver,
                setup,
                witness_eval_fn,
                prover_configs: _,
            }) => Precomputed {
                circuit_type,
                selection,
                configs: configs.clone(),
                compiled_circuit: Arc::new(compiled_circuit),
                setup,
                table_driver,
                witness_eval_fn,
                trace_len,
                setup_commitments: OnceLock::new(),
            },
            CanonicalCircuitSetup::Delegation(setup) => Precomputed {
                circuit_type,
                selection,
                configs: configs.clone(),
                compiled_circuit: Arc::new(setup.compiled_circuit),
                setup: setup.setup,
                table_driver: setup.table_driver,
                witness_eval_fn: None,
                trace_len: setup.trace_len,
                setup_commitments: OnceLock::new(),
            },
        };
        assert_eq!(
            precomputed.trace_len,
            circuit_type.get_domain_size(),
            "setup trace length disagrees with CircuitType geometry for {circuit_type:?}"
        );
        Ok(Self(Arc::new(CpuPrecomputed::BabyBear(Box::new(
            precomputed,
        )))))
    }

    pub(crate) fn config_for_request(
        &self,
        circuit_type: CircuitType,
        selection: ProvingSelection,
        profile: ProofProfile,
    ) -> Result<&ProverConfig, SelectionError> {
        if self.circuit_type != circuit_type {
            return Err(SelectionError::PreparedCircuitMismatch {
                prepared: self.circuit_type,
                requested: circuit_type,
            });
        }
        if self.selection != selection {
            return Err(SelectionError::PreparedSelectionMismatch {
                prepared: self.selection,
                requested: selection,
            });
        }
        Ok(self.configs.get(&profile).unwrap_or_else(|| {
            panic!("ProofProfile::{profile:?} was not declared for this binary")
        }))
    }

    /// The largest WHIR message among the declared profiles (the twiddle size setup
    /// initialization needs), after the same circuit/selection checks as
    /// [`Self::config_for_request`].
    pub(crate) fn whir_message_size_log2_for_request(
        &self,
        circuit_type: CircuitType,
        selection: ProvingSelection,
    ) -> Result<usize, SelectionError> {
        let any = *self
            .configs
            .keys()
            .next()
            .expect("a prepared circuit declares at least one profile");
        self.config_for_request(circuit_type, selection, any)?;
        Ok(self
            .configs
            .values()
            .map(ProverConfig::whir_message_size_log2)
            .max()
            .expect("a prepared circuit declares at least one profile"))
    }

    pub(crate) fn l1_wrap(&self) -> &L1WrapPrecomputed {
        match &*self.0 {
            CpuPrecomputed::L1Wrap(precomputed) => precomputed,
            CpuPrecomputed::BabyBear(_) => panic!("L1Wrap requires Proth precomputations"),
        }
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
    selection: ProvingSelection,
    profiles: &[ProofProfile],
) -> Result<BTreeMap<ProofProfile, ProverConfig>, SelectionError> {
    profiles
        .iter()
        .map(|&profile| {
            let config = match profile {
                ProofProfile::Standard => {
                    circuit_type.try_prover_config_in_mode(compiled, selection)?
                }
                l1 => prover_config(circuit_type, l1, selection.security_level),
            };
            Ok((profile, config))
        })
        .collect()
}

impl Precomputed {
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

#[cfg(test)]
mod tests {
    use super::*;
    use execution_prover::config::SoundnessMode;
    use execution_prover::setup::build_delegation_setup;
    use execution_prover_model::circuit_type::DelegationCircuitType;

    #[test]
    fn prepared_selection_mismatch_is_rejected() {
        let worker = Worker::new_with_num_threads(1);
        let delegation = DelegationCircuitType::Blake2GFunction;
        let circuit = CircuitType::Delegation(delegation);
        for &mode in SoundnessMode::ALL {
            let selection = ProvingSelection {
                soundness_mode: mode,
                ..ProvingSelection::default()
            };
            let prepared = CpuCircuitPrecomputations::from_canonical(
                circuit,
                build_delegation_setup(delegation, &worker),
                selection,
                &[ProofProfile::Standard],
            )
            .unwrap();
            let config = prepared
                .config_for_request(circuit, selection, ProofProfile::Standard)
                .unwrap();
            assert_eq!(
                config,
                &circuit
                    .try_prover_config_in_mode(prepared.compiled_circuit(), selection)
                    .unwrap()
            );
            let clone = prepared.clone();
            assert!(core::ptr::eq(
                config,
                clone
                    .config_for_request(circuit, selection, ProofProfile::Standard)
                    .unwrap()
            ));
            assert!(prepared.setup_commitments.get().is_none());
            let other_mode = if mode == SoundnessMode::PessimisticConjecture {
                SoundnessMode::EthproofsSoundnessCalc
            } else {
                SoundnessMode::PessimisticConjecture
            };
            let requested = ProvingSelection {
                soundness_mode: other_mode,
                ..selection
            };
            assert!(matches!(
                prepared.config_for_request(circuit, requested, ProofProfile::Standard),
                Err(SelectionError::PreparedSelectionMismatch { .. })
            ));
            assert!(matches!(
                prepared.config_for_request(
                    CircuitType::Delegation(DelegationCircuitType::BigIntWithControl),
                    selection,
                    ProofProfile::Standard,
                ),
                Err(SelectionError::PreparedCircuitMismatch { .. })
            ));
            assert!(prepared.setup_commitments.get().is_none());
        }
    }
}
