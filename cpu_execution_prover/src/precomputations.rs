use crate::config::CpuStoragePolicy;
use crate::upstream::{
    CircuitSetup, ColumnMajorBaseOracleForLDE, CosetByCosetBaseCommitment, CpuGKRSetup,
    DefaultTreeConstructor, GKRCircuitArtifact, Keccak256MerkleTreeWithCap, L1WrapSetup,
    MerkleTreeCapVarLength, Proth120, ProverConfig, SecurityLevel, SetupCommitment, TableDriver,
    TwiddleSetOps, Twiddles, UnrolledCircuitWitnessEvalFn, WhirOracleStorage, BF,
    EVM_PRODUCTION_PACK_LOG2,
};
use execution_prover::backend::CircuitPrecomputation;
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
    BabyBear(Precomputed),
    L1Wrap(L1WrapPrecomputed),
}

pub(crate) struct L1WrapPrecomputed {
    pub(crate) setup: L1WrapSetup,
    committed: OnceLock<L1WrapCommittedSetup>,
}

pub(crate) struct L1WrapCommittedSetup {
    pub(crate) commitment: SetupCommitment<Proth120, Keccak256MerkleTreeWithCap>,
    pub(crate) twiddles: Twiddles<Proth120, Global>,
    pub(crate) config: ProverConfig,
    pub(crate) storage: WhirOracleStorage,
}

impl L1WrapPrecomputed {
    pub(crate) fn initialize_setup(
        &self,
        security_level: SecurityLevel,
        policy: CpuStoragePolicy,
        worker: &Worker,
    ) {
        let config = prover_config(CircuitType::L1Wrap, ProofProfile::L1Wrap, security_level);
        let committed = self
            .committed
            .get_or_init(|| L1WrapCommittedSetup::new(&self.setup.setup, config, policy, worker));
        assert_eq!(
            committed.storage,
            l1_wrap_storage(policy),
            "L1Wrap setup storage policy changed"
        );
    }

    pub(crate) fn committed(&self) -> &L1WrapCommittedSetup {
        self.committed
            .get()
            .expect("L1Wrap setup initialization must run before proving")
    }
}

impl L1WrapCommittedSetup {
    fn new(
        setup: &CpuGKRSetup<Proth120>,
        config: ProverConfig,
        policy: CpuStoragePolicy,
        worker: &Worker,
    ) -> Self {
        let pack_log2 = EVM_PRODUCTION_PACK_LOG2;
        let twiddles = Twiddles::new(1 << (config.trace_len_log2 + pack_log2), worker);
        let storage = l1_wrap_storage(policy);
        let oracle = match policy {
            CpuStoragePolicy::Auto | CpuStoragePolicy::Recompute => {
                let inputs: Vec<&[Proth120]> = setup
                    .hypercube_evals
                    .iter()
                    .map(|column| &column[..])
                    .collect();
                ColumnMajorBaseOracleForLDE::CosetRecompute(
                    CosetByCosetBaseCommitment::commit_packed(
                        &inputs,
                        &twiddles,
                        config.lde_factor,
                        config.base_oracles_values_per_leaf.trailing_zeros() as usize,
                        config.cap_size,
                        config.trace_len_log2,
                        pack_log2,
                        worker,
                    ),
                )
            }
            CpuStoragePolicy::InMemory => setup.commit_packed::<Keccak256MerkleTreeWithCap>(
                &twiddles,
                config.lde_factor,
                config.whir_schedule.whir_steps_schedule[0],
                config.cap_size,
                config.trace_len_log2,
                pack_log2,
                worker,
            ),
        };
        Self {
            commitment: SetupCommitment::InMemory(oracle),
            twiddles,
            config,
            storage,
        }
    }
}

fn l1_wrap_storage(policy: CpuStoragePolicy) -> WhirOracleStorage {
    match policy {
        CpuStoragePolicy::Auto | CpuStoragePolicy::Recompute => {
            WhirOracleStorage::fully_recompute()
        }
        CpuStoragePolicy::InMemory => WhirOracleStorage::fully_in_memory_continuous(),
    }
}

pub struct Precomputed {
    circuit_type: CircuitType,
    profiles: Vec<ProofProfile>,
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
        profiles: &[ProofProfile],
    ) -> Self {
        let precomputed = match setup {
            CanonicalCircuitSetup::L1Wrap(setup) => {
                assert_eq!(
                    circuit_type,
                    CircuitType::L1Wrap,
                    "Proth setup requires CircuitType::L1Wrap"
                );
                assert_eq!(
                    profiles,
                    &[ProofProfile::L1Wrap],
                    "L1Wrap setup requires exactly ProofProfile::L1Wrap"
                );
                assert_eq!(
                    setup.trace_len,
                    circuit_type.get_domain_size(),
                    "L1Wrap setup trace length disagrees with CircuitType geometry"
                );
                return Self(Arc::new(CpuPrecomputed::L1Wrap(L1WrapPrecomputed {
                    setup,
                    committed: OnceLock::new(),
                })));
            }
            CanonicalCircuitSetup::Riscv(CircuitSetup {
                family_idx: _,
                trace_len,
                compiled_circuit,
                table_driver,
                setup,
                witness_eval_fn,
            }) => Precomputed {
                circuit_type,
                profiles: profiles.to_vec(),
                compiled_circuit: Arc::new(compiled_circuit),
                setup,
                table_driver,
                witness_eval_fn,
                trace_len,
                setup_commitments: OnceLock::new(),
            },
            CanonicalCircuitSetup::Delegation(setup) => Precomputed {
                circuit_type,
                profiles: profiles.to_vec(),
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
        assert_ne!(
            circuit_type,
            CircuitType::L1Wrap,
            "L1Wrap requires a Proth setup"
        );
        Self(Arc::new(CpuPrecomputed::BabyBear(precomputed)))
    }

    pub(crate) fn l1_wrap(&self) -> &L1WrapPrecomputed {
        match &*self.0 {
            CpuPrecomputed::L1Wrap(precomputed) => precomputed,
            CpuPrecomputed::BabyBear(_) => panic!("L1Wrap requires Proth precomputations"),
        }
    }

    pub(crate) fn initialize_setup<T: TwiddleSetOps<BF>>(
        &self,
        security_level: SecurityLevel,
        twiddles: &T,
        worker: &Worker,
    ) -> &BTreeMap<ProofProfile, SetupCommitment<BF, DefaultTreeConstructor>> {
        self.setup_commitments.get_or_init(|| {
            let configs: Vec<_> = self
                .profiles
                .iter()
                .map(|&profile| {
                    (
                        profile,
                        prover_config(self.circuit_type, profile, security_level),
                    )
                })
                .collect();
            let (_, max_config) = configs
                .iter()
                .max_by_key(|(_, config)| config.lde_factor)
                .expect("CPU setup needs at least one ProofProfile");
            for (_, config) in &configs {
                assert!(
                    config.cap_size == max_config.cap_size
                        && config.base_oracles_values_per_leaf
                            == max_config.base_oracles_values_per_leaf
                        && config.whir_schedule.whir_steps_schedule[0]
                            == max_config.whir_schedule.whir_steps_schedule[0],
                    "declared profiles must share cap size and leaf width"
                );
            }
            let commitment = self.setup.commit::<DefaultTreeConstructor>(
                twiddles.plain(),
                max_config.lde_factor,
                max_config.whir_schedule.whir_steps_schedule[0],
                max_config.cap_size,
                self.trace_len_log2(),
                worker,
            );
            if configs.len() == 1 {
                return BTreeMap::from([(configs[0].0, commitment)]);
            }
            let base = Arc::new(commitment.into_in_memory_base());
            configs
                .into_iter()
                .map(|(profile, config)| {
                    (
                        profile,
                        SetupCommitment::derived(&base, config.lde_factor, config.cap_size),
                    )
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
        assert!(
            self.profiles.contains(&profile),
            "ProofProfile::{profile:?} was not declared for this binary"
        );
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
    use crate::upstream::PrimeField;

    #[test]
    fn l1_wrap_storage_policy_keeps_intermediates_bounded() {
        for (policy, expected) in [
            (CpuStoragePolicy::Auto, WhirOracleStorage::fully_recompute()),
            (
                CpuStoragePolicy::Recompute,
                WhirOracleStorage::fully_recompute(),
            ),
            (
                CpuStoragePolicy::InMemory,
                WhirOracleStorage::fully_in_memory_continuous(),
            ),
        ] {
            assert_eq!(l1_wrap_storage(policy), expected);
        }
    }

    #[test]
    fn l1_wrap_setup_storage_modes_have_identical_caps_and_queries() {
        let worker = Worker::new_with_num_threads(2);
        let mut config = ProofProfile::L1Wrap.prover_config(22, SecurityLevel::Sec100);
        config.trace_len_log2 = 6;
        let trace_len = 1 << config.trace_len_log2;
        let setup = CpuGKRSetup {
            hypercube_evals: (0..3)
                .map(|column| {
                    let values: Vec<_> = (0..trace_len)
                        .map(|row| {
                            Proth120::from_u32_unchecked((17 * column + row * row + 1) as u32)
                        })
                        .collect();
                    Arc::new(values.into())
                })
                .collect(),
        };
        let direct =
            L1WrapCommittedSetup::new(&setup, config.clone(), CpuStoragePolicy::InMemory, &worker);
        let SetupCommitment::InMemory(direct_oracle @ ColumnMajorBaseOracleForLDE::InMemory(_)) =
            &direct.commitment
        else {
            panic!("InMemory must materialize the packed setup");
        };
        let leaves_per_coset =
            (trace_len << EVM_PRODUCTION_PACK_LOG2) / config.base_oracles_values_per_leaf;
        let indices: Vec<_> = (0..config.lde_factor)
            .flat_map(|coset| [coset * leaves_per_coset, (coset + 1) * leaves_per_coset - 1])
            .collect();
        let expected = direct_oracle.query_many(&indices, &direct.twiddles, &worker);
        for policy in [CpuStoragePolicy::Auto, CpuStoragePolicy::Recompute] {
            let recompute = L1WrapCommittedSetup::new(&setup, config.clone(), policy, &worker);
            assert_eq!(
                recompute.twiddles.domain_size,
                trace_len << EVM_PRODUCTION_PACK_LOG2
            );
            assert_eq!(direct.commitment.get_cap(), recompute.commitment.get_cap());
            let SetupCommitment::InMemory(oracle @ ColumnMajorBaseOracleForLDE::CosetRecompute(_)) =
                &recompute.commitment
            else {
                panic!("Auto/Recompute must retain only the packed setup monomials and top tree");
            };
            let actual = oracle.query_many(&indices, &recompute.twiddles, &worker);
            assert_eq!(actual.len(), expected.len());
            for ((values, query), (expected_values, expected_query)) in actual.iter().zip(&expected)
            {
                assert_eq!(values, expected_values);
                assert_eq!(query.index, expected_query.index);
                assert_eq!(
                    query.leaf_values_concatenated,
                    expected_query.leaf_values_concatenated
                );
                assert_eq!(query.path, expected_query.path);
            }
        }
    }
}
