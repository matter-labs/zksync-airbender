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
    pub(crate) fn initialize_setup(&self, security_level: SecurityLevel, worker: &Worker) {
        let config = prover_config(CircuitType::L1Wrap, ProofProfile::L1Wrap, security_level);
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
        let pack_log2 = EVM_PRODUCTION_PACK_LOG2;
        let twiddles = Twiddles::new(1 << (config.trace_len_log2 + pack_log2), worker);
        let inputs: Vec<&[Proth120]> = setup
            .hypercube_evals
            .iter()
            .map(|column| &column[..])
            .collect();
        let oracle =
            ColumnMajorBaseOracleForLDE::CosetRecompute(CosetByCosetBaseCommitment::commit_packed(
                &inputs,
                &twiddles,
                config.lde_factor,
                config.base_oracles_values_per_leaf.trailing_zeros() as usize,
                config.cap_size,
                config.trace_len_log2,
                pack_log2,
                worker,
            ));
        Self {
            commitment: SetupCommitment::InMemory(oracle),
            twiddles,
            config,
            storage: WhirOracleStorage::fully_recompute(),
        }
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
            self.profiles
                .iter()
                .map(|&profile| {
                    let config = prover_config(self.circuit_type, profile, security_level);
                    let commitment = self.setup.commit::<DefaultTreeConstructor>(
                        twiddles.plain(),
                        config.lde_factor,
                        config.whir_schedule.whir_steps_schedule[0],
                        config.cap_size,
                        self.trace_len_log2(),
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
