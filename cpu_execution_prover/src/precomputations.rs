use crate::upstream::{
    CircuitSetup, CpuGKRSetup, DefaultTreeConstructor, GKRCircuitArtifact, MerkleTreeCapVarLength,
    SecurityLevel, SetupCommitment, TableDriver, TwiddleSetOps, UnrolledCircuitWitnessEvalFn, BF,
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
pub struct CpuCircuitPrecomputations(Arc<Precomputed>);

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
        &self.0
    }
}

impl CpuCircuitPrecomputations {
    pub(crate) fn from_canonical(
        circuit_type: CircuitType,
        setup: CanonicalCircuitSetup,
        profiles: &[ProofProfile],
    ) -> Self {
        let precomputed = match setup {
            CanonicalCircuitSetup::L1Wrap(_) => panic!("CPU L1Wrap setup is not implemented"),
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
        Self(Arc::new(precomputed))
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
        &self.0.compiled_circuit
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
