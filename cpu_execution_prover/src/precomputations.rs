//! What the CPU backend keeps per circuit: the whole canonical setup, because
//! CPU witness generation reads all of it, plus the setup commitment published
//! when setup initialization runs.

use crate::upstream::{
    CircuitSetup, CpuGKRSetup, DefaultTreeConstructor, GKRCircuitArtifact, MerkleTreeCapVarLength,
    ProverConfig, SetupCommitment, TableDriver, TwiddleSetOps, UnrolledCircuitWitnessEvalFn, BF,
};
use execution_prover::backend::CircuitPrecomputation;
use execution_prover::setup::CanonicalCircuitSetup;
use execution_prover_model::circuit_type::CircuitType;
use std::alloc::Global;
use std::ops::Deref;
use std::sync::{Arc, OnceLock};
use worker::Worker;

/// Cloning shares the state, so a precomputation travels inside every request
/// for its circuit.
#[derive(Clone)]
pub struct CpuCircuitPrecomputations(Arc<Precomputed>);

pub struct Precomputed {
    pub(crate) compiled_circuit: Arc<GKRCircuitArtifact<BF>>,
    pub(crate) setup: CpuGKRSetup<BF>,
    pub(crate) table_driver: TableDriver<BF>,
    /// `None` for delegation circuits and standalone inits-and-teardowns.
    pub(crate) witness_eval_fn: Option<UnrolledCircuitWitnessEvalFn<Global>>,
    pub(crate) trace_len: usize,
    pub(crate) setup_commitment: OnceLock<SetupCommitment<BF, DefaultTreeConstructor>>,
}

impl Deref for CpuCircuitPrecomputations {
    type Target = Precomputed;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl CpuCircuitPrecomputations {
    pub(crate) fn from_canonical(circuit_type: CircuitType, setup: CanonicalCircuitSetup) -> Self {
        let precomputed = match setup {
            CanonicalCircuitSetup::Riscv(CircuitSetup {
                family_idx: _,
                trace_len,
                compiled_circuit,
                table_driver,
                setup,
                witness_eval_fn,
            }) => Precomputed {
                compiled_circuit: Arc::new(compiled_circuit),
                setup,
                table_driver,
                witness_eval_fn,
                trace_len,
                setup_commitment: OnceLock::new(),
            },
            CanonicalCircuitSetup::Delegation(setup) => Precomputed {
                compiled_circuit: Arc::new(setup.compiled_circuit),
                setup: setup.setup,
                table_driver: setup.table_driver,
                witness_eval_fn: None,
                trace_len: setup.trace_len,
                setup_commitment: OnceLock::new(),
            },
        };
        assert_eq!(
            precomputed.trace_len,
            circuit_type.get_domain_size(),
            "setup trace length disagrees with CircuitType geometry for {circuit_type:?}"
        );
        Self(Arc::new(precomputed))
    }

    /// Commit this circuit's setup columns once; the first commitment wins.
    pub(crate) fn initialize_setup<T: TwiddleSetOps<BF>>(
        &self,
        config: &ProverConfig,
        twiddles: &T,
        worker: &Worker,
    ) -> &SetupCommitment<BF, DefaultTreeConstructor> {
        self.setup_commitment.get_or_init(|| {
            self.setup.commit::<DefaultTreeConstructor>(
                twiddles.plain(),
                config.lde_factor,
                config.whir_schedule.whir_steps_schedule[0],
                config.cap_size,
                self.trace_len_log2(),
                worker,
            )
        })
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

    /// `None` for a circuit with no setup columns: its commitment is empty, and
    /// an empty cap is not something the verifier's parameters carry.
    fn setup_cap(&self) -> Option<MerkleTreeCapVarLength> {
        if self.setup.hypercube_evals.is_empty() {
            return None;
        }
        let commitment = self
            .setup_commitment
            .get()
            .expect("setup initialization must run before a setup cap is read");
        Some(commitment.get_cap())
    }
}
