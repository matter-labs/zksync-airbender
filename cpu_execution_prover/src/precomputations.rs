//! What the CPU backend keeps per circuit: the whole canonical setup, because
//! CPU witness generation reads all of it — the evaluator, the table driver,
//! the decoder rows with their holes intact, the padding PC. The only thing
//! added is the setup commitment, published when setup initialization runs.

use crate::upstream::{
    CircuitSetup, CpuGKRSetup, DefaultTreeConstructor, ExecutorFamilyDecoderData,
    GKRCircuitArtifact, MerkleTreeCapVarLength, ProverConfig, SetupCommitment, TableDriver,
    TwiddleSetOps, UnrolledCircuitWitnessEvalFn, BF,
};
use execution_prover::backend::CircuitPrecomputation;
use execution_prover::setup::CanonicalCircuitSetup;
use execution_prover_model::circuit_type::CircuitType;
use std::alloc::Global;
use std::sync::{Arc, OnceLock};
use worker::Worker;

/// One circuit's prepared CPU state. Cloning shares it, which is what lets a
/// precomputation travel inside every request for its circuit.
#[derive(Clone)]
pub struct CpuCircuitPrecomputations {
    inner: Arc<Inner>,
}

struct Inner {
    circuit_type: CircuitType,
    compiled_circuit: Arc<GKRCircuitArtifact<BF>>,
    setup: CpuGKRSetup<BF>,
    table_driver: TableDriver<BF>,
    /// `None` for delegation circuits and standalone inits-and-teardowns, which
    /// have no per-family decoder table or witness evaluator.
    witness_eval_fn: Option<UnrolledCircuitWitnessEvalFn<Global>>,
    trace_len: usize,
    /// The committed setup, not just its cap: proving needs the commitment
    /// itself. A circuit with no setup columns still commits — an empty
    /// commitment is a different thing from never having run.
    setup_commitment: OnceLock<SetupCommitment<BF, DefaultTreeConstructor>>,
}

impl CpuCircuitPrecomputations {
    pub(crate) fn from_canonical(circuit_type: CircuitType, setup: CanonicalCircuitSetup) -> Self {
        let inner = match setup {
            CanonicalCircuitSetup::Riscv(CircuitSetup {
                family_idx: _,
                trace_len,
                compiled_circuit,
                table_driver,
                setup,
                witness_eval_fn,
            }) => Inner {
                circuit_type,
                compiled_circuit: Arc::new(compiled_circuit),
                setup,
                table_driver,
                witness_eval_fn,
                trace_len,
                setup_commitment: OnceLock::new(),
            },
            CanonicalCircuitSetup::Delegation(setup) => Inner {
                circuit_type,
                compiled_circuit: Arc::new(setup.compiled_circuit),
                setup: setup.setup,
                table_driver: setup.table_driver,
                witness_eval_fn: None,
                trace_len: setup.trace_len,
                setup_commitment: OnceLock::new(),
            },
        };
        assert_eq!(
            inner.trace_len,
            circuit_type.get_domain_size(),
            "setup trace length disagrees with CircuitType geometry for {circuit_type:?}"
        );
        Self {
            inner: Arc::new(inner),
        }
    }

    pub(crate) fn circuit_type(&self) -> CircuitType {
        self.inner.circuit_type
    }

    pub(crate) fn trace_len(&self) -> usize {
        self.inner.trace_len
    }

    pub(crate) fn trace_len_log2(&self) -> usize {
        self.inner.trace_len.trailing_zeros() as usize
    }

    pub(crate) fn table_driver(&self) -> &TableDriver<BF> {
        &self.inner.table_driver
    }

    pub(crate) fn witness_eval_fn(&self) -> Option<&UnrolledCircuitWitnessEvalFn<Global>> {
        self.inner.witness_eval_fn.as_ref()
    }

    /// One decoder entry per ROM word. Witness generation distinguishes
    /// absent entries (`None`) from defaulted rows.
    pub(crate) fn decoder_table(&self) -> &[Option<ExecutorFamilyDecoderData>] {
        match self.witness_eval_fn() {
            Some(
                UnrolledCircuitWitnessEvalFn::NonMemory { decoder_table, .. }
                | UnrolledCircuitWitnessEvalFn::Memory { decoder_table, .. }
                | UnrolledCircuitWitnessEvalFn::Unified { decoder_table, .. },
            ) => decoder_table,
            None => panic!(
                "{:?} carries no witness evaluator, so it has no decoder rows",
                self.circuit_type()
            ),
        }
    }

    pub(crate) fn default_pc_value_in_padding(&self) -> u32 {
        match self.witness_eval_fn() {
            Some(UnrolledCircuitWitnessEvalFn::NonMemory {
                default_pc_value_in_padding,
                ..
            }) => *default_pc_value_in_padding,
            _ => panic!(
                "{:?} is not a non-memory family, so it has no padding PC",
                self.circuit_type()
            ),
        }
    }

    pub(crate) fn setup_columns(&self) -> &CpuGKRSetup<BF> {
        &self.inner.setup
    }

    /// Commit this circuit's setup columns once; the first published
    /// commitment wins, so two requests cannot disagree.
    pub(crate) fn initialize_setup<T: TwiddleSetOps<BF>>(
        &self,
        config: &ProverConfig,
        twiddles: &T,
        worker: &Worker,
    ) -> &SetupCommitment<BF, DefaultTreeConstructor> {
        self.inner.setup_commitment.get_or_init(|| {
            self.inner.setup.commit::<DefaultTreeConstructor>(
                twiddles.plain(),
                config.lde_factor,
                config.whir_schedule.whir_steps_schedule[0],
                config.cap_size,
                self.trace_len_log2(),
                worker,
            )
        })
    }

    pub(crate) fn setup_commitment(&self) -> Option<&SetupCommitment<BF, DefaultTreeConstructor>> {
        self.inner.setup_commitment.get()
    }

    #[cfg(test)]
    pub(crate) fn has_setup_columns(&self) -> bool {
        !self.inner.setup.hypercube_evals.is_empty()
    }
}

impl CircuitPrecomputation for CpuCircuitPrecomputations {
    fn compiled_circuit(&self) -> &Arc<GKRCircuitArtifact<BF>> {
        &self.inner.compiled_circuit
    }

    /// `None` for a circuit with no setup columns: its commitment is empty, and
    /// an empty cap is not something the verifier's parameters carry.
    fn setup_cap(&self) -> Option<MerkleTreeCapVarLength> {
        if self.inner.setup.hypercube_evals.is_empty() {
            return None;
        }
        let commitment = self
            .setup_commitment()
            .expect("setup initialization must run before a setup cap is read");
        Some(commitment.get_cap())
    }
}
