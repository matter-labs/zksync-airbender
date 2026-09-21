//! Retain witness evaluators for CPU proving; GPU backends consume a subset.

mod common;
mod unrolled;

pub use common::{build_common_setups, build_delegation_setup, build_inits_and_teardowns_setup};
pub use unrolled::{build_unified_setup, build_unrolled_setup};

use crate::upstream::{
    CSExecutorFamilyDecoderData, CircuitSetup, CpuGKRSetup, DelegationCircuitSetup,
    GKRCircuitArtifact, TableDriver, UnrolledCircuitWitnessEvalFn, BF,
};
use std::alloc::Global;

pub enum CanonicalCircuitSetup {
    Riscv(CircuitSetup<Global>),
    Delegation(DelegationCircuitSetup),
}

pub struct CanonicalSetupInputs {
    pub compiled_circuit: GKRCircuitArtifact<BF>,
    pub setup: CpuGKRSetup<BF>,
    /// `None` for circuits with no decoder table (delegations, standalone
    /// inits-and-teardowns).
    pub decoder_data: Option<Vec<CSExecutorFamilyDecoderData>>,
    pub trace_len: usize,
}

impl CanonicalCircuitSetup {
    pub fn compiled_circuit(&self) -> &GKRCircuitArtifact<BF> {
        match self {
            Self::Riscv(setup) => &setup.compiled_circuit,
            Self::Delegation(setup) => &setup.compiled_circuit,
        }
    }

    pub fn setup(&self) -> &CpuGKRSetup<BF> {
        match self {
            Self::Riscv(setup) => &setup.setup,
            Self::Delegation(setup) => &setup.setup,
        }
    }

    pub fn table_driver(&self) -> &TableDriver<BF> {
        match self {
            Self::Riscv(setup) => &setup.table_driver,
            Self::Delegation(setup) => &setup.table_driver,
        }
    }

    pub fn trace_len(&self) -> usize {
        match self {
            Self::Riscv(setup) => setup.trace_len,
            Self::Delegation(setup) => setup.trace_len,
        }
    }

    /// One row per ROM word, with absent decoder entries defaulted.
    pub fn decoder_data(&self) -> Option<Vec<CSExecutorFamilyDecoderData>> {
        let witness_eval_fn = match self {
            Self::Riscv(setup) => setup.witness_eval_fn.as_ref()?,
            Self::Delegation(_) => return None,
        };
        let decoder_table = match witness_eval_fn {
            UnrolledCircuitWitnessEvalFn::NonMemory { decoder_table, .. } => decoder_table,
            UnrolledCircuitWitnessEvalFn::Memory { decoder_table, .. } => decoder_table,
            UnrolledCircuitWitnessEvalFn::Unified { decoder_table, .. } => decoder_table,
        };
        Some(
            decoder_table
                .iter()
                .map(|entry| entry.as_ref().copied().unwrap_or_default())
                .collect(),
        )
    }

    /// Consume into the backend-facing subset, dropping the CPU-only data.
    pub fn into_backend_inputs(self) -> CanonicalSetupInputs {
        let decoder_data = self.decoder_data();
        let trace_len = self.trace_len();
        match self {
            Self::Riscv(setup) => CanonicalSetupInputs {
                compiled_circuit: setup.compiled_circuit,
                setup: setup.setup,
                decoder_data,
                trace_len,
            },
            Self::Delegation(setup) => CanonicalSetupInputs {
                compiled_circuit: setup.compiled_circuit,
                setup: setup.setup,
                decoder_data,
                trace_len,
            },
        }
    }
}

#[cfg(test)]
mod tests;
