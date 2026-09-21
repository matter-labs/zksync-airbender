//! Canonical circuit setup construction, shared by every backend.
//!
//! Setups are built here from the upstream `setups` constructors with nothing
//! stripped, because a CPU backend needs the evaluator function, the table
//! driver and the decoder entries at witness-generation time. A backend that
//! wants less derives it, through [`CanonicalCircuitSetup::into_backend_inputs`].

mod common;
mod unified;
mod unrolled;

pub use common::{build_common_setups, build_delegation_setup, build_inits_and_teardowns_setup};
pub use unified::build_unified_setup;
pub use unrolled::build_unrolled_setup;

use crate::upstream::{
    CSExecutorFamilyDecoderData, CircuitSetup, CpuGKRSetup, DelegationCircuitSetup,
    GKRCircuitArtifact, TableDriver, UnrolledCircuitWitnessEvalFn, BF,
};
use std::alloc::Global;

/// A fully built setup for one circuit. Two variants because a delegation
/// setup carries neither a per-family decoder table nor a witness evaluator.
pub enum CanonicalCircuitSetup {
    Riscv(CircuitSetup<Global>),
    Delegation(DelegationCircuitSetup),
}

/// The subset a backend needs to build its own prepared state: the compiled
/// artifact, the CPU setup and the decoder rows in dense form.
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

    /// The circuit's decoder rows in the dense form a backend's decoder table
    /// wants: one entry per ROM word, absent entries defaulted.
    ///
    /// Reads the table back out of the witness evaluator, which is where the
    /// upstream constructors store the exact slice they were given.
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
