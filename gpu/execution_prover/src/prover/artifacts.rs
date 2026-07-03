//! Public read-only access to the compiled circuits and CPU setups behind a
//! registered binary. `program_prover` consumes these to assemble a
//! `full_statement_verifier::ProgramProof` (which embeds the compiled circuit
//! artifacts) and the per-family setup-cap map its ND streams are prefixed
//! with — neither of which `ProveResult` carries.

use super::*;
use crate::precomputations::CircuitPrecomputations;
use crate::upstream::{CpuGKRSetup, GKRCircuitArtifact};

/// Compiled circuit + CPU setup for one circuit the prover can produce proofs
/// for. The setup merkle cap is not materialized here; callers commit the CPU
/// setup themselves (`GKRSetup::commit`) with the prover config matching the
/// configured security level.
#[derive(Clone)]
pub struct CircuitArtifact {
    pub compiled_circuit: Arc<GKRCircuitArtifact<BF>>,
    pub cpu_setup: Arc<CpuGKRSetup<BF>>,
}

impl CircuitArtifact {
    fn from_precomputations(precomputations: &CircuitPrecomputations) -> Self {
        Self {
            compiled_circuit: Arc::clone(&precomputations.compiled_circuit),
            cpu_setup: Arc::clone(precomputations.setup_host.cpu_setup()),
        }
    }
}

/// Everything program-level proof assembly needs beyond `ProveResult`:
/// the per-binary RISC-V family circuits plus the binary-independent
/// inits-and-teardowns and delegation circuits.
pub struct ProgramArtifacts {
    /// Keyed by circuit family index. For `ExecutionKind::Unified` this is the
    /// single unified (reduced-machine) family.
    pub riscv_families: BTreeMap<u32, CircuitArtifact>,
    /// `None` for `ExecutionKind::Unified` (inits and teardowns are inline in
    /// the unified circuit).
    pub inits_and_teardowns: Option<CircuitArtifact>,
    /// Keyed by delegation type id.
    pub delegations: BTreeMap<u32, CircuitArtifact>,
}

impl ExecutionProver {
    /// Snapshot the compiled-circuit artifacts for a registered binary.
    pub fn program_artifacts(&self, handle: &BinaryHandle) -> ProgramArtifacts {
        let holder = &self.binary_holders[&handle.0];
        let riscv_families = holder
            .precomputations
            .iter()
            .map(|(circuit_type, precomputations)| {
                (
                    circuit_type.get_family_idx() as u32,
                    CircuitArtifact::from_precomputations(precomputations),
                )
            })
            .collect();
        let mut inits_and_teardowns = None;
        let mut delegations = BTreeMap::new();
        for (circuit_type, precomputations) in self.common_precomputations.iter() {
            match circuit_type {
                CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
                    inits_and_teardowns =
                        Some(CircuitArtifact::from_precomputations(precomputations));
                }
                CircuitType::Delegation(delegation_type) => {
                    delegations.insert(
                        delegation_type.get_delegation_type_id() as u32,
                        CircuitArtifact::from_precomputations(precomputations),
                    );
                }
                _ => {}
            }
        }
        if holder.execution_kind == ExecutionKind::Unified {
            inits_and_teardowns = None;
        }
        ProgramArtifacts {
            riscv_families,
            inits_and_teardowns,
            delegations,
        }
    }
}
