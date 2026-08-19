//! Public read-only access to the compiled circuits and GPU-committed setup
//! caps behind a registered binary. `gpu_program_prover` consumes these to
//! assemble a `full_statement_verifier::ProgramProof` (which embeds the compiled
//! circuit artifacts) and the per-family setup-cap map its ND streams are
//! prefixed with — neither of which `ProveResult` carries.

use super::*;
use crate::precomputations::CircuitPrecomputations;
use crate::upstream::{GKRCircuitArtifact, MerkleTreeCapVarLength};

/// Compiled circuit + GPU-committed setup cap for one RISC-V family circuit.
/// The cap is copied out of the family's initialized `GpuGKRSetupHost`
/// (guaranteed by `add_binary`'s setup batch) — it is the exact digest
/// sequence the GPU committed and every proof of this family binds.
#[derive(Clone)]
pub struct RiscvFamilyArtifact {
    pub compiled_circuit: Arc<GKRCircuitArtifact<BF>>,
    pub setup_cap: MerkleTreeCapVarLength,
}

impl RiscvFamilyArtifact {
    fn from_precomputations(precomputations: &CircuitPrecomputations) -> Self {
        let setup_host = precomputations
            .setup_host
            .get_initialized()
            .expect("RISC-V family setup must have columns");
        Self {
            compiled_circuit: Arc::clone(precomputations.gkr_programs.compiled_circuit()),
            setup_cap: MerkleTreeCapVarLength {
                cap: setup_host.unified_tree_cap().to_vec(),
            },
        }
    }
}

/// Compiled circuit for a binary-independent circuit (delegations,
/// inits-and-teardowns). These carry no program-level setup cap: delegation
/// setup params are compile-time constants in the fsv verifiers, and
/// inits-and-teardowns has no setup columns at all.
#[derive(Clone)]
pub struct CommonCircuitArtifact {
    pub compiled_circuit: Arc<GKRCircuitArtifact<BF>>,
}

impl CommonCircuitArtifact {
    fn from_precomputations(precomputations: &CircuitPrecomputations) -> Self {
        Self {
            compiled_circuit: Arc::clone(precomputations.gkr_programs.compiled_circuit()),
        }
    }
}

/// Everything program-level proof assembly needs beyond `ProveResult`:
/// the per-binary RISC-V family circuits plus the binary-independent
/// inits-and-teardowns and delegation circuits.
pub struct ProgramArtifacts {
    /// Keyed by circuit family index. For `ExecutionKind::Unified` this is the
    /// single unified (reduced-machine) family.
    pub riscv_families: BTreeMap<u32, RiscvFamilyArtifact>,
    /// `None` for `ExecutionKind::Unified` (inits and teardowns are inline in
    /// the unified circuit).
    pub inits_and_teardowns: Option<CommonCircuitArtifact>,
    /// Keyed by delegation type id.
    pub delegations: BTreeMap<u32, CommonCircuitArtifact>,
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
                    RiscvFamilyArtifact::from_precomputations(precomputations),
                )
            })
            .collect();
        let mut inits_and_teardowns = None;
        let mut delegations = BTreeMap::new();
        for (circuit_type, precomputations) in self.common_precomputations.iter() {
            match circuit_type {
                CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
                    inits_and_teardowns =
                        Some(CommonCircuitArtifact::from_precomputations(precomputations));
                }
                CircuitType::Delegation(delegation_type) => {
                    delegations.insert(
                        delegation_type.get_delegation_type_id() as u32,
                        CommonCircuitArtifact::from_precomputations(precomputations),
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
