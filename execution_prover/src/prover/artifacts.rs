//! Compiled circuits and committed setup caps behind a registered binary:
//! what program-level proof assembly needs and `ProveResult` does not carry.

use super::*;
use crate::upstream::{GKRCircuitArtifact, MerkleTreeCapVarLength};

pub struct RiscvFamilyArtifact {
    pub compiled_circuit: Arc<GKRCircuitArtifact<BF>>,
    pub setup_cap: MerkleTreeCapVarLength,
}

pub struct ProgramArtifacts {
    /// Keyed by circuit family index. For `ExecutionKind::Unified` this is the
    /// single unified (reduced-machine) family.
    pub riscv_families: BTreeMap<u32, RiscvFamilyArtifact>,
    /// `None` for `ExecutionKind::Unified`, where inits and teardowns are
    /// inline in the unified circuit.
    pub inits_and_teardowns: Option<Arc<GKRCircuitArtifact<BF>>>,
    /// Keyed by delegation type id.
    pub delegations: BTreeMap<u32, Arc<GKRCircuitArtifact<BF>>>,
}

impl<B: ExecutionBackend> ExecutionProver<B> {
    /// Snapshot the compiled-circuit artifacts for a registered binary.
    pub fn program_artifacts(&self, handle: &BinaryHandle) -> ProgramArtifacts {
        let holder = &self.binary_holders[&handle.0];
        let riscv_families = holder
            .precomputations
            .iter()
            .map(|(circuit_type, precomputations)| {
                let setup_cap = precomputations
                    .setup_cap()
                    .expect("a RISC-V family setup must have columns");
                (
                    circuit_type.get_family_idx() as u32,
                    RiscvFamilyArtifact {
                        compiled_circuit: Arc::clone(precomputations.compiled_circuit()),
                        setup_cap,
                    },
                )
            })
            .collect();
        let mut inits_and_teardowns = None;
        let mut delegations = BTreeMap::new();
        for (circuit_type, precomputations) in self.common_precomputations.iter() {
            match circuit_type {
                CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns) => {
                    inits_and_teardowns = Some(Arc::clone(precomputations.compiled_circuit()));
                }
                CircuitType::Delegation(delegation_type) => {
                    delegations.insert(
                        delegation_type.get_delegation_type_id() as u32,
                        Arc::clone(precomputations.compiled_circuit()),
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
