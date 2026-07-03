use std::collections::BTreeMap;

use common_constants::TimestampScalar;

use super::BinaryHandle;
use crate::upstream::{
    DefaultTreeConstructor, FinalRegisterValue, GKRProof, MerkleTreeCapVarLength,
};
use gpu_core::primitives::field::{BF, E4};

pub struct CommitMemoryResult {
    pub final_register_values: [FinalRegisterValue; 32],
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
    pub circuit_families_memory_caps: BTreeMap<u8, Vec<Vec<MerkleTreeCapVarLength>>>,
    pub inits_and_teardowns_memory_caps: Vec<Vec<MerkleTreeCapVarLength>>,
    pub delegation_circuits_memory_caps: BTreeMap<u32, Vec<Vec<MerkleTreeCapVarLength>>>,
    /// Set by [`ExecutionProver::commit_memory`] from the binary handle passed
    /// in. Read back in `prove`/`commit_memory_and_prove` to recover the binary
    /// associated with this commitment. Defaults to a placeholder for the inner
    /// path; the public entry point always overwrites it.
    pub(super) binary_handle: BinaryHandle,
}

pub struct ProveResult {
    pub register_final_values: [FinalRegisterValue; 32],
    pub final_pc: u32,
    pub final_timestamp: TimestampScalar,
    pub circuit_families_proofs: BTreeMap<u8, Vec<GKRProof<BF, E4, DefaultTreeConstructor>>>,
    pub inits_and_teardowns_proofs: Vec<GKRProof<BF, E4, DefaultTreeConstructor>>,
    pub delegation_proofs: BTreeMap<u32, Vec<GKRProof<BF, E4, DefaultTreeConstructor>>>,
    pub pow_challenge: u64,
    /// `Some` for `ExecutionKind::Unified` only: the number of trailing
    /// unified circuits that carry real inits-and-teardowns data (the leading
    /// ones are dummies). The unified verifier consumes this as an extra ND
    /// word (`ProgramProof::num_it_circuits`).
    pub num_unified_it_circuits: Option<u32>,
}

pub(super) enum ExecutionProverResult {
    CommitMemory(CommitMemoryResult),
    Prove(ProveResult),
}

impl ExecutionProverResult {
    pub fn into_memory_commitment_result(self) -> CommitMemoryResult {
        match self {
            ExecutionProverResult::CommitMemory(result) => result,
            _ => panic!("expected CommitMemoryResult"),
        }
    }

    pub fn into_proof_result(self) -> ProveResult {
        match self {
            ExecutionProverResult::Prove(result) => result,
            _ => panic!("expected ProveResult"),
        }
    }
}
