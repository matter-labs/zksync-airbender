//! BabyBear execution proving: the circuit setups, the multi-chunk
//! commit/prove pipeline over the RISC-V family, inits-and-teardowns and
//! delegation circuits, its results, and the circuit artifacts that
//! program-level proof assembly reads.

pub(super) mod artifacts;
mod pipeline;
mod proof_artifacts;
pub(super) mod result;
pub(super) mod setup;

use super::non_determinism_wrapper::NonDeterminismWrapper;
use super::*;
use result::ExecutionProverResult;

use crate::backend::CircuitPrecomputation;
use crate::messages::{
    InitsAndTeardownsData, MemoryCommitmentRequest, MemoryCommitmentResult, MemoryPartialTrees,
    ProofRequest, ProofResult, TracingData,
};
use crate::upstream::{
    Blake2sTranscript, FinalRegisterValue, GKRExternalChallenges, MerkleTreeCapVarLength, BF, E4,
};
use crate::CommitmentMode;
use common_constants::TimestampScalar;
use execution_prover_model::circuit_type::{
    DelegationCircuitType, UnrolledMemoryCircuitType, UnrolledNonMemoryCircuitType,
};
use log::debug;
use std::collections::VecDeque;
use verifier_common::MEMORY_DELEGATION_POW_BITS;
