//! The proof handler against the generated verifier, and its memory
//! re-commitment check.

use crate::host_storage::CpuTraceAllocator;
use crate::jobs::CpuJobs;
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::{MerkleTreeCapVarLength, BF, E4};
use execution_prover::messages::{
    MemoryCommitmentRequest, ProofRequest, ScheduledProof, SetupInitializationRequest, WorkRequest,
    WorkResult,
};
use execution_prover::setup::build_delegation_setup;
use execution_prover_model::circuit_type::{CircuitType, DelegationCircuitType};
use execution_prover_model::trace::{
    ChunkedTraceHolder, DelegationTracingDataHost, TracingDataHost,
};
use prover::definitions::{GKRExternalChallenges, SecurityLevel};
use worker::Worker;

const SECURITY_LEVEL: SecurityLevel = SecurityLevel::Sec100;
/// The smallest delegation circuit.
const DELEGATION: DelegationCircuitType = DelegationCircuitType::Blake2GFunction;

/// Fixed, non-zero challenges: zero challenges would let a handler that
/// dropped them pass by accident.
fn challenges() -> GKRExternalChallenges<BF, E4> {
    let total = GKRExternalChallenges::<BF, E4>::TOTAL_CHALLENGES;
    let values: Vec<E4> = (0..total as u32)
        .map(|index| {
            E4::from_array_of_base([
                BF::new(2 + index),
                BF::new(5 + index * 7),
                BF::new(42 + index * 11),
                BF::new(123 + index * 13),
            ])
        })
        .collect();
    GKRExternalChallenges::from_slice(&values)
}

fn empty_trace() -> TracingDataHost<CpuTraceAllocator> {
    TracingDataHost::Delegation(DelegationTracingDataHost::Blake2GFunction(
        ChunkedTraceHolder { chunks: Vec::new() },
    ))
}

/// Setup initialization, memory commitment, then a proof against the caps the
/// commitment produced, passed through `memory_caps`.
fn prove(
    memory_caps: impl FnOnce(Vec<MerkleTreeCapVarLength>) -> Vec<MerkleTreeCapVarLength>,
) -> (CpuCircuitPrecomputations, ScheduledProof) {
    let worker = Worker::new();
    let mut jobs = CpuJobs::default();
    let circuit_type = CircuitType::Delegation(DELEGATION);
    let precomputations = CpuCircuitPrecomputations::from_canonical(
        circuit_type,
        build_delegation_setup(DELEGATION, &worker),
    );
    jobs.execute::<CpuTraceAllocator>(
        WorkRequest::SetupInitialization(SetupInitializationRequest {
            batch_id: 0,
            circuit_type,
            sequence_id: 0,
            precomputations: precomputations.clone(),
            security_level: SECURITY_LEVEL,
        }),
        &worker,
    );
    let WorkResult::MemoryCommitment(committed) = jobs.execute(
        WorkRequest::MemoryCommitment(MemoryCommitmentRequest {
            batch_id: 0,
            circuit_type,
            sequence_id: 0,
            precomputations: precomputations.clone(),
            inits_and_teardowns: None,
            tracing_data: Some(empty_trace()),
            security_level: SECURITY_LEVEL,
        }),
        &worker,
    ) else {
        panic!("memory commitment request produced the wrong result kind");
    };
    let WorkResult::Proof(proved) = jobs.execute(
        WorkRequest::Proof(ProofRequest {
            batch_id: 0,
            circuit_type,
            sequence_id: 0,
            precomputations: precomputations.clone(),
            inits_and_teardowns: None,
            tracing_data: Some(empty_trace()),
            external_challenges: challenges(),
            memory_caps: memory_caps(committed.merkle_tree_caps),
            security_level: SECURITY_LEVEL,
        }),
        &worker,
    ) else {
        panic!("proof request produced the wrong result kind");
    };
    (precomputations, proved.proof)
}

#[cfg(feature = "verifiers")]
#[test]
fn a_delegation_proof_verifies_natively() {
    use execution_prover::backend::CircuitPrecomputation;
    use full_statement_verifier::imports::blake2_g_function_sec_100;
    use verifier_common::errors::DebugErrorCreator;

    let (precomputations, proof) = prove(|caps| caps);
    let stream = verifier_common::gkr::flatten::flatten_gkr_proof_for_nds(
        &proof,
        precomputations.compiled_circuit(),
    );
    let challenges = challenges();
    // The verifier recurses deeply, so it gets its own stack.
    std::thread::Builder::new()
        .stack_size(1 << 27)
        .spawn(move || {
            let mut source = stream.into_iter();
            blake2_g_function_sec_100::verify::<_, DebugErrorCreator>(&challenges, &mut source)
                .expect("the verifier rejected a proof this handler produced");
        })
        .unwrap()
        .join()
        .unwrap();
}

/// The proof re-commits memory; a prior cap that does not match it means the
/// two passes described different traces.
#[test]
#[should_panic(expected = "disagrees with the cap committed")]
fn an_altered_prior_memory_cap_is_rejected() {
    prove(|mut caps| {
        caps[0].cap[0][0] ^= 1;
        caps
    });
}
