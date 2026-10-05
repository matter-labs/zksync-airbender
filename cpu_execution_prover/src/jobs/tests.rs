use crate::jobs::CpuJobs;
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::{MerkleTreeCapVarLength, BF, E4};
use execution_prover::messages::{
    MemoryCommitmentRequest, ProofRequest, ProofResult, SetupInitializationRequest, WorkRequest,
    WorkResult,
};
use execution_prover::setup::build_delegation_setup;
use execution_prover::CommitmentMode;
use execution_prover::ProofProfile;
use execution_prover_model::allocator::CpuTraceAllocator;
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

fn prove(
    memory_caps: impl FnOnce(Vec<MerkleTreeCapVarLength>) -> Vec<MerkleTreeCapVarLength>,
) -> (CpuCircuitPrecomputations, ProofResult<CpuTraceAllocator>) {
    let worker = Worker::new();
    let mut jobs = CpuJobs::default();
    let circuit_type = CircuitType::Delegation(DELEGATION);
    let precomputations = CpuCircuitPrecomputations::from_canonical(
        circuit_type,
        build_delegation_setup(DELEGATION, &worker),
        &[ProofProfile::Standard],
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
            commitment_mode: CommitmentMode::SeparateMemoryAndWitness,
            profile: ProofProfile::Standard,
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
            commitment_mode: CommitmentMode::SeparateMemoryAndWitness,
            profile: ProofProfile::Standard,
        }),
        &worker,
    ) else {
        panic!("proof request produced the wrong result kind");
    };
    (precomputations, proved)
}

#[cfg(feature = "verifiers")]
#[test]
fn a_delegation_proof_verifies_natively() {
    use execution_prover::backend::CircuitPrecomputation;
    use full_statement_verifier::imports::blake2_g_function_sec_100;
    use verifier_common::errors::DebugErrorCreator;

    let (precomputations, proved) = prove(|caps| caps);
    let stream = verifier_common::gkr::flatten::flatten_gkr_proof_for_nds(
        &proved.proof,
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

#[test]
#[should_panic(expected = "disagrees with the cap committed")]
fn an_altered_prior_memory_cap_is_rejected() {
    prove(|mut caps| {
        caps[0].cap[0][0] ^= 1;
        caps
    });
}

#[test]
#[ignore = "2^23 setup commits"]
fn multi_profile_setup_caps_match_direct_commits() {
    use crate::upstream::{DefaultTreeConstructor, SetupCommitment, TwiddleSetOps};
    use execution_prover::backend::CircuitPrecomputation;
    use execution_prover::setup::build_unrolled_setup;
    use execution_prover::MachineType;
    use execution_prover::ProofProfile::{L1Feeder, Standard};
    use execution_prover_model::circuit_type::UnrolledCircuitType;
    use std::alloc::Global;
    use std::sync::Arc;

    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let (_, mut binary) = setups::read_binary(&root.join("examples/basic_fibonacci/app.bin"));
    let (_, mut text) = setups::read_binary(&root.join("examples/basic_fibonacci/app.text"));
    setups::pad_bytecode_for_proving(&mut binary);
    setups::pad_bytecode_for_proving(&mut text);
    let worker = Worker::new();
    let circuit_type = CircuitType::Unrolled(UnrolledCircuitType::Unified);
    let precomputations = CpuCircuitPrecomputations::from_canonical(
        circuit_type,
        build_unrolled_setup(
            MachineType::Reduced,
            UnrolledCircuitType::Unified,
            &binary,
            &text,
            &worker,
        ),
        &[Standard, L1Feeder],
    );
    let mut jobs = CpuJobs::default();
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
    let twiddles = jobs.twiddles(precomputations.trace_len, &worker);
    let first = precomputations.initialize_setup(SECURITY_LEVEL, &*twiddles, &worker);
    let second = precomputations.initialize_setup(SECURITY_LEVEL, &*twiddles, &worker);
    assert!(std::ptr::eq(first, second));
    assert_eq!(first.len(), 2);
    match (&first[&Standard], &first[&L1Feeder]) {
        (
            SetupCommitment::Derived { base: standard, .. },
            SetupCommitment::Derived { base: feeder, .. },
        ) => {
            assert!(Arc::ptr_eq(standard, feeder));
            assert_eq!(standard.num_cosets(), 16);
        }
        _ => panic!("multi-profile setup must derive both profiles from one base"),
    }
    let standard = setups::program_setups::compute_unified_program_setups::<Global>(
        &binary,
        &text,
        true,
        SECURITY_LEVEL,
        &worker,
    );
    let family = UnrolledCircuitType::Unified.get_family_idx() as u32;
    assert_eq!(
        precomputations.setup_cap(Standard).unwrap().cap.as_slice(),
        standard[&family].setup_caps.cap.as_slice(),
    );
    let config = execution_prover::prover_config(circuit_type, L1Feeder, SECURITY_LEVEL);
    let feeder = precomputations
        .setup
        .commit::<DefaultTreeConstructor>(
            twiddles.plain(),
            config.lde_factor,
            config.whir_schedule.whir_steps_schedule[0],
            config.cap_size,
            precomputations.trace_len_log2(),
            &worker,
        )
        .get_cap();
    assert_eq!(precomputations.setup_cap(L1Feeder).unwrap().cap, feeder.cap);
    let profile_setups = setups::program_setups::compute_unified_program_setups_for_profile::<Global>(
        &binary,
        &text,
        true,
        SECURITY_LEVEL,
        L1Feeder,
        &worker,
    );
    assert_eq!(
        precomputations.setup_cap(L1Feeder).unwrap().cap.as_slice(),
        profile_setups[&family].setup_caps.cap.as_slice()
    );
}

#[test]
fn storage_policy_selects_the_expected_oracles() {
    use super::whir_storage;
    use crate::upstream::WhirOracleStorage;
    use crate::CpuStoragePolicy::{Auto, InMemory, Recompute};
    use execution_prover::ProofProfile::{L1Feeder, Standard};

    for (policy, profile, expected) in [
        (Auto, Standard, WhirOracleStorage::fully_in_memory()),
        (InMemory, Standard, WhirOracleStorage::fully_in_memory()),
        (
            Auto,
            L1Feeder,
            WhirOracleStorage::recompute_base_materialized_intermediates(),
        ),
        (InMemory, L1Feeder, WhirOracleStorage::fully_in_memory()),
        (
            Recompute,
            L1Feeder,
            WhirOracleStorage::recompute_base_materialized_intermediates(),
        ),
    ] {
        let config = profile.prover_config(23, SECURITY_LEVEL);
        assert_eq!(whir_storage(policy, profile, &config), expected);
    }
}

#[test]
#[should_panic(expected = "CpuStoragePolicy::Recompute needs cap size <= LDE factor")]
fn recompute_with_standard_cap_is_rejected() {
    let profile = execution_prover::ProofProfile::Standard;
    super::whir_storage(
        crate::CpuStoragePolicy::Recompute,
        profile,
        &profile.prover_config(23, SECURITY_LEVEL),
    );
}
