use super::{inits_and_teardowns, rows};
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::{
    evaluate_gkr_witness_for_executor_family, l1_wrap_2p21, l1_wrap_2p22,
    prove_configured_with_gkr_with_storage_and_backend, Field, GKRExternalChallenges,
    GKRFullWitnessTrace, Keccak256MerkleTreeWithCap, Keccak256Transcript, L1WrapSetup,
    NaiveGKRBackend, Proth120, Proth120WorkStealingLazyBackend, UnifiedRiscvCircuitOracle,
    NUM_PERMUTATION_ARGUMENT_KEY_PARTS,
};
use execution_prover::messages::{L1WrapProofRequest, L1WrapProofResult};
use execution_prover::L1WrapResult;
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::CircuitType;
use execution_prover_model::trace::{InitsAndTeardownsTraceHost, UnrolledUnifiedTraceHost};
use std::alloc::Global;
use std::marker::PhantomData;
use worker::Worker;

pub(super) fn run<A: HostTraceAllocator>(
    request: L1WrapProofRequest<A, CpuCircuitPrecomputations>,
    worker: &Worker,
) -> L1WrapProofResult<A> {
    let L1WrapProofRequest {
        batch_id,
        circuit_type,
        precomputations,
        inits_and_teardowns,
        tracing_data,
        commitment_mode,
    } = request;
    let precomputed = precomputations.l1_wrap();
    assert_eq!(
        circuit_type, precomputed.circuit_type,
        "L1Wrap request disagrees with its precomputations"
    );
    let committed = precomputed.committed();
    let setup = &precomputed.setup;
    assert_eq!(
        setup.trace_len.trailing_zeros() as usize,
        committed.config.trace_len_log2,
        "L1Wrap setup trace length disagrees with the committed prover config"
    );
    let witness = evaluate_witness(
        circuit_type,
        setup,
        &inits_and_teardowns,
        &tracing_data,
        worker,
    );
    // Packed mode derives the challenges from the boundary state in commitment_mode.
    let external_challenges = GKRExternalChallenges::<Proth120, Proth120> {
        permutation_argument_linearization_challenges: [Proth120::ZERO;
            NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1],
        permutation_argument_additive_part: Proth120::ZERO,
        _marker: PhantomData,
    };
    let proof = prove_configured_with_gkr_with_storage_and_backend::<
        Proth120,
        Proth120,
        Keccak256MerkleTreeWithCap,
        Keccak256Transcript,
        _,
        _,
    >(
        &setup.circuit,
        &external_challenges,
        witness,
        &setup.setup,
        &committed.commitment,
        &committed.twiddles,
        &committed.config,
        commitment_mode,
        committed.storage,
        inits_and_teardowns.top_bits.clone(),
        setup.trace_len,
        &Proth120WorkStealingLazyBackend,
        &NaiveGKRBackend,
        worker,
    );
    L1WrapProofResult {
        batch_id,
        circuit_type,
        inits_and_teardowns,
        tracing_data,
        result: L1WrapResult {
            proof,
            commitment_mode,
        },
    }
}

pub(crate) fn evaluate_witness<A: HostTraceAllocator>(
    circuit_type: CircuitType,
    setup: &L1WrapSetup,
    inits_and_teardowns: &InitsAndTeardownsTraceHost<A>,
    tracing_data: &UnrolledUnifiedTraceHost<A>,
    worker: &Worker,
) -> GKRFullWitnessTrace<Proth120, Global, Global> {
    assert!(
        setup.trace_len.is_power_of_two(),
        "L1Wrap setup trace length must be a power of two"
    );
    let sets = inits_and_teardowns::expand::<Proth120, _>(
        inits_and_teardowns,
        setup.circuit.memory_layout.teardown_sets.len(),
        setup.trace_len.trailing_zeros(),
    );
    let rows = rows(tracing_data);
    let oracle = UnifiedRiscvCircuitOracle {
        inner: &rows,
        decoder_table: &setup.decoder_table,
    };
    let witness_eval_fn = match circuit_type {
        CircuitType::L1Wrap => l1_wrap_2p22::witness_eval_fn,
        CircuitType::L1Wrap21 => l1_wrap_2p21::witness_eval_fn,
        other => panic!("{other:?} is not an L1 wrap circuit"),
    };
    evaluate_gkr_witness_for_executor_family::<Proth120, _, _, _>(
        &setup.circuit,
        witness_eval_fn,
        setup.trace_len,
        &oracle,
        &setup.table_driver,
        worker,
        Some(sets),
        Global,
        Global,
    )
}
