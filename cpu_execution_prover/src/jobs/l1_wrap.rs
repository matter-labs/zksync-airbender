use super::{inits_and_teardowns, rows};
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::{
    evaluate_gkr_witness_for_executor_family, l1_wrap_witness_eval_fn,
    prove_configured_with_gkr_with_storage_and_backend, Field, GKRExternalChallenges,
    Keccak256MerkleTreeWithCap, Keccak256Transcript, NaiveGKRBackend, Proth120,
    Proth120WorkStealingLazyBackend, UnifiedRiscvCircuitOracle, NUM_PERMUTATION_ARGUMENT_KEY_PARTS,
};
use execution_prover::messages::{L1WrapProofRequest, L1WrapProofResult};
use execution_prover::L1WrapResult;
use execution_prover_model::allocator::HostTraceAllocator;
use std::alloc::Global;
use std::marker::PhantomData;
use worker::Worker;

pub(super) fn run<A: HostTraceAllocator>(
    request: L1WrapProofRequest<A, CpuCircuitPrecomputations>,
    worker: &Worker,
) -> L1WrapProofResult<A> {
    let L1WrapProofRequest {
        batch_id,
        precomputations,
        inits_and_teardowns,
        tracing_data,
        commitment_mode,
    } = request;
    let precomputed = precomputations.l1_wrap();
    let committed = precomputed.committed();
    let setup = &precomputed.setup;
    let sets = inits_and_teardowns::expand::<Proth120, _>(
        &inits_and_teardowns,
        setup.circuit.memory_layout.teardown_sets.len(),
        committed.config.trace_len_log2 as u32,
    );
    let witness = {
        let rows = rows(&tracing_data);
        let oracle = UnifiedRiscvCircuitOracle {
            inner: &rows,
            decoder_table: &setup.decoder_table,
        };
        evaluate_gkr_witness_for_executor_family::<Proth120, _, _, _>(
            &setup.circuit,
            l1_wrap_witness_eval_fn,
            setup.trace_len,
            &oracle,
            &setup.table_driver,
            worker,
            Some(sets),
            Global,
            Global,
        )
    };
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
        inits_and_teardowns,
        tracing_data,
        result: L1WrapResult {
            proof,
            commitment_mode,
        },
    }
}
