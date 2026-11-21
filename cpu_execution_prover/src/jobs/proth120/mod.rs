use super::{inits_and_teardowns, rows};
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::{
    evaluate_gkr_witness_for_executor_family, l1_wrap,
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
        operation_mode,
    } = request;
    let precomputed = precomputations.l1_wrap();
    assert_eq!(
        precomputed.setup.trace_len,
        circuit_type.get_domain_size(),
        "L1 wrap request {circuit_type:?} disagrees with its setup"
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
    // Single-chunk proving derives challenges from the boundary state in operation_mode.
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
        operation_mode,
        crate::upstream::WhirOracleStorage::fully_recompute(),
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
            operation_mode,
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
        CircuitType::L1Wrap21 | CircuitType::L1Wrap22 => l1_wrap::witness_eval_fn,
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

/// CPU production expansion used by `gpu_trace`'s Proth120 parity tests.
#[cfg(any(test, feature = "test-support"))]
#[doc(hidden)]
pub fn expand_inits_and_teardowns<A: HostTraceAllocator>(
    trace: &InitsAndTeardownsTraceHost<A>,
    num_sets: usize,
    trace_len_log2: u32,
) -> Vec<([Vec<Proth120>; 2], [Vec<Proth120>; 2])> {
    inits_and_teardowns::expand::<Proth120, A>(trace, num_sets, trace_len_log2)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::upstream::{CpuGKRSetup, OperationMode, TableDriver};
    use execution_prover::config::SoundnessMode;
    use execution_prover::ProofProfile;
    use execution_prover_model::allocator::CpuTraceAllocator;
    use execution_prover_model::trace::ChunkedTraceHolder;
    use prover::definitions::FinalRegisterValue;

    #[test]
    #[should_panic(expected = "L1 wrap request L1Wrap22 disagrees with its setup")]
    fn l1_wrap_request_identity_must_match_its_setup() {
        let circuit_type = CircuitType::L1Wrap21;
        let rom = circuit_type.rom();
        let setup = L1WrapSetup {
            circuit: l1_wrap::circuit_artifact(),
            table_driver: TableDriver::new(),
            decoder_table: vec![None; rom.word_size()],
            setup: CpuGKRSetup {
                hypercube_evals: Vec::new(),
            },
            trace_len: circuit_type.get_domain_size(),
            rom,
        };
        let config = ProofProfile::L1Wrap.prover_config(
            circuit_type.get_domain_size_log2() as usize,
            SoundnessMode::PessimisticConjecture,
        );
        let request = L1WrapProofRequest::<CpuTraceAllocator, _> {
            batch_id: 0,
            circuit_type: CircuitType::L1Wrap22,
            precomputations: CpuCircuitPrecomputations::l1_with_config(circuit_type, setup, config),
            inits_and_teardowns: InitsAndTeardownsTraceHost {
                page_indices: ChunkedTraceHolder { chunks: vec![] },
                values_packed: ChunkedTraceHolder { chunks: vec![] },
                timestamps_packed: ChunkedTraceHolder { chunks: vec![] },
                top_bits: vec![0, 0],
            },
            tracing_data: ChunkedTraceHolder { chunks: vec![] },
            operation_mode: OperationMode::SingleChunk {
                external_challenges_pow_bits: 0,
                register_final_state: [FinalRegisterValue {
                    value: 0,
                    last_access_timestamp: 0,
                }; 32],
                final_pc: 0,
                final_timestamp: 0,
            },
        };
        run(request, &Worker::new_with_num_threads(1));
    }
}
