use super::{inits_and_teardowns, rows};
use crate::precomputations::CpuCircuitPrecomputations;
use crate::upstream::{
    evaluate_gkr_witness_for_executor_family, l1_wrap_witness_eval_fn,
    prove_configured_with_gkr_with_storage_and_backend, CommitmentMode, Field,
    GKRExternalChallenges, Keccak256MerkleTreeWithCap, Keccak256Transcript, NaiveGKRBackend,
    Proth120, Proth120WorkStealingLazyBackend, UnifiedRiscvCircuitOracle,
    EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS, EVM_PRODUCTION_PACK_LOG2,
    NUM_PERMUTATION_ARGUMENT_KEY_PARTS,
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
    assert_l1_wrap_mode(commitment_mode);
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

fn assert_l1_wrap_mode(mode: CommitmentMode) {
    assert!(
        matches!(
            mode,
            CommitmentMode::MergedAndPackedMemoryAndWitness {
                pack_log2: EVM_PRODUCTION_PACK_LOG2,
                external_challenges_pow_bits: EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS,
                ..
            }
        ),
        "L1Wrap requires MergedAndPackedMemoryAndWitness with production packing parameters"
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use prover::definitions::FinalRegisterValue;

    fn packed_mode(pack_log2: usize, external_challenges_pow_bits: u32) -> CommitmentMode {
        CommitmentMode::MergedAndPackedMemoryAndWitness {
            pack_log2,
            external_challenges_pow_bits,
            final_pc: 4,
            final_timestamp: 16,
            register_final_state: [FinalRegisterValue {
                value: 0,
                last_access_timestamp: 0,
            }; 32],
        }
    }

    #[test]
    fn l1_wrap_accepts_only_the_production_packed_mode() {
        assert_l1_wrap_mode(packed_mode(
            EVM_PRODUCTION_PACK_LOG2,
            EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS,
        ));
        for mode in [
            CommitmentMode::SeparateMemoryAndWitness,
            CommitmentMode::MergedMemoryAndWitness,
            packed_mode(
                EVM_PRODUCTION_PACK_LOG2 - 1,
                EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS,
            ),
            packed_mode(
                EVM_PRODUCTION_PACK_LOG2,
                EVM_PRODUCTION_EXTERNAL_CHALLENGES_POW_BITS - 1,
            ),
        ] {
            assert!(std::panic::catch_unwind(|| assert_l1_wrap_mode(mode)).is_err());
        }
    }
}
