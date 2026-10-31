//! Base (memory / witness) commitments of the prover's initial stage. Every
//! routine takes the [`ProverConfig`] and derives ALL of the commitment geometry
//! from it — LDE factor, leaf size (`base_oracles_values_per_leaf`), cap,
//! `trace_len_log2` and the packing `pack_log2` — so a commitment made here (or
//! ahead of the proof, by a caller that later passes the same config) cannot
//! disagree with the proof. `twiddles` must cover the
//! `2^(trace_len_log2 + pack_log2)` domain.

use super::*;
use crate::allocation_pool::AllocationPool;
use crate::gkr::prover::commitment_utils::*;
use crate::gkr::prover_config::ProverConfig;
use crate::gkr::whir::coset_commit::CosetByCosetBaseCommitment;

fn mem_inputs<F: PrimeField>(
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
) -> Vec<&[F]> {
    witness_eval_data
        .column_major_memory_trace
        .iter()
        .map(|el| &el[..])
        .collect()
}

fn wit_inputs<F: PrimeField>(
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
) -> Vec<&[F]> {
    witness_eval_data
        .column_major_witness_trace
        .iter()
        .map(|el| &el[..])
        .collect()
}

/// Memory columns followed by witness columns: the layout of the merged
/// commitment and of the merged claims.
fn merged_inputs<F: PrimeField>(
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
) -> Vec<&[F]> {
    witness_eval_data
        .column_major_memory_trace
        .iter()
        .chain(witness_eval_data.column_major_witness_trace.iter())
        .map(|el| &el[..])
        .collect()
}

/// Commit memory and witness as two SEPARATE base oracles, each packed by
/// `2^pack_log2` consecutive columns (`pack_log2 == 0`: one committed column per
/// base column — see [`commit_trace_part_for_config`]). Every RS codeword is
/// materialized in memory.
pub fn commit_separate_memory_and_witness_subtrees<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    B: crate::gkr::prover::backend::Backend<F, E>,
>(
    backend: &B,
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
    twiddles: &B::TwiddleSet,
    prover_config: &ProverConfig,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) -> (
    ColumnMajorBaseOracleForLDE<F, T>,
    ColumnMajorBaseOracleForLDE<F, T>,
) {
    let mem: ColumnMajorBaseOracleForLDE<F, T> = commit_trace_part_for_config(
        backend,
        &mem_inputs(witness_eval_data),
        twiddles,
        prover_config,
        pool,
        worker,
    );
    let wit: ColumnMajorBaseOracleForLDE<F, T> = commit_trace_part_for_config(
        backend,
        &wit_inputs(witness_eval_data),
        twiddles,
        prover_config,
        pool,
        worker,
    );

    (mem, wit)
}

/// Commit the union of the memory and witness columns (memory columns first,
/// then witness) as ONE base oracle, packed by `2^pack_log2` consecutive
/// columns (`pack_log2 == 0`: unpacked). Our packing relies on the observation
/// that one can make a multilinear poly m(Y, X) such that m(0, X) = a(X) and
/// m(1, X) = b(X), and the same trick works for deriving evaluations at a
/// random point: m(r', r) = a(r) + (b(r) - a(r)) * r'. We just need to have the
/// matching enumeration of the extending coordinates in both cases (see
/// `merge_claims`). Every RS codeword is materialized in memory.
pub fn commit_merged_memory_and_witness_subtrees<
    F: PrimeField + TwoAdicField,
    E: FieldExtension<F> + Field,
    T: ColumnMajorMerkleTreeConstructor<F>,
    B: crate::gkr::prover::backend::Backend<F, E>,
>(
    backend: &B,
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
    twiddles: &B::TwiddleSet,
    prover_config: &ProverConfig,
    pool: &dyn AllocationPool<F, E>,
    worker: &Worker,
) -> ColumnMajorBaseOracleForLDE<F, T> {
    commit_trace_part_for_config(
        backend,
        &merged_inputs(witness_eval_data),
        twiddles,
        prover_config,
        pool,
        worker,
    )
}

/// Coset-by-coset commitment of one (non-empty) column set with the config's
/// geometry, packed by `2^pack_log2` consecutive columns (`pack_log2 == 0`:
/// unpacked). The resulting commitment keeps only the compact per-column
/// monomial forms + the small top tree and serves round-0 queries by batched
/// per-coset recomputation. Byte-identical to the materialized
/// [`commit_trace_part_for_config`] oracle.
fn coset_recompute_commitment<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    inputs: &[&[F]],
    twiddles: &Twiddles<F, Global>,
    prover_config: &ProverConfig,
    worker: &Worker,
) -> CosetByCosetBaseCommitment<F, T> {
    for column in inputs.iter() {
        assert_eq!(
            column.len(),
            1usize << prover_config.trace_len_log2,
            "every committed column must have 2^trace_len_log2 = 2^{} elements",
            prover_config.trace_len_log2
        );
    }
    let whir_first_fold_step_log2 = prover_config
        .base_oracles_values_per_leaf()
        .trailing_zeros() as usize;
    if prover_config.pack_log2() == 0 {
        CosetByCosetBaseCommitment::<F, T>::commit(
            inputs,
            twiddles,
            prover_config.lde_factor(),
            whir_first_fold_step_log2,
            prover_config.cap_size,
            prover_config.trace_len_log2,
            worker,
        )
    } else {
        // pack + monomialize over ALL (base + pack_log2) variables at once, so
        // each packed poly is one faithful multilinear (consistent with
        // `merge_claims`); the packed LDE codeword (2^(N + pack_log2) x
        // lde_factor) is never materialized whole.
        CosetByCosetBaseCommitment::<F, T>::commit_packed(
            inputs,
            twiddles,
            prover_config.lde_factor(),
            whir_first_fold_step_log2,
            prover_config.cap_size,
            prover_config.trace_len_log2,
            prover_config.pack_log2(),
            worker,
        )
    }
}

/// Commit one column set coset-by-coset ([`coset_recompute_commitment`]). An
/// empty column set yields an empty in-memory oracle over the packed domain
/// (nothing to commit or recompute).
fn commit_trace_part_recompute<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    inputs: &[&[F]],
    twiddles: &Twiddles<F, Global>,
    prover_config: &ProverConfig,
    worker: &Worker,
) -> ColumnMajorBaseOracleForLDE<F, T> {
    if inputs.is_empty() {
        return ColumnMajorBaseOracleForLDE::empty(
            prover_config.base_oracles_values_per_leaf(),
            prover_config.whir_message_size_log2(),
            prover_config.lde_factor(),
        );
    }
    ColumnMajorBaseOracleForLDE::CosetRecompute(coset_recompute_commitment::<F, T>(
        inputs,
        twiddles,
        prover_config,
        worker,
    ))
}

/// Coset-by-coset (recompute) sibling of
/// [`commit_separate_memory_and_witness_subtrees`]: memory and witness are
/// committed separately (each packed by `2^pack_log2`), each serving round-0
/// queries by batched recomputation.
pub fn commit_separate_memory_and_witness_recompute<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
    twiddles: &Twiddles<F, Global>,
    prover_config: &ProverConfig,
    worker: &Worker,
) -> (
    ColumnMajorBaseOracleForLDE<F, T>,
    ColumnMajorBaseOracleForLDE<F, T>,
) {
    let mem = commit_trace_part_recompute(
        &mem_inputs(witness_eval_data),
        twiddles,
        prover_config,
        worker,
    );
    let wit = commit_trace_part_recompute(
        &wit_inputs(witness_eval_data),
        twiddles,
        prover_config,
        worker,
    );
    (mem, wit)
}

/// Coset-by-coset (recompute) sibling of
/// [`commit_merged_memory_and_witness_subtrees`]: commits the union of the
/// memory+witness columns (packed by `2^pack_log2`), byte-identical to the
/// materialized merged oracle.
pub fn commit_merged_memory_and_witness_recompute<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
    twiddles: &Twiddles<F, Global>,
    prover_config: &ProverConfig,
    worker: &Worker,
) -> ColumnMajorBaseOracleForLDE<F, T> {
    let merged_inputs = merged_inputs(witness_eval_data);
    assert!(
        !merged_inputs.is_empty(),
        "merged memory+witness commitment requires at least one column"
    );
    ColumnMajorBaseOracleForLDE::CosetRecompute(coset_recompute_commitment::<F, T>(
        &merged_inputs,
        twiddles,
        prover_config,
        worker,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fft::Twiddles;
    use crate::gkr::prover::backend::NaiveBackend;
    use crate::merkle_trees::DefaultTreeConstructor;
    use field::baby_bear::base::BabyBearField;
    use rand::{RngCore, SeedableRng};

    type F = BabyBearField;

    const TRACE_LEN_LOG2: usize = 10;
    const LDE_FACTOR: usize = 16;
    const CAP_SIZE: usize = 16;
    const VALUES_PER_LEAF_LOG2: usize = 1;

    fn columns(rng: &mut impl RngCore, count: usize) -> Vec<Vec<F>> {
        (0..count)
            .map(|_| {
                (0..1usize << TRACE_LEN_LOG2)
                    .map(|_| F::from_u32_with_reduction(rng.next_u32()))
                    .collect()
            })
            .collect()
    }

    #[test]
    fn merged_recompute_commit_matches_subtrees() {
        let worker = Worker::new_with_num_threads(2);
        let mut config = crate::gkr::prover_config::ProverConfig::whir_only(
            TRACE_LEN_LOG2,
            crate::gkr::prover::WhirSchedule::from_legacy_arrays(
                LDE_FACTOR,
                CAP_SIZE,
                0,
                &[VALUES_PER_LEAF_LOG2],
                &[1],
                &[],
                &[0],
            ),
            crate::definitions::SecurityLevel::Sec100,
        );
        config.commitment_mode = crate::gkr::prover_config::CommitmentMode::MergedMemoryAndWitness;
        let twiddles = Twiddles::<F, Global>::new(1 << TRACE_LEN_LOG2, &worker);
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x3e46);
        let trace = GKRFullWitnessTrace::<F, Global, Global> {
            column_major_memory_trace: columns(&mut rng, 3),
            column_major_witness_trace: columns(&mut rng, 2),
            column_major_scratch_space_trace: Vec::new(),
            generic_lookup_mapping: Vec::new(),
            range_check_16_lookup_mapping: Vec::new(),
            timestamp_range_check_lookup_mapping: Vec::new(),
        };

        let subtrees: ColumnMajorBaseOracleForLDE<F, DefaultTreeConstructor> =
            commit_merged_memory_and_witness_subtrees::<F, F, _, _>(
                &NaiveBackend,
                &trace,
                &twiddles,
                &config,
                &*crate::allocation_pool::default_proxy_pool_for(),
                &worker,
            );
        let recompute: ColumnMajorBaseOracleForLDE<F, DefaultTreeConstructor> =
            commit_merged_memory_and_witness_recompute(&trace, &twiddles, &config, &worker);

        assert_eq!(subtrees.get_cap().cap, recompute.get_cap().cap);
        let indices: Vec<usize> =
            (0..(LDE_FACTOR << TRACE_LEN_LOG2) >> VALUES_PER_LEAF_LOG2).collect();
        let expected = subtrees.query_many(&indices, &twiddles, &worker);
        let actual = recompute.query_many(&indices, &twiddles, &worker);
        assert_eq!(expected.len(), actual.len());
        for ((ev, eq), (av, aq)) in expected.iter().zip(actual.iter()) {
            assert_eq!(ev, av);
            assert_eq!(eq.index, aq.index);
            assert_eq!(eq.leaf_values_concatenated, aq.leaf_values_concatenated);
            assert_eq!(eq.path, aq.path);
        }
    }
}
