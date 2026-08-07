use super::*;
use crate::gkr::prover::commitment_utils::*;
use crate::gkr::whir::coset_commit::CosetByCosetBaseCommitment;

pub fn commit_separate_memory_and_witness_subtrees<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    whir_first_fold_step_log2: usize,
    tree_cap_size: usize,
    trace_len_log2: usize,
    worker: &Worker,
) -> (
    ColumnMajorBaseOracleForLDE<F, T>,
    ColumnMajorBaseOracleForLDE<F, T>,
)
where
    [(); F::DEGREE]: Sized,
{
    let mem_inputs: Vec<_> = witness_eval_data
        .column_major_memory_trace
        .iter()
        .map(|el| &el[..])
        .collect();
    let mem: ColumnMajorBaseOracleForLDE<F, T> = commit_trace_part(
        &mem_inputs,
        twiddles,
        lde_factor,
        whir_first_fold_step_log2,
        tree_cap_size,
        trace_len_log2,
        worker,
    );

    let wit_inputs: Vec<_> = witness_eval_data
        .column_major_witness_trace
        .iter()
        .map(|el| &el[..])
        .collect();
    let wit: ColumnMajorBaseOracleForLDE<F, T> = commit_trace_part(
        &wit_inputs,
        twiddles,
        lde_factor,
        whir_first_fold_step_log2,
        tree_cap_size,
        trace_len_log2,
        worker,
    );

    (mem, wit)
}

pub fn commit_merged_memory_and_witness_subtrees<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    whir_first_fold_step_log2: usize,
    tree_cap_size: usize,
    trace_len_log2: usize,
    worker: &Worker,
) -> ColumnMajorBaseOracleForLDE<F, T>
where
    [(); F::DEGREE]: Sized,
{
    let merged_inputs: Vec<_> = witness_eval_data
        .column_major_memory_trace
        .iter()
        .chain(witness_eval_data.column_major_witness_trace.iter())
        .map(|el| &el[..])
        .collect();
    let merged: ColumnMajorBaseOracleForLDE<F, T> = commit_trace_part(
        &merged_inputs,
        twiddles,
        lde_factor,
        whir_first_fold_step_log2,
        tree_cap_size,
        trace_len_log2,
        worker,
    );

    merged
}

pub fn commit_packed_merged_memory_and_witness_subtrees<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    whir_first_fold_step_log2: usize,
    tree_cap_size: usize,
    trace_len_log2: usize,
    pack_log2: usize,
    worker: &Worker,
) -> ColumnMajorBaseOracleForLDE<F, T>
where
    [(); F::DEGREE]: Sized,
{
    use fft::*;
    use std::sync::Arc;

    // our packing relies on the observation that one can make multilinear poly m(Y, X) such
    // that m(0, X) = a(X) and m(1, X) = b(X), and same trick would work about deriving evaluations
    // on random point m(r', r) = a(r) + (b(r) - a(r)) * r'. We just need to have the matching
    // enumeration of extending coordinates in both cases
    let merged_inputs: Vec<_> = witness_eval_data
        .column_major_memory_trace
        .iter()
        .chain(witness_eval_data.column_major_witness_trace.iter())
        .map(|el| &el[..])
        .collect();

    let mut monomials =
        pack_polys_parallel_from_hypercubes_to_monomials(&merged_inputs, pack_log2, worker);

    // now get RS code words and make trees

    let next_root = domain_generator_for_size::<F>(((1 << trace_len_log2) * lde_factor) as u64);
    let root_powers =
        materialize_powers_serial_starting_with_one::<F, Global>(next_root, lde_factor);
    assert_eq!(root_powers[0], F::ONE);

    let values_per_leaf = 1 << whir_first_fold_step_log2;
    use crate::gkr::whir::{ColumnMajorBaseOracleForCoset, InMemoryBaseOracle, MaterializedCosets};
    let mut cosets = Vec::with_capacity(lde_factor);
    let new_coset_size_log2 = trace_len_log2 + pack_log2;

    for i in 0..lde_factor {
        let mut sources = if i == lde_factor - 1 {
            core::mem::replace(&mut monomials, vec![])
        } else {
            monomials.clone()
        };
        let offset = root_powers[i];
        // compute the corresponding coset FFT
        for src in sources.iter_mut() {
            if i != 0 {
                distribute_powers_parallel(src, F::ONE, offset, worker);
            }
            bitreverse_enumeration_inplace(src);
            fft::naive::parallel_ct_ntt_bitreversed_to_natural(
                src,
                trace_len_log2 as u32,
                &twiddles.forward_twiddles,
                worker,
            );
        }

        let original_values_normal_order: Vec<_> = sources
            .into_iter()
            .map(|el| ColumnMajorCosetBoundTracePart {
                column: Arc::new(el.into_boxed_slice()),
                offset,
            })
            .collect();

        let trace_part = ColumnMajorBaseOracleForCoset {
            original_values_normal_order,
            offset,
            coset_size_log2: new_coset_size_log2,
        };
        cosets.push(trace_part);
    }

    assert_eq!(cosets.len(), lde_factor);

    let source: Vec<_> = cosets
        .iter()
        .map(|el| {
            let columns: Vec<_> = el
                .original_values_normal_order
                .iter()
                .map(|el| &el.column[..])
                .collect();

            columns
        })
        .collect();
    let source_ref: Vec<_> = source.iter().map(|el| &el[..]).collect();

    let tree = T::construct_from_cosets::<F>(
        &source_ref[..],
        values_per_leaf,
        tree_cap_size,
        true,
        true,
        false,
        worker,
    );

    ColumnMajorBaseOracleForLDE::InMemory(InMemoryBaseOracle {
        cosets: MaterializedCosets { cosets },
        tree,
        values_per_leaf,
        coset_size_log2: new_coset_size_log2,
    })
}

/// Commit one column set coset-by-coset: the resulting oracle keeps only the
/// compact commitment (per-column monomial forms + the small top tree) and serves
/// round-0 queries by batched per-coset recomputation. An empty column set yields
/// an empty in-memory oracle (nothing to commit or recompute). Byte-identical
/// commitment to [`commit_trace_part`].
fn commit_trace_part_recompute<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    columns: &[Vec<F>],
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    whir_first_fold_step_log2: usize,
    tree_cap_size: usize,
    trace_len_log2: usize,
    worker: &Worker,
) -> ColumnMajorBaseOracleForLDE<F, T>
where
    [(); F::DEGREE]: Sized,
{
    if columns.is_empty() {
        return ColumnMajorBaseOracleForLDE::empty(
            1 << whir_first_fold_step_log2,
            trace_len_log2,
            lde_factor,
        );
    }
    let inputs: Vec<&[F]> = columns.iter().map(|c| &c[..]).collect();
    ColumnMajorBaseOracleForLDE::CosetRecompute(CosetByCosetBaseCommitment::<F, T>::commit(
        &inputs,
        twiddles,
        lde_factor,
        whir_first_fold_step_log2,
        tree_cap_size,
        trace_len_log2,
        worker,
    ))
}

/// Coset-by-coset (recompute) sibling of
/// [`commit_separate_memory_and_witness_subtrees`]: memory and witness are
/// committed separately, each serving round-0 queries by batched recomputation.
pub fn commit_separate_memory_and_witness_recompute<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    whir_first_fold_step_log2: usize,
    tree_cap_size: usize,
    trace_len_log2: usize,
    worker: &Worker,
) -> (
    ColumnMajorBaseOracleForLDE<F, T>,
    ColumnMajorBaseOracleForLDE<F, T>,
)
where
    [(); F::DEGREE]: Sized,
{
    let mem = commit_trace_part_recompute(
        &witness_eval_data.column_major_memory_trace,
        twiddles,
        lde_factor,
        whir_first_fold_step_log2,
        tree_cap_size,
        trace_len_log2,
        worker,
    );
    let wit = commit_trace_part_recompute(
        &witness_eval_data.column_major_witness_trace,
        twiddles,
        lde_factor,
        whir_first_fold_step_log2,
        tree_cap_size,
        trace_len_log2,
        worker,
    );
    (mem, wit)
}

/// Coset-by-coset (recompute) sibling of
/// [`commit_merged_memory_and_witness_subtrees`]: commits the union of
/// memory+witness columns (no packing), byte-identical to the materialized
/// merged oracle.
pub fn commit_merged_memory_and_witness_recompute<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    whir_first_fold_step_log2: usize,
    tree_cap_size: usize,
    trace_len_log2: usize,
    worker: &Worker,
) -> ColumnMajorBaseOracleForLDE<F, T>
where
    [(); F::DEGREE]: Sized,
{
    let merged_inputs: Vec<&[F]> = witness_eval_data
        .column_major_memory_trace
        .iter()
        .chain(witness_eval_data.column_major_witness_trace.iter())
        .map(|el| &el[..])
        .collect();
    assert!(
        !merged_inputs.is_empty(),
        "merged memory+witness commitment requires at least one column"
    );
    ColumnMajorBaseOracleForLDE::CosetRecompute(CosetByCosetBaseCommitment::<F, T>::commit(
        &merged_inputs,
        twiddles,
        lde_factor,
        whir_first_fold_step_log2,
        tree_cap_size,
        trace_len_log2,
        worker,
    ))
}

/// Coset-by-coset (recompute) sibling of
/// [`commit_packed_merged_memory_and_witness_subtrees`]: packs groups of
/// `2^pack_log2` merged memory+witness columns into single multilinears and
/// commits them coset-by-coset, keeping only the packed monomial forms + the
/// small top tree. The packed LDE codeword (2^(N + pack_log2) x lde_factor) is
/// never materialized whole.
pub fn commit_packed_merged_memory_and_witness_recompute<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
>(
    witness_eval_data: &GKRFullWitnessTrace<F, Global, Global>,
    twiddles: &Twiddles<F, Global>,
    lde_factor: usize,
    whir_first_fold_step_log2: usize,
    tree_cap_size: usize,
    trace_len_log2: usize,
    pack_log2: usize,
    worker: &Worker,
) -> ColumnMajorBaseOracleForLDE<F, T>
where
    [(); F::DEGREE]: Sized,
{
    let merged_inputs: Vec<&[F]> = witness_eval_data
        .column_major_memory_trace
        .iter()
        .chain(witness_eval_data.column_major_witness_trace.iter())
        .map(|el| &el[..])
        .collect();
    ColumnMajorBaseOracleForLDE::CosetRecompute(CosetByCosetBaseCommitment::<F, T>::commit_packed(
        &merged_inputs,
        twiddles,
        lde_factor,
        whir_first_fold_step_log2,
        tree_cap_size,
        trace_len_log2,
        pack_log2,
        worker,
    ))
}
