use super::*;
use crate::gkr::prover::commitment_utils::commit_trace_part;

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
    todo!();
}
