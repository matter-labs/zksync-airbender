use cs::definitions::gkr::NoFieldSingleColumnLookupRelation;

use crate::gkr::sumcheck::evaluation_kernels::BatchedGKRKernel;

use super::*;

pub fn forward_evaluate_lookup_from_base_inputs_with_setup<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    input: &NoFieldSingleColumnLookupRelation,
    setup: [GKRAddress; 2],
    output: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    worker: &Worker,
) {
    todo!();
}
