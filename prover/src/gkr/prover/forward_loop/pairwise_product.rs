use crate::gkr::sumcheck::evaluation_kernels::{fixed_kernels, BatchedGKRKernel};

use super::*;

pub fn forward_evaluate_pairwise_product<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    inputs: [GKRAddress; 2],
    output: GKRAddress,
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    worker: &Worker,
) {
    // we just need to evaluate the corresponding kernel in the forward direction
    let kernel = fixed_kernels::SameSizeProductGKRRelation { inputs, output };
    kernel.evaluate_forward_over_storage(gkr_storage, expected_output_layer, trace_len, worker);
}
