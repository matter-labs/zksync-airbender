use crate::gkr::sumcheck::evaluation_kernels::{
    lookup_masked_ext_minus_multiplicity_ext, BatchedGKRKernel,
};

use super::*;

pub fn forward_evaluate_masked_lookup_from_vector_inputs_with_setup<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    input: [GKRAddress; 2],
    setup: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    worker: &Worker,
) {
    let kernel = lookup_masked_ext_minus_multiplicity_ext::LookupBaseExtMinusBaseExtGKRRelation {
        nums: [input[0], setup[0]],
        dens: [input[1], setup[1]],
        outputs,
    };
    kernel.evaluate_forward_over_storage(gkr_storage, expected_output_layer, trace_len, worker);
}

// pub fn forward_evaluate_lookup_from_vector_inputs_with_setup<
//     F: PrimeField,
//     E: FieldExtension<F> + Field,
// >(
//     input: &NoFieldSingleColumnLookupRelation,
//     setup: [GKRAddress; 2],
//     output: [GKRAddress; 2],
//     gkr_storage: &mut GKRStorage<F, E>,
//     expected_output_layer: usize,
//     trace_len: usize,
//     worker: &Worker,
// ) {
//     todo!();
// }
