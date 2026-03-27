use crate::gkr::sumcheck::evaluation_kernels::{
    lookup_ext_minus_multiplicity_ext, lookup_ext_pair, lookup_masked_ext_minus_multiplicity_ext,
    lookup_rational_with_unbalanced_ext, BatchedGKRKernel,
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
    lookup_additive_challenge: E,
    worker: &Worker,
) {
    let kernel = lookup_masked_ext_minus_multiplicity_ext::LookupBaseExtMinusBaseExtGKRRelation {
        nums: [input[0], setup[0]],
        dens: [input[1], setup[1]],
        outputs,
        lookup_additive_challenge,
        _marker: core::marker::PhantomData,
    };
    kernel.evaluate_forward_over_storage(gkr_storage, expected_output_layer, trace_len, worker);
}

pub fn forward_evaluate_lookup_from_vector_inputs_pair<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    inputs: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    lookup_additive_challenge: E,
    worker: &Worker,
) {
    let kernel = lookup_ext_pair::LookupExtensionPairGKRRelation {
        inputs,
        outputs,
        lookup_additive_challenge,
        _marker: core::marker::PhantomData,
    };
    kernel.evaluate_forward_over_storage(gkr_storage, expected_output_layer, trace_len, worker);
}

pub fn forward_evaluate_lookup_rational_with_vector_remainder_input<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    inputs: [GKRAddress; 2],
    remainder: GKRAddress,
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    lookup_additive_challenge: E,
    worker: &Worker,
) {
    let kernel =
        lookup_rational_with_unbalanced_ext::LookupRationalPairWithUnbalancedExtensionGKRRelation {
            inputs,
            remainder,
            outputs,
            lookup_additive_challenge,
            _marker: core::marker::PhantomData,
        };
    kernel.evaluate_forward_over_storage(gkr_storage, expected_output_layer, trace_len, worker);
}

pub fn forward_evaluate_lookup_from_vector_inputs_with_setup<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    input: GKRAddress,
    setup: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    lookup_additive_challenge: E,
    worker: &Worker,
) {
    let kernel =
        lookup_ext_minus_multiplicity_ext::LookupExtensionMinusMultiplicityByExtensionGKRRelation {
            input,
            setup,
            outputs,
            lookup_additive_challenge,
            _marker: core::marker::PhantomData,
        };
    kernel.evaluate_forward_over_storage(gkr_storage, expected_output_layer, trace_len, worker);
}
