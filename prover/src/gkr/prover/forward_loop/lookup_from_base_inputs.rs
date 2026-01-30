use crate::gkr::sumcheck::evaluation_kernels::{
    lookup_base_minus_multiplicity_base, lookup_base_pair, BatchedGKRKernel,
};

use super::*;

pub fn forward_evaluate_lookup_from_base_inputs_with_setup<
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
        lookup_base_minus_multiplicity_base::LookupBaseMinusMultiplicityByBaseGKRRelation {
            input,
            setup,
            outputs,
            lookup_additive_challenge,
            _marker: core::marker::PhantomData,
        };
    kernel.evaluate_forward_over_storage(gkr_storage, expected_output_layer, trace_len, worker);
}

pub fn forward_evaluate_lookup_base_inputs_pair<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    lookup_additive_challenge: E,
    worker: &Worker,
) {
    let kernel = lookup_base_pair::LookupBasePairGKRRelation {
        inputs,
        outputs,
        lookup_additive_challenge,
        _marker: core::marker::PhantomData,
    };
    kernel.evaluate_forward_over_storage(gkr_storage, expected_output_layer, trace_len, worker);
}
