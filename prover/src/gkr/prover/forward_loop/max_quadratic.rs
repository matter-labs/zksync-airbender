// This module's only item is the `gkr_self_checks` self-check below, so every import here
// is gated the same way.
#[cfg(feature = "gkr_self_checks")]
use super::*;
#[cfg(feature = "gkr_self_checks")]
use crate::gkr::sumcheck::evaluation_kernels::{
    enforce_max_quadratic_constraint, BatchedGKRKernel,
};
#[cfg(feature = "gkr_self_checks")]
use cs::gkr_compiler::NoFieldMaxQuadraticGKRRelation;

#[cfg(feature = "gkr_self_checks")]
pub fn self_check_max_quadratic_constraint<F: PrimeField, E: FieldExtension<F> + Field>(
    input: &NoFieldMaxQuadraticGKRRelation<F>,
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    worker: &Worker,
) {
    let kernel = enforce_max_quadratic_constraint::EnforceSingleMaxQuadraticConstraintGKRRelation {
        relation: input.clone(),
    };
    kernel.evaluate_forward_over_storage(gkr_storage, expected_output_layer, trace_len, worker);
}
