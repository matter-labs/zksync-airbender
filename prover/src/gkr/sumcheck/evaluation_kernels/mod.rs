use crate::gkr::sumcheck::access_and_fold::GKRStorage;
use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, PrimeField};
use std::collections::BTreeMap;
use worker::Worker;

pub use crate::definitions::sumcheck_kernel::dynamic_over_single_input_type::*;
pub use crate::definitions::sumcheck_kernel::*;

pub mod kernel_impls;

pub mod generic_kernel;
pub mod simple_in_base;
pub mod simple_in_extension;
pub mod simple_mixed;

pub use self::generic_kernel::*;
pub use self::kernel_impls::*;
pub use self::simple_in_base::*;
pub use self::simple_in_extension::*;
pub use self::simple_mixed::*;

pub trait TwoInputTypesBatchSumcheckEvaluationKernel<F: PrimeField, E: FieldExtension<F> + Field> {
    fn num_challenges(&self) -> usize;

    fn evaluate_first_round<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        R1: EvaluationRepresentation<F, E>,
        S1: EvaluationFormStorage<F, E, R1>,
        ROUT: EvaluationRepresentation<F, E>,
        SOUT: EvaluationFormStorage<F, E, ROUT>,
    >(
        &self,
        index: usize,
        r0_sources: &[S0],
        r1_sources: &[S1],
        _output_sources: &[SOUT],
        batch_challenges: &[E],
    ) -> [E; 2] {
        self.evaluate::<R0, S0, R1, S1, false>(index, r0_sources, r1_sources, batch_challenges)
    }

    fn evaluate<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        R1: EvaluationRepresentation<F, E>,
        S1: EvaluationFormStorage<F, E, R1>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        index: usize,
        r0_sources: &[S0],
        r1_sources: &[S1],
        batch_challenges: &[E],
    ) -> [E; 2];
}
