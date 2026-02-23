use super::*;

pub trait ExtensionFieldInOutFixedSizesEvaluationKernelCore<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN: usize,
    const OUT: usize,
>: Send + Sync
{
    fn pointwise_eval(&self, input: &[ExtensionFieldRepresentation<F, E>; IN]) -> [E; OUT];

    fn pointwise_eval_quadratic_term_only(
        &self,
        input: &[ExtensionFieldRepresentation<F, E>; IN],
    ) -> [E; OUT];

    #[inline(always)]
    fn pointwise_eval_forward(&self, input: &[ExtensionFieldRepresentation<F, E>; IN]) -> [E; OUT] {
        self.pointwise_eval(input)
    }

    fn pointwise_eval_by_ref(&self, input: [&ExtensionFieldRepresentation<F, E>; IN]) -> [E; OUT];
}
