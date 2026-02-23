use super::*;

pub trait BaseFieldInOutFixedSizesEvaluationKernelCore<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN: usize,
    const OUT: usize,
>: Send + Sync
{
    fn pointwise_eval<R: EvaluationRepresentation<F, E>>(&self, input: &[R; IN]) -> [R; OUT];

    fn pointwise_eval_quadratic_term_only<R: EvaluationRepresentation<F, E>>(
        &self,
        input: &[R; IN],
    ) -> [R; OUT];

    #[inline(always)]
    fn pointwise_eval_forward(&self, input: &[BaseFieldRepresentation<F>; IN]) -> [F; OUT] {
        self.pointwise_eval(input).map(|el| el.0)
    }

    fn pointwise_eval_by_ref<R: EvaluationRepresentation<F, E>>(&self, input: [&R; IN])
        -> [R; OUT];
}
