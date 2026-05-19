use super::*;

pub trait SingleInputTypeBatchSumcheckEvaluationKernelCore<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const OUT: usize,
>: Send + Sync
{
    fn pointwise_eval(&self, input: &[E]) -> [E; OUT];
}

pub trait SingleInputTypeBatchSumcheckEvaluationKernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const OUT: usize,
>: Send + Sync + SingleInputTypeBatchSumcheckEvaluationKernelCore<F, E, OUT>
{
    fn num_challenges(&self) -> usize {
        OUT
    }
    fn evaluate_forward<SB: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>>(
        &self,
        index: usize,
        sources: &[SB],
    ) -> [F; OUT];
    fn evaluate_first_round<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        ROUT: EvaluationRepresentation<F, E>,
        SOUT: EvaluationFormStorage<F, E, ROUT>,
    >(
        &self,
        index: usize,
        r0_sources: &[S0],
        output_sources: &[SOUT], // we keep it dynamic as there is no need to then make a dummy one for batch constraints
        batch_challenges: &[E],
        collapse_ctx: &R0::CollapseContext,
        out_collapse_ctx: &ROUT::CollapseContext,
    ) -> [E; 2];

    fn evaluate<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        index: usize,
        r0_sources: &[S0],
        batch_challenges: &[E],
        collapse_ctx: &R0::CollapseContext,
    ) -> [E; 2];
}
