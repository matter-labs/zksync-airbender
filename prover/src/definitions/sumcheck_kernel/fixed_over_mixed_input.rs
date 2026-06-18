use super::*;

pub trait MixedFieldsInOutFixedSizesEvaluationKernelCore<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN_BASE: usize,
    const IN_EXT: usize,
    const OUT: usize,
>: Send + Sync
{
    fn pointwise_eval<RB: EvaluationRepresentation<F, E>>(
        &self,
        input: &[RB; IN_BASE],
        ext_input: &[ExtensionFieldRepresentation<F, E>; IN_EXT],
        ctx: &RB::CollapseContext,
    ) -> [E; OUT];

    fn pointwise_eval_quadratic_term_only<RB: EvaluationRepresentation<F, E>>(
        &self,
        input: &[RB; IN_BASE],
        ext_input: &[ExtensionFieldRepresentation<F, E>; IN_EXT],
        ctx: &RB::CollapseContext,
    ) -> [E; OUT];

    #[inline(always)]
    fn pointwise_eval_forward(
        &self,
        input: &[BaseFieldRepresentation<F>; IN_BASE],
        ext_input: &[ExtensionFieldRepresentation<F, E>; IN_EXT],
    ) -> [E; OUT] {
        self.pointwise_eval(input, ext_input, &())
    }

    fn pointwise_eval_by_ref<RB: EvaluationRepresentation<F, E>>(
        &self,
        input: [&RB; IN_BASE],
        ext_input: [&ExtensionFieldRepresentation<F, E>; IN_EXT],
        ctx: &RB::CollapseContext,
    ) -> [E; OUT];
}
