use super::*;
use std::mem::MaybeUninit;

pub trait BaseFieldInOutFixedSizesEvaluationKernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN: usize,
    const OUT: usize,
>
{
    fn evaluate_first_round<
        S: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>,
        SOUT: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>,
    >(
        &self,
        index: usize,
        sources: &[S; IN],
        output_sources: &[SOUT; OUT],
        batch_challenges: &[E; OUT],
    ) -> [E; 2] {
        assert!(IN > 0);
        assert!(OUT > 0);
        unsafe {
            let mut result = [const { MaybeUninit::uninit() }; 2];
            // we have access to output
            {
                let outputs = output_sources.each_ref().map(|el| el.get_f0_only(index));
                let mut eval = batch_challenges[0];
                eval.mul_assign_by_base(&outputs[0].0);
                for i in 0..OUT {
                    let mut t = batch_challenges[i];
                    t.mul_assign_by_base(&outputs[i].0);
                    eval.add_assign(&t);
                }
                result[0].write(eval);
            }
            {
                let sources = sources.each_ref().map(|el| el.get_f1_minus_f0_only(index));
                let evals = self.pointwise_eval(&sources);
                let mut eval = batch_challenges[0];
                eval.mul_assign_by_base(&evals[0].0);
                for i in 0..OUT {
                    let mut t = batch_challenges[i];
                    t.mul_assign_by_base(&evals[i].0);
                    eval.add_assign(&t);
                }
                result[1].write(eval);
            }

            result.map(|el| el.assume_init())
        }
    }

    fn evaluate<
        R: EvaluationRepresentation<F, E>,
        S: EvaluationFormStorage<F, E, R>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        index: usize,
        sources: &[S; IN],
        batch_challenges: &[E; OUT],
        collapse_ctx: &R::CollapseContext,
    ) -> [E; 2] {
        assert!(IN > 0);
        assert!(OUT > 0);
        unsafe {
            let mut result = [const { MaybeUninit::uninit() }; 2];
            let mut p0s = [const { MaybeUninit::uninit() }; IN];
            let mut p1s = [const { MaybeUninit::uninit() }; IN];
            for i in 0..IN {
                let [f0, f1] = sources[i].get_two_points::<EXPLICIT_FORM>(index);
                p0s[i].write(f0);
                p1s[i].write(f1);
            }
            let p0s = p0s.map(|el| el.assume_init());
            let p1s = p1s.map(|el| el.assume_init());

            for (j, p) in [&p0s, &p1s].into_iter().enumerate() {
                let evals = self.pointwise_eval(p);
                let mut eval = evals[0].collapse_for_batch_eval(collapse_ctx, &batch_challenges[0]);
                for i in 0..OUT {
                    eval.add_assign(
                        &evals[i].collapse_for_batch_eval(collapse_ctx, &batch_challenges[i]),
                    );
                }
                result[j].write(eval);
            }

            result.map(|el| el.assume_init())
        }
    }

    fn pointwise_eval<R: EvaluationRepresentation<F, E>>(&self, input: &[R; IN]) -> [R; OUT];

    #[inline(always)]
    fn pointwise_eval_forward(&self, input: &[BaseFieldRepresentation<F>; IN]) -> [F; OUT] {
        self.pointwise_eval(input).map(|el| el.0)
    }
}

fn evaluate_base_field_in_out_fixed_sizes_evaluation_kernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN: usize,
    const OUT: usize,
    K: BaseFieldInOutFixedSizesEvaluationKernel<F, E, IN, OUT>,
    R: EvaluationRepresentation<F, E>,
    S: EvaluationFormStorage<F, E, R>,
    const EXPLICIT_FORM: bool,
>(
    kernel: &K,
    index: usize,
    sources: &[S],
    batch_challenges: &[E],
) -> [E; 2] {
    debug_assert_eq!(sources.len(), IN);
    debug_assert_eq!(batch_challenges.len(), OUT);
    unsafe {
        let inputs = sources.as_array().unwrap_unchecked();
        let challenges = batch_challenges.as_array().unwrap_unchecked();
        let ctx = inputs.get_unchecked(0).get_collapse_context();
        K::evaluate::<R, S, EXPLICIT_FORM>(kernel, index, inputs, challenges, ctx)
    }
}

fn evaluate_base_field_in_out_fixed_sizes_evaluation_kernel_first_round<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const IN: usize,
    const OUT: usize,
    K: BaseFieldInOutFixedSizesEvaluationKernel<F, E, IN, OUT>,
    S: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>,
    SOUT: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>,
>(
    kernel: &K,
    index: usize,
    sources: &[S],
    outputs: &[SOUT],
    batch_challenges: &[E],
) -> [E; 2] {
    debug_assert_eq!(sources.len(), IN);
    debug_assert_eq!(outputs.len(), OUT);
    debug_assert_eq!(batch_challenges.len(), OUT);
    unsafe {
        let inputs = sources.as_array().unwrap_unchecked();
        let outputs = outputs.as_array().unwrap_unchecked();
        let challenges = batch_challenges.as_array().unwrap_unchecked();
        K::evaluate_first_round::<S, SOUT>(kernel, index, inputs, outputs, challenges)
    }
}
