use cs::definitions::GKRAddress;
use worker::Worker;

use crate::definitions::sumcheck_kernel::fixed_over_mixed_input::MixedFieldsInOutFixedSizesEvaluationKernelCore;

use super::*;

#[derive(Debug)]
pub struct LookupBaseExtMinusBaseExtGKRRelation {
    pub nums: [GKRAddress; 2],
    pub dens: [GKRAddress; 2],
    pub outputs: [GKRAddress; 2],
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for LookupBaseExtMinusBaseExtGKRRelation
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: self.nums.to_vec(),
            inputs_in_extension: self.dens.to_vec(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: self.outputs.to_vec(),
        }
    }

    fn evaluate_forward_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        expected_output_layer: usize,
        trace_len: usize,
        worker: &Worker,
    ) {
        let kernel = LookupBaseExtMinusBaseExtGKRRelationKernel {
            _marker: core::marker::PhantomData,
        };
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);
        forward_evaluate_mixed_input_type_fixed_in_out_kernel_with_extension_inputs(
            &kernel,
            &inputs,
            storage,
            expected_output_layer,
            trace_len,
            worker,
        );
    }

    fn evaluate_over_storage<const N: usize>(
        &self,
        storage: &mut GKRStorage<F, E>,
        step: usize,
        batch_challenges: &[E],
        folding_challenges: &[E],
        accumulator: &mut [[E; 2]],
        total_sumcheck_rounds: usize,
        last_evaluations: &mut BTreeMap<GKRAddress, [E; N]>,
        worker: &Worker,
    ) {
        assert_eq!(
            batch_challenges.len(),
            <Self as BatchedGKRKernel<F, E>>::num_challenges(self)
        );
        let kernel = LookupBaseExtMinusBaseExtGKRRelationKernel {
            _marker: core::marker::PhantomData,
        };
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);

        // println!(
        //     "Evaluating {} with inputs {:?}",
        //     std::any::type_name::<Self>(),
        //     &inputs
        // );

        evaluate_mixed_input_type_fixed_in_out_kernel_with_extension_inputs(
            &kernel,
            &inputs,
            storage,
            step,
            batch_challenges,
            folding_challenges,
            accumulator,
            total_sumcheck_rounds,
            last_evaluations,
            worker,
        );
    }
}

// Assumes reordering of access implementors, to have lhs at 0 and rhs at 1
pub struct LookupBaseExtMinusBaseExtGKRRelationKernel<F: PrimeField, E: FieldExtension<F> + Field> {
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    MixedFieldsInOutFixedSizesEvaluationKernelCore<F, E, 2, 2, 2>
    for LookupBaseExtMinusBaseExtGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn pointwise_eval<RB: EvaluationRepresentation<F, E>>(
        &self,
        input: &[RB; 2],
        ext_input: &[ExtensionFieldRepresentation<F, E>; 2],
        ctx: &RB::CollapseContext,
    ) -> [E; 2] {
        // a/b - c/d -> (d*a - c*b), bd
        let [a, c] = input;
        let [b, d] = ext_input;
        let mut ad = a.mul_by_ext::<true>(&d.value, ctx);
        let cb = c.mul_by_ext::<true>(&b.value, ctx);
        ad.sub_assign(&cb);
        let mut den = *b;
        den.repr_mul_assign::<true>(d);

        [ad, den.into_value()]
    }

    #[inline(always)]
    fn pointwise_eval_quadratic_term_only<RB: EvaluationRepresentation<F, E>>(
        &self,
        input: &[RB; 2],
        ext_input: &[ExtensionFieldRepresentation<F, E>; 2],
        ctx: &RB::CollapseContext,
    ) -> [E; 2] {
        self.pointwise_eval(input, ext_input, ctx)
    }

    fn pointwise_eval_by_ref<RB: EvaluationRepresentation<F, E>>(
        &self,
        _input: [&RB; 2],
        _ext_input: [&ExtensionFieldRepresentation<F, E>; 2],
        _ctx: &RB::CollapseContext,
    ) -> [E; 2] {
        todo!()
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    MixedFieldsInOutFixedSizesEvaluationKernel<F, E, 2, 2, 2>
    for LookupBaseExtMinusBaseExtGKRRelationKernel<F, E>
{
}
