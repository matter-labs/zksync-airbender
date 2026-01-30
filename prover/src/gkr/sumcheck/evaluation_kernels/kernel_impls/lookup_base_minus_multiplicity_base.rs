use cs::definitions::GKRAddress;
use worker::Worker;

use super::*;

pub struct LookupBaseMinusMultiplicityByBaseGKRRelation<F: PrimeField, E: FieldExtension<F> + Field>
{
    pub input: GKRAddress,
    pub setup: [GKRAddress; 2],
    pub outputs: [GKRAddress; 2],
    pub lookup_additive_challenge: E,
    pub _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for LookupBaseMinusMultiplicityByBaseGKRRelation<F, E>
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: vec![self.input, self.setup[0], self.setup[1]],
            inputs_in_extension: Vec::new(),
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
        let kernel = LookupBaseMinusMultiplicityByBaseGKRRelationKernel::<F, E> {
            lookup_additive_challenge: self.lookup_additive_challenge,
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

    fn evaluate_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        step: usize,
        batch_challenges: &[E],
        folding_challenges: &[E],
        accumulator: &mut [[E; 2]],
        total_sumcheck_rounds: usize,
        last_evaluations: &mut BTreeMap<GKRAddress, [E; 2]>,
        worker: &Worker,
    ) {
        todo!();

        // assert_eq!(
        //     batch_challenges.len(),
        //     <Self as BatchedGKRKernel<F, E>>::num_challenges(self)
        // );
        // let kernel = LookupBaseExtMinusBaseExtGKRRelationKernel {
        //     _marker: core::marker::PhantomData,
        // };
        // let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);

        // evaluate_mixed_input_type_fixed_in_out_kernel_with_extension_inputs(
        //     &kernel,
        //     &inputs,
        //     storage,
        //     step,
        //     batch_challenges,
        //     folding_challenges,
        //     accumulator,
        //     total_sumcheck_rounds,
        //     last_evaluations,
        //     worker,
        // );
    }
}

// Assumes reordering of access implementors, to have lhs at 0 and rhs at 1
pub struct LookupBaseMinusMultiplicityByBaseGKRRelationKernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
> {
    pub lookup_additive_challenge: E,
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    MixedFieldsInOutFixedSizesEvaluationKernel<F, E, 3, 0, 2>
    for LookupBaseMinusMultiplicityByBaseGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn pointwise_eval<RB: EvaluationRepresentation<F, E>>(
        &self,
        input: &[RB; 3],
        _ext_input: &[ExtensionFieldRepresentation<F, E>; 0],
        ctx: &RB::CollapseContext,
    ) -> [E; 2] {
        // 1/b - c/d -> (d - c*b), bd
        let [b, c, d] = input;
        let b = b.add_with_ext_repr::<true>(
            &ExtensionFieldRepresentation::new(self.lookup_additive_challenge),
            ctx,
        );
        let d = d.add_with_ext_repr::<true>(
            &ExtensionFieldRepresentation::new(self.lookup_additive_challenge),
            ctx,
        );
        let cb = c.mul_by_ext_repr::<true>(&ExtensionFieldRepresentation::new(b), ctx);
        let mut num = d;
        num.sub_assign(&cb);

        let mut den = b;
        den.mul_assign(&d);

        [num, den]
    }
}
