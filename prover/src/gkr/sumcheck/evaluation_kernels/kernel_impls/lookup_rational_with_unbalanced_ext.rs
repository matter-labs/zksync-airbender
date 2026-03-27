use cs::definitions::GKRAddress;
use worker::Worker;

use crate::definitions::sumcheck_kernel::fixed_over_extension::ExtensionFieldInOutFixedSizesEvaluationKernelCore;

use super::*;

#[derive(Debug)]
pub struct LookupRationalPairWithUnbalancedExtensionGKRRelation<
    F: PrimeField,
    E: FieldExtension<F> + Field,
> {
    pub inputs: [GKRAddress; 2],
    pub remainder: GKRAddress,
    pub outputs: [GKRAddress; 2],
    pub lookup_additive_challenge: E,
    pub _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for LookupRationalPairWithUnbalancedExtensionGKRRelation<F, E>
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn get_inputs(&self) -> GKRInputs {
        GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: vec![self.inputs[0], self.inputs[1], self.remainder],
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
        let kernel = LookupRationalPairWithUnbalancedExtensionGKRRelationKernel::<F, E>::new(
            self.lookup_additive_challenge,
        );
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);
        forward_evaluate_single_input_type_fixed_in_out_kernel_with_extension_inputs(
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
        let kernel = LookupRationalPairWithUnbalancedExtensionGKRRelationKernel::<F, E>::new(
            self.lookup_additive_challenge,
        );
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);

        // println!(
        //     "Evaluating {} with inputs {:?}",
        //     std::any::type_name::<Self>(),
        //     &inputs
        // );

        evaluate_single_input_type_fixed_in_out_kernel_with_extension_inputs(
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

#[derive(Debug)]
pub struct LookupRationalPairWithUnbalancedExtensionGKRRelationKernel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
> {
    pub lookup_additive_challenge: E,
    _marker: core::marker::PhantomData<(F, E)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    LookupRationalPairWithUnbalancedExtensionGKRRelationKernel<F, E>
{
    pub(crate) fn new(lookup_additive_challenge: E) -> Self {
        Self {
            lookup_additive_challenge,
            _marker: core::marker::PhantomData,
        }
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    ExtensionFieldInOutFixedSizesEvaluationKernelCore<F, E, 3, 2>
    for LookupRationalPairWithUnbalancedExtensionGKRRelationKernel<F, E>
{
    #[inline(always)]
    fn pointwise_eval(&self, input: &[ExtensionFieldRepresentation<F, E>; 3]) -> [E; 2] {
        pointwise_eval_impl(input, &self.lookup_additive_challenge)
    }

    #[inline(always)]
    fn pointwise_eval_quadratic_term_only(
        &self,
        input: &[ExtensionFieldRepresentation<F, E>; 3],
    ) -> [E; 2] {
        pointwise_eval_quadratic_only_impl(input)
    }

    fn pointwise_eval_by_ref(&self, _input: [&ExtensionFieldRepresentation<F, E>; 3]) -> [E; 2] {
        todo!()
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    ExtensionFieldInOutFixedSizesEvaluationKernel<F, E, 3, 2>
    for LookupRationalPairWithUnbalancedExtensionGKRRelationKernel<F, E>
{
}

#[inline(always)]
fn pointwise_eval_impl<F: PrimeField, E: FieldExtension<F> + Field>(
    input: &[ExtensionFieldRepresentation<F, E>; 3],
    lookup_additive_challenge: &E,
) -> [E; 2] {
    // a/b + 1/(d+gamma) -> (a*(d+gamma) + b), b*(d+gamma)
    let [a, b, d] = input;
    let mut d = d.into_value();
    d.add_assign(lookup_additive_challenge);

    let mut num = a.into_value();
    num.mul_assign(&d);
    num.add_assign(&b.value);

    let mut den = b.into_value();
    den.mul_assign(&d);

    [num, den]
}

#[inline(always)]
fn pointwise_eval_quadratic_only_impl<F: PrimeField, E: FieldExtension<F> + Field>(
    input: &[ExtensionFieldRepresentation<F, E>; 3],
) -> [E; 2] {
    // a/b + 1/(d+gamma) -> ad, bd
    let [a, b, d] = input;
    let a = a.into_value();
    let b = b.into_value();
    let d = d.into_value();

    let mut num = a;
    num.mul_assign(&d);

    let mut den = b;
    den.mul_assign(&d);

    [num, den]
}
