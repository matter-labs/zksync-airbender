use super::*;
use cs::{definitions::GKRAddress, gkr_compiler::NoFieldMaxQuadraticGKRRelation};

#[derive(Debug)]
pub struct EnforceSingleMaxQuadraticConstraintGKRRelation {
    pub relation: NoFieldMaxQuadraticGKRRelation,
}

pub(crate) fn remap<F: PrimeField>(
    relation: &NoFieldMaxQuadraticGKRRelation,
) -> (
    Vec<GKRAddress>,
    EnforceSingleMaxQuadraticConstraintGKRKernel<F>,
) {
    let mut remapper = DenseInputRemapper::default();
    let mut inputs = vec![];
    let mut kernel = EnforceSingleMaxQuadraticConstraintGKRKernel {
        relation: relation.clone(),
        quadratic_parts: Vec::new(),
        linear_parts: Vec::new(),
        constant_offset: F::from_u32_unchecked(relation.constant),
    };

    for (a, other) in relation.quadratic_terms.iter() {
        let (is_new, a_offset) = remapper.remap(*a);
        if is_new {
            inputs.push(*a);
        }
        for (c, b) in other.iter() {
            let b_offset = if *a != *b {
                let (is_new, b_offset) = remapper.remap(*b);

                if is_new {
                    inputs.push(*b);
                }

                b_offset
            } else {
                a_offset
            };

            kernel
                .quadratic_parts
                .push(((a_offset, b_offset), F::from_u32_unchecked(*c)));
        }
    }

    for (c, a) in relation.linear_terms.iter() {
        let (is_new, a_offset) = remapper.remap(*a);
        if is_new {
            inputs.push(*a);
        }

        kernel
            .linear_parts
            .push((a_offset, F::from_u32_unchecked(*c)));
    }

    (inputs, kernel)
}

impl<F: PrimeField, E: FieldExtension<F> + Field> BatchedGKRKernel<F, E>
    for EnforceSingleMaxQuadraticConstraintGKRRelation
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn get_inputs(&self) -> GKRInputs {
        // use remapper to match the kernel
        let inputs_in_base = remap::<F>(&self.relation).0;
        GKRInputs {
            inputs_in_base,
            inputs_in_extension: Vec::new(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        }
    }

    fn terms(
        &self,
        _challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    ) -> Vec<BatchedGKRTermDescription<F, E>> {
        let mut term = BatchedGKRTermDescription::default();

        for (a, other_terms) in self.relation.quadratic_terms.iter() {
            for (c, b) in other_terms.iter() {
                term.add_base_by_base(*a, *b, E::from_base(F::from_u32_unchecked(*c)));
            }
        }

        for (c, b) in self.relation.linear_terms.iter() {
            term.add_linear_with_base(*b, E::from_base(F::from_u32_unchecked(*c)));
        }
        term.add_constant(E::from_base(F::from_u32_unchecked(self.relation.constant)));

        // just no output

        vec![term]
    }

    fn evaluate_forward_over_storage(
        &self,
        storage: &mut GKRStorage<F, E>,
        expected_output_layer: usize,
        trace_len: usize,
        worker: &Worker,
    ) {
        let inputs = <Self as BatchedGKRKernel<F, E>>::get_inputs(self);
        let kernel = remap(&self.relation).1;
        forward_evaluate_single_input_kernel_with_base_inputs(
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
        _storage: &mut GKRStorage<F, E>,
        _step: usize,
        _batch_challenges: &[E],
        _folding_challenges: &[E],
        _accumulator: &mut [[E; 2]],
        _total_sumcheck_rounds: usize,
        _last_evaluations: &mut BTreeMap<GKRAddress, [E; N]>,
        _worker: &Worker,
    ) {
        unimplemented!("not used");
    }
}

#[derive(Debug)]
// Assumes reordering of access implementors, to have lhs at 0 and rhs at 1
pub struct EnforceSingleMaxQuadraticConstraintGKRKernel<F: PrimeField> {
    pub relation: NoFieldMaxQuadraticGKRRelation,
    pub quadratic_parts: Vec<((usize, usize), F)>,
    pub linear_parts: Vec<(usize, F)>,
    pub constant_offset: F,
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    SingleInputTypeBatchSumcheckEvaluationKernelCore<F, E, 0>
    for EnforceSingleMaxQuadraticConstraintGKRKernel<F>
{
    #[inline(always)]
    fn pointwise_eval(&self, _input: &[E]) -> [E; 0] {
        unimplemented!("not used")
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field>
    SingleInputTypeBatchSumcheckEvaluationKernel<F, E, 0>
    for EnforceSingleMaxQuadraticConstraintGKRKernel<F>
{
    fn num_challenges(&self) -> usize {
        1
    }

    #[inline(always)]
    fn evaluate_forward<SB: EvaluationFormStorage<F, E, BaseFieldRepresentation<F>>>(
        &self,
        index: usize,
        sources: &[SB],
    ) -> [F; 0] {
        let mut result = self.constant_offset;
        for ((a, b), c) in self.quadratic_parts.iter() {
            let mut t = sources[*a].get_at_index(index).0;
            t.mul_assign(&sources[*b].get_at_index(index).0);
            t.mul_assign(c);
            result.add_assign(&t);
        }

        for (a, c) in self.linear_parts.iter() {
            let mut t = sources[*a].get_at_index(index).0;
            t.mul_assign(c);
            result.add_assign(&t);
        }

        if result.is_zero() == false {
            for (i, source) in sources.iter().enumerate() {
                let value = source.get_at_index(index).0;
                println!("Source {} = {}", i, value);
            }
            panic!("Constraint kernel {:?} diverged at index {}", self, index);
        }

        []
    }

    #[inline(always)]
    fn evaluate_first_round<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        ROUT: EvaluationRepresentation<F, E>,
        SOUT: EvaluationFormStorage<F, E, ROUT>,
    >(
        &self,
        _index: usize,
        _r0_sources: &[S0],
        _output_sources: &[SOUT],
        _batch_challenges: &[E],
        _ctx: &R0::CollapseContext,
        _out_collapse_ctx: &ROUT::CollapseContext,
    ) -> [E; 2] {
        unimplemented!("not used")
    }

    #[inline(always)]
    fn evaluate<
        R0: EvaluationRepresentation<F, E>,
        S0: EvaluationFormStorage<F, E, R0>,
        const EXPLICIT_FORM: bool,
    >(
        &self,
        _index: usize,
        _r0_sources: &[S0],
        _batch_challenges: &[E],
        _ctx: &R0::CollapseContext,
    ) -> [E; 2] {
        unimplemented!("not used")
    }
}
