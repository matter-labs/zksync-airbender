use super::*;

impl<F: PrimeField, E: FieldExtension<F> + Field> SameSizeSymbolicGKRKernel<F>
    for LookupRationalPairWithUnbalancedBaseGKRRelation<F, E>
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        todo!();

        // // a/b + 1/(d+gamma) -> (a*(d+gamma) + b), b*(d+gamma)
        // let [a, b] = self.inputs;
        // let d = self.remainder;

        // let mut num_term = BatchedGKRTermDescription::default();
        // num_term.add_base_by_ext(d, a, E::ONE);
        // num_term.add_linear_with_ext(a, challenge_constants.lookup_challenges_additive_part);
        // num_term.add_linear_with_ext(b, E::ONE);
        // num_term.set_extension_output(self.outputs[0]);

        // let mut den_term = BatchedGKRTermDescription::default();
        // den_term.add_base_by_ext(d, b, E::ONE);
        // den_term.add_linear_with_ext(b, challenge_constants.lookup_challenges_additive_part);
        // den_term.set_extension_output(self.outputs[1]);

        // vec![num_term, den_term]
    }
}
