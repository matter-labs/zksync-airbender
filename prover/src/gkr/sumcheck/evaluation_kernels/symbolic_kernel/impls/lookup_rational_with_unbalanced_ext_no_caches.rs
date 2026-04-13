use super::*;

impl<F: PrimeField> SameSizeSymbolicGKRKernel<F>
    for LookupRationalPairWithUnbalancedExtensionWithoutCachesGKRRelation
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        todo!();

        // // a/b + 1/(d + gamma) -> (a*(d+gamma) + b), b * (d+gamma)
        // let [a, b] = self.inputs;
        // let d = &self.remainder;

        // let d = vector_lookup_as_flattened_relation::<F, E, true>(
        //     d,
        //     challenge_constants.lookup_challenges_multiplicative_part,
        //     challenge_constants.lookup_challenges_additive_part,
        // );

        // let mut num_term = SymbolicGKRTermDescription::default();
        // num_term.add_product_ext_by_linear_base(a, d.clone());
        // num_term.add_linear_with_ext(b, E::ONE);
        // num_term.set_extension_output(self.outputs[0]);

        // let mut den_term = SymbolicGKRTermDescription::default();
        // den_term.add_product_ext_by_linear_base(b, d);
        // den_term.set_extension_output(self.outputs[1]);

        // vec![num_term, den_term]
    }
}
