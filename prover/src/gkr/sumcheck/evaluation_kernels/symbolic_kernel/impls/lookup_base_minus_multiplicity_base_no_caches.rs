use super::*;

impl<F: PrimeField, E: FieldExtension<F> + Field> SameSizeSymbolicGKRKernel<F>
    for LookupBaseMinusMultiplicityByBaseWithoutCachesGKRRelation<F, E>
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        todo!()
    }

    // fn terms(
    //     &self,
    //     challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    // ) -> Vec<BatchedGKRTermDescription<F, E>> {
    //     // 1/(b + gamma) - c/(d + gamma) -> ((d + gamma) - c*(b + gamma)), (b+gamma)*(d+gamma)
    //     let (a, b) = &self.masked_input;
    //     let (c, d) = &self.setup;

    //     let b = vector_lookup_as_flattened_relation::<F, E, true>(
    //         b,
    //         challenge_constants.lookup_challenges_multiplicative_part,
    //         challenge_constants.lookup_challenges_additive_part,
    //     );
    //     let a = (BTreeMap::from_iter([(*a, E::ONE)]), E::ZERO);

    //     let mut d_terms = BTreeMap::new();
    //     let mut challenge = E::ONE;
    //     for el in d.iter() {
    //         assert!(d_terms.insert(*el, challenge).is_none());
    //         challenge.mul_assign(&challenge_constants.lookup_challenges_multiplicative_part);
    //     }
    //     let d = (d_terms, challenge_constants.lookup_challenges_additive_part);
    //     let c = (BTreeMap::from_iter([(*c, E::MINUS_ONE)]), E::ZERO);

    //     let mut num_term = BatchedGKRTermDescription::default();
    //     num_term.add_product_of_linear_base_terms(a, b.clone());
    //     num_term.add_product_of_linear_base_terms(c, d.clone());
    //     num_term.set_extension_output(self.outputs[0]);

    //     let mut den_term = BatchedGKRTermDescription::default();
    //     den_term.add_product_of_linear_base_terms(b, d);
    //     den_term.set_extension_output(self.outputs[1]);

    //     vec![num_term, den_term]
    // }
}
