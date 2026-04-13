use super::*;

impl<F: PrimeField, E: FieldExtension<F> + Field> SameSizeSymbolicGKRKernel<F>
    for LookupBaseMinusMultiplicityByBaseGKRRelation<F, E>
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        // 1/(b + gamma) - c/(d + gamma) -> ((d + gamma) - c*(b + gamma)), (b+gamma)*(d+gamma)
        let [c, d] = self.setup;
        let b = self.input;

        let b = (
            vec![SymbolicGKRLinearTerm {
                a: SymbolicGKRInput::BaseField(b),
                coefficient_0: SymbolicGKRCoefficient::one(),
                coefficient_1: SymbolicGKRCoefficient::one(),
            }],
            vec![SymbolicGKRCoefficient {
                constant: F::ONE,
                challenge: Some(ChallengeType::LookupAdditivePart),
            }],
        );
        let d = (
            vec![SymbolicGKRLinearTerm {
                a: SymbolicGKRInput::BaseField(d),
                coefficient_0: SymbolicGKRCoefficient::one(),
                coefficient_1: SymbolicGKRCoefficient::one(),
            }],
            vec![SymbolicGKRCoefficient {
                constant: F::ONE,
                challenge: Some(ChallengeType::LookupAdditivePart),
            }],
        );
        let c = (
            vec![SymbolicGKRLinearTerm {
                a: SymbolicGKRInput::BaseField(c),
                coefficient_0: SymbolicGKRCoefficient::from_base_field(F::MINUS_ONE),
                coefficient_1: SymbolicGKRCoefficient::one(),
            }],
            vec![],
        );

        let mut num_term = SymbolicGKRTermDescription::default();
        num_term.add_linear_terms(d.clone());
        num_term.add_product_of_linear_base_terms(c, b.clone());
        num_term.set_extension_output(self.outputs[0]);

        let mut den_term = SymbolicGKRTermDescription::default();
        den_term.add_product_of_linear_base_terms(b, d);
        den_term.set_extension_output(self.outputs[1]);

        vec![num_term, den_term]
    }
}
