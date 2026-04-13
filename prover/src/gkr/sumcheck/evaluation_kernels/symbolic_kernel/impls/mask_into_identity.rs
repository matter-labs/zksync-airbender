use super::*;

impl<F: PrimeField> SameSizeSymbolicGKRKernel<F> for MaskIntoIdentityProductGKRRelation {
    fn num_challenges(&self) -> usize {
        1
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        // (input(X) - 1) * mask(X) + 1

        let mut term = SymbolicGKRTermDescription::default();
        term.quadratic_terms.push(SymbolicGKRQuadraticTerm {
            a: SymbolicGKRInput::BaseField(self.mask),
            b: SymbolicGKRInput::ExtensionField(self.input),
            coefficient_0: SymbolicGKRCoefficient::one(),
            coefficient_1: SymbolicGKRCoefficient::one(),
        });
        term.linear_terms.push(SymbolicGKRLinearTerm {
            a: SymbolicGKRInput::BaseField(self.mask),
            coefficient_0: SymbolicGKRCoefficient::from_base_field(F::MINUS_ONE),
            coefficient_1: SymbolicGKRCoefficient::one(),
        });
        term.add_simple_constant_term(SymbolicGKRCoefficient::from_base_field(F::ONE));
        term.set_extension_output(self.output);

        vec![term]
    }
}
