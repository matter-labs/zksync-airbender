use super::*;

impl<F: PrimeField> SameSizeSymbolicGKRKernel<F> for SameSizeProductGKRRelation {
    fn num_challenges(&self) -> usize {
        1
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        let [a, b] = self.inputs;

        let mut term = SymbolicGKRTermDescription::default();
        term.quadratic_terms.push(SymbolicGKRQuadraticTerm {
            a: SymbolicGKRInput::ExtensionField(a),
            b: SymbolicGKRInput::ExtensionField(b),
            coefficient_0: SymbolicGKRCoefficient::one(),
            coefficient_1: SymbolicGKRCoefficient::one(),
        });
        term.set_extension_output(self.output);

        vec![term]
    }
}
