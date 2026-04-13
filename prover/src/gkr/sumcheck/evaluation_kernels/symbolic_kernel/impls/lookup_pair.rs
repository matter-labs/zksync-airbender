use super::*;

impl<F: PrimeField> SameSizeSymbolicGKRKernel<F> for LookupPairGKRRelation {
    fn num_challenges(&self) -> usize {
        2
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        // a/b + c/d = (a*d + c*b) / (b*d)
        let [[a, b], [c, d]] = self.inputs;

        let mut num_term = SymbolicGKRTermDescription::default();
        num_term.quadratic_terms.push(SymbolicGKRQuadraticTerm {
            a: SymbolicGKRInput::ExtensionField(a),
            b: SymbolicGKRInput::ExtensionField(d),
            coefficient_0: SymbolicGKRCoefficient::one(),
            coefficient_1: SymbolicGKRCoefficient::one(),
        });
        num_term.quadratic_terms.push(SymbolicGKRQuadraticTerm {
            a: SymbolicGKRInput::ExtensionField(b),
            b: SymbolicGKRInput::ExtensionField(c),
            coefficient_0: SymbolicGKRCoefficient::one(),
            coefficient_1: SymbolicGKRCoefficient::one(),
        });
        num_term.set_extension_output(self.outputs[0]);

        let mut den_term = SymbolicGKRTermDescription::default();
        den_term.quadratic_terms.push(SymbolicGKRQuadraticTerm {
            a: SymbolicGKRInput::ExtensionField(b),
            b: SymbolicGKRInput::ExtensionField(d),
            coefficient_0: SymbolicGKRCoefficient::one(),
            coefficient_1: SymbolicGKRCoefficient::one(),
        });
        den_term.set_extension_output(self.outputs[1]);

        vec![num_term, den_term]
    }
}
