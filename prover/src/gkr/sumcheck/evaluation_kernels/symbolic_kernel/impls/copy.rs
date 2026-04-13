use super::*;

impl<F: PrimeField> SameSizeSymbolicGKRKernel<F> for BaseFieldCopyGKRRelation {
    fn num_challenges(&self) -> usize {
        1
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        let mut term = SymbolicGKRTermDescription::default();
        term.linear_terms.push(SymbolicGKRLinearTerm {
            a: SymbolicGKRInput::BaseField(self.input),
            coefficient_0: SymbolicGKRCoefficient::one(),
            coefficient_1: SymbolicGKRCoefficient::one(),
        });
        term.set_base_output(self.output);
        vec![term]
    }
}

impl<F: PrimeField> SameSizeSymbolicGKRKernel<F> for ExtensionCopyGKRRelation {
    fn num_challenges(&self) -> usize {
        1
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        let mut term = SymbolicGKRTermDescription::default();
        term.linear_terms.push(SymbolicGKRLinearTerm {
            a: SymbolicGKRInput::ExtensionField(self.input),
            coefficient_0: SymbolicGKRCoefficient::one(),
            coefficient_1: SymbolicGKRCoefficient::one(),
        });
        term.set_extension_output(self.output);
        vec![term]
    }
}
