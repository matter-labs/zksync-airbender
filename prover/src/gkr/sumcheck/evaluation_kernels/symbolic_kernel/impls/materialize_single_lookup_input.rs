use crate::gkr::sumcheck::evaluation_kernels::utils::single_column_lookup_as_linear_symbolic_term;

use super::*;

impl<F: PrimeField> SameSizeSymbolicGKRKernel<F> for MaterializeSingleLookupInputGKRRelation {
    fn num_challenges(&self) -> usize {
        1
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        let mut term = SymbolicGKRTermDescription::default();
        term.add_linear_terms(single_column_lookup_as_linear_symbolic_term::<F, false>(
            &self.input,
        ));
        term.set_base_output(self.output);

        vec![term]
    }
}
