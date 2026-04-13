use crate::gkr::sumcheck::evaluation_kernels::utils::memory_query_as_linear_symbolic_term;

use super::*;

impl<F: PrimeField> SameSizeSymbolicGKRKernel<F> for MaterializeMemoryTermGKRRelation {
    fn num_challenges(&self) -> usize {
        1
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        let mut term = SymbolicGKRTermDescription::default();
        term.add_linear_terms(memory_query_as_linear_symbolic_term(&self.relation));
        term.set_extension_output(self.output);

        vec![term]
    }
}
