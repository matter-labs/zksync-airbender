use crate::gkr::sumcheck::evaluation_kernels::utils::memory_query_as_linear_symbolic_term;

use super::*;

impl<F: PrimeField> SameSizeSymbolicGKRKernel<F> for SameSizeProductGKRRelationWithoutCaches {
    fn num_challenges(&self) -> usize {
        1
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        let [a, b] = &self.inputs;
        let mut term = SymbolicGKRTermDescription::default();
        term.add_product_of_linear_base_terms(
            memory_query_as_linear_symbolic_term(a),
            memory_query_as_linear_symbolic_term(b),
        );
        term.set_extension_output(self.output);

        vec![term]
    }
}
