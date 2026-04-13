use crate::gkr::sumcheck::evaluation_kernels::utils::vector_lookup_as_linear_symbolic_term;

use super::*;

impl<F: PrimeField> SameSizeSymbolicGKRKernel<F> for LookupExtensionPairWithoutCachesGKRRelation {
    fn num_challenges(&self) -> usize {
        2
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        // 1/(b + gamma) + 1/(d + gamma) -> ((d+gamma) + (b+gamma)), (b+gamma) * (d+gamma)
        let [b, d] = &self.inputs;

        let b = vector_lookup_as_linear_symbolic_term::<F, true>(b);

        let d = vector_lookup_as_linear_symbolic_term::<F, true>(d);

        let mut num_term = SymbolicGKRTermDescription::default();
        num_term.add_linear_terms(b.clone());
        num_term.add_linear_terms(d.clone());
        num_term.set_extension_output(self.outputs[0]);

        let mut den_term = SymbolicGKRTermDescription::default();
        den_term.add_product_of_linear_base_terms(b, d);
        den_term.set_extension_output(self.outputs[1]);

        vec![num_term, den_term]
    }
}
