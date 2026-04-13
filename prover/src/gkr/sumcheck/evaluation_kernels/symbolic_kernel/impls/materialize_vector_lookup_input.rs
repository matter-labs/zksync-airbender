use crate::gkr::sumcheck::evaluation_kernels::utils::vector_lookup_as_linear_symbolic_term;

use super::*;

impl<F: PrimeField, E: FieldExtension<F> + Field> SameSizeSymbolicGKRKernel<F>
    for MaterializeVectorLookupInputGKRRelation<F, E>
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        // NOTE: we do not mix-in additive parts in such cases
        let mut term = SymbolicGKRTermDescription::default();
        term.add_linear_terms(vector_lookup_as_linear_symbolic_term::<F, false>(
            &self.relation,
        ));
        term.set_extension_output(self.output);

        vec![term]
    }
}
