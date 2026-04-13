use super::*;
use crate::gkr::sumcheck::evaluation_kernels::utils::vector_lookup_as_linear_symbolic_term;
use cs::definitions::gkr::NoFieldLinearRelation;
use cs::definitions::gkr::NoFieldVectorLookupRelation;

impl<F: PrimeField> SameSizeSymbolicGKRKernel<F>
    for LookupExtensionMinusMultiplicityByExtensionWithoutCachesGKRRelation
{
    fn num_challenges(&self) -> usize {
        2
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        // 1/(b + gamma) - c/(d + gamma) -> ((d+gamma) - c*(b+gamma)), (b+gamma) * (d+gamma)
        let b = &self.input;
        let (c, d) = &self.setup;
        assert_eq!(b.columns.len(), d.len());

        let setup_as_rel = NoFieldVectorLookupRelation {
            columns: d
                .iter()
                .map(|el| NoFieldLinearRelation {
                    linear_terms: vec![(F::ONE.as_u32_reduced(), *el)].into_boxed_slice(),
                    constant: 0,
                })
                .collect::<Vec<_>>()
                .into_boxed_slice(),
            lookup_set_index: usize::MAX, // not important
        };

        let b = vector_lookup_as_linear_symbolic_term::<F, true>(b);
        let d = vector_lookup_as_linear_symbolic_term::<F, true>(&setup_as_rel);

        let c = (
            vec![SymbolicGKRLinearTerm {
                a: SymbolicGKRInput::BaseField(*c),
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
