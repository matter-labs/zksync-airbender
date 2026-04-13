use super::*;
use crate::gkr::sumcheck::evaluation_kernels::utils::inits_or_teardowns_as_linear_symbolic_term;
use cs::gkr_compiler::InitsOrTeardownsTimestampAndValue;

impl<F: PrimeField> SameSizeSymbolicGKRKernel<F>
    for InitsAndTeardownsInitialProductWithoutCachesGKRRelation
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        let mut term = SymbolicGKRTermDescription::default();
        match self.inputs {
            InitsOrTeardownsTimestampAndValue::Init => {
                let a = inits_or_teardowns_as_linear_symbolic_term(
                    None,
                    self.setup,
                    self.address_high_bits[0],
                    self.address_high_bits_shift,
                );
                let b = inits_or_teardowns_as_linear_symbolic_term(
                    None,
                    self.setup,
                    self.address_high_bits[1],
                    self.address_high_bits_shift,
                );
                term.add_product_of_linear_base_terms(a, b);
            }
            InitsOrTeardownsTimestampAndValue::Teardown {
                lhs_timestamp,
                lhs_value,
                rhs_timestamp,
                rhs_value,
            } => {
                let a = inits_or_teardowns_as_linear_symbolic_term(
                    Some((
                        lhs_timestamp.map(GKRAddress::BaseLayerMemory),
                        lhs_value.map(GKRAddress::BaseLayerMemory),
                    )),
                    self.setup,
                    self.address_high_bits[0],
                    self.address_high_bits_shift,
                );
                let b = inits_or_teardowns_as_linear_symbolic_term(
                    Some((
                        rhs_timestamp.map(GKRAddress::BaseLayerMemory),
                        rhs_value.map(GKRAddress::BaseLayerMemory),
                    )),
                    self.setup,
                    self.address_high_bits[1],
                    self.address_high_bits_shift,
                );
                term.add_product_of_linear_base_terms(a, b);
            }
        }

        term.set_extension_output(self.output);

        vec![term]
    }
}
