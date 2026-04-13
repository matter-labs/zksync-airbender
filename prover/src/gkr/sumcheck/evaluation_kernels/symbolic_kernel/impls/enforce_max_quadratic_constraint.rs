use super::*;

impl<F: PrimeField> SameSizeSymbolicGKRKernel<F>
    for EnforceSingleMaxQuadraticConstraintGKRRelation
{
    fn num_challenges(&self) -> usize {
        1
    }

    fn terms(&self) -> Vec<SymbolicGKRTermDescription<F>> {
        let mut term = SymbolicGKRTermDescription::default();

        for (a, other_terms) in self.relation.quadratic_terms.iter() {
            for (c, b) in other_terms.iter() {
                let t = SymbolicGKRQuadraticTerm {
                    a: SymbolicGKRInput::BaseField(*a),
                    b: SymbolicGKRInput::BaseField(*b),
                    coefficient_0: SymbolicGKRCoefficient {
                        constant: F::from_u32_unchecked(*c),
                        challenge: None,
                    },
                    coefficient_1: SymbolicGKRCoefficient::one(),
                };
                term.quadratic_terms.push(t);
            }
        }

        for (c, a) in self.relation.linear_terms.iter() {
            let t = SymbolicGKRLinearTerm {
                a: SymbolicGKRInput::BaseField(*a),
                coefficient_0: SymbolicGKRCoefficient {
                    constant: F::from_u32_unchecked(*c),
                    challenge: None,
                },
                coefficient_1: SymbolicGKRCoefficient::one(),
            };
            term.linear_terms.push(t);
        }
        let constant = F::from_u32_unchecked(self.relation.constant);
        if constant.is_zero() == false {
            term.add_simple_constant_term(SymbolicGKRCoefficient::from_base_field(constant));
        }

        // just no output

        vec![term]
    }
}
