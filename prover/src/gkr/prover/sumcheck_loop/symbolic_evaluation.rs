use super::*;

#[derive(Clone, Debug, Default)]
struct SymbolicGKRDescriptionDraft<F: PrimeField, E: FieldExtension<F> + Field> {
    terms: Vec<(E, SymbolicGKRTermDescription<F>)>,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> KernelCollector<F, E> {
    pub(crate) fn make_symbolic_description(
        &self,
        _layer: usize,
    ) -> SymbolicGKRDescriptionDraft<F, E> {
        let mut draft = SymbolicGKRDescriptionDraft::<F, E>::default();
        for kernel in self.kernels.iter() {
            let terms = kernel.get_symbolic_terms();
            let challenges = kernel.batch_challenges();
            assert_eq!(
                terms.len(),
                challenges.len(),
                "number of challenges diverged for kernel {:?}",
                kernel
            );

            for (batch_challege, term) in challenges.iter().zip(terms.into_iter()) {
                draft.terms.push((*batch_challege, term));
            }
        }

        draft
    }
}

#[cfg(feature = "gkr_self_checks")]
impl<F: PrimeField, E: FieldExtension<F> + Field> KernelCollector<F, E> {
    fn read_eval<const N: usize>(
        last_evaluations: &BTreeMap<GKRAddress, [E; N]>,
        place: SymbolicGKRInput,
        idx: usize,
    ) -> E {
        let address = place.raw_address();
        last_evaluations
            .get(&address)
            .unwrap_or_else(|| panic!("input addr {address:?} not in last_evaluations"))[idx]
    }

    pub(crate) fn evaluate_symbolic_kernel_terms<const N: usize>(
        last_evaluations: &BTreeMap<GKRAddress, [E; N]>,
        challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
        kernel: &dyn SameSizeSymbolicGKRKernel<F>,
        challenges: &[E],
        accumulator: &mut [E; 2],
    ) {
        let terms = kernel.terms();
        assert_eq!(terms.len(), challenges.len());
        for j in 0..2usize {
            for (term_idx, term) in terms.iter().enumerate() {
                let mut contribution = E::ZERO;
                for quadratic in term.quadratic_terms.iter() {
                    let mut a = Self::read_eval(last_evaluations, quadratic.a, j);
                    let b = Self::read_eval(last_evaluations, quadratic.b, j);
                    a.mul_assign(&b);
                    a.mul_assign(&quadratic.coefficient_0.evaluate(challenge_constants));
                    a.mul_assign(&quadratic.coefficient_1.evaluate(challenge_constants));
                    contribution.add_assign(&a);
                }
                for linear in term.linear_terms.iter() {
                    let mut a = Self::read_eval(last_evaluations, linear.a, j);
                    a.mul_assign(&linear.coefficient_0.evaluate(challenge_constants));
                    a.mul_assign(&linear.coefficient_1.evaluate(challenge_constants));
                    contribution.add_assign(&a);
                }
                for constant in term.constant_terms.iter() {
                    let mut a = constant.coefficient_0.evaluate(challenge_constants);
                    a.mul_assign(&constant.coefficient_1.evaluate(challenge_constants));
                    contribution.add_assign(&a);
                }

                contribution.mul_assign(&challenges[term_idx]);
                accumulator[j].add_assign(&contribution);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use cs::gkr_compiler::*;
    use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
    use crate::tests::gkr::deserialize_from_file;

    type F = BabyBearField;
    type E = BabyBearExt4;

    #[test]
    fn compute_stats() {
        let circuit: GKRCircuitArtifact<BabyBearField> = {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_preprocessed_layout_no_caches_gkr.json",
            )
        };

        let layer_idx = 0;
        let layer = &circuit.layers[layer_idx];
        let batch_challenge_base = E::ONE;

        let collector = KernelCollector::<F, E>::from_layer(
            layer,
            layer_idx,
            batch_challenge_base,
            &mut GKRStorage::default(),
            E::ONE,
            E::ONE,
            E::ONE,
            &[],
            0,
        );

        let _ = collector.make_symbolic_description(layer_idx);
    }
}