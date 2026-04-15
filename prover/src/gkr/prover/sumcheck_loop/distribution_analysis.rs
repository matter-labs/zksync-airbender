use std::collections::BTreeSet;

use super::*;
use cs::definitions::NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES;

impl<F: PrimeField, E: FieldExtension<F> + Field> KernelCollector<F, E> {
    pub(crate) fn analyze_terms(
        &self,
    ) {
        let challenge_constants = BatchedGKRTermDescriptionConstants {
            external_challenges: GKRExternalChallenges { permutation_argument_linearization_challenges: [E::ONE; NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES], permutation_argument_additive_part: E::ONE, _marker: core::marker::PhantomData },
            lookup_challenges_additive_part: E::ONE,
            lookup_challenges_multiplicative_part: E::ONE,
            constraints_batch_challenge: E::ONE,
            _marker: core::marker::PhantomData
        };
        let batched_description = self.make_batched_description(
            &challenge_constants,
            self.layer
        );

        #[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
        struct Occurances {
            quad_terms_with_base: BTreeSet<GKRAddress>,
            quad_terms_with_ext: BTreeSet<GKRAddress>,
            linear_terms: bool,
        }

        let mut occurances_of_base = BTreeMap::<_, Occurances>::new();
        let mut occurances_of_ext = BTreeMap::<_, Occurances>::new();
        for (a, other) in batched_description.quadratic_part_base_by_base.iter() {
            let e = occurances_of_base.entry(*a).or_default();
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                e.quad_terms_with_base.insert(*b);
            }
            // symmetric
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                let e = occurances_of_base.entry(*b).or_default();
                e.quad_terms_with_base.insert(*a);
            }
        }
        for (a, other) in batched_description.quadratic_part_base_by_ext.iter() {
            let e = occurances_of_base.entry(*a).or_default();
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                e.quad_terms_with_ext.insert(*b);
            }
            // symmetric
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                let e = occurances_of_ext.entry(*b).or_default();
                e.quad_terms_with_base.insert(*a);
            }
        }
        for (a, other) in batched_description.quadratic_part_base_by_ext.iter() {
            let e = occurances_of_ext.entry(*a).or_default();
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                e.quad_terms_with_ext.insert(*b);
            }
            // symmetric
            for (b, _) in other.iter() {
                if *a == *b {
                    continue;
                }
                let e = occurances_of_ext.entry(*b).or_default();
                e.quad_terms_with_ext.insert(*a);
            }
        }
        for (a, _) in batched_description.linear_part_base_by_everything.iter() {
            let e = occurances_of_base.entry(*a).or_default();
            e.linear_terms = true;
        }
        for (a, _) in batched_description.linear_part_ext_by_everything.iter() {
            let e = occurances_of_ext.entry(*a).or_default();
            e.linear_terms = true;
        }

        for (a, o) in occurances_of_base.iter() {
            let with_base = o.quad_terms_with_base.len();
            let with_ext = o.quad_terms_with_ext.len();
            let in_linear = o.linear_terms as usize;
            println!("Base variable {:?} happens in {} quad terms with base, {} quad terms with ext and {} linear terms", a, with_base, with_ext, in_linear);
        }

        for (a, o) in occurances_of_ext.iter() {
            let with_base = o.quad_terms_with_base.len();
            let with_ext = o.quad_terms_with_ext.len();
            let in_linear = o.linear_terms as usize;
            println!("Ext variable {:?} happens in {} quad terms with base, {} quad terms with ext and {} linear terms", a, with_base, with_ext, in_linear);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    
    const USE_GKR_WITH_CACHES: bool = true;
    use field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
    use cs::gkr_compiler::GKRCircuitArtifact;
    use crate::tests::gkr::deserialize_from_file;

    type F = BabyBearField;
    type E = BabyBearExt4;

    #[test]
    fn analyze_terms_in_circuit() {
        let circuit: GKRCircuitArtifact<BabyBearField> = if USE_GKR_WITH_CACHES {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_preprocessed_layout_gkr.json",
            )
        } else {
            deserialize_from_file(
                "../cs/compiled_circuits/add_sub_lui_auipc_mop_preprocessed_layout_no_caches_gkr.json",
            )
        };

        let layer_idx = 0;
        let layer = &circuit.layers[layer_idx];

        let collector = KernelCollector::<F, E>::from_layer(
            layer,
            layer_idx,
            E::ONE,
            E::ONE,
            E::ONE,
            E::ONE,
            &[],
            0
        );

        collector.analyze_terms();
    }
}