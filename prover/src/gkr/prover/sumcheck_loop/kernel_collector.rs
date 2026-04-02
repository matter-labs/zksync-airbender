use std::collections::BTreeMap;

use crate::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use crate::gkr::prover::dimension_reduction::kernels::logup::LookupPairDimensionReducingGKRRelation;
use crate::gkr::prover::dimension_reduction::kernels::pairwise_product::PairwiseProductDimensionReducingGKRRelation;
use crate::gkr::sumcheck::access_and_fold::GKRStorage;
use crate::gkr::sumcheck::evaluation_kernels::{
    BaseFieldCopyGKRRelation, BatchConstraintEvalGKRRelation, BatchedGKRKernel,
    ExtensionCopyGKRRelation, LookupBaseExtMinusBaseExtGKRRelation,
    LookupBaseMinusMultiplicityByBaseGKRRelation, LookupBasePairGKRRelation,
    LookupExtensionMinusMultiplicityByExtensionGKRRelation, LookupExtensionPairGKRRelation,
    LookupExtensionPairGKRRelationKernel, LookupPairGKRRelation,
    LookupRationalPairWithUnbalancedBaseGKRRelation,
    LookupRationalPairWithUnbalancedExtensionGKRRelation,
    LookupRationalPairWithUnbalancedExtensionGKRRelationKernel, MaskIntoIdentityProductGKRRelation,
    MaterializeVectoLookupInputGKRRelation, MaxQuadraticGKRRelation, SameSizeProductGKRRelation,
};
use crate::worker::Worker;
use field::{Field, FieldExtension, PrimeField};

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRLayerDescription, NoFieldGKRRelation, OutputType};

macro_rules! define_kernel_variants {
    (
        single { $($s_name:ident($s_type:ty)),* $(,)? }
        pair { $($p_name:ident($p_type:ty)),* $(,)? }
        no_output { $($n_name:ident($n_type:ty)),* $(,)? }
    ) => {
        #[derive(Debug)]
        pub(super) enum KernelVariant<F: PrimeField, E: FieldExtension<F> + Field> {
            $($s_name($s_type, [E; 1], GKRAddress),)*
            $($p_name($p_type, [E; 2], [GKRAddress; 2]),)*
            $($n_name($n_type, [E; 1]),)*
        }

        impl<F: PrimeField, E: FieldExtension<F> + Field> KernelVariant<F, E> {
            pub fn num_challenges(&self) -> usize {
                match self {
                    $(KernelVariant::$s_name(ref k, _, _) => BatchedGKRKernel::<F, E>::num_challenges(k),)*
                    $(KernelVariant::$p_name(ref k, _, _) => BatchedGKRKernel::<F, E>::num_challenges(k),)*
                    $(KernelVariant::$n_name(ref k, _) => BatchedGKRKernel::<F, E>::num_challenges(k),)*
                }
            }

            pub const fn batch_challenges(&self) -> &[E] {
                match self {
                    $(KernelVariant::$s_name(_, bc, _) => bc,)*
                    $(KernelVariant::$p_name(_, bc, _) => bc,)*
                    $(KernelVariant::$n_name(_, bc) => bc,)*
                }
            }

            pub fn evaluate_over_storage<const N: usize>(
                &self,
                storage: &mut GKRStorage<F, E>,
                step: usize,
                folding_challenges: &[E],
                accumulator: &mut [[E; 2]],
                total_sumcheck_rounds: usize,
                last_evaluations: &mut BTreeMap<GKRAddress, [E; N]>,
                worker: &Worker,
            ) {
                let batch_challenges = self.batch_challenges();
                debug_assert_eq!(batch_challenges.len(), self.num_challenges());

                match self {
                    $(KernelVariant::$s_name(ref k, _, _) => k.evaluate_over_storage(
                        storage, step, batch_challenges, folding_challenges,
                        accumulator, total_sumcheck_rounds, last_evaluations, worker,
                    ),)*
                    $(KernelVariant::$p_name(ref k, _, _) => k.evaluate_over_storage(
                        storage, step, batch_challenges, folding_challenges,
                        accumulator, total_sumcheck_rounds, last_evaluations, worker,
                    ),)*
                    $(KernelVariant::$n_name(ref k, _) => k.evaluate_over_storage(
                        storage, step, batch_challenges, folding_challenges,
                        accumulator, total_sumcheck_rounds, last_evaluations, worker,
                    ),)*
                }
            }

            pub fn compute_output_claim(&self, output_claims: &BTreeMap<GKRAddress, E>) -> E {
                match self {
                    $(KernelVariant::$s_name(_, challenge, output_addr) => {
                        let mut res = challenge[0];
                        let Some(out_claim) = output_claims
                            .get(output_addr) else {
                                panic!("Claim missing for {:?} in kernel {:?}", output_addr, self);
                            };
                        res.mul_assign(out_claim);
                        res
                    })*
                    $(KernelVariant::$p_name(_, challenges, addrs) => {
                        let mut res = E::ZERO;
                        for (challenge, addr) in challenges.iter().zip(addrs.iter()) {
                            if let Some(claim) = output_claims.get(addr) {
                                let mut weighted = *claim;
                                weighted.mul_assign(challenge);
                                res.add_assign(&weighted);
                            } else {
                                panic!("Claim missing for {:?} in kernel {:?}", addr, self);
                            }
                        }
                        res
                    })*
                    $(KernelVariant::$n_name(..) => E::ZERO,)*
                }
            }
        }
    };
}

define_kernel_variants! {
    // single challenge, single output
    single {
        BaseCopy(BaseFieldCopyGKRRelation),
        ExtCopy(ExtensionCopyGKRRelation),
        Product(SameSizeProductGKRRelation),
        MaskIdentity(MaskIntoIdentityProductGKRRelation),
        PairwiseProductDimensionReducing(PairwiseProductDimensionReducingGKRRelation),
        MaxQuadratic(MaxQuadraticGKRRelation::<F, E>),
        MaterializeVectorLookupInput(MaterializeVectoLookupInputGKRRelation<F, E>),
    }
    // 2 challenges, two outputs
    pair {
        AggregateLookupPair(LookupPairGKRRelation),
        LookupBasePair(LookupBasePairGKRRelation<F, E>),
        LookupVectorPair(LookupExtensionPairGKRRelation<F, E>),
        LookupBaseMinusMultiplicityByBase(LookupBaseMinusMultiplicityByBaseGKRRelation<F, E>),
        LookupExtensionMinusMultiplicityByExtension(LookupExtensionMinusMultiplicityByExtensionGKRRelation<F, E>),
        LookupUnbalancedWithBase(LookupRationalPairWithUnbalancedBaseGKRRelation<F, E>),
        LookupUnbalancedWithExtension(LookupRationalPairWithUnbalancedExtensionGKRRelation<F, E>),
        LookupMaskedVectorMinusSetup(LookupBaseExtMinusBaseExtGKRRelation<F, E>),
        LookupPairDimensionReducing(LookupPairDimensionReducingGKRRelation),
    }
    // single challenge, no output
    no_output {
        EnforceConstraintsMaxQuadratic(BatchConstraintEvalGKRRelation<F, E>),
    }
}

impl<F: PrimeField, E: FieldExtension<F> + Field> KernelVariant<F, E> {
    pub fn from_enforced_relations(
        relation: &NoFieldGKRRelation,
        layer_idx: usize,
        gkr_storage: &GKRStorage<F, E>,
        lookup_challenges_multiplicative_part: E,
        lookup_challenges_additive_part: E,
        challenge_for_constraints: E,
        current_batch_challenge: &mut E,
        batch_challenge_base: &E,
    ) -> Self {
        let mut get_challenge = || {
            let c = *current_batch_challenge;
            current_batch_challenge.mul_assign(batch_challenge_base);
            c
        };

        match relation {
            NoFieldGKRRelation::Copy { input, output } => {
                let challenge = [get_challenge()];
                let is_base_field = gkr_storage.layers[layer_idx]
                    .base_field_inputs
                    .contains_key(input);
                if is_base_field {
                    assert!(
                        gkr_storage.layers[layer_idx]
                            .extension_field_inputs
                            .contains_key(input)
                            == false
                    );
                    Self::BaseCopy(
                        BaseFieldCopyGKRRelation {
                            input: *input,
                            output: *output,
                        },
                        challenge,
                        *output,
                    )
                } else {
                    assert!(
                        gkr_storage.layers[layer_idx]
                            .base_field_inputs
                            .contains_key(input)
                            == false
                    );
                    Self::ExtCopy(
                        ExtensionCopyGKRRelation {
                            input: *input,
                            output: *output,
                        },
                        challenge,
                        *output,
                    )
                }
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
            | NoFieldGKRRelation::TrivialProduct { input, output } => {
                let challenge = [get_challenge()];
                Self::Product(
                    SameSizeProductGKRRelation {
                        inputs: *input,
                        output: *output,
                    },
                    challenge,
                    *output,
                )
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                let challenge = [get_challenge()];
                Self::MaskIdentity(
                    MaskIntoIdentityProductGKRRelation {
                        input: *input,
                        mask: *mask,
                        output: *output,
                    },
                    challenge,
                    *output,
                )
            }
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                let challenges = [get_challenge(), get_challenge()];
                Self::AggregateLookupPair(
                    LookupPairGKRRelation {
                        inputs: *input,
                        outputs: *output,
                    },
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                let challenges = [get_challenge(), get_challenge()];
                Self::LookupBasePair(
                    LookupBasePairGKRRelation {
                        inputs: *input,
                        outputs: *output,
                        lookup_additive_challenge: lookup_challenges_additive_part,
                        _marker: core::marker::PhantomData,
                    },
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                let challenges = [get_challenge(), get_challenge()];
                Self::LookupBaseMinusMultiplicityByBase(
                    LookupBaseMinusMultiplicityByBaseGKRRelation {
                        input: *input,
                        setup: *setup,
                        outputs: *output,
                        lookup_additive_challenge: lookup_challenges_additive_part,
                        _marker: core::marker::PhantomData,
                    },
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                let challenges = [get_challenge(), get_challenge()];
                Self::LookupUnbalancedWithBase(
                    LookupRationalPairWithUnbalancedBaseGKRRelation {
                        inputs: *input,
                        remainder: *remainder,
                        outputs: *output,
                        lookup_additive_challenge: lookup_challenges_additive_part,
                        _marker: core::marker::PhantomData,
                    },
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                input,
                remainder,
                output,
            } => {
                let challenges = [get_challenge(), get_challenge()];
                Self::LookupUnbalancedWithExtension(
                    LookupRationalPairWithUnbalancedExtensionGKRRelation {
                        inputs: *input,
                        remainder: *remainder,
                        outputs: *output,
                        lookup_additive_challenge: lookup_challenges_additive_part,
                        _marker: core::marker::PhantomData,
                    },
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                let challenges = [get_challenge(), get_challenge()];
                Self::LookupMaskedVectorMinusSetup(
                    LookupBaseExtMinusBaseExtGKRRelation {
                        nums: [input[0], setup[0]],
                        dens: [input[1], setup[1]],
                        outputs: *output,
                        lookup_additive_challenge: lookup_challenges_additive_part,
                        _marker: core::marker::PhantomData,
                    },
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { input } => {
                let challenge = [get_challenge()];
                Self::EnforceConstraintsMaxQuadratic(
                    BatchConstraintEvalGKRRelation::new(input, challenge_for_constraints),
                    challenge,
                )
            }
            NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { input, output } => {
                let challenges = [get_challenge(), get_challenge()];
                Self::LookupVectorPair(
                    LookupExtensionPairGKRRelation {
                        inputs: *input,
                        outputs: *output,
                        lookup_additive_challenge: lookup_challenges_additive_part,
                        _marker: core::marker::PhantomData,
                    },
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::MaxQuadratic { input, output } => {
                let challenges = [get_challenge()];
                Self::MaxQuadratic(
                    MaxQuadraticGKRRelation::new(input, *output),
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let challenges = [get_challenge(), get_challenge()];
                Self::LookupExtensionMinusMultiplicityByExtension(
                    LookupExtensionMinusMultiplicityByExtensionGKRRelation {
                        input: *input,
                        setup: *setup,
                        outputs: *output,
                        lookup_additive_challenge: lookup_challenges_additive_part,
                        _marker: core::marker::PhantomData,
                    },
                    challenges,
                    *output,
                )
            }
            NoFieldGKRRelation::MaterializedVectorLookupInput { input, output } => {
                let challenges = [get_challenge()];
                Self::MaterializeVectorLookupInput(
                    MaterializeVectoLookupInputGKRRelation::new(
                        input,
                        *output,
                        lookup_challenges_multiplicative_part,
                    ),
                    challenges,
                    *output,
                )
            }
            // NoFieldGKRRelation::MaterializeSingleLookupInput { .. } => todo!(),
            // NoFieldGKRRelation::MaterializedVectorLookupInput { .. } => todo!(),
            // NoFieldGKRRelation::LookupPairFromBaseInputs { .. } => todo!(),
            // NoFieldGKRRelation::LookupPairFromVectorInputs { .. } => todo!(),
            a @ _ => {
                panic!("Relation {:?} is not yet implemented", a);
            }
        }
    }

    #[cfg(feature = "gkr_self_checks")]
    #[allow(dead_code)]
    pub fn debug_compute_final_step_contribution<const N: usize>(
        &self,
        last_evaluations: &BTreeMap<GKRAddress, [E; N]>,
    ) -> [E; 2] {
        use crate::definitions::sumcheck_kernel::{
            dynamic_over_single_input_type::SingleInputTypeBatchSumcheckEvaluationKernelCore,
            evaluation_representation::ExtensionFieldRepresentation,
            fixed_over_base::BaseFieldInOutFixedSizesEvaluationKernelCore,
            fixed_over_extension::ExtensionFieldInOutFixedSizesEvaluationKernelCore,
            fixed_over_mixed_input::MixedFieldsInOutFixedSizesEvaluationKernelCore,
        };
        use crate::gkr::prover::dimension_reduction::kernels::{
            logup::LookupPairDimensionReducingGKRRelationKernel,
            pairwise_product::PairwiseProductDimensionReducingGKRRelationKernel,
            DimensionReducingEvaluationKernel,
        };
        use crate::gkr::sumcheck::evaluation_kernels::{
            BaseFieldCopyGKRRelationKernel, ExtensionCopyGKRRelationKernel,
            LookupAdditionGKRRelationKernel, LookupBaseExtMinusBaseExtGKRRelationKernel,
            LookupBaseMinusMultiplicityByBaseGKRRelationKernel, LookupBasePairGKRRelationKernel,
            LookupRationalPairWithUnbalancedBaseGKRRelationKernel,
            LookupRationalPairWithUnbalancedExtensionGKRRelationKernel,
            MaskIntoIdentityProductGKRRelationKernel, ProductGKRRelationKernel,
        };

        let get = |addr: GKRAddress, j: usize| -> E {
            last_evaluations
                .get(&addr)
                .unwrap_or_else(|| panic!("input addr {addr:?} not in last_evaluations"))[j]
        };

        let efr = |v: E| ExtensionFieldRepresentation::<F, E> {
            value: v,
            _marker: core::marker::PhantomData,
        };

        let mut acc = [E::ZERO; 2];
        match self {
            KernelVariant::BaseCopy(rel, challenge, _) => {
                let k = BaseFieldCopyGKRRelationKernel::<F, E>::default();
                for j in 0..2usize {
                    let in0 = efr(get(rel.input, j));
                    let [out] =
                        BaseFieldInOutFixedSizesEvaluationKernelCore::<F, E, 1, 1>::pointwise_eval(
                            &k,
                            &[in0],
                        );
                    let mut val = out.value;
                    val.mul_assign(&challenge[0]);
                    acc[j].add_assign(&val);
                }
            }
            KernelVariant::ExtCopy(rel, challenge, _) => {
                let k = ExtensionCopyGKRRelationKernel::<F, E>::default();
                for j in 0..2usize {
                    let in0 = efr(get(rel.input, j));
                    let [mut val] = ExtensionFieldInOutFixedSizesEvaluationKernelCore::<
                        F,
                        E,
                        1,
                        1,
                    >::pointwise_eval(&k, &[in0]);
                    val.mul_assign(&challenge[0]);
                    acc[j].add_assign(&val);
                }
            }
            KernelVariant::Product(rel, challenge, _) => {
                let k = ProductGKRRelationKernel::<F, E>::default();
                for j in 0..2usize {
                    let in0 = efr(get(rel.inputs[0], j));
                    let in1 = efr(get(rel.inputs[1], j));
                    let [mut val] = ExtensionFieldInOutFixedSizesEvaluationKernelCore::<
                        F,
                        E,
                        2,
                        1,
                    >::pointwise_eval(&k, &[in0, in1]);
                    val.mul_assign(&challenge[0]);
                    acc[j].add_assign(&val);
                }
            }
            KernelVariant::MaskIdentity(rel, challenge, _) => {
                let k = MaskIntoIdentityProductGKRRelationKernel::<F, E>::default();
                for j in 0..2usize {
                    let in_base = efr(get(rel.mask, j));
                    let in_ext = efr(get(rel.input, j));
                    let [mut val] = MixedFieldsInOutFixedSizesEvaluationKernelCore::<
                        F,
                        E,
                        1,
                        1,
                        1,
                    >::pointwise_eval(&k, &[in_base], &[in_ext], &());
                    val.mul_assign(&challenge[0]);
                    acc[j].add_assign(&val);
                }
            }
            KernelVariant::AggregateLookupPair(rel, challenges, _) => {
                let k = LookupAdditionGKRRelationKernel::<F, E>::default();
                for j in 0..2usize {
                    let in0 = efr(get(rel.inputs[0][0], j));
                    let in1 = efr(get(rel.inputs[0][1], j));
                    let in2 = efr(get(rel.inputs[1][0], j));
                    let in3 = efr(get(rel.inputs[1][1], j));
                    let computed = ExtensionFieldInOutFixedSizesEvaluationKernelCore::<
                        F,
                        E,
                        4,
                        2,
                    >::pointwise_eval(&k, &[in0, in1, in2, in3]);

                    let mut val0 = computed[0];
                    val0.mul_assign(&challenges[0]);
                    acc[j].add_assign(&val0);

                    let mut val1 = computed[1];
                    val1.mul_assign(&challenges[1]);
                    acc[j].add_assign(&val1);
                }
            }
            KernelVariant::LookupBasePair(rel, challenges, _) => {
                let k = LookupBasePairGKRRelationKernel::<F, E>::new(rel.lookup_additive_challenge);
                for j in 0..2usize {
                    let in0 = efr(get(rel.inputs[0], j));
                    let in1 = efr(get(rel.inputs[1], j));
                    let computed = MixedFieldsInOutFixedSizesEvaluationKernelCore::<
                        F,
                        E,
                        2,
                        0,
                        2,
                    >::pointwise_eval(&k, &[in0, in1], &[], &());

                    let mut val0 = computed[0];
                    val0.mul_assign(&challenges[0]);
                    acc[j].add_assign(&val0);

                    let mut val1 = computed[1];
                    val1.mul_assign(&challenges[1]);
                    acc[j].add_assign(&val1);
                }
            }
            KernelVariant::LookupVectorPair(rel, challenges, _) => {
                let k = LookupExtensionPairGKRRelationKernel::<F, E>::new(
                    rel.lookup_additive_challenge,
                );
                for j in 0..2usize {
                    let in0 = efr(get(rel.inputs[0], j));
                    let in1 = efr(get(rel.inputs[1], j));
                    let computed = ExtensionFieldInOutFixedSizesEvaluationKernelCore::<
                        F,
                        E,
                        2,
                        2,
                    >::pointwise_eval(&k, &[in0, in1]);

                    let mut val0 = computed[0];
                    val0.mul_assign(&challenges[0]);
                    acc[j].add_assign(&val0);

                    let mut val1 = computed[1];
                    val1.mul_assign(&challenges[1]);
                    acc[j].add_assign(&val1);
                }
            }
            KernelVariant::LookupBaseMinusMultiplicityByBase(rel, challenges, _) => {
                let k = LookupBaseMinusMultiplicityByBaseGKRRelationKernel::<F, E>::new(
                    rel.lookup_additive_challenge,
                );
                for j in 0..2usize {
                    let in0 = efr(get(rel.input, j));
                    let in1 = efr(get(rel.setup[0], j));
                    let in2 = efr(get(rel.setup[1], j));
                    let computed = MixedFieldsInOutFixedSizesEvaluationKernelCore::<
                        F,
                        E,
                        3,
                        0,
                        2,
                    >::pointwise_eval(&k, &[in0, in1, in2], &[], &());

                    let mut val0 = computed[0];
                    val0.mul_assign(&challenges[0]);
                    acc[j].add_assign(&val0);

                    let mut val1 = computed[1];
                    val1.mul_assign(&challenges[1]);
                    acc[j].add_assign(&val1);
                }
            }
            KernelVariant::LookupUnbalancedWithBase(rel, challenges, _) => {
                let k = LookupRationalPairWithUnbalancedBaseGKRRelationKernel::<F, E>::new(
                    rel.lookup_additive_challenge,
                );
                for j in 0..2usize {
                    let in_base = efr(get(rel.remainder, j));
                    let in_ext0 = efr(get(rel.inputs[0], j));
                    let in_ext1 = efr(get(rel.inputs[1], j));
                    let computed = MixedFieldsInOutFixedSizesEvaluationKernelCore::<
                        F,
                        E,
                        1,
                        2,
                        2,
                    >::pointwise_eval(&k, &[in_base], &[in_ext0, in_ext1], &());

                    let mut val0 = computed[0];
                    val0.mul_assign(&challenges[0]);
                    acc[j].add_assign(&val0);

                    let mut val1 = computed[1];
                    val1.mul_assign(&challenges[1]);
                    acc[j].add_assign(&val1);
                }
            }
            KernelVariant::LookupExtensionMinusMultiplicityByExtension(rel, challenges, _) => {
                use crate::gkr::sumcheck::evaluation_kernels::LookupExtensionMinusMultiplicityByExtensionGKRRelationKernel;

                let k = LookupExtensionMinusMultiplicityByExtensionGKRRelationKernel::<F, E>::new(
                    rel.lookup_additive_challenge,
                );
                for j in 0..2usize {
                    let b_in0 = efr(get(rel.setup[0], j));
                    let e_in0 = efr(get(rel.input, j));
                    let e_in1 = efr(get(rel.setup[1], j));
                    let computed = MixedFieldsInOutFixedSizesEvaluationKernelCore::<
                        F,
                        E,
                        1,
                        2,
                        2,
                    >::pointwise_eval(&k, &[b_in0], &[e_in0, e_in1], &());

                    let mut val0 = computed[0];
                    val0.mul_assign(&challenges[0]);
                    acc[j].add_assign(&val0);

                    let mut val1 = computed[1];
                    val1.mul_assign(&challenges[1]);
                    acc[j].add_assign(&val1);
                }
            }
            KernelVariant::LookupUnbalancedWithExtension(rel, challenges, _) => {
                let k = LookupRationalPairWithUnbalancedExtensionGKRRelationKernel::<F, E>::new(
                    rel.lookup_additive_challenge,
                );
                for j in 0..2usize {
                    let in_ext0 = efr(get(rel.inputs[0], j));
                    let in_ext1 = efr(get(rel.inputs[1], j));
                    let remainder_in_ext = efr(get(rel.remainder, j));
                    let computed = ExtensionFieldInOutFixedSizesEvaluationKernelCore::<
                        F,
                        E,
                        3,
                        2,
                    >::pointwise_eval(&k, &[in_ext0, in_ext1, remainder_in_ext]);

                    let mut val0 = computed[0];
                    val0.mul_assign(&challenges[0]);
                    acc[j].add_assign(&val0);

                    let mut val1 = computed[1];
                    val1.mul_assign(&challenges[1]);
                    acc[j].add_assign(&val1);
                }
            }
            KernelVariant::LookupMaskedVectorMinusSetup(rel, challenges, _) => {
                let k = LookupBaseExtMinusBaseExtGKRRelationKernel::<F, E>::new(
                    rel.lookup_additive_challenge,
                );
                for j in 0..2usize {
                    let in_base0 = efr(get(rel.nums[0], j));
                    let in_base1 = efr(get(rel.nums[1], j));
                    let in_ext0 = efr(get(rel.dens[0], j));
                    let in_ext1 = efr(get(rel.dens[1], j));
                    let computed = MixedFieldsInOutFixedSizesEvaluationKernelCore::<
                        F,
                        E,
                        2,
                        2,
                        2,
                    >::pointwise_eval(&k, &[in_base0, in_base1], &[in_ext0, in_ext1], &());

                    let mut val0 = computed[0];
                    val0.mul_assign(&challenges[0]);
                    acc[j].add_assign(&val0);

                    let mut val1 = computed[1];
                    val1.mul_assign(&challenges[1]);
                    acc[j].add_assign(&val1);
                }
            }
            KernelVariant::MaterializeVectorLookupInput(rel, challenge, _) => {
                for j in 0..2usize {
                    let inputs_vec: Vec<E> = rel.inputs.iter().map(|addr| get(*addr, j)).collect();
                    let [val] = rel.kernel.pointwise_eval(&inputs_vec);
                    let mut contrib = val;
                    contrib.mul_assign(&challenge[0]);
                    acc[j].add_assign(&contrib);
                }
            }
            KernelVariant::MaxQuadratic(rel, challenge, _) => {
                for j in 0..2usize {
                    let inputs_vec: Vec<E> = rel.inputs.iter().map(|addr| get(*addr, j)).collect();
                    let [val] = rel.kernel.pointwise_eval(&inputs_vec);
                    let mut contrib = val;
                    contrib.mul_assign(&challenge[0]);
                    acc[j].add_assign(&contrib);
                }
            }
            KernelVariant::EnforceConstraintsMaxQuadratic(rel, challenge) => {
                for j in 0..2usize {
                    let inputs_vec: Vec<E> = rel
                        .inputs
                        .iter()
                        .map(|addr| {
                            if *addr == GKRAddress::placeholder() {
                                E::ZERO
                            } else {
                                get(*addr, j)
                            }
                        })
                        .collect();
                    let [val] = rel.kernel.pointwise_eval(&inputs_vec);
                    let mut contrib = val;
                    contrib.mul_assign(&challenge[0]);
                    acc[j].add_assign(&contrib);
                }
            }
            KernelVariant::PairwiseProductDimensionReducing(rel, challenge, _) => {
                let k = PairwiseProductDimensionReducingGKRRelationKernel::default();
                let evals = last_evaluations.get(&rel.input).unwrap_or_else(|| {
                    panic!("input addr {:?} not in last_evaluations", rel.input)
                });
                let [val0] = k.pointwise_eval(&[efr(evals[0])], &[efr(evals[1])]);
                let mut v0 = val0;
                v0.mul_assign(&challenge[0]);
                acc[0].add_assign(&v0);

                let [val1] = k.pointwise_eval(&[efr(evals[2])], &[efr(evals[3])]);
                let mut v1 = val1;
                v1.mul_assign(&challenge[0]);
                acc[1].add_assign(&v1);
            }
            KernelVariant::LookupPairDimensionReducing(rel, challenges, _) => {
                let k = LookupPairDimensionReducingGKRRelationKernel::default();
                let v0 = last_evaluations.get(&rel.inputs[0]).unwrap_or_else(|| {
                    panic!("input addr {:?} not in last_evaluations", rel.inputs[0])
                });
                let v1 = last_evaluations.get(&rel.inputs[1]).unwrap_or_else(|| {
                    panic!("input addr {:?} not in last_evaluations", rel.inputs[1])
                });

                let computed0 =
                    k.pointwise_eval(&[efr(v0[0]), efr(v1[0])], &[efr(v0[1]), efr(v1[1])]);
                let mut c0 = computed0[0];
                c0.mul_assign(&challenges[0]);
                acc[0].add_assign(&c0);
                let mut c1 = computed0[1];
                c1.mul_assign(&challenges[1]);
                acc[0].add_assign(&c1);

                let computed1 =
                    k.pointwise_eval(&[efr(v0[2]), efr(v1[2])], &[efr(v0[3]), efr(v1[3])]);
                let mut c2 = computed1[0];
                c2.mul_assign(&challenges[0]);
                acc[1].add_assign(&c2);
                let mut c3 = computed1[1];
                c3.mul_assign(&challenges[1]);
                acc[1].add_assign(&c3);
            }
        }

        acc
    }
}

pub(super) struct KernelCollector<F: PrimeField, E: FieldExtension<F> + Field> {
    kernels: Vec<KernelVariant<F, E>>,
    current_batch_challenge: E,
    batch_challenge_base: E,
}

impl<F: PrimeField, E: FieldExtension<F> + Field> KernelCollector<F, E> {
    pub(super) const fn new(batch_challenge_base: E) -> Self {
        Self {
            kernels: Vec::new(),
            current_batch_challenge: E::ONE,
            batch_challenge_base,
        }
    }

    pub(super) const fn is_empty(&self) -> bool {
        self.kernels.is_empty()
    }

    pub(super) fn register(&mut self, kernel: KernelVariant<F, E>) {
        // Kernels can have a bug in them, place to debug
        match kernel {
            // KernelVariant::MaterializeVectorLookupInput(..) => {},
            // KernelVariant::EnforceConstraintsMaxQuadratic(..) => {},
            // KernelVariant::LookupExtensionMinusMultiplicityByExtension(..) => {},
            _ => self.kernels.push(kernel),
        }
    }

    pub(super) fn compute_combined_claim(&self, output_claims: &BTreeMap<GKRAddress, E>) -> E {
        self.kernels.iter().fold(E::ZERO, |mut acc, kernel| {
            acc.add_assign(&kernel.compute_output_claim(output_claims));
            acc
        })
    }

    pub(super) fn from_layer(
        layer: &GKRLayerDescription,
        layer_idx: usize,
        batch_challenge_base: E,
        gkr_storage: &GKRStorage<F, E>,
        lookup_challenges_multiplicative_part: E,
        lookup_challenges_additive_part: E,
        challenge_for_constraints: E,
    ) -> Self {
        let mut collector = Self::new(batch_challenge_base);

        debug_assert!(layer.gates.is_empty() ^ layer.gates_with_external_connections.is_empty());

        let batch_base = collector.batch_challenge_base;

        for gate in layer
            .gates
            .iter()
            .chain(layer.gates_with_external_connections.iter())
        {
            let kernel = KernelVariant::from_enforced_relations(
                &gate.enforced_relation,
                layer_idx,
                gkr_storage,
                lookup_challenges_multiplicative_part,
                lookup_challenges_additive_part,
                challenge_for_constraints,
                &mut collector.current_batch_challenge,
                &batch_base,
            );

            collector.register(kernel);
        }

        collector
    }

    pub(super) fn from_dimension_reducing_relations(
        layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
        _layer_idx: usize,
        batch_challenge_base: E,
    ) -> Self {
        let mut collector = Self::new(batch_challenge_base);
        let batch_base = collector.batch_challenge_base;

        let get_challenge = |cbc: &mut E| {
            let c = *cbc;
            cbc.mul_assign(&batch_base);
            c
        };

        for (k, v) in layer {
            match *k {
                OutputType::PermutationProduct => {
                    for (inp, out) in v.inputs.iter().zip(v.output.iter()) {
                        let challenge = [get_challenge(&mut collector.current_batch_challenge)];
                        collector.register(KernelVariant::PairwiseProductDimensionReducing(
                            PairwiseProductDimensionReducingGKRRelation {
                                input: *inp,
                                output: *out,
                            },
                            challenge,
                            *out,
                        ));
                    }
                }
                OutputType::Lookup16Bits
                | OutputType::LookupTimestamps
                | OutputType::GenericLookup => {
                    let challenges = [
                        get_challenge(&mut collector.current_batch_challenge),
                        get_challenge(&mut collector.current_batch_challenge),
                    ];
                    let outputs: [GKRAddress; 2] = v.output.clone().try_into().unwrap();
                    collector.register(KernelVariant::LookupPairDimensionReducing(
                        LookupPairDimensionReducingGKRRelation {
                            inputs: v.inputs.clone().try_into().unwrap(),
                            outputs,
                        },
                        challenges,
                        outputs,
                    ));
                }
            }
        }

        collector
    }

    pub(super) fn evaluate_kernels_over_storage<const N: usize>(
        &self,
        storage: &mut GKRStorage<F, E>,
        step: usize,
        folding_challenges: &[E],
        accumulator: &mut [[E; 2]],
        folding_steps: usize,
        last_evaluations: &mut BTreeMap<GKRAddress, [E; N]>,
        worker: &Worker,
    ) {
        // let is_final_step = step + 1 == folding_steps;
        self.kernels.iter().for_each(|kernel| {
            // let before = if is_final_step && accumulator.len() == 1 {
            //     Some(accumulator[0])
            // } else {
            //     None
            // };

            kernel.evaluate_over_storage(
                storage,
                step,
                folding_challenges,
                accumulator,
                folding_steps,
                last_evaluations,
                worker,
            );

            // if let Some(before) = before {
            //     let after = accumulator[0];
            //     let mut delta0 = after[0];
            //     delta0.sub_assign(&before[0]);
            //     let mut delta1 = after[1];
            //     delta1.sub_assign(&before[1]);
            //     #[cfg(feature = "gkr_self_checks")]
            //     let expected = kernel.debug_compute_final_step_contribution(last_evaluations);
            //     println!(
            //         "Final-step kernel contribution {:?}: actual=[{:?}, {:?}]{}",
            //         kernel,
            //         delta0,
            //         delta1,
            //         {
            //             #[cfg(feature = "gkr_self_checks")]
            //             {
            //                 format!(", expected=[{:?}, {:?}]", expected[0], expected[1])
            //             }
            //             #[cfg(not(feature = "gkr_self_checks"))]
            //             {
            //                 String::new()
            //             }
            //         }
            //     );
            //     #[cfg(feature = "gkr_self_checks")]
            //     if [delta0, delta1] != expected {
            //         println!(
            //             "Final-step kernel mismatch for {:?}: actual=[{:?}, {:?}], expected=[{:?}, {:?}]",
            //             kernel, delta0, delta1, expected[0], expected[1]
            //         );
            //     }
            // }
        });
    }
}

#[cfg(feature = "gkr_self_checks")]
impl<F: PrimeField, E: FieldExtension<F> + Field> KernelCollector<F, E> {
    pub(super) fn compute_last_step_accumulator_from_evals<const N: usize>(
        &self,
        last_evaluations: &BTreeMap<GKRAddress, [E; N]>,
    ) -> [E; 2] {
        use crate::definitions::sumcheck_kernel::{
            evaluation_representation::ExtensionFieldRepresentation,
            fixed_over_base::BaseFieldInOutFixedSizesEvaluationKernelCore,
            fixed_over_extension::ExtensionFieldInOutFixedSizesEvaluationKernelCore,
            fixed_over_mixed_input::MixedFieldsInOutFixedSizesEvaluationKernelCore,
        };
        use crate::gkr::sumcheck::evaluation_kernels::{
            BaseFieldCopyGKRRelationKernel, ExtensionCopyGKRRelationKernel,
            LookupAdditionGKRRelationKernel, LookupBaseExtMinusBaseExtGKRRelationKernel,
            LookupBaseMinusMultiplicityByBaseGKRRelationKernel, LookupBasePairGKRRelationKernel,
            LookupRationalPairWithUnbalancedBaseGKRRelationKernel,
            MaskIntoIdentityProductGKRRelationKernel, ProductGKRRelationKernel,
            SingleInputTypeBatchSumcheckEvaluationKernelCore,
        };

        use crate::gkr::prover::dimension_reduction::kernels::{
            logup::LookupPairDimensionReducingGKRRelationKernel,
            pairwise_product::PairwiseProductDimensionReducingGKRRelationKernel,
            DimensionReducingEvaluationKernel,
        };

        let mut acc = [E::ZERO; 2];

        let get = |addr: GKRAddress, j: usize| -> E {
            last_evaluations
                .get(&addr)
                .unwrap_or_else(|| panic!("input addr {addr:?} not in last_evaluations"))[j]
        };

        let efr = |v: E| ExtensionFieldRepresentation::<F, E> {
            value: v,
            _marker: core::marker::PhantomData,
        };

        for kernel in &self.kernels {
            match kernel {
                KernelVariant::BaseCopy(rel, challenge, _) => {
                    let k = BaseFieldCopyGKRRelationKernel::<F, E>::default();
                    for j in 0..2usize {
                        let in0 = efr(get(rel.input, j));
                        let [out] = BaseFieldInOutFixedSizesEvaluationKernelCore::<F, E, 1, 1>::pointwise_eval(&k, &[in0]);
                        let mut val = out.value;
                        val.mul_assign(&challenge[0]);
                        acc[j].add_assign(&val);
                    }
                }
                KernelVariant::ExtCopy(rel, challenge, _) => {
                    let k = ExtensionCopyGKRRelationKernel::<F, E>::default();
                    for j in 0..2usize {
                        let in0 = efr(get(rel.input, j));
                        let [mut val] = ExtensionFieldInOutFixedSizesEvaluationKernelCore::<
                            F,
                            E,
                            1,
                            1,
                        >::pointwise_eval(&k, &[in0]);
                        val.mul_assign(&challenge[0]);
                        acc[j].add_assign(&val);
                    }
                }
                KernelVariant::Product(rel, challenge, _) => {
                    let k = ProductGKRRelationKernel::<F, E>::default();
                    for j in 0..2usize {
                        let in0 = efr(get(rel.inputs[0], j));
                        let in1 = efr(get(rel.inputs[1], j));
                        let [mut val] = ExtensionFieldInOutFixedSizesEvaluationKernelCore::<
                            F,
                            E,
                            2,
                            1,
                        >::pointwise_eval(&k, &[in0, in1]);
                        val.mul_assign(&challenge[0]);
                        acc[j].add_assign(&val);
                    }
                }
                KernelVariant::MaskIdentity(rel, challenge, _) => {
                    let k = MaskIntoIdentityProductGKRRelationKernel::<F, E>::default();
                    for j in 0..2usize {
                        let in_base = efr(get(rel.mask, j));
                        let in_ext = efr(get(rel.input, j));
                        let [mut val] = MixedFieldsInOutFixedSizesEvaluationKernelCore::<
                            F,
                            E,
                            1,
                            1,
                            1,
                        >::pointwise_eval(
                            &k, &[in_base], &[in_ext], &()
                        );
                        val.mul_assign(&challenge[0]);
                        acc[j].add_assign(&val);
                    }
                }
                KernelVariant::AggregateLookupPair(rel, challenges, _) => {
                    let k = LookupAdditionGKRRelationKernel::<F, E>::default();
                    for j in 0..2usize {
                        let in0 = efr(get(rel.inputs[0][0], j));
                        let in1 = efr(get(rel.inputs[0][1], j));
                        let in2 = efr(get(rel.inputs[1][0], j));
                        let in3 = efr(get(rel.inputs[1][1], j));
                        let computed = ExtensionFieldInOutFixedSizesEvaluationKernelCore::<
                            F,
                            E,
                            4,
                            2,
                        >::pointwise_eval(
                            &k, &[in0, in1, in2, in3]
                        );

                        let mut val0 = computed[0];
                        val0.mul_assign(&challenges[0]);
                        acc[j].add_assign(&val0);

                        let mut val1 = computed[1];
                        val1.mul_assign(&challenges[1]);
                        acc[j].add_assign(&val1);
                    }
                }
                KernelVariant::LookupBasePair(rel, challenges, _) => {
                    let k =
                        LookupBasePairGKRRelationKernel::<F, E>::new(rel.lookup_additive_challenge);
                    for j in 0..2usize {
                        let in0 = efr(get(rel.inputs[0], j));
                        let in1 = efr(get(rel.inputs[1], j));
                        let computed = MixedFieldsInOutFixedSizesEvaluationKernelCore::<
                            F,
                            E,
                            2,
                            0,
                            2,
                        >::pointwise_eval(
                            &k, &[in0, in1], &[], &()
                        );

                        let mut val0 = computed[0];
                        val0.mul_assign(&challenges[0]);
                        acc[j].add_assign(&val0);

                        let mut val1 = computed[1];
                        val1.mul_assign(&challenges[1]);
                        acc[j].add_assign(&val1);
                    }
                }
                KernelVariant::LookupVectorPair(rel, challenges, _) => {
                    let k = LookupExtensionPairGKRRelationKernel::<F, E>::new(
                        rel.lookup_additive_challenge,
                    );
                    for j in 0..2usize {
                        let in0 = efr(get(rel.inputs[0], j));
                        let in1 = efr(get(rel.inputs[1], j));
                        let computed = ExtensionFieldInOutFixedSizesEvaluationKernelCore::<
                            F,
                            E,
                            2,
                            2,
                        >::pointwise_eval(&k, &[in0, in1]);

                        let mut val0 = computed[0];
                        val0.mul_assign(&challenges[0]);
                        acc[j].add_assign(&val0);

                        let mut val1 = computed[1];
                        val1.mul_assign(&challenges[1]);
                        acc[j].add_assign(&val1);
                    }
                }
                KernelVariant::LookupBaseMinusMultiplicityByBase(rel, challenges, _) => {
                    let k = LookupBaseMinusMultiplicityByBaseGKRRelationKernel::<F, E>::new(
                        rel.lookup_additive_challenge,
                    );
                    for j in 0..2usize {
                        let in0 = efr(get(rel.input, j));
                        let in1 = efr(get(rel.setup[0], j));
                        let in2 = efr(get(rel.setup[1], j));
                        let computed = MixedFieldsInOutFixedSizesEvaluationKernelCore::<
                            F,
                            E,
                            3,
                            0,
                            2,
                        >::pointwise_eval(
                            &k, &[in0, in1, in2], &[], &()
                        );

                        let mut val0 = computed[0];
                        val0.mul_assign(&challenges[0]);
                        acc[j].add_assign(&val0);

                        let mut val1 = computed[1];
                        val1.mul_assign(&challenges[1]);
                        acc[j].add_assign(&val1);
                    }
                }
                KernelVariant::LookupUnbalancedWithBase(rel, challenges, _) => {
                    let k = LookupRationalPairWithUnbalancedBaseGKRRelationKernel::<F, E>::new(
                        rel.lookup_additive_challenge,
                    );
                    for j in 0..2usize {
                        let in_base = efr(get(rel.remainder, j));
                        let in_ext0 = efr(get(rel.inputs[0], j));
                        let in_ext1 = efr(get(rel.inputs[1], j));
                        let computed = MixedFieldsInOutFixedSizesEvaluationKernelCore::<
                            F,
                            E,
                            1,
                            2,
                            2,
                        >::pointwise_eval(
                            &k, &[in_base], &[in_ext0, in_ext1], &()
                        );

                        let mut val0 = computed[0];
                        val0.mul_assign(&challenges[0]);
                        acc[j].add_assign(&val0);

                        let mut val1 = computed[1];
                        val1.mul_assign(&challenges[1]);
                        acc[j].add_assign(&val1);
                    }
                }
                KernelVariant::LookupExtensionMinusMultiplicityByExtension(rel, challenges, _) => {
                    use crate::gkr::sumcheck::evaluation_kernels::LookupExtensionMinusMultiplicityByExtensionGKRRelationKernel;

                    let k =
                        LookupExtensionMinusMultiplicityByExtensionGKRRelationKernel::<F, E>::new(
                            rel.lookup_additive_challenge,
                        );
                    for j in 0..2usize {
                        let b_in0 = efr(get(rel.setup[0], j));
                        let e_in0 = efr(get(rel.input, j));
                        let e_in1 = efr(get(rel.setup[1], j));
                        let computed = MixedFieldsInOutFixedSizesEvaluationKernelCore::<
                            F,
                            E,
                            1,
                            2,
                            2,
                        >::pointwise_eval(
                            &k, &[b_in0], &[e_in0, e_in1], &()
                        );

                        let mut val0 = computed[0];
                        val0.mul_assign(&challenges[0]);
                        acc[j].add_assign(&val0);

                        let mut val1 = computed[1];
                        val1.mul_assign(&challenges[1]);
                        acc[j].add_assign(&val1);
                    }
                }
                KernelVariant::LookupUnbalancedWithExtension(rel, challenges, _) => {
                    let k = LookupRationalPairWithUnbalancedExtensionGKRRelationKernel::<F, E>::new(
                        rel.lookup_additive_challenge,
                    );
                    for j in 0..2usize {
                        let in_ext0 = efr(get(rel.inputs[0], j));
                        let in_ext1 = efr(get(rel.inputs[1], j));
                        let remainder_in_ext = efr(get(rel.remainder, j));
                        let computed = ExtensionFieldInOutFixedSizesEvaluationKernelCore::<
                            F,
                            E,
                            3,
                            2,
                        >::pointwise_eval(
                            &k, &[in_ext0, in_ext1, remainder_in_ext]
                        );

                        let mut val0 = computed[0];
                        val0.mul_assign(&challenges[0]);
                        acc[j].add_assign(&val0);

                        let mut val1 = computed[1];
                        val1.mul_assign(&challenges[1]);
                        acc[j].add_assign(&val1);
                    }
                }
                KernelVariant::LookupMaskedVectorMinusSetup(rel, challenges, _) => {
                    let k = LookupBaseExtMinusBaseExtGKRRelationKernel::<F, E>::new(
                        rel.lookup_additive_challenge,
                    );
                    for j in 0..2usize {
                        let in_base0 = efr(get(rel.nums[0], j));
                        let in_base1 = efr(get(rel.nums[1], j));
                        let in_ext0 = efr(get(rel.dens[0], j));
                        let in_ext1 = efr(get(rel.dens[1], j));
                        let computed = MixedFieldsInOutFixedSizesEvaluationKernelCore::<
                            F,
                            E,
                            2,
                            2,
                            2,
                        >::pointwise_eval(
                            &k, &[in_base0, in_base1], &[in_ext0, in_ext1], &()
                        );

                        let mut val0 = computed[0];
                        val0.mul_assign(&challenges[0]);
                        acc[j].add_assign(&val0);

                        let mut val1 = computed[1];
                        val1.mul_assign(&challenges[1]);
                        acc[j].add_assign(&val1);
                    }
                }
                KernelVariant::MaterializeVectorLookupInput(rel, challenge, _) => {
                    for j in 0..2usize {
                        let inputs_vec: Vec<E> =
                            rel.inputs.iter().map(|addr| get(*addr, j)).collect();
                        let [val] = rel.kernel.pointwise_eval(&inputs_vec);
                        let mut contrib = val;
                        contrib.mul_assign(&challenge[0]);
                        acc[j].add_assign(&contrib);
                    }
                }
                KernelVariant::MaxQuadratic(rel, challenge, _) => {
                    for j in 0..2usize {
                        let inputs_vec: Vec<E> =
                            rel.inputs.iter().map(|addr| get(*addr, j)).collect();
                        let [val] = rel.kernel.pointwise_eval(&inputs_vec);
                        let mut contrib = val;
                        contrib.mul_assign(&challenge[0]);
                        acc[j].add_assign(&contrib);
                    }
                }
                KernelVariant::EnforceConstraintsMaxQuadratic(rel, challenge) => {
                    // BatchConstraintEval: sum of quadratic/linear/constant terms over the input
                    // polys. For a valid circuit each pointwise evaluation is zero, so this
                    // contributes nothing to acc — but we compute it for completeness/debugging.
                    for j in 0..2usize {
                        let inputs_vec: Vec<E> = rel
                            .inputs
                            .iter()
                            .map(|addr| {
                                if *addr == GKRAddress::placeholder() {
                                    E::ZERO
                                } else {
                                    get(*addr, j)
                                }
                            })
                            .collect();
                        let [val] = rel.kernel.pointwise_eval(&inputs_vec);
                        let mut contrib = val;
                        contrib.mul_assign(&challenge[0]);
                        acc[j].add_assign(&contrib);
                    }
                }

                // --- Dimension Reducing Evaluators ---
                // For N=4 the layout of last_evaluations[addr] is [v0, v1, v2, v3] where the
                // memory is split as [first_half (x_last=0): v0,v1 | second_half (x_last=1): v2,v3].
                // get_f0_and_f1(pair_a=0) → [v[0], v[2]], get_f0_and_f1(pair_b=1) → [v[1], v[3]].
                // So acc[0] uses (a0=v[0], b0=v[1]) and acc[1] uses (a1=v[2], b1=v[3]).
                KernelVariant::PairwiseProductDimensionReducing(rel, challenge, _) => {
                    let k = PairwiseProductDimensionReducingGKRRelationKernel::default();
                    let evals = last_evaluations.get(&rel.input).unwrap_or_else(|| {
                        panic!("input addr {:?} not in last_evaluations", rel.input)
                    });
                    // j=0: pair_a=evals[0], pair_b=evals[1]
                    let [val0] = k.pointwise_eval(&[efr(evals[0])], &[efr(evals[1])]);
                    let mut v0 = val0;
                    v0.mul_assign(&challenge[0]);
                    acc[0].add_assign(&v0);
                    // j=1: pair_a=evals[2], pair_b=evals[3]
                    let [val1] = k.pointwise_eval(&[efr(evals[2])], &[efr(evals[3])]);
                    let mut v1 = val1;
                    v1.mul_assign(&challenge[0]);
                    acc[1].add_assign(&v1);
                }
                KernelVariant::LookupPairDimensionReducing(rel, challenges, _) => {
                    let k = LookupPairDimensionReducingGKRRelationKernel::default();
                    let v0 = last_evaluations.get(&rel.inputs[0]).unwrap_or_else(|| {
                        panic!("input addr {:?} not in last_evaluations", rel.inputs[0])
                    });
                    let v1 = last_evaluations.get(&rel.inputs[1]).unwrap_or_else(|| {
                        panic!("input addr {:?} not in last_evaluations", rel.inputs[1])
                    });
                    // j=0: pair_0 = (v0[0], v1[0]), pair_1 = (v0[1], v1[1])
                    let computed0 =
                        k.pointwise_eval(&[efr(v0[0]), efr(v1[0])], &[efr(v0[1]), efr(v1[1])]);
                    let mut c0 = computed0[0];
                    c0.mul_assign(&challenges[0]);
                    acc[0].add_assign(&c0);
                    let mut c1 = computed0[1];
                    c1.mul_assign(&challenges[1]);
                    acc[0].add_assign(&c1);
                    // j=1: pair_0 = (v0[2], v1[2]), pair_1 = (v0[3], v1[3])
                    let computed1 =
                        k.pointwise_eval(&[efr(v0[2]), efr(v1[2])], &[efr(v0[3]), efr(v1[3])]);
                    let mut c2 = computed1[0];
                    c2.mul_assign(&challenges[0]);
                    acc[1].add_assign(&c2);
                    let mut c3 = computed1[1];
                    c3.mul_assign(&challenges[1]);
                    acc[1].add_assign(&c3);
                }
            }
        }

        acc
    }
}
