//! Dynamic-challenge main-layer blueprint builder. Relocated from
//! `backward/tests/helpers.rs` (row 30 transitive dep): apex `smoke` drives
//! `GpuGKRMainLayerBackwardState::prepare_next_layer` (the dynamic-challenge
//! form), which builds blueprints through this. `pub(in crate::backward)` —
//! only reachable via that `#[doc(hidden)] pub` method + gpu_gkr's own tests.
use gpu_core::primitives::field::BF;

// `backward::*` brings the `#[allow(unused_imports)] pub(crate) use builders::*`
// + `pub(crate) use kernels::*` re-exports (the `build_*_inputs_and_metadata`
// helpers, the `GpuGKRMainLayer*` blueprint types, `GpuGKRStorage`).
use super::super::lookup_builders::build_materialized_vector_lookup_input_inputs_and_metadata;
#[allow(unused_imports)]
use super::super::*;
use crate::upstream::{
    BaseFieldCopyGKRRelation, BatchedGKRKernel, ExtensionCopyGKRRelation, Field, FieldExtension,
    GKRExternalChallenges, GKRLayerDescription, LookupBaseExtMinusBaseExtGKRRelation,
    LookupBaseMinusMultiplicityByBaseGKRRelation, LookupBasePairGKRRelation,
    LookupExtensionMinusMultiplicityByExtensionGKRRelation, LookupExtensionPairGKRRelation,
    LookupPairGKRRelation, LookupRationalPairWithUnbalancedBaseGKRRelation,
    LookupRationalPairWithUnbalancedExtensionGKRRelation, MaskIntoIdentityProductGKRRelation,
    NoFieldGKRRelation, SameSizeProductGKRRelation,
};

pub(in crate::backward) fn build_main_layer_kernel_blueprints<E: Field + FieldExtension<BF>>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    storage: &GpuGKRStorage<BF, E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    inits_and_teardowns_top_bits: &[u32],
    inits_and_teardowns_address_high_bits_shift: u32,
    batch_challenge_base: E,
    lookup_multiplicative_challenge: E,
    lookup_additive_challenge: E,
) -> Vec<GpuGKRMainLayerKernelBlueprint<E>> {
    let mut current_batch_challenge = E::ONE;
    let mut next_batch_challenge_offset = 0usize;
    let mut get_challenge = || {
        let challenge = current_batch_challenge;
        current_batch_challenge.mul_assign(&batch_challenge_base);
        challenge
    };

    let mut blueprints = Vec::new();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        let push_challenges = |count: usize,
                               next_batch_challenge_offset: &mut usize,
                               get_challenge: &mut dyn FnMut() -> E| {
            let batch_challenge_offset = *next_batch_challenge_offset;
            *next_batch_challenge_offset += count;
            let batch_challenges = (0..count).map(|_| get_challenge()).collect::<Vec<_>>();
            (batch_challenge_offset, batch_challenges)
        };
        match &gate.enforced_relation {
            NoFieldGKRRelation::CopyInBaseField { input, output }
            | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                let (batch_challenge_offset, batch_challenges) =
                    push_challenges(1, &mut next_batch_challenge_offset, &mut get_challenge);
                if storage.layers[layer_idx]
                    .base_field_inputs
                    .contains_key(input)
                {
                    let relation = BaseFieldCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    blueprints.push(GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::BaseCopy,
                        inputs: <BaseFieldCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges,
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: None,
                    });
                } else {
                    let relation = ExtensionCopyGKRRelation {
                        input: *input,
                        output: *output,
                    };
                    blueprints.push(GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::ExtCopy,
                        inputs: <ExtensionCopyGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                        batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges,
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: None,
                    });
                }
            }
            NoFieldGKRRelation::InitialGrandProductFromCaches { input, output }
            | NoFieldGKRRelation::TrivialProduct { input, output } => {
                let relation = SameSizeProductGKRRelation {
                    inputs: *input,
                    output: *output,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::Product,
                    inputs: <SameSizeProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::InitialGrandProductWithoutCaches { input, output } => {
                let (inputs, constraint_metadata) =
                    build_initial_grand_product_without_caches_inputs_and_metadata(
                        input,
                        *output,
                        external_challenges,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::InitialGrandProductWithoutCaches,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::MaskIntoIdentityProduct {
                input,
                mask,
                output,
            } => {
                let relation = MaskIntoIdentityProductGKRRelation {
                    input: *input,
                    mask: *mask,
                    output: *output,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaskIdentity,
                    inputs:
                        <MaskIntoIdentityProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::AggregateLookupRationalPair { input, output } => {
                let relation = LookupPairGKRRelation {
                    inputs: *input,
                    outputs: *output,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPair,
                    inputs: <LookupPairGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, output } => {
                let relation = LookupBasePairGKRRelation::<BF, E> {
                    inputs: *input,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupBasePair,
                    inputs:
                        <LookupBasePairGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromBaseInputs { input, output, .. } => {
                let (inputs, constraint_metadata) =
                    build_lookup_pair_from_base_inputs_inputs_and_metadata(
                        input,
                        *output,
                        lookup_additive_challenge,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPairFromBaseInputs,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseMinusMultiplicityByBaseGKRRelation::<BF, E> {
                    input: *input,
                    setup: *setup,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
                    inputs:
                        <LookupBaseMinusMultiplicityByBaseGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
                input,
                setup,
                output,
            } => {
                let (inputs, constraint_metadata) =
                    build_lookup_with_dens_and_setup_expressions_inputs_and_metadata(
                        input,
                        setup,
                        *output,
                        lookup_multiplicative_challenge,
                        lookup_additive_challenge,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupWithDensAndSetupExpressions,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupFromMaterializedVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupExtensionMinusMultiplicityByExtensionGKRRelation::<BF, E> {
                    input: *input,
                    setup: *setup,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupExtMinusMultiplicityByExt,
                    inputs: <LookupExtensionMinusMultiplicityByExtensionGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { input, output }
            | NoFieldGKRRelation::LookupPairFromCachedVectorInputs { input, output } => {
                let relation = LookupExtensionPairGKRRelation::<BF, E> {
                    inputs: *input,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(
                    GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::LookupExtPair,
                        inputs: <LookupExtensionPairGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                        batch_challenge_offset: next_batch_challenge_offset,
                        batch_challenge_count: 2,
                        batch_challenges: {
                            next_batch_challenge_offset += 2;
                            vec![get_challenge(), get_challenge()]
                        },
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                                lookup_additive_challenge,
                            ),
                        constraint_metadata_source: None,
                    },
                );
            }
            NoFieldGKRRelation::LookupPairFromVectorInputs { input, output } => {
                let (inputs, constraint_metadata) =
                    build_lookup_pair_from_vector_inputs_inputs_and_metadata(
                        input,
                        *output,
                        lookup_multiplicative_challenge,
                        lookup_additive_challenge,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPairFromVectorInputs,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
                input,
                remainder,
                output,
            } => {
                let relation = LookupRationalPairWithUnbalancedBaseGKRRelation::<BF, E> {
                    inputs: *input,
                    remainder: *remainder,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalanced,
                    inputs: <LookupRationalPairWithUnbalancedBaseGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                            lookup_additive_challenge,
                        ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
                input,
                remainder,
                output,
            } => {
                let relation = LookupRationalPairWithUnbalancedExtensionGKRRelation::<BF, E> {
                    inputs: *input,
                    remainder: *remainder,
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalancedExtension,
                    inputs: <LookupRationalPairWithUnbalancedExtensionGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                            lookup_additive_challenge,
                        ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::MaterializedVectorLookupInput { input, output } => {
                let (inputs, constraint_metadata) =
                    build_materialized_vector_lookup_input_inputs_and_metadata(
                        input,
                        *output,
                        lookup_multiplicative_challenge,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
                input,
                remainder,
                output,
            } => {
                let (inputs, constraint_metadata) =
                    build_lookup_unbalanced_pair_with_vector_inputs_inputs_and_metadata(
                        *input,
                        remainder,
                        *output,
                        lookup_multiplicative_challenge,
                        lookup_additive_challenge,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalancedPairWithVectorInputs,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupWithCachedDensAndSetup {
                input,
                setup,
                output,
            } => {
                let relation = LookupBaseExtMinusBaseExtGKRRelation::<BF, E> {
                    nums: [input[0], setup[0]],
                    dens: [input[1], setup[1]],
                    outputs: *output,
                    lookup_additive_challenge: E::ZERO,
                    _marker: core::marker::PhantomData,
                };
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
                    inputs: <LookupBaseExtMinusBaseExtGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { .. } => {
                unreachable!(
                    "batched max-quadratic constraints not supported on GPU; cs/ must emit EnforceSingleMaxQuadraticConstraint (USE_BATCHING=false)"
                );
            }
            NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input } => {
                let (inputs, constraint_metadata) =
                    build_single_max_quadratic_constraint_inputs_and_metadata::<E>(input);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::MaterializeSingleLookupInput { input, output, .. } => {
                let (inputs, constraint_metadata) =
                    build_linear_base_kernel_inputs_and_metadata::<E>(&input.input, *output);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LinearBaseOutput,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupFromVectorInputWithSetup {
                input,
                setup,
                output,
            } => {
                let (inputs, constraint_metadata) =
                    build_lookup_from_vector_input_with_setup_inputs_and_metadata(
                        input,
                        setup,
                        *output,
                        lookup_multiplicative_challenge,
                        lookup_additive_challenge,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupFromVectorInputWithSetup,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: {
                        next_batch_challenge_offset += 2;
                        vec![get_challenge(), get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::MaterializeGrandProductTermExpression { input, output } => {
                let (inputs, constraint_metadata) =
                    build_materialize_grand_product_term_expression_inputs_and_metadata(
                        input,
                        *output,
                        external_challenges,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LinearBaseFieldRelation { input, output } => {
                let (inputs, constraint_metadata) =
                    build_linear_base_kernel_inputs_and_metadata::<E>(input, *output);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LinearBaseOutput,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::InitsOrTeardownsInitialPair {
                timestamp_and_value,
                setup,
                output,
                set_idxes,
            } => {
                let (inputs, constraint_metadata) =
                    build_inits_and_teardowns_initial_pair_inputs_and_metadata(
                        timestamp_and_value,
                        *setup,
                        *output,
                        set_idxes.map(|idx| inits_and_teardowns_top_bits[idx]),
                        inits_and_teardowns_address_high_bits_shift,
                        external_challenges,
                    );
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::InitsAndTeardownsInitialPair,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::MaxQuadratic { input, output } => {
                let (inputs, constraint_metadata) =
                    build_max_quadratic_relation_inputs_and_metadata::<E>(input, *output);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaxQuadraticBaseOutput,
                    inputs,
                    batch_challenge_offset: next_batch_challenge_offset,
                    batch_challenge_count: 1,
                    batch_challenges: {
                        next_batch_challenge_offset += 1;
                        vec![get_challenge()]
                    },
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. } => {
                unimplemented!(
                    "unsupported GPU main-layer relation: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }

    blueprints
}
