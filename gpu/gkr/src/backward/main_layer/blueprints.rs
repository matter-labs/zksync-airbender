use std::collections::BTreeMap;

use super::super::builders::{
    build_initial_grand_product_without_caches_inputs_and_metadata,
    build_inits_and_teardowns_initial_pair_inputs_and_metadata,
    build_linear_base_kernel_inputs_and_metadata,
    build_materialize_grand_product_term_expression_inputs_and_metadata,
    build_max_quadratic_relation_inputs_and_metadata,
    build_single_max_quadratic_constraint_inputs_and_metadata,
    canonical_inits_and_teardowns_top_bits,
};
use super::super::kernels::*;
use super::super::lookup_builders::{
    build_lookup_from_vector_input_with_setup_inputs_and_template,
    build_lookup_pair_from_base_inputs_inputs_and_template,
    build_lookup_pair_from_vector_inputs_inputs_and_template,
    build_lookup_unbalanced_pair_with_vector_inputs_inputs_and_template,
    build_lookup_with_dens_and_setup_expressions_inputs_and_template,
    build_materialized_vector_lookup_input_inputs_and_template,
};
use crate::upstream::{
    high_bits_offset_for_inits_and_teardowns, BaseFieldCopyGKRRelation, BatchedGKRKernel,
    DimensionReducingInputOutput, ExtensionCopyGKRRelation, Field, FieldExtension, GKRAddress,
    GKRCircuitArtifact, GKRExternalChallenges, GKRInputs, GKRLayerDescription,
    LookupBaseExtMinusBaseExtGKRRelation, LookupBaseMinusMultiplicityByBaseGKRRelation,
    LookupBasePairGKRRelation, LookupExtensionMinusMultiplicityByExtensionGKRRelation,
    LookupExtensionPairGKRRelation, LookupPairGKRRelation,
    LookupRationalPairWithUnbalancedBaseGKRRelation,
    LookupRationalPairWithUnbalancedExtensionGKRRelation, MaskIntoIdentityProductGKRRelation,
    NoFieldGKRRelation, OutputType, SameSizeProductGKRRelation,
};
use crate::GpuSumcheckRound0LaunchDescriptors;
use gpu_core::primitives::field::BF;

pub(in crate::backward) fn build_dimension_reducing_kernel_blueprints_static<E: Field>(
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
) -> Vec<DimensionReducingKernelBlueprint<E>> {
    let mut next_batch_challenge_offset = 0usize;
    let mut blueprints = Vec::new();
    for (output_type, reduced_io) in layer.iter() {
        // FS-safe merge: both passes iterate `BTreeMap<OutputType>`
        // with the derived `Ord`; `InitsAndTeardownsProduct` is the last
        // discriminant (cs/src/definitions/gkr_layers.rs:5-10), so its 2
        // pairwise records / 2 challenges are always squeezed AFTER the
        // PermutationProduct + lookup records — identical to the CPU order.
        match *output_type {
            OutputType::PermutationProduct | OutputType::InitsAndTeardownsProduct => {
                for (input, output) in reduced_io.inputs.iter().zip(reduced_io.output.iter()) {
                    let batch_challenge_offset = next_batch_challenge_offset;
                    next_batch_challenge_offset += 1;
                    blueprints.push(DimensionReducingKernelBlueprint {
                        kind: GpuGKRDimensionReducingKernelKind::Pairwise,
                        inputs: GKRInputs {
                            inputs_in_base: Vec::new(),
                            inputs_in_extension: vec![*input],
                            outputs_in_base: Vec::new(),
                            outputs_in_extension: vec![*output],
                        },
                        batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges: Vec::new(),
                    });
                }
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let inputs: [GKRAddress; 2] = reduced_io
                    .inputs
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup kernels expect exactly two inputs");
                let outputs: [GKRAddress; 2] = reduced_io
                    .output
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup kernels expect exactly two outputs");
                let batch_challenge_offset = next_batch_challenge_offset;
                next_batch_challenge_offset += 2;
                blueprints.push(DimensionReducingKernelBlueprint {
                    kind: GpuGKRDimensionReducingKernelKind::Lookup,
                    inputs: GKRInputs {
                        inputs_in_base: Vec::new(),
                        inputs_in_extension: inputs.to_vec(),
                        outputs_in_base: Vec::new(),
                        outputs_in_extension: outputs.to_vec(),
                    },
                    batch_challenge_offset,
                    batch_challenge_count: 2,
                    batch_challenges: Vec::new(),
                });
            }
        }
    }

    blueprints
}

pub(super) fn summarize_main_layer_constraint_metadata_source<E: Field>(
    source: Option<&GpuGKRMainLayerConstraintMetadataSource<E>>,
) -> Option<(usize, usize, E)> {
    match source {
        None => None,
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata)) => Some((
            metadata.quadratic_terms.len(),
            metadata.linear_terms.len(),
            metadata.constant_offset,
        )),
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(template)) => Some((
            template.quadratic_terms.len(),
            template.linear_terms.len(),
            E::ZERO,
        )),
    }
}

pub(super) struct PreparedMainLayerKernelStaticData<E: Copy> {
    pub(super) kind: GpuGKRMainLayerKernelKind,
    pub(super) round0_descriptors: GpuSumcheckRound0LaunchDescriptors<BF, E>,
}

pub(crate) fn build_main_layer_kernel_blueprints_static<E: Field + FieldExtension<BF>>(
    layer: &GKRLayerDescription,
    is_base_field_at_layer: &dyn Fn(&GKRAddress) -> bool,
    external_challenges: &GKRExternalChallenges<BF, E>,
    inits_and_teardowns_top_bits: &[u32],
    inits_and_teardowns_address_high_bits_shift: u32,
) -> Vec<GpuGKRMainLayerKernelBlueprint<E>> {
    let mut next_batch_challenge_offset = 0usize;
    let mut blueprints = Vec::new();
    for gate in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        let push_empty = |count: usize, next_batch_challenge_offset: &mut usize| {
            let batch_challenge_offset = *next_batch_challenge_offset;
            *next_batch_challenge_offset += count;
            (batch_challenge_offset, count)
        };
        match &gate.enforced_relation {
            NoFieldGKRRelation::CopyInBaseField { input, output }
            | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                if is_base_field_at_layer(input) {
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
                        batch_challenge_count,
                        batch_challenges: Vec::new(),
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
                        batch_challenge_count,
                        batch_challenges: Vec::new(),
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::Product,
                    inputs: <SameSizeProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::InitialGrandProductWithoutCaches,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaskIdentity,
                    inputs:
                        <MaskIntoIdentityProductGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPair,
                    inputs: <LookupPairGKRRelation as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupBasePair,
                    inputs:
                        <LookupBasePairGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                            &relation,
                        ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupPairFromBaseInputs { input, output, .. } => {
                let (inputs, constraint_metadata) =
                    build_lookup_pair_from_base_inputs_inputs_and_template(input, *output);
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPairFromBaseInputs,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
                    inputs:
                        <LookupBaseMinusMultiplicityByBaseGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
                input,
                setup,
                output,
            } => {
                let (inputs, constraint_metadata) =
                    build_lookup_with_dens_and_setup_expressions_inputs_and_template(
                        input, setup, *output,
                    );
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupWithDensAndSetupExpressions,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupExtMinusMultiplicityByExt,
                    inputs: <LookupExtensionMinusMultiplicityByExtensionGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(
                    GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::LookupExtPair,
                        inputs: <LookupExtensionPairGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                        batch_challenge_offset,
                        batch_challenge_count,
                        batch_challenges: Vec::new(),
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                        constraint_metadata_source: None,
                    },
                );
            }
            NoFieldGKRRelation::LookupPairFromVectorInputs { input, output } => {
                let (inputs, constraint_metadata) =
                    build_lookup_pair_from_vector_inputs_inputs_and_template(input, *output);
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupPairFromVectorInputs,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalanced,
                    inputs: <LookupRationalPairWithUnbalancedBaseGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalancedExtension,
                    inputs: <LookupRationalPairWithUnbalancedExtensionGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::MaterializedVectorLookupInput { input, output } => {
                let (inputs, constraint_metadata) =
                    build_materialized_vector_lookup_input_inputs_and_template(input, *output);
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
                input,
                remainder,
                output,
            } => {
                let (inputs, constraint_metadata) =
                    build_lookup_unbalanced_pair_with_vector_inputs_inputs_and_template(
                        *input, remainder, *output,
                    );
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalancedPairWithVectorInputs,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
                    inputs: <LookupBaseExtMinusBaseExtGKRRelation<BF, E> as BatchedGKRKernel<
                        BF,
                        E,
                    >>::get_inputs(&relation),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source:
                        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive,
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { .. } => {
                unreachable!(
                    "batched max-quadratic constraints not supported on GPU; cs/ must emit EnforceSingleMaxQuadraticConstraint (USE_BATCHING=false)"
                );
            }
            NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input, .. } => {
                let (inputs, constraint_metadata) =
                    build_single_max_quadratic_constraint_inputs_and_metadata::<E>(input);
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LinearBaseOutput,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
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
                    build_lookup_from_vector_input_with_setup_inputs_and_template(
                        input, setup, *output,
                    );
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupFromVectorInputWithSetup,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Deferred(constraint_metadata),
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LinearBaseOutput,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
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
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::InitsAndTeardownsInitialPair,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        E::ZERO,
                    ),
                    constraint_metadata_source: Some(
                        GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                    ),
                });
            }
            NoFieldGKRRelation::MaxQuadratic { input, output, .. } => {
                let (inputs, constraint_metadata) =
                    build_max_quadratic_relation_inputs_and_metadata::<E>(input, *output);
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::MaxQuadraticBaseOutput,
                    inputs,
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
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

/// Collects, per main layer, the sorted unique set of input addresses that
/// `schedule_execute_main_layer_from_workflow_state` will eventually observe
/// in `final_evaluation_sources_for_last_step` — i.e. the keys of the
/// `BTreeMap<GKRAddress, Vec<E>>` stored in
/// `SumcheckIntermediateProofValues::final_step_evaluations` for that layer.
///
/// Walks `compiled_circuit` directly without consulting `GpuGKRStorage`.
/// `build_main_layer_kernel_blueprints_static` reads
/// `storage.layers[layer_idx].base_field_inputs.contains_key(input)` only to
/// choose between the BaseCopy and ExtCopy kernel kinds for `CopyInBaseField` /
/// `CopyInExtensionField` relations; the collected
/// `inputs_in_base ∪ inputs_in_extension` set is invariant across that branch
/// (both `BaseFieldCopyGKRRelation::get_inputs` and `ExtensionCopyGKRRelation::get_inputs`
/// emit `{relation.input}`), and every other relation variant ignores `storage`.
/// We therefore feed an always-`false` storage check and recover an address
/// set identical to any storage-aware result.
///
/// Result is indexed by natural `layer_idx` (0-based position in
/// `compiled_circuit.layers`), not by backward-scheduler slot. Callers that
/// build `ProofLayoutInputs.backward_layers` in scheduler order (high-to-low
/// layer_idx after dim-reducing) index into the returned Vec accordingly.
pub fn collect_main_layer_input_addresses_per_layer<E>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> Vec<Vec<GKRAddress>>
where
    E: Field + FieldExtension<BF>,
{
    let inits_and_teardowns_top_bits =
        canonical_inits_and_teardowns_top_bits(compiled_circuit.memory_layout.teardown_sets.len());
    let inits_and_teardowns_address_high_bits_shift =
        if compiled_circuit.memory_layout.teardown_sets.is_empty() {
            0
        } else {
            high_bits_offset_for_inits_and_teardowns::<2>(compiled_circuit.trace_len)
        };
    let mut per_layer = Vec::with_capacity(compiled_circuit.layers.len());
    for layer in compiled_circuit.layers.iter() {
        let blueprints = build_main_layer_kernel_blueprints_static::<E>(
            layer,
            &|addr| {
                matches!(
                    addr,
                    GKRAddress::BaseLayerWitness(_)
                        | GKRAddress::BaseLayerMemory(_)
                        | GKRAddress::Setup(_)
                        | GKRAddress::ScratchSpace(_)
                )
            },
            external_challenges,
            &inits_and_teardowns_top_bits,
            inits_and_teardowns_address_high_bits_shift,
        );
        let mut addresses: std::collections::BTreeSet<GKRAddress> =
            std::collections::BTreeSet::new();
        for kernel in blueprints.iter() {
            for addr in kernel
                .inputs
                .inputs_in_base
                .iter()
                .chain(kernel.inputs.inputs_in_extension.iter())
            {
                if *addr == GKRAddress::placeholder() {
                    continue;
                }
                // Protocol/claim identity, not storage: map any scratch alias
                // back to its logical `InnerLayer` address so the proof's
                // `final_step_eval_addresses` (and their commit order) match the
                // CPU verifier. See `transform::logical_protocol_address`.
                addresses.insert(crate::transform::logical_protocol_address(
                    *addr,
                    &compiled_circuit.scratch_space_mapping_rev,
                ));
            }
        }
        per_layer.push(addresses.into_iter().collect());
    }
    per_layer
}

/// Sibling of [`collect_main_layer_input_addresses_per_layer`] that
/// collects the deduplicated `outputs_in_base ∪ outputs_in_extension` per
/// layer. These are the addresses that each layer's kernels claim about — i.e.,
/// the addresses looked up via `claim_layout.claim_idx` in the desc_pairs build
/// inside `schedule_execute_main_layer_from_workflow_state`.
///
/// Walks `compiled_circuit` directly without consulting `GpuGKRStorage`; the
/// `storage`-derived branch in `build_main_layer_kernel_blueprints_static`
/// only affects BaseCopy/ExtCopy classification, which preserves the
/// `outputs_in_*` set.
///
/// Result is indexed by natural `layer_idx` (0-based position in
/// `compiled_circuit.layers`), matching the inputs-side helper.
pub fn collect_main_layer_kernel_output_addresses_per_layer<E>(
    compiled_circuit: &GKRCircuitArtifact<BF>,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> Vec<Vec<GKRAddress>>
where
    E: Field + FieldExtension<BF>,
{
    let inits_and_teardowns_top_bits =
        canonical_inits_and_teardowns_top_bits(compiled_circuit.memory_layout.teardown_sets.len());
    let inits_and_teardowns_address_high_bits_shift =
        if compiled_circuit.memory_layout.teardown_sets.is_empty() {
            0
        } else {
            high_bits_offset_for_inits_and_teardowns::<2>(compiled_circuit.trace_len)
        };
    let mut per_layer = Vec::with_capacity(compiled_circuit.layers.len());
    for layer in compiled_circuit.layers.iter() {
        let blueprints = build_main_layer_kernel_blueprints_static::<E>(
            layer,
            &|addr| {
                matches!(
                    addr,
                    GKRAddress::BaseLayerWitness(_)
                        | GKRAddress::BaseLayerMemory(_)
                        | GKRAddress::Setup(_)
                        | GKRAddress::ScratchSpace(_)
                )
            },
            external_challenges,
            &inits_and_teardowns_top_bits,
            inits_and_teardowns_address_high_bits_shift,
        );
        let mut addresses: std::collections::BTreeSet<GKRAddress> =
            std::collections::BTreeSet::new();
        for kernel in blueprints.iter() {
            for addr in kernel
                .inputs
                .outputs_in_base
                .iter()
                .chain(kernel.inputs.outputs_in_extension.iter())
            {
                if *addr == GKRAddress::placeholder() {
                    continue;
                }
                // Protocol/claim identity, not storage: map any scratch alias
                // back to its logical `InnerLayer` address so the per-layer
                // claim layout (`claim_idx`) matches the CPU verifier and the
                // sibling input-address collector. See
                // `transform::logical_protocol_address`.
                addresses.insert(crate::transform::logical_protocol_address(
                    *addr,
                    &compiled_circuit.scratch_space_mapping_rev,
                ));
            }
        }
        per_layer.push(addresses.into_iter().collect());
    }
    per_layer
}

/// Computes the cached-relation dependency evaluations that each main layer
/// must append to its final-step evaluations before drawing the next batching
/// challenge.
///
/// This is the address-only form of the CPU prover's
/// `extra_evaluations_from_caching_relations`: for every layer, take the
/// cached-relation dependencies that are absent from that layer's initial
/// `new_claims` set. Both inputs are already expressed in logical protocol
/// address space. The result is sorted and deduplicated to match the CPU
/// `BTreeMap` transcript order, including for layer 0.
pub fn compute_main_layer_extra_evaluation_addresses_per_layer(
    inputs_per_layer: &[Vec<GKRAddress>],
    cached_dependencies_per_layer: &[Vec<GKRAddress>],
) -> Vec<Vec<GKRAddress>> {
    assert_eq!(
        inputs_per_layer.len(),
        cached_dependencies_per_layer.len(),
        "inputs and cached dependencies must have matching layer counts",
    );
    inputs_per_layer
        .iter()
        .zip(cached_dependencies_per_layer)
        .map(|(layer_inputs, cached_dependencies)| {
            let layer_inputs: std::collections::BTreeSet<GKRAddress> =
                layer_inputs.iter().copied().collect();
            cached_dependencies
                .iter()
                .copied()
                .filter(|addr| !layer_inputs.contains(addr))
                .collect::<std::collections::BTreeSet<_>>()
                .into_iter()
                .collect()
        })
        .collect()
}

/// Collects each layer's cached-relation dependencies in logical protocol
/// address space. Iteration through `BTreeMap` plus the final `BTreeSet` keeps
/// the exact deterministic ordering consumed by the transcript payload. The
/// cache-relation compiler currently restricts dependencies to base-field
/// polynomials; the execution-side resolver enforces that invariant.
pub fn collect_main_layer_cached_dependencies_per_layer(
    compiled_circuit: &GKRCircuitArtifact<BF>,
) -> Vec<Vec<GKRAddress>> {
    compiled_circuit
        .layers
        .iter()
        .map(|layer| {
            layer
                .cached_relations
                .values()
                .flat_map(|relation| relation.dependencies())
                .map(|address| {
                    crate::transform::logical_protocol_address(
                        address,
                        &compiled_circuit.scratch_space_mapping_rev,
                    )
                })
                .collect::<std::collections::BTreeSet<_>>()
                .into_iter()
                .collect()
        })
        .collect()
}

#[cfg(test)]
mod unified_cap_tests {
    use std::collections::BTreeMap;

    use super::build_dimension_reducing_kernel_blueprints_static;
    use crate::backward::kernels::{
        GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN, GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER,
    };
    use crate::upstream::{DimensionReducingInputOutput, GKRAddress, OutputType};
    use gpu_core::primitives::field::E4;

    fn io(layer: usize, base_offset: usize) -> DimensionReducingInputOutput {
        let addr = |off: usize| GKRAddress::InnerLayer { layer, offset: off };
        DimensionReducingInputOutput {
            inputs: vec![addr(base_offset), addr(base_offset + 1)],
            output: vec![addr(base_offset + 2), addr(base_offset + 3)],
        }
    }

    // The unified dim-reducing layer carries PermutationProduct + all three
    // lookups + InitsAndTeardownsProduct. PermutationProduct and i/t each emit
    // 2 pairwise records / 2 challenges (one per input/output pair); the 3
    // lookups emit 1 record / 2 challenges each: 2+2+3 = 7 records, 2+2+6 = 10
    // challenges. This exceeds the pre-#305 caps of 5 records / 8 challenges.
    #[test]
    fn unified_dim_reducing_layer_fits_raised_caps() {
        let mut layer: BTreeMap<OutputType, DimensionReducingInputOutput> = BTreeMap::new();
        layer.insert(OutputType::PermutationProduct, io(0, 0));
        layer.insert(OutputType::Lookup16Bits, io(0, 4));
        layer.insert(OutputType::LookupTimestamps, io(0, 8));
        layer.insert(OutputType::GenericLookup, io(0, 12));
        layer.insert(OutputType::InitsAndTeardownsProduct, io(0, 16));

        let blueprints = build_dimension_reducing_kernel_blueprints_static::<E4>(&layer);
        let record_count = blueprints.len();
        let challenge_count: usize = blueprints.iter().map(|b| b.batch_challenge_count).sum();

        assert_eq!(record_count, 7, "unified layer must produce 7 records");
        assert_eq!(
            challenge_count, 10,
            "unified layer must consume 10 challenges"
        );
        assert!(record_count <= GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER);
        assert!(challenge_count <= GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN);
    }
}
