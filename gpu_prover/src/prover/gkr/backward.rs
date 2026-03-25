use std::cell::UnsafeCell;
use std::collections::{BTreeMap, VecDeque};
use std::mem::align_of;
use std::ptr::{null, null_mut};
use std::slice;
use std::sync::{Arc, Mutex};

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{
    GKRCircuitArtifact, GKRLayerDescription, NoFieldGKRRelation,
    NoFieldMaxQuadraticConstraintsGKRRelation, OutputType,
};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSliceMut, DeviceSlice};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use field::{Field, FieldExtension, PrimeField};
use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use prover::gkr::prover::SumcheckIntermediateProofValues;
use prover::gkr::sumcheck::evaluation_kernels::{
    BaseFieldCopyGKRRelation, BatchConstraintEvalGKRRelation, BatchedGKRKernel,
    ExtensionCopyGKRRelation, GKRInputs, LookupBaseExtMinusBaseExtGKRRelation,
    LookupBaseMinusMultiplicityByBaseGKRRelation, LookupBasePairGKRRelation, LookupPairGKRRelation,
    LookupRationalPairWithUnbalancedBaseGKRRelation,
    LookupRationalPairWithUnbalancedExtensionGKRRelation, MaskIntoIdentityProductGKRRelation,
    SameSizeProductGKRRelation,
};
use prover::gkr::sumcheck::{
    evaluate_eq_poly, evaluate_small_univariate_poly, output_univariate_monomial_form_max_quadratic,
};
use prover::transcript::Seed;

pub(crate) use super::backward_kernels::*;
use super::{
    alloc_host_and_schedule_copy, GpuBaseFieldPolySource,
    GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor,
    GpuBaseFieldPolySourceAfterTwoFoldingsLaunchDescriptor,
    GpuExtensionFieldPolyContinuingLaunchDescriptor, GpuExtensionFieldPolyInitialSource,
    GpuGKRStorage, GpuSumcheckRound0HostLaunchDescriptors, GpuSumcheckRound0LaunchDescriptors,
    GpuSumcheckRound0ScheduledLaunchDescriptors, GpuSumcheckRound1HostLaunchDescriptors,
    GpuSumcheckRound1PreparedStorage, GpuSumcheckRound1ScheduledLaunchDescriptors,
    GpuSumcheckRound2HostLaunchDescriptors, GpuSumcheckRound2PreparedStorage,
    GpuSumcheckRound2ScheduledLaunchDescriptors, GpuSumcheckRound3AndBeyondHostLaunchDescriptors,
    GpuSumcheckRound3AndBeyondPreparedStorage,
    GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{
    get_reduce_temp_storage_bytes, reduce, Reduce, ReduceOperation,
};
use crate::ops::simple::{mul_into_y, BinaryOp, Mul};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::{DeviceVectorChunk, DeviceVectorChunkMut};
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E2, E4, E6};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

fn build_dimension_reducing_kernel_blueprints<E: Field>(
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    batch_challenge_base: E,
) -> Vec<DimensionReducingKernelBlueprint<E>> {
    let mut current_batch_challenge = E::ONE;
    let mut next_batch_challenge_offset = 0usize;
    let mut get_challenge = || {
        let challenge = current_batch_challenge;
        current_batch_challenge.mul_assign(&batch_challenge_base);
        challenge
    };

    let mut blueprints = Vec::new();
    for (output_type, reduced_io) in layer.iter() {
        match *output_type {
            OutputType::PermutationProduct => {
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
                        batch_challenges: vec![get_challenge()],
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
                    batch_challenges: vec![get_challenge(), get_challenge()],
                });
            }
        }
    }

    blueprints
}

fn build_dimension_reducing_kernel_blueprints_static<E: Field>(
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
) -> Vec<DimensionReducingKernelBlueprint<E>> {
    let mut next_batch_challenge_offset = 0usize;
    let mut blueprints = Vec::new();
    for (output_type, reduced_io) in layer.iter() {
        match *output_type {
            OutputType::PermutationProduct => {
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

struct PreparedDimensionReducingKernelStaticData<B, E: Copy> {
    kind: GpuGKRDimensionReducingKernelKind,
    batch_challenge_offset: usize,
    batch_challenge_count: usize,
    round0_descriptors: GpuSumcheckRound0LaunchDescriptors<B, E>,
    round1_descriptors: GpuSumcheckRound1HostLaunchDescriptors<B, E>,
    round2_descriptors: Option<GpuSumcheckRound2HostLaunchDescriptors<B, E>>,
    round3_descriptors: Vec<GpuGKRDimensionReducingRound3HostDescriptors<E>>,
}

fn build_dimension_reducing_round0_batch_template<B, E: Field>(
    folding_steps: usize,
    static_data: &[PreparedDimensionReducingKernelStaticData<B, E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> GpuGKRDimensionReducingRound0Batch<E> {
    let mut batch = GpuGKRDimensionReducingRound0Batch::default();
    batch.record_count = static_data.len() as u32;
    batch.challenge_offset = 1;
    batch.challenge_count = (folding_steps - 1) as u32;
    let mut inline_builder = InlinePayloadBuilder::new();

    for (idx, kernel) in static_data.iter().enumerate() {
        debug_assert!(kernel.round0_descriptors.base_field_inputs.is_empty());
        debug_assert!(kernel.round0_descriptors.base_field_outputs.is_empty());
        let mark = inline_builder.mark();
        let inline_ext_inputs =
            inline_builder.try_push_copy(&kernel.round0_descriptors.extension_field_inputs);
        let inline_ext_outputs =
            inline_builder.try_push_copy(&kernel.round0_descriptors.extension_field_outputs);
        let (record_mode, extension_inputs, extension_outputs) =
            if let (Some(extension_inputs), Some(extension_outputs)) =
                (inline_ext_inputs, inline_ext_outputs)
            {
                (
                    GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors,
                    extension_inputs,
                    extension_outputs,
                )
            } else {
                inline_builder.restore(mark);
                (
                    GpuGKRDimensionReducingBatchRecordMode::PointerDescriptors,
                    spill_builder.push_copy(&kernel.round0_descriptors.extension_field_inputs),
                    spill_builder.push_copy(&kernel.round0_descriptors.extension_field_outputs),
                )
            };

        batch.records[idx] = GpuGKRDimensionReducingRound0BatchRecord {
            kind: kernel.kind.as_u32(),
            record_mode: record_mode.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            extension_outputs,
            batch_challenge_offset: kernel.batch_challenge_offset as u32,
            batch_challenge_count: kernel.batch_challenge_count as u32,
        };
    }

    batch.inline_payload = inline_builder.into_bytes();
    batch
}

fn build_dimension_reducing_round1_batch_template<B, E: Field>(
    folding_steps: usize,
    static_data: &[PreparedDimensionReducingKernelStaticData<B, E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> GpuGKRDimensionReducingRound1Batch<E> {
    let mut batch = GpuGKRDimensionReducingRound1Batch::default();
    batch.record_count = static_data.len() as u32;
    batch.challenge_offset = 2;
    batch.challenge_count = (folding_steps - 2) as u32;
    let mut inline_builder = InlinePayloadBuilder::new();

    for (idx, kernel) in static_data.iter().enumerate() {
        debug_assert!(kernel.round1_descriptors.base_field_inputs.is_empty());
        let mark = inline_builder.mark();
        let inline_ext_inputs =
            inline_builder.try_push_copy(&kernel.round1_descriptors.extension_field_inputs);
        let (record_mode, extension_inputs) = if let Some(extension_inputs) = inline_ext_inputs {
            (
                GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors,
                extension_inputs,
            )
        } else {
            inline_builder.restore(mark);
            (
                GpuGKRDimensionReducingBatchRecordMode::PointerDescriptors,
                spill_builder.push_copy(&kernel.round1_descriptors.extension_field_inputs),
            )
        };

        batch.records[idx] = GpuGKRDimensionReducingContinuationBatchRecord {
            kind: kernel.kind.as_u32(),
            record_mode: record_mode.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            batch_challenge_offset: kernel.batch_challenge_offset as u32,
            batch_challenge_count: kernel.batch_challenge_count as u32,
        };
    }

    batch.inline_payload = inline_builder.into_bytes();
    batch
}

fn build_dimension_reducing_round2_batch_template<B, E: Field>(
    folding_steps: usize,
    static_data: &[PreparedDimensionReducingKernelStaticData<B, E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> GpuGKRDimensionReducingRound2Batch<E> {
    let mut batch = GpuGKRDimensionReducingRound2Batch::default();
    batch.record_count = static_data.len() as u32;
    batch.challenge_offset = 3;
    batch.challenge_count = (folding_steps - 3) as u32;
    let mut inline_builder = InlinePayloadBuilder::new();

    for (idx, kernel) in static_data.iter().enumerate() {
        let descriptors = kernel
            .round2_descriptors
            .as_ref()
            .expect("round 2 descriptors must be present when round 2 template is built");
        debug_assert!(descriptors.base_field_inputs.is_empty());
        let mark = inline_builder.mark();
        let inline_ext_inputs = inline_builder.try_push_copy(&descriptors.extension_field_inputs);
        let (record_mode, extension_inputs) = if let Some(extension_inputs) = inline_ext_inputs {
            (
                GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors,
                extension_inputs,
            )
        } else {
            inline_builder.restore(mark);
            (
                GpuGKRDimensionReducingBatchRecordMode::PointerDescriptors,
                spill_builder.push_copy(&descriptors.extension_field_inputs),
            )
        };

        batch.records[idx] = GpuGKRDimensionReducingContinuationBatchRecord {
            kind: kernel.kind.as_u32(),
            record_mode: record_mode.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            batch_challenge_offset: kernel.batch_challenge_offset as u32,
            batch_challenge_count: kernel.batch_challenge_count as u32,
        };
    }

    batch.inline_payload = inline_builder.into_bytes();
    batch
}

fn build_dimension_reducing_round3_batch_templates<B, E: Field>(
    folding_steps: usize,
    static_data: &[PreparedDimensionReducingKernelStaticData<B, E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> Vec<GpuGKRDimensionReducingRound3BatchTemplate<E>> {
    let mut result = Vec::with_capacity(folding_steps.saturating_sub(3));
    for step in 3..folding_steps {
        let mut batch = GpuGKRDimensionReducingRound3Batch::default();
        batch.record_count = static_data.len() as u32;
        batch.challenge_offset = (step + 1) as u32;
        batch.challenge_count = (folding_steps - step - 1) as u32;
        let mut inline_builder = InlinePayloadBuilder::new();

        for (idx, kernel) in static_data.iter().enumerate() {
            let descriptors = kernel
                .round3_descriptors
                .iter()
                .find(|descriptors| descriptors.step == step)
                .unwrap_or_else(|| {
                    panic!("missing dimension-reducing round 3 descriptors for step {step}")
                });
            debug_assert!(descriptors.descriptors.base_field_inputs.is_empty());
            let mark = inline_builder.mark();
            let inline_ext_inputs =
                inline_builder.try_push_copy(&descriptors.descriptors.extension_field_inputs);
            let (record_mode, extension_inputs) = if let Some(extension_inputs) = inline_ext_inputs
            {
                (
                    GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors,
                    extension_inputs,
                )
            } else {
                inline_builder.restore(mark);
                (
                    GpuGKRDimensionReducingBatchRecordMode::PointerDescriptors,
                    spill_builder.push_copy(&descriptors.descriptors.extension_field_inputs),
                )
            };

            batch.records[idx] = GpuGKRDimensionReducingContinuationBatchRecord {
                kind: kernel.kind.as_u32(),
                record_mode: record_mode.as_u32(),
                _reserved0: 0,
                _reserved1: 0,
                extension_inputs,
                batch_challenge_offset: kernel.batch_challenge_offset as u32,
                batch_challenge_count: kernel.batch_challenge_count as u32,
            };
        }

        batch.inline_payload = inline_builder.into_bytes();
        result.push(GpuGKRDimensionReducingRound3BatchTemplate { step, batch });
    }
    result
}

fn build_dimension_reducing_batch_templates<B, E: Field>(
    folding_steps: usize,
    static_data: &[PreparedDimensionReducingKernelStaticData<B, E>],
) -> (
    GpuGKRDimensionReducingRound0Batch<E>,
    GpuGKRDimensionReducingRound1Batch<E>,
    Option<GpuGKRDimensionReducingRound2Batch<E>>,
    Vec<GpuGKRDimensionReducingRound3BatchTemplate<E>>,
    Vec<u8>,
) {
    let mut spill_builder = SpillPayloadBuilder::default();
    let round0 = build_dimension_reducing_round0_batch_template(
        folding_steps,
        static_data,
        &mut spill_builder,
    );
    let round1 = build_dimension_reducing_round1_batch_template(
        folding_steps,
        static_data,
        &mut spill_builder,
    );
    let round2 = (folding_steps >= 3).then(|| {
        build_dimension_reducing_round2_batch_template(
            folding_steps,
            static_data,
            &mut spill_builder,
        )
    });
    let round3 = build_dimension_reducing_round3_batch_templates(
        folding_steps,
        static_data,
        &mut spill_builder,
    );
    (round0, round1, round2, round3, spill_builder.bytes)
}

fn build_constraint_metadata_template(
    input: &NoFieldMaxQuadraticConstraintsGKRRelation,
    num_memory_polys: usize,
    num_witness_polys: usize,
) -> GpuGKRMainLayerConstraintTemplate {
    let remap_offset = |a: GKRAddress| match a {
        GKRAddress::BaseLayerMemory(offset) => {
            assert!(offset < num_memory_polys);
            offset
        }
        GKRAddress::BaseLayerWitness(offset) => {
            assert!(offset < num_witness_polys);
            offset + num_memory_polys
        }
        GKRAddress::Setup(..) => unreachable!(),
        _ => unreachable!(),
    };

    let quadratic_terms = input
        .quadratic_terms
        .iter()
        .map(
            |((lhs, rhs), terms)| GpuGKRMainLayerConstraintQuadraticTemplate {
                lhs: remap_offset(*lhs) as u32,
                rhs: remap_offset(*rhs) as u32,
                challenge_terms: terms
                    .iter()
                    .map(|(coeff, power)| GpuGKRMainLayerConstraintChallengeTerm {
                        coeff: BF::from_u32_with_reduction(*coeff),
                        power: *power as u32,
                    })
                    .collect(),
            },
        )
        .collect();
    let linear_terms = input
        .linear_terms
        .iter()
        .map(|(input, terms)| GpuGKRMainLayerConstraintLinearTemplate {
            input: remap_offset(*input) as u32,
            challenge_terms: terms
                .iter()
                .map(|(coeff, power)| GpuGKRMainLayerConstraintChallengeTerm {
                    coeff: BF::from_u32_with_reduction(*coeff),
                    power: *power as u32,
                })
                .collect(),
        })
        .collect();
    let constant_terms = input
        .constants
        .iter()
        .map(|(coeff, power)| GpuGKRMainLayerConstraintChallengeTerm {
            coeff: BF::from_u32_with_reduction(*coeff),
            power: *power as u32,
        })
        .collect();

    GpuGKRMainLayerConstraintTemplate {
        quadratic_terms,
        linear_terms,
        constant_terms,
    }
}

pub(super) fn evaluate_constraint_prefactor<E: Field + FieldExtension<BF>>(
    challenge_terms: &[GpuGKRMainLayerConstraintChallengeTerm],
    challenge: E,
) -> E {
    let mut total = E::ZERO;
    for term in challenge_terms.iter() {
        let mut contribution = challenge.pow(term.power);
        contribution.mul_assign_by_base(&term.coeff);
        total.add_assign(&contribution);
    }
    total
}

fn resolve_main_layer_auxiliary_challenge<E: Copy>(
    source: GpuGKRMainLayerAuxiliaryChallengeSource<E>,
    lookup_additive_challenge: E,
) -> E {
    match source {
        GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(value) => value,
        GpuGKRMainLayerAuxiliaryChallengeSource::LookupAdditive => lookup_additive_challenge,
    }
}

fn resolve_main_layer_constraint_metadata<E: Field + FieldExtension<BF>>(
    source: Option<GpuGKRMainLayerConstraintMetadataSource<E>>,
    constraint_batch_challenge: E,
) -> Option<GpuGKRMainLayerConstraintHostMetadata<E>> {
    match source {
        None => None,
        Some(GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata)) => Some(metadata),
        Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(template)) => {
            Some(GpuGKRMainLayerConstraintHostMetadata {
                quadratic_terms: template
                    .quadratic_terms
                    .iter()
                    .map(|term| GpuGKRMainLayerConstraintQuadraticTerm {
                        lhs: term.lhs,
                        rhs: term.rhs,
                        challenge: evaluate_constraint_prefactor(
                            &term.challenge_terms,
                            constraint_batch_challenge,
                        ),
                    })
                    .collect(),
                linear_terms: template
                    .linear_terms
                    .iter()
                    .map(|term| GpuGKRMainLayerConstraintLinearTerm {
                        input: term.input,
                        challenge: evaluate_constraint_prefactor(
                            &term.challenge_terms,
                            constraint_batch_challenge,
                        ),
                    })
                    .collect(),
                constant_offset: evaluate_constraint_prefactor(
                    &template.constant_terms,
                    constraint_batch_challenge,
                ),
            })
        }
    }
}

struct PreparedMainLayerKernelStaticData<E: Copy> {
    kind: GpuGKRMainLayerKernelKind,
    batch_challenge_offset: usize,
    batch_challenge_count: usize,
    auxiliary_challenge: E,
    constraint_metadata: Option<GpuGKRMainLayerConstraintHostMetadata<E>>,
    round0_descriptors: GpuSumcheckRound0LaunchDescriptors<BF, E>,
    round1_descriptors: GpuSumcheckRound1HostLaunchDescriptors<BF, E>,
    round2_descriptors: GpuSumcheckRound2HostLaunchDescriptors<BF, E>,
    round3_descriptors: Vec<GpuGKRMainLayerRound3HostDescriptors<E>>,
}

fn pack_metadata_block<E: Field>(
    metadata: Option<&GpuGKRMainLayerConstraintHostMetadata<E>>,
    inline_builder: &mut InlinePayloadBuilder,
    spill_builder: &mut SpillPayloadBuilder,
) -> (
    bool,
    GpuGKRMainLayerPayloadRange,
    GpuGKRMainLayerPayloadRange,
    E,
) {
    let Some(metadata) = metadata else {
        return (
            true,
            GpuGKRMainLayerPayloadRange::default(),
            GpuGKRMainLayerPayloadRange::default(),
            E::ZERO,
        );
    };

    let mark = inline_builder.mark();
    let inline_quadratic = inline_builder.try_push_copy(&metadata.quadratic_terms);
    let inline_linear = inline_builder.try_push_copy(&metadata.linear_terms);
    if let (Some(quadratic_terms), Some(linear_terms)) = (inline_quadratic, inline_linear) {
        return (
            true,
            quadratic_terms,
            linear_terms,
            metadata.constant_offset,
        );
    }
    inline_builder.restore(mark);
    (
        false,
        spill_builder.push_copy(&metadata.quadratic_terms),
        spill_builder.push_copy(&metadata.linear_terms),
        metadata.constant_offset,
    )
}

fn build_main_layer_round0_batch_template<E: Field>(
    folding_steps: usize,
    static_data: &[PreparedMainLayerKernelStaticData<E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> GpuGKRMainRound0Batch<E> {
    let mut batch = GpuGKRMainRound0Batch::default();
    batch.record_count = static_data.len() as u32;
    batch.challenge_offset = 1;
    batch.challenge_count = (folding_steps - 1) as u32;
    let mut inline_builder = InlinePayloadBuilder::new();

    for (idx, kernel) in static_data.iter().enumerate() {
        let mark = inline_builder.mark();
        let inline_base_inputs =
            inline_builder.try_push_copy(&kernel.round0_descriptors.base_field_inputs);
        let inline_ext_inputs =
            inline_builder.try_push_copy(&kernel.round0_descriptors.extension_field_inputs);
        let inline_base_outputs =
            inline_builder.try_push_copy(&kernel.round0_descriptors.base_field_outputs);
        let inline_ext_outputs =
            inline_builder.try_push_copy(&kernel.round0_descriptors.extension_field_outputs);

        let (record_mode, base_inputs, extension_inputs, base_outputs, extension_outputs) =
            if let (
                Some(base_inputs),
                Some(extension_inputs),
                Some(base_outputs),
                Some(extension_outputs),
            ) = (
                inline_base_inputs,
                inline_ext_inputs,
                inline_base_outputs,
                inline_ext_outputs,
            ) {
                (
                    GpuGKRMainLayerBatchRecordMode::InlineAll,
                    base_inputs,
                    extension_inputs,
                    base_outputs,
                    extension_outputs,
                )
            } else {
                inline_builder.restore(mark);
                (
                    GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
                    spill_builder.push_copy(&kernel.round0_descriptors.base_field_inputs),
                    spill_builder.push_copy(&kernel.round0_descriptors.extension_field_inputs),
                    spill_builder.push_copy(&kernel.round0_descriptors.base_field_outputs),
                    spill_builder.push_copy(&kernel.round0_descriptors.extension_field_outputs),
                )
            };

        let (metadata_inline, quadratic_terms, linear_terms, constant_offset) = pack_metadata_block(
            kernel.constraint_metadata.as_ref(),
            &mut inline_builder,
            spill_builder,
        );

        batch.records[idx] = GpuGKRMainRound0BatchRecord {
            kind: kernel.kind.as_u32(),
            record_mode: match (record_mode, metadata_inline) {
                (GpuGKRMainLayerBatchRecordMode::InlineAll, true) => {
                    GpuGKRMainLayerBatchRecordMode::InlineAll
                }
                (GpuGKRMainLayerBatchRecordMode::InlineAll, false) => {
                    GpuGKRMainLayerBatchRecordMode::InlineNoMetadata
                }
                _ => GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
            }
            .as_u32(),
            metadata_inline: metadata_inline as u32,
            _reserved: 0,
            base_inputs,
            extension_inputs,
            base_outputs,
            extension_outputs,
            batch_challenge_offset: kernel.batch_challenge_offset as u32,
            batch_challenge_count: kernel.batch_challenge_count as u32,
            quadratic_terms,
            linear_terms,
            auxiliary_challenge: kernel.auxiliary_challenge,
            constant_offset,
        };
    }

    batch.inline_payload = inline_builder.into_bytes();
    batch
}

fn build_main_layer_round1_batch_template<E: Field>(
    folding_steps: usize,
    static_data: &[PreparedMainLayerKernelStaticData<E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> GpuGKRMainRound1Batch<E> {
    let mut batch = GpuGKRMainRound1Batch::default();
    batch.record_count = static_data.len() as u32;
    batch.challenge_offset = 2;
    batch.challenge_count = (folding_steps - 2) as u32;
    let mut inline_builder = InlinePayloadBuilder::new();

    for (idx, kernel) in static_data.iter().enumerate() {
        let mark = inline_builder.mark();
        let inline_base_inputs =
            inline_builder.try_push_copy(&kernel.round1_descriptors.base_field_inputs);
        let inline_ext_inputs =
            inline_builder.try_push_copy(&kernel.round1_descriptors.extension_field_inputs);

        let (record_mode, base_inputs, extension_inputs) =
            if let (Some(base_inputs), Some(extension_inputs)) =
                (inline_base_inputs, inline_ext_inputs)
            {
                (
                    GpuGKRMainLayerBatchRecordMode::InlineAll,
                    base_inputs,
                    extension_inputs,
                )
            } else {
                inline_builder.restore(mark);
                (
                    GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
                    spill_builder.push_copy(&kernel.round1_descriptors.base_field_inputs),
                    spill_builder.push_copy(&kernel.round1_descriptors.extension_field_inputs),
                )
            };

        let (metadata_inline, quadratic_terms, linear_terms, constant_offset) = pack_metadata_block(
            kernel.constraint_metadata.as_ref(),
            &mut inline_builder,
            spill_builder,
        );

        batch.records[idx] = GpuGKRMainRound1BatchRecord {
            kind: kernel.kind.as_u32(),
            record_mode: match (record_mode, metadata_inline) {
                (GpuGKRMainLayerBatchRecordMode::InlineAll, true) => {
                    GpuGKRMainLayerBatchRecordMode::InlineAll
                }
                (GpuGKRMainLayerBatchRecordMode::InlineAll, false) => {
                    GpuGKRMainLayerBatchRecordMode::InlineNoMetadata
                }
                _ => GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
            }
            .as_u32(),
            metadata_inline: metadata_inline as u32,
            _reserved: 0,
            base_inputs,
            extension_inputs,
            batch_challenge_offset: kernel.batch_challenge_offset as u32,
            batch_challenge_count: kernel.batch_challenge_count as u32,
            quadratic_terms,
            linear_terms,
            auxiliary_challenge: kernel.auxiliary_challenge,
            constant_offset,
        };
    }

    batch.inline_payload = inline_builder.into_bytes();
    batch
}

fn build_main_layer_round2_batch_template<E: Field>(
    folding_steps: usize,
    static_data: &[PreparedMainLayerKernelStaticData<E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> GpuGKRMainRound2Batch<E> {
    let mut batch = GpuGKRMainRound2Batch::default();
    batch.record_count = static_data.len() as u32;
    batch.challenge_offset = 3;
    batch.challenge_count = (folding_steps - 3) as u32;
    let mut inline_builder = InlinePayloadBuilder::new();

    for (idx, kernel) in static_data.iter().enumerate() {
        let mark = inline_builder.mark();
        let inline_base_inputs =
            inline_builder.try_push_copy(&kernel.round2_descriptors.base_field_inputs);
        let inline_ext_inputs =
            inline_builder.try_push_copy(&kernel.round2_descriptors.extension_field_inputs);

        let (record_mode, base_inputs, extension_inputs) =
            if let (Some(base_inputs), Some(extension_inputs)) =
                (inline_base_inputs, inline_ext_inputs)
            {
                (
                    GpuGKRMainLayerBatchRecordMode::InlineAll,
                    base_inputs,
                    extension_inputs,
                )
            } else {
                inline_builder.restore(mark);
                (
                    GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
                    spill_builder.push_copy(&kernel.round2_descriptors.base_field_inputs),
                    spill_builder.push_copy(&kernel.round2_descriptors.extension_field_inputs),
                )
            };

        let (metadata_inline, quadratic_terms, linear_terms, constant_offset) = pack_metadata_block(
            kernel.constraint_metadata.as_ref(),
            &mut inline_builder,
            spill_builder,
        );

        batch.records[idx] = GpuGKRMainRound2BatchRecord {
            kind: kernel.kind.as_u32(),
            record_mode: match (record_mode, metadata_inline) {
                (GpuGKRMainLayerBatchRecordMode::InlineAll, true) => {
                    GpuGKRMainLayerBatchRecordMode::InlineAll
                }
                (GpuGKRMainLayerBatchRecordMode::InlineAll, false) => {
                    GpuGKRMainLayerBatchRecordMode::InlineNoMetadata
                }
                _ => GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
            }
            .as_u32(),
            metadata_inline: metadata_inline as u32,
            _reserved: 0,
            base_inputs,
            extension_inputs,
            batch_challenge_offset: kernel.batch_challenge_offset as u32,
            batch_challenge_count: kernel.batch_challenge_count as u32,
            quadratic_terms,
            linear_terms,
            auxiliary_challenge: kernel.auxiliary_challenge,
            constant_offset,
        };
    }

    batch.inline_payload = inline_builder.into_bytes();
    batch
}

fn build_main_layer_round3_batch_templates<E: Field>(
    folding_steps: usize,
    static_data: &[PreparedMainLayerKernelStaticData<E>],
    spill_builder: &mut SpillPayloadBuilder,
) -> Vec<GpuGKRMainLayerRound3BatchTemplate<E>> {
    let mut result = Vec::with_capacity(folding_steps.saturating_sub(3));
    for step in 3..folding_steps {
        let mut batch = GpuGKRMainRound3Batch::default();
        batch.record_count = static_data.len() as u32;
        batch.challenge_offset = (step + 1) as u32;
        batch.challenge_count = (folding_steps - step - 1) as u32;
        let mut inline_builder = InlinePayloadBuilder::new();

        for (idx, kernel) in static_data.iter().enumerate() {
            let descriptors = kernel
                .round3_descriptors
                .iter()
                .find(|descriptors| descriptors.step == step)
                .unwrap_or_else(|| panic!("missing round 3 descriptors for step {step}"));

            let mark = inline_builder.mark();
            let inline_base_inputs =
                inline_builder.try_push_copy(&descriptors.descriptors.base_field_inputs);
            let inline_ext_inputs =
                inline_builder.try_push_copy(&descriptors.descriptors.extension_field_inputs);

            let (record_mode, base_inputs, extension_inputs) =
                if let (Some(base_inputs), Some(extension_inputs)) =
                    (inline_base_inputs, inline_ext_inputs)
                {
                    (
                        GpuGKRMainLayerBatchRecordMode::InlineAll,
                        base_inputs,
                        extension_inputs,
                    )
                } else {
                    inline_builder.restore(mark);
                    (
                        GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
                        spill_builder.push_copy(&descriptors.descriptors.base_field_inputs),
                        spill_builder.push_copy(&descriptors.descriptors.extension_field_inputs),
                    )
                };

            let (metadata_inline, quadratic_terms, linear_terms, constant_offset) =
                pack_metadata_block(
                    kernel.constraint_metadata.as_ref(),
                    &mut inline_builder,
                    spill_builder,
                );

            batch.records[idx] = GpuGKRMainRound3BatchRecord {
                kind: kernel.kind.as_u32(),
                record_mode: match (record_mode, metadata_inline) {
                    (GpuGKRMainLayerBatchRecordMode::InlineAll, true) => {
                        GpuGKRMainLayerBatchRecordMode::InlineAll
                    }
                    (GpuGKRMainLayerBatchRecordMode::InlineAll, false) => {
                        GpuGKRMainLayerBatchRecordMode::InlineNoMetadata
                    }
                    _ => GpuGKRMainLayerBatchRecordMode::PointerDescriptors,
                }
                .as_u32(),
                metadata_inline: metadata_inline as u32,
                _reserved: 0,
                base_inputs,
                extension_inputs,
                batch_challenge_offset: kernel.batch_challenge_offset as u32,
                batch_challenge_count: kernel.batch_challenge_count as u32,
                quadratic_terms,
                linear_terms,
                auxiliary_challenge: kernel.auxiliary_challenge,
                constant_offset,
            };
        }

        batch.inline_payload = inline_builder.into_bytes();
        result.push(GpuGKRMainLayerRound3BatchTemplate { step, batch });
    }
    result
}

fn build_main_layer_batch_templates<E: Field>(
    folding_steps: usize,
    static_data: &[PreparedMainLayerKernelStaticData<E>],
) -> (
    GpuGKRMainRound0Batch<E>,
    GpuGKRMainRound1Batch<E>,
    GpuGKRMainRound2Batch<E>,
    Vec<GpuGKRMainLayerRound3BatchTemplate<E>>,
    Vec<u8>,
) {
    let mut spill_builder = SpillPayloadBuilder::default();
    let round0 =
        build_main_layer_round0_batch_template(folding_steps, static_data, &mut spill_builder);
    let round1 =
        build_main_layer_round1_batch_template(folding_steps, static_data, &mut spill_builder);
    let round2 =
        build_main_layer_round2_batch_template(folding_steps, static_data, &mut spill_builder);
    let round3 =
        build_main_layer_round3_batch_templates(folding_steps, static_data, &mut spill_builder);
    (round0, round1, round2, round3, spill_builder.bytes)
}

fn build_main_layer_kernel_blueprints<E: Field + FieldExtension<BF>>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    storage: &GpuGKRStorage<BF, E>,
    batch_challenge_base: E,
    lookup_additive_challenge: E,
    constraint_batch_challenge: E,
    num_base_layer_memory_polys: usize,
    num_base_layer_witness_polys: usize,
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
            NoFieldGKRRelation::Copy { input, output } => {
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
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalanced,
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
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { input } => {
                let relation = BatchConstraintEvalGKRRelation::<BF, E>::new(
                    input,
                    num_base_layer_memory_polys,
                    num_base_layer_witness_polys,
                    constraint_batch_challenge,
                );
                let constraint_metadata = GpuGKRMainLayerConstraintHostMetadata {
                    quadratic_terms: relation
                        .kernel
                        .quadratic_parts
                        .iter()
                        .map(
                            |((lhs, rhs), challenge)| GpuGKRMainLayerConstraintQuadraticTerm {
                                lhs: *lhs as u32,
                                rhs: *rhs as u32,
                                challenge: *challenge,
                            },
                        )
                        .collect(),
                    linear_terms: relation
                        .kernel
                        .linear_parts
                        .iter()
                        .map(|(input, challenge)| GpuGKRMainLayerConstraintLinearTerm {
                            input: *input as u32,
                            challenge: *challenge,
                        })
                        .collect(),
                    constant_offset: relation.kernel.constant_offset,
                };
                blueprints.push(
                    GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
                        inputs: <BatchConstraintEvalGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                        batch_challenge_offset: next_batch_challenge_offset,
                        batch_challenge_count: 1,
                        batch_challenges: {
                            next_batch_challenge_offset += 1;
                            vec![get_challenge()]
                        },
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: Some(
                            GpuGKRMainLayerConstraintMetadataSource::Immediate(constraint_metadata),
                        ),
                    },
                );
            }
            NoFieldGKRRelation::LinearBaseFieldRelation { .. }
            | NoFieldGKRRelation::MaxQuadratic { .. }
            | NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. }
            | NoFieldGKRRelation::MaterializeSingleLookupInput { .. }
            | NoFieldGKRRelation::MaterializedVectorLookupInput { .. }
            | NoFieldGKRRelation::LookupPairFromBaseInputs { .. }
            | NoFieldGKRRelation::LookupPairFromVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromCachedVectorInputs { .. } => {
                unimplemented!(
                    "unsupported GPU main-layer relation: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }

    blueprints
}

fn build_main_layer_kernel_blueprints_static<E: Field + FieldExtension<BF>>(
    layer: &GKRLayerDescription,
    layer_idx: usize,
    storage: &GpuGKRStorage<BF, E>,
    lookup_additive_challenge: E,
    constraint_batch_challenge: E,
    num_base_layer_memory_polys: usize,
    num_base_layer_witness_polys: usize,
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
            NoFieldGKRRelation::Copy { input, output } => {
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
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
                    lookup_additive_challenge,
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
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
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
                    lookup_additive_challenge,
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
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
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
                    lookup_additive_challenge,
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
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
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
                    lookup_additive_challenge,
                    _marker: core::marker::PhantomData,
                };
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(2, &mut next_batch_challenge_offset);
                blueprints.push(GpuGKRMainLayerKernelBlueprint {
                    kind: GpuGKRMainLayerKernelKind::LookupUnbalanced,
                    inputs: <LookupRationalPairWithUnbalancedExtensionGKRRelation<BF, E> as BatchedGKRKernel<BF, E>>::get_inputs(
                        &relation,
                    ),
                    batch_challenge_offset,
                    batch_challenge_count,
                    batch_challenges: Vec::new(),
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
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
                    lookup_additive_challenge,
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
                    auxiliary_challenge_source: GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(
                        lookup_additive_challenge,
                    ),
                    constraint_metadata_source: None,
                });
            }
            NoFieldGKRRelation::EnforceConstraintsMaxQuadratic { input } => {
                let relation = BatchConstraintEvalGKRRelation::<BF, E>::new(
                    input,
                    num_base_layer_memory_polys,
                    num_base_layer_witness_polys,
                    constraint_batch_challenge,
                );
                let constraint_metadata = build_constraint_metadata_template(
                    input,
                    num_base_layer_memory_polys,
                    num_base_layer_witness_polys,
                );
                let (batch_challenge_offset, batch_challenge_count) =
                    push_empty(1, &mut next_batch_challenge_offset);
                blueprints.push(
                    GpuGKRMainLayerKernelBlueprint {
                        kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
                        inputs: <BatchConstraintEvalGKRRelation<BF, E> as BatchedGKRKernel<
                            BF,
                            E,
                        >>::get_inputs(&relation),
                        batch_challenge_offset,
                        batch_challenge_count,
                        batch_challenges: Vec::new(),
                        auxiliary_challenge_source:
                            GpuGKRMainLayerAuxiliaryChallengeSource::Immediate(E::ZERO),
                        constraint_metadata_source: Some(
                            GpuGKRMainLayerConstraintMetadataSource::Immediate(
                                resolve_main_layer_constraint_metadata(
                                    Some(GpuGKRMainLayerConstraintMetadataSource::Deferred(
                                        constraint_metadata,
                                    )),
                                    constraint_batch_challenge,
                                )
                                .expect("constraint metadata must resolve"),
                            ),
                        ),
                    },
                );
            }
            NoFieldGKRRelation::LinearBaseFieldRelation { .. }
            | NoFieldGKRRelation::MaxQuadratic { .. }
            | NoFieldGKRRelation::UnbalancedGrandProductWithCache { .. }
            | NoFieldGKRRelation::MaterializeSingleLookupInput { .. }
            | NoFieldGKRRelation::MaterializedVectorLookupInput { .. }
            | NoFieldGKRRelation::LookupPairFromBaseInputs { .. }
            | NoFieldGKRRelation::LookupPairFromVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs { .. }
            | NoFieldGKRRelation::LookupPairFromCachedVectorInputs { .. } => {
                unimplemented!(
                    "unsupported GPU main-layer relation: {:?}",
                    gate.enforced_relation
                )
            }
        }
    }

    blueprints
}

impl<B, E> GpuGKRDimensionReducingBackwardState<B, E> {
    pub(super) fn new(
        forward_tracing_ranges: Vec<Range>,
        storage: GpuGKRStorage<B, E>,
        initial_layer_for_sumcheck: usize,
        dimension_reducing_inputs: BTreeMap<
            usize,
            BTreeMap<OutputType, DimensionReducingInputOutput>,
        >,
    ) -> Self {
        let first_output_addr = dimension_reducing_inputs[&initial_layer_for_sumcheck]
            .values()
            .next()
            .and_then(|io| io.output.first())
            .copied()
            .expect("dimension-reducing backward state requires at least one reduced output");
        let next_trace_len_after_reduction = storage.get_ext_poly(first_output_addr).len();
        let pending_layers = dimension_reducing_inputs.into_iter().rev().collect();

        Self {
            forward_tracing_ranges,
            storage,
            pending_layers,
            next_trace_len_after_reduction,
        }
    }

    pub(crate) fn storage(&self) -> &GpuGKRStorage<B, E> {
        &self.storage
    }

    pub(crate) fn purge_up_to_layer(&mut self, layer: usize) {
        self.storage.purge_up_to_layer(layer);
    }
}

impl<E: Field> GpuGKRDimensionReducingBackwardState<BF, E> {
    pub(crate) fn into_main_layer_backward_state(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        lookup_additive_challenge: E,
        constraint_batch_challenge: E,
    ) -> GpuGKRMainLayerBackwardState<E> {
        assert!(
            self.pending_layers.is_empty(),
            "main-layer handoff requires dimension-reducing layers to be exhausted"
        );
        GpuGKRMainLayerBackwardState {
            forward_tracing_ranges: self.forward_tracing_ranges,
            storage: self.storage,
            pending_layers: compiled_circuit
                .layers
                .into_iter()
                .enumerate()
                .rev()
                .collect(),
            trace_len: compiled_circuit.trace_len,
            lookup_additive_challenge,
            constraint_batch_challenge,
            num_base_layer_memory_polys: compiled_circuit.memory_layout.total_width,
            num_base_layer_witness_polys: compiled_circuit.witness_layout.total_width,
        }
    }
}

impl<B: 'static, E: Field + Reduce> GpuGKRDimensionReducingBackwardState<B, E> {
    fn prepare_layer_from_blueprints(
        &mut self,
        layer_idx: usize,
        blueprints: Vec<DimensionReducingKernelBlueprint<E>>,
        batch_challenge_base: Option<E>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingSumcheckLayerPlan<B, E>> {
        let trace_len_after_reduction = self.next_trace_len_after_reduction;
        assert!(trace_len_after_reduction.is_power_of_two());
        let folding_steps = trace_len_after_reduction.trailing_zeros() as usize;
        assert!(folding_steps >= 2);
        assert!(
            blueprints.len() <= GKR_BACKWARD_MAX_KERNELS_PER_LAYER,
            "fused dimension-reducing backward supports at most {} kernels per layer, got {}",
            GKR_BACKWARD_MAX_KERNELS_PER_LAYER,
            blueprints.len()
        );

        let mut round0_descriptors = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round0_descriptors.push(self.storage.get_for_sumcheck_round_0(&blueprint.inputs));
        }

        let mut round1_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round1_prepared_all.push(
                self.storage
                    .prepare_for_sumcheck_round_1(&blueprint.inputs, context)?,
            );
        }

        let mut round2_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round2_prepared_all.push(if folding_steps >= 3 {
                Some(
                    self.storage
                        .prepare_for_sumcheck_round_2(&blueprint.inputs, context)?,
                )
            } else {
                None
            });
        }

        let mut round3_prepared_all = Vec::with_capacity(blueprints.len());
        round3_prepared_all.resize_with(blueprints.len(), Vec::new);
        for step in 3..folding_steps {
            for (prepared_for_kernel, blueprint) in
                round3_prepared_all.iter_mut().zip(blueprints.iter())
            {
                let prepared = self.storage.prepare_for_sumcheck_round_3_and_beyond(
                    &blueprint.inputs,
                    step,
                    context,
                )?;
                prepared_for_kernel.push(GpuGKRDimensionReducingRound3Prepared { step, prepared });
            }
        }

        let mut static_data = Vec::with_capacity(blueprints.len());
        let mut kernel_plans = Vec::with_capacity(blueprints.len());
        for (
            (((blueprint, round0_descriptors_for_kernel), round1_prepared), round2_prepared),
            round3_and_beyond_prepared,
        ) in blueprints
            .into_iter()
            .zip(round0_descriptors.iter())
            .zip(round1_prepared_all.into_iter())
            .zip(round2_prepared_all.into_iter())
            .zip(round3_prepared_all.into_iter())
        {
            let round1_descriptors = round1_prepared.build_launch_descriptors();
            let round2_descriptors = round2_prepared
                .as_ref()
                .map(GpuSumcheckRound2PreparedStorage::build_launch_descriptors);
            let round3_descriptors = round3_and_beyond_prepared
                .iter()
                .map(|round3| GpuGKRDimensionReducingRound3HostDescriptors {
                    step: round3.step,
                    descriptors: round3.prepared.build_launch_descriptors(),
                })
                .collect();

            static_data.push(PreparedDimensionReducingKernelStaticData {
                kind: blueprint.kind,
                batch_challenge_offset: blueprint.batch_challenge_offset,
                batch_challenge_count: blueprint.batch_challenge_count,
                round0_descriptors: GpuSumcheckRound0LaunchDescriptors {
                    base_field_inputs: Vec::new(),
                    extension_field_inputs: round0_descriptors_for_kernel
                        .extension_field_inputs
                        .clone(),
                    base_field_outputs: Vec::new(),
                    extension_field_outputs: round0_descriptors_for_kernel
                        .extension_field_outputs
                        .clone(),
                },
                round1_descriptors,
                round2_descriptors,
                round3_descriptors,
            });
            kernel_plans.push(GpuGKRDimensionReducingKernelPlan {
                kind: blueprint.kind,
                inputs: blueprint.inputs,
                batch_challenge_offset: blueprint.batch_challenge_offset,
                batch_challenge_count: blueprint.batch_challenge_count,
                batch_challenges: blueprint.batch_challenges,
                round1_prepared,
                round2_prepared,
                round3_and_beyond_prepared,
            });
        }

        let (
            round0_batch_template,
            round1_batch_template,
            round2_batch_template,
            round3_batch_templates,
            static_spill_bytes,
        ) = build_dimension_reducing_batch_templates(folding_steps, &static_data);

        let max_acc_size = trace_len_after_reduction / 2;
        let reduction_temp_storage_bytes =
            get_reduce_temp_storage_bytes::<E>(ReduceOperation::Sum, max_acc_size as i32)?;

        let round_scratch = GpuGKRDimensionReducingRoundScratch {
            claim_point: context.alloc(folding_steps + 1, AllocationPlacement::Top)?,
            accumulator: context.alloc(max_acc_size * 2, AllocationPlacement::Top)?,
            reduction_output: context.alloc(2, AllocationPlacement::Top)?,
            reduction_temp_storage: context
                .alloc(reduction_temp_storage_bytes, AllocationPlacement::Top)?,
        };

        self.next_trace_len_after_reduction *= 2;

        Ok(GpuGKRDimensionReducingSumcheckLayerPlan {
            layer_idx,
            trace_len_after_reduction,
            folding_steps,
            batch_challenge_base,
            kernel_plans,
            round0_descriptors,
            round0_batch_template,
            round1_batch_template,
            round2_batch_template,
            round3_batch_templates,
            static_spill_bytes,
            round_scratch,
        })
    }

    pub(crate) fn prepare_next_layer(
        &mut self,
        batch_challenge_base: E,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRDimensionReducingSumcheckLayerPlan<B, E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };
        let blueprints = build_dimension_reducing_kernel_blueprints(&layer, batch_challenge_base);
        Ok(Some(self.prepare_layer_from_blueprints(
            layer_idx,
            blueprints,
            Some(batch_challenge_base),
            context,
        )?))
    }

    pub(crate) fn prepare_next_layer_static(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRDimensionReducingSumcheckLayerPlan<B, E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };
        let blueprints = build_dimension_reducing_kernel_blueprints_static::<E>(&layer);
        Ok(Some(self.prepare_layer_from_blueprints(
            layer_idx, blueprints, None, context,
        )?))
    }
}

impl<E: Field> GpuGKRMainLayerBackwardState<E> {
    pub(crate) fn storage(&self) -> &GpuGKRStorage<BF, E> {
        &self.storage
    }

    pub(crate) fn purge_up_to_layer(&mut self, layer: usize) {
        self.storage.purge_up_to_layer(layer);
    }
}

impl<E: Field + FieldExtension<BF> + Reduce> GpuGKRMainLayerBackwardState<E> {
    fn prepare_layer_from_blueprints(
        &mut self,
        layer_idx: usize,
        blueprints: Vec<GpuGKRMainLayerKernelBlueprint<E>>,
        batch_challenge_base: Option<E>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerSumcheckLayerPlan<E>> {
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        assert!(
            blueprints.len() <= GKR_BACKWARD_MAX_KERNELS_PER_LAYER,
            "fused main-layer backward supports at most {} kernels per layer, got {}",
            GKR_BACKWARD_MAX_KERNELS_PER_LAYER,
            blueprints.len()
        );

        let mut round0_descriptors = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round0_descriptors.push(self.storage.get_for_sumcheck_round_0(&blueprint.inputs));
        }

        let mut round1_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round1_prepared_all.push(
                self.storage
                    .prepare_for_sumcheck_round_1(&blueprint.inputs, context)?,
            );
        }

        let mut round2_prepared_all = Vec::with_capacity(blueprints.len());
        for blueprint in blueprints.iter() {
            round2_prepared_all.push(
                self.storage
                    .prepare_for_sumcheck_round_2(&blueprint.inputs, context)?,
            );
        }

        let mut round3_prepared_all = Vec::with_capacity(blueprints.len());
        round3_prepared_all.resize_with(blueprints.len(), Vec::new);
        for step in 3..folding_steps {
            for (prepared_for_kernel, blueprint) in
                round3_prepared_all.iter_mut().zip(blueprints.iter())
            {
                let prepared = self.storage.prepare_for_sumcheck_round_3_and_beyond(
                    &blueprint.inputs,
                    step,
                    context,
                )?;
                prepared_for_kernel.push(GpuGKRMainLayerRound3Prepared { step, prepared });
            }
        }

        let mut static_data = Vec::with_capacity(blueprints.len());
        let mut kernel_plans = Vec::with_capacity(blueprints.len());
        for (
            (((blueprint, round0_descriptors_for_kernel), round1_prepared), round2_prepared),
            round3_and_beyond_prepared,
        ) in blueprints
            .into_iter()
            .zip(round0_descriptors.iter().cloned())
            .zip(round1_prepared_all.into_iter())
            .zip(round2_prepared_all.into_iter())
            .zip(round3_prepared_all.into_iter())
        {
            let auxiliary_challenge = resolve_main_layer_auxiliary_challenge(
                blueprint.auxiliary_challenge_source,
                self.lookup_additive_challenge,
            );
            let constraint_metadata = resolve_main_layer_constraint_metadata(
                blueprint.constraint_metadata_source.clone(),
                self.constraint_batch_challenge,
            );
            let constraint_metadata_summary = constraint_metadata.as_ref().map(|metadata| {
                (
                    metadata.quadratic_terms.len(),
                    metadata.linear_terms.len(),
                    metadata.constant_offset,
                )
            });
            let round1_descriptors = round1_prepared.build_launch_descriptors();
            let round2_descriptors = round2_prepared.build_launch_descriptors();
            let round3_descriptors = round3_and_beyond_prepared
                .iter()
                .map(|round3| GpuGKRMainLayerRound3HostDescriptors {
                    step: round3.step,
                    descriptors: round3.prepared.build_launch_descriptors(),
                })
                .collect();

            static_data.push(PreparedMainLayerKernelStaticData {
                kind: blueprint.kind,
                batch_challenge_offset: blueprint.batch_challenge_offset,
                batch_challenge_count: blueprint.batch_challenge_count,
                auxiliary_challenge,
                constraint_metadata: constraint_metadata.clone(),
                round0_descriptors: round0_descriptors_for_kernel,
                round1_descriptors,
                round2_descriptors,
                round3_descriptors,
            });
            kernel_plans.push(GpuGKRMainLayerKernelPlan {
                kind: blueprint.kind,
                inputs: blueprint.inputs,
                batch_challenge_offset: blueprint.batch_challenge_offset,
                batch_challenge_count: blueprint.batch_challenge_count,
                batch_challenges: blueprint.batch_challenges,
                auxiliary_challenge_source: blueprint.auxiliary_challenge_source,
                constraint_metadata_source: blueprint.constraint_metadata_source,
                auxiliary_challenge,
                constraint_metadata_summary,
                round1_prepared,
                round2_prepared,
                round3_and_beyond_prepared,
            });
        }

        let (
            round0_batch_template,
            round1_batch_template,
            round2_batch_template,
            round3_batch_templates,
            static_spill_bytes,
        ) = build_main_layer_batch_templates(folding_steps, &static_data);

        let max_acc_size = self.trace_len / 2;
        let reduction_temp_storage_bytes =
            get_reduce_temp_storage_bytes::<E>(ReduceOperation::Sum, max_acc_size as i32)?;
        let round_scratch = GpuGKRMainLayerRoundScratch {
            claim_point: context.alloc(folding_steps + 1, AllocationPlacement::Top)?,
            eq_values: context.alloc(max_acc_size, AllocationPlacement::Top)?,
            accumulator: context.alloc(max_acc_size * 2, AllocationPlacement::Top)?,
            reduction_output: context.alloc(2, AllocationPlacement::Top)?,
            reduction_temp_storage: context
                .alloc(reduction_temp_storage_bytes, AllocationPlacement::Top)?,
        };

        Ok(GpuGKRMainLayerSumcheckLayerPlan {
            layer_idx,
            trace_len: self.trace_len,
            folding_steps,
            batch_challenge_base,
            kernel_plans,
            round0_descriptors,
            round0_batch_template,
            round1_batch_template,
            round2_batch_template,
            round3_batch_templates,
            static_spill_bytes,
            round_scratch,
        })
    }

    pub(crate) fn prepare_next_layer(
        &mut self,
        batch_challenge_base: E,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRMainLayerSumcheckLayerPlan<E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };

        assert!(self.trace_len.is_power_of_two());
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        assert!(folding_steps >= 4);

        let blueprints = build_main_layer_kernel_blueprints(
            &layer,
            layer_idx,
            &self.storage,
            batch_challenge_base,
            self.lookup_additive_challenge,
            self.constraint_batch_challenge,
            self.num_base_layer_memory_polys,
            self.num_base_layer_witness_polys,
        );
        let plan = self.prepare_layer_from_blueprints(
            layer_idx,
            blueprints,
            Some(batch_challenge_base),
            context,
        )?;
        Ok(Some(plan))
    }

    pub(crate) fn prepare_next_layer_static(
        &mut self,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRMainLayerSumcheckLayerPlan<E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };

        assert!(self.trace_len.is_power_of_two());
        let folding_steps = self.trace_len.trailing_zeros() as usize;
        assert!(folding_steps >= 4);

        let blueprints = build_main_layer_kernel_blueprints_static(
            &layer,
            layer_idx,
            &self.storage,
            self.lookup_additive_challenge,
            self.constraint_batch_challenge,
            self.num_base_layer_memory_polys,
            self.num_base_layer_witness_polys,
        );
        Ok(Some(self.prepare_layer_from_blueprints(
            layer_idx, blueprints, None, context,
        )?))
    }
}

impl<B, E> GpuGKRDimensionReducingSumcheckLayerPlan<B, E> {
    pub(crate) fn kernel_plans(&self) -> &[GpuGKRDimensionReducingKernelPlan<B, E>] {
        &self.kernel_plans
    }

    pub(crate) fn round0_descriptors(&self) -> &[GpuSumcheckRound0LaunchDescriptors<B, E>] {
        &self.round0_descriptors
    }
}

impl<E> GpuGKRMainLayerSumcheckLayerPlan<E> {
    pub(crate) fn kernel_plans(&self) -> &[GpuGKRMainLayerKernelPlan<E>] {
        &self.kernel_plans
    }

    pub(crate) fn round0_descriptors(&self) -> &[GpuSumcheckRound0LaunchDescriptors<BF, E>] {
        &self.round0_descriptors
    }
}

impl<E: Field + 'static> GpuGKRMainLayerSumcheckLayerPlan<E> {
    pub(crate) fn schedule_round_1(
        &self,
        callbacks: &mut Callbacks<'static>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound1ScheduledLaunchDescriptors<BF, E>>> {
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round1_prepared
                    .schedule_upload_launch_descriptors(context, callbacks)
            })
            .collect()
    }

    pub(crate) fn schedule_round_2(
        &self,
        callbacks: &mut Callbacks<'static>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound2ScheduledLaunchDescriptors<BF, E>>> {
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round2_prepared
                    .schedule_upload_launch_descriptors(context, callbacks)
            })
            .collect()
    }

    pub(crate) fn schedule_round_3_and_beyond(
        &self,
        step: usize,
        callbacks: &mut Callbacks<'static>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>>> {
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|prepared| prepared.step == step)
                    .unwrap_or_else(|| panic!("missing prepared round 3+ storage for step {step}"))
                    .prepared
                    .schedule_upload_launch_descriptors(context, callbacks)
            })
            .collect()
    }
}

impl<B: 'static, E: 'static> GpuGKRDimensionReducingSumcheckLayerPlan<B, E>
where
    E: Field + FieldExtension<BF> + Reduce + GpuDimensionReducingKernelSet,
    Mul: BinaryOp<E, E, E>,
    [(); E::DEGREE]: Sized,
{
    fn compute_combined_claim(&self, output_claims: &BTreeMap<GKRAddress, E>) -> E {
        let mut result = E::ZERO;
        for kernel in self.kernel_plans.iter() {
            for (output, challenge) in kernel
                .inputs
                .outputs_in_extension
                .iter()
                .zip(kernel.batch_challenges.iter())
            {
                let mut term = output_claims
                    .get(output)
                    .copied()
                    .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                term.mul_assign(challenge);
                result.add_assign(&term);
            }
        }

        result
    }

    fn batch_challenge_base_ptr(&self) -> *const E {
        unsafe {
            self.round_scratch
                .claim_point
                .as_ptr()
                .add(self.folding_steps)
        }
    }

    fn compute_combined_claim_with_batch_base(
        &self,
        output_claims: &BTreeMap<GKRAddress, E>,
        batch_challenge_base: E,
    ) -> E {
        let mut result = E::ZERO;
        for kernel in self.kernel_plans.iter() {
            let mut challenge = field_pow(batch_challenge_base, kernel.batch_challenge_offset);
            for output in kernel.inputs.outputs_in_extension.iter() {
                let mut term = output_claims
                    .get(output)
                    .copied()
                    .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                term.mul_assign(&challenge);
                result.add_assign(&term);
                challenge.mul_assign(&batch_challenge_base);
            }
        }

        result
    }

    fn launch_round0_kernels(
        &mut self,
        acc_size: usize,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.round0_batch_template;
        batch.claim_point = self.round_scratch.claim_point.as_ptr();
        batch.batch_challenge_base = self.batch_challenge_base_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.spill_payload = static_spill_upload
            .map(|upload| upload.device.as_ptr())
            .unwrap_or(null());
        launch_dim_reducing_round0_batched(&batch, acc_size, context)
    }

    fn launch_round1_kernels(
        &mut self,
        folding_challenge: &ScheduledChallengeBuffer<E>,
        acc_size: usize,
        explicit_form: bool,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.round1_batch_template;
        batch.claim_point = self.round_scratch.claim_point.as_ptr();
        batch.batch_challenge_base = self.batch_challenge_base_ptr();
        batch.folding_challenge = folding_challenge.as_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.spill_payload = static_spill_upload
            .map(|upload| upload.device.as_ptr())
            .unwrap_or(null());
        batch.explicit_form = explicit_form;
        launch_dim_reducing_round1_batched(&batch, acc_size, context)
    }

    fn launch_round2_kernels(
        &mut self,
        folding_challenge: &ScheduledChallengeBuffer<E>,
        acc_size: usize,
        explicit_form: bool,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self
            .round2_batch_template
            .expect("round 2 batch template must be present");
        batch.claim_point = self.round_scratch.claim_point.as_ptr();
        batch.batch_challenge_base = self.batch_challenge_base_ptr();
        batch.folding_challenge = folding_challenge.as_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.spill_payload = static_spill_upload
            .map(|upload| upload.device.as_ptr())
            .unwrap_or(null());
        batch.explicit_form = explicit_form;
        launch_dim_reducing_round2_batched(&batch, acc_size, context)
    }

    fn launch_round3_kernels(
        &mut self,
        step: usize,
        folding_challenge: &ScheduledChallengeBuffer<E>,
        acc_size: usize,
        explicit_form: bool,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self
            .round3_batch_templates
            .iter()
            .find(|template| template.step == step)
            .unwrap_or_else(|| {
                panic!("missing dimension-reducing round 3 template for step {step}")
            })
            .batch;
        batch.claim_point = self.round_scratch.claim_point.as_ptr();
        batch.batch_challenge_base = self.batch_challenge_base_ptr();
        batch.folding_challenge = folding_challenge.as_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.spill_payload = static_spill_upload
            .map(|upload| upload.device.as_ptr())
            .unwrap_or(null());
        batch.explicit_form = explicit_form;
        launch_dim_reducing_round3_batched(&batch, acc_size, context)
    }

    fn schedule_round_coefficients_reduction(
        &mut self,
        step: usize,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
        let challenge_count = self.folding_steps - step - 1;
        assert_eq!(acc_size, 1usize << challenge_count);
        let stream = context.get_exec_stream();
        let reduction_temp = unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.round_scratch.reduction_temp_storage.as_mut_ptr(),
                self.round_scratch.reduction_temp_storage.len(),
            )
        };
        {
            let low_half = DeviceVectorChunk::new(&self.round_scratch.accumulator, 0, acc_size);
            reduce(
                ReduceOperation::Sum,
                reduction_temp,
                &low_half,
                &mut self.round_scratch.reduction_output[0],
                stream,
            )?;
        }
        {
            let high_half =
                DeviceVectorChunk::new(&self.round_scratch.accumulator, acc_size, acc_size);
            reduce(
                ReduceOperation::Sum,
                reduction_temp,
                &high_half,
                &mut self.round_scratch.reduction_output[1],
                stream,
            )?;
        }

        let mut reduction_host = unsafe { context.alloc_host_uninit_slice(2) };
        memory_copy_async(
            &mut reduction_host,
            &self.round_scratch.reduction_output,
            context.get_exec_stream(),
        )?;
        Ok(reduction_host)
    }

    fn schedule_device_values_readback_from_raw_ptr(
        &self,
        ptr: *const E,
        len: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
        let device = unsafe { DeviceSlice::from_raw_parts(ptr, len) };
        let mut host = unsafe { context.alloc_host_uninit_slice(len) };
        memory_copy_async(&mut host, device, context.get_exec_stream())?;
        Ok(host)
    }

    fn evaluate_with_two_variable_eq_ext(values: &[E; 4], r_before_last: E, r_last: E) -> E {
        let mut result = E::ZERO;

        let mut w00 = E::ONE;
        w00.sub_assign(&r_before_last);
        let mut tmp = E::ONE;
        tmp.sub_assign(&r_last);
        w00.mul_assign(&tmp);
        let mut term = values[0];
        term.mul_assign(&w00);
        result.add_assign(&term);

        let mut w01 = E::ONE;
        w01.sub_assign(&r_before_last);
        w01.mul_assign(&r_last);
        let mut term = values[1];
        term.mul_assign(&w01);
        result.add_assign(&term);

        let mut w10 = r_before_last;
        let mut tmp = E::ONE;
        tmp.sub_assign(&r_last);
        w10.mul_assign(&tmp);
        let mut term = values[2];
        term.mul_assign(&w10);
        result.add_assign(&term);

        let mut w11 = r_before_last;
        w11.mul_assign(&r_last);
        let mut term = values[3];
        term.mul_assign(&w11);
        result.add_assign(&term);

        result
    }

    fn final_evaluation_sources_for_last_step(
        &self,
        last_step: usize,
    ) -> BTreeMap<GKRAddress, *const E> {
        let mut result = BTreeMap::new();
        for kernel in self.kernel_plans.iter() {
            let sources = match last_step {
                1 => &kernel.round1_prepared.extension_field_inputs,
                2 => {
                    &kernel
                        .round2_prepared
                        .as_ref()
                        .expect("round 2 storage must be prepared")
                        .extension_field_inputs
                }
                step => {
                    &kernel
                        .round3_and_beyond_prepared
                        .iter()
                        .find(|prepared| prepared.step == step)
                        .unwrap_or_else(|| {
                            panic!("missing prepared round 3+ storage for step {step}")
                        })
                        .prepared
                        .extension_field_inputs
                }
            };
            for (address, source) in kernel.inputs.inputs_in_extension.iter().zip(sources.iter()) {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                result.insert(*address, source.this_layer_start.cast_const());
            }
        }

        result
    }

    fn schedule_last_evaluations_readback(
        &self,
        last_step: usize,
        context: &ProverContext,
    ) -> CudaResult<BTreeMap<GKRAddress, HostAllocation<[E]>>> {
        let mut result = BTreeMap::new();
        for (address, ptr) in self.final_evaluation_sources_for_last_step(last_step) {
            result.insert(
                address,
                self.schedule_device_values_readback_from_raw_ptr(ptr, 4, context)?,
            );
        }
        Ok(result)
    }

    pub(crate) fn schedule_execute_dimension_reducing_layer(
        &mut self,
        output_layer_claims: &BTreeMap<GKRAddress, E>,
        previous_claim_point: &[E],
        seed: Seed,
        batch_challenge_base: E,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingScheduledLayerExecution<B, E>> {
        assert_eq!(
            previous_claim_point.len(),
            self.folding_steps,
            "dimension-reducing claim point must match folding steps"
        );
        if let Some(prepared_base) = self.batch_challenge_base {
            assert_eq!(
                prepared_base, batch_challenge_base,
                "dimension-reducing execution batching challenge must match prepared layer state"
            );
        }

        let last_step = self.folding_steps - 1;
        let static_spill_upload = schedule_static_spill_upload(context, &self.static_spill_bytes)?;
        let mut round_challenge_buffers = Vec::with_capacity(last_step);
        let round_challenge_device = if last_step == 0 {
            None
        } else {
            Some(Arc::new(SharedChallengeDevice::new(
                context.alloc(last_step, AllocationPlacement::Top)?,
            )))
        };
        let mut start_callbacks = Callbacks::new();
        let mut claim_point_values = previous_claim_point.to_vec();
        claim_point_values.push(batch_challenge_base);
        let claim_point_host =
            alloc_host_and_schedule_copy(context, &mut start_callbacks, claim_point_values);
        memory_copy_async(
            &mut self.round_scratch.claim_point,
            &claim_point_host,
            context.get_exec_stream(),
        )?;
        drop(claim_point_host);

        let shared_state = Arc::new(Mutex::new(ScheduledDimensionReducingLayerExecutionState {
            seed,
            claim: self.compute_combined_claim(output_layer_claims),
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps + 1),
            internal_round_coefficients: Vec::with_capacity(self.folding_steps - 1),
            result: None,
        }));
        let mut reduction_states = Vec::with_capacity(last_step);

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(acc_size, static_spill_upload.as_ref(), context)?;
            } else {
                match step {
                    1 => self.launch_round1_kernels(
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    2 => self.launch_round2_kernels(
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    _ => self.launch_round3_kernels(
                        step,
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                }
            }

            let reduction_output =
                self.schedule_round_coefficients_reduction(step, acc_size, context)?;
            let reduction_accessor = reduction_output.get_accessor();
            let next_round_challenges_offset = if step < last_step { Some(step) } else { None };
            let shared_state_for_callback = Arc::clone(&shared_state);
            let previous_claim_coord = previous_claim_point[step];
            let callback = move |dst: &mut [E]| {
                debug_assert_eq!(dst.len(), 1);
                unsafe {
                    let reduction = reduction_accessor.get();
                    let c0 = reduction[0];
                    let c2 = reduction[1];
                    let mut state = shared_state_for_callback.lock().unwrap();
                    let mut normalized_claim = state.claim;
                    normalized_claim.mul_assign(
                        &state
                            .eq_prefactor
                            .inverse()
                            .expect("eq prefactor must be non-zero"),
                    );
                    let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E>(
                        previous_claim_coord,
                        normalized_claim,
                        c0,
                        c2,
                    );
                    commit_field_els(&mut state.seed, &coeffs);
                    state.internal_round_coefficients.push(coeffs);

                    let folding_challenge = draw_random_field_els::<BF, E>(&mut state.seed, 1)[0];
                    state.claim =
                        evaluate_small_univariate_poly::<BF, E, _>(&coeffs, &folding_challenge);
                    state.eq_prefactor =
                        evaluate_eq_poly::<BF, E>(&folding_challenge, &previous_claim_coord);
                    state.folding_challenges.push(folding_challenge);
                    dst[0] = folding_challenge;
                }
            };
            let callbacks = if let (Some(device), Some(offset)) = (
                round_challenge_device.as_ref().cloned(),
                next_round_challenges_offset,
            ) {
                round_challenge_buffers.push(schedule_packed_round_challenge_upload(
                    context, device, offset, 1, callback,
                )?);
                Callbacks::new()
            } else {
                let mut callbacks = Callbacks::new();
                callbacks.schedule(
                    move || {
                        let mut tmp = [E::ZERO; 1];
                        callback(&mut tmp);
                    },
                    context.get_exec_stream(),
                )?;
                callbacks
            };
            drop(reduction_output);
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks,
                _phantom: std::marker::PhantomData,
            });
        }

        match last_step {
            1 => self.launch_round1_kernels(
                &round_challenge_buffers[last_step - 1],
                1,
                true,
                static_spill_upload.as_ref(),
                context,
            )?,
            2 => self.launch_round2_kernels(
                &round_challenge_buffers[last_step - 1],
                1,
                true,
                static_spill_upload.as_ref(),
                context,
            )?,
            step => self.launch_round3_kernels(
                step,
                &round_challenge_buffers[last_step - 1],
                1,
                true,
                static_spill_upload.as_ref(),
                context,
            )?,
        }
        let final_evaluations = self.schedule_last_evaluations_readback(last_step, context)?;
        let final_evaluation_accessors: Vec<_> = final_evaluations
            .iter()
            .map(|(addr, values)| (*addr, values.get_accessor()))
            .collect();
        let shared_state_for_callback = Arc::clone(&shared_state);
        let folding_steps = self.folding_steps;
        let mut final_readback_callbacks = Callbacks::new();
        final_readback_callbacks.schedule(
            move || unsafe {
                let mut last_evaluations = BTreeMap::new();
                for (address, accessor) in final_evaluation_accessors.iter() {
                    let values: [E; 4] = accessor.get().try_into().unwrap();
                    last_evaluations.insert(*address, values);
                }

                let transcript_inputs: Vec<E> = last_evaluations
                    .values()
                    .flat_map(|values| values.iter().copied())
                    .collect();
                let mut state = shared_state_for_callback.lock().unwrap();
                commit_field_els(&mut state.seed, &transcript_inputs);

                let challenges = draw_random_field_els::<BF, E>(&mut state.seed, 3);
                let [r_before_last, r_last, next_batching_challenge]: [E; 3] =
                    challenges.try_into().unwrap();
                let mut new_claim_point = state.folding_challenges.clone();
                new_claim_point.push(r_before_last);
                new_claim_point.push(r_last);

                let new_claims = last_evaluations
                    .iter()
                    .map(|(addr, values)| {
                        (
                            *addr,
                            Self::evaluate_with_two_variable_eq_ext(values, r_before_last, r_last),
                        )
                    })
                    .collect();

                let proof = SumcheckIntermediateProofValues::<BF, E> {
                    sumcheck_num_rounds: folding_steps,
                    internal_round_coefficients: state.internal_round_coefficients.clone(),
                    final_step_evaluations: last_evaluations
                        .iter()
                        .map(|(addr, values)| (*addr, values.to_vec()))
                        .collect(),
                    extra_evaluations_from_caching_relations: BTreeMap::new(),
                    _marker: core::marker::PhantomData,
                };

                state.result = Some(GpuGKRDimensionReducingLayerExecution {
                    proof,
                    new_claims,
                    new_claim_point,
                    next_batching_challenge,
                    updated_seed: state.seed,
                });
            },
            context.get_exec_stream(),
        )?;

        Ok(GpuGKRDimensionReducingScheduledLayerExecution {
            tracing_ranges: Vec::new(),
            start_callbacks,
            static_spill_upload,
            round_challenge_buffers,
            reduction_states,
            final_readback: {
                drop(final_evaluations);
                ScheduledDimensionReducingFinalReadback {
                    callbacks: final_readback_callbacks,
                    _phantom: std::marker::PhantomData,
                }
            },
            shared_state,
            _phantom: std::marker::PhantomData,
        })
    }

    pub(crate) fn schedule_execute_dimension_reducing_layer_from_workflow_state(
        &mut self,
        workflow_state: Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingScheduledLayerExecution<B, E>> {
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let layer_name = format!("gkr.backward.dimension_reducing.layer.{}", self.layer_idx);
        let layer_range = Range::new(layer_name.clone())?;
        layer_range.start(stream)?;
        let last_step = self.folding_steps - 1;
        let mut start_callbacks = Callbacks::new();
        let static_spill_upload = schedule_static_spill_upload(context, &self.static_spill_bytes)?;
        let shared_state = Arc::new(Mutex::new(ScheduledDimensionReducingLayerExecutionState {
            seed: Seed::default(),
            claim: E::ZERO,
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps + 1),
            internal_round_coefficients: Vec::with_capacity(self.folding_steps - 1),
            result: None,
        }));

        let mut claim_point_host =
            unsafe { context.alloc_host_uninit_slice(self.folding_steps + 1) };
        let claim_point_accessor = claim_point_host.get_mut_accessor();
        let workflow_state_for_start = Arc::clone(&workflow_state);
        let shared_state_for_start = Arc::clone(&shared_state);
        let layer_claim_callback = self
            .kernel_plans
            .iter()
            .map(|kernel| {
                (
                    kernel.batch_challenge_offset,
                    kernel.inputs.outputs_in_extension.clone(),
                )
            })
            .collect::<Vec<_>>();
        start_callbacks.schedule(
            move || unsafe {
                let workflow_state = workflow_state_for_start.lock().unwrap();
                let dst = claim_point_accessor.get_mut();
                let claim_len = dst.len() - 1;
                dst[..claim_len].copy_from_slice(&workflow_state.current_claim_point);
                dst[claim_len] = workflow_state.current_batching_challenge;
                let mut layer_state = shared_state_for_start.lock().unwrap();
                layer_state.seed = workflow_state.seed;
                layer_state.claim = {
                    let mut result = E::ZERO;
                    for (offset, outputs) in layer_claim_callback.iter() {
                        let mut challenge =
                            field_pow(workflow_state.current_batching_challenge, *offset);
                        for output in outputs.iter() {
                            let mut term = workflow_state
                                .current_claims
                                .get(output)
                                .copied()
                                .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                            term.mul_assign(&challenge);
                            result.add_assign(&term);
                            challenge.mul_assign(&workflow_state.current_batching_challenge);
                        }
                    }
                    result
                };
                layer_state.eq_prefactor = E::ONE;
                layer_state.folding_challenges.clear();
                layer_state.internal_round_coefficients.clear();
            },
            stream,
        )?;
        memory_copy_async(
            &mut self.round_scratch.claim_point,
            &claim_point_host,
            stream,
        )?;
        let mut round_challenge_buffers = Vec::with_capacity(last_step);
        let round_challenge_device = if last_step == 0 {
            None
        } else {
            Some(Arc::new(SharedChallengeDevice::new(
                context.alloc(last_step, AllocationPlacement::Top)?,
            )))
        };
        let mut reduction_states = Vec::with_capacity(last_step);

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(acc_size, static_spill_upload.as_ref(), context)?;
            } else {
                match step {
                    1 => self.launch_round1_kernels(
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    2 => self.launch_round2_kernels(
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    _ => self.launch_round3_kernels(
                        step,
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                }
            }

            let reduction_output =
                self.schedule_round_coefficients_reduction(step, acc_size, context)?;
            let reduction_accessor = reduction_output.get_accessor();
            let next_round_challenges_offset = if step < last_step { Some(step) } else { None };
            let shared_state_for_callback = Arc::clone(&shared_state);
            let previous_claim_coord_idx = step;
            let claim_point_for_callback = Arc::clone(&workflow_state);
            let callback = move |dst: &mut [E]| unsafe {
                debug_assert_eq!(dst.len(), 1);
                let reduction = reduction_accessor.get();
                let c0 = reduction[0];
                let c2 = reduction[1];
                let previous_claim_coord =
                    claim_point_for_callback.lock().unwrap().current_claim_point
                        [previous_claim_coord_idx];
                let mut state = shared_state_for_callback.lock().unwrap();
                let mut normalized_claim = state.claim;
                normalized_claim.mul_assign(
                    &state
                        .eq_prefactor
                        .inverse()
                        .expect("eq prefactor must be non-zero"),
                );
                let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E>(
                    previous_claim_coord,
                    normalized_claim,
                    c0,
                    c2,
                );
                commit_field_els(&mut state.seed, &coeffs);
                state.internal_round_coefficients.push(coeffs);

                let folding_challenge = draw_random_field_els::<BF, E>(&mut state.seed, 1)[0];
                state.claim =
                    evaluate_small_univariate_poly::<BF, E, _>(&coeffs, &folding_challenge);
                state.eq_prefactor =
                    evaluate_eq_poly::<BF, E>(&folding_challenge, &previous_claim_coord);
                state.folding_challenges.push(folding_challenge);
                dst[0] = folding_challenge;
            };
            let callbacks = if let (Some(device), Some(offset)) = (
                round_challenge_device.as_ref().cloned(),
                next_round_challenges_offset,
            ) {
                round_challenge_buffers.push(schedule_packed_round_challenge_upload(
                    context, device, offset, 1, callback,
                )?);
                Callbacks::new()
            } else {
                let mut callbacks = Callbacks::new();
                callbacks.schedule(
                    move || {
                        let mut tmp = [E::ZERO; 1];
                        callback(&mut tmp);
                    },
                    stream,
                )?;
                callbacks
            };
            drop(reduction_output);
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks,
                _phantom: std::marker::PhantomData,
            });
        }

        match last_step {
            1 => self.launch_round1_kernels(
                &round_challenge_buffers[last_step - 1],
                1,
                true,
                static_spill_upload.as_ref(),
                context,
            )?,
            2 => self.launch_round2_kernels(
                &round_challenge_buffers[last_step - 1],
                1,
                true,
                static_spill_upload.as_ref(),
                context,
            )?,
            step => self.launch_round3_kernels(
                step,
                &round_challenge_buffers[last_step - 1],
                1,
                true,
                static_spill_upload.as_ref(),
                context,
            )?,
        }
        let final_evaluations = self.schedule_last_evaluations_readback(last_step, context)?;
        let final_evaluation_accessors: Vec<_> = final_evaluations
            .iter()
            .map(|(addr, values)| (*addr, values.get_accessor()))
            .collect();
        let shared_state_for_callback = Arc::clone(&shared_state);
        let workflow_state_for_callback = Arc::clone(&workflow_state);
        let folding_steps = self.folding_steps;
        let layer_idx = self.layer_idx;
        let mut final_readback_callbacks = Callbacks::new();
        final_readback_callbacks.schedule(
            move || unsafe {
                let mut last_evaluations = BTreeMap::new();
                for (address, accessor) in final_evaluation_accessors.iter() {
                    let values: [E; 4] = accessor.get().try_into().unwrap();
                    last_evaluations.insert(*address, values);
                }

                let transcript_inputs: Vec<E> = last_evaluations
                    .values()
                    .flat_map(|values| values.iter().copied())
                    .collect();
                let mut state = shared_state_for_callback.lock().unwrap();
                commit_field_els(&mut state.seed, &transcript_inputs);

                let challenges = draw_random_field_els::<BF, E>(&mut state.seed, 3);
                let [r_before_last, r_last, next_batching_challenge]: [E; 3] =
                    challenges.try_into().unwrap();
                let mut new_claim_point = state.folding_challenges.clone();
                new_claim_point.push(r_before_last);
                new_claim_point.push(r_last);

                let new_claims = last_evaluations
                    .iter()
                    .map(|(addr, values)| {
                        (
                            *addr,
                            Self::evaluate_with_two_variable_eq_ext(values, r_before_last, r_last),
                        )
                    })
                    .collect::<BTreeMap<_, _>>();

                let proof = SumcheckIntermediateProofValues::<BF, E> {
                    sumcheck_num_rounds: folding_steps,
                    internal_round_coefficients: state.internal_round_coefficients.clone(),
                    final_step_evaluations: last_evaluations
                        .iter()
                        .map(|(addr, values)| (*addr, values.to_vec()))
                        .collect(),
                    extra_evaluations_from_caching_relations: BTreeMap::new(),
                    _marker: core::marker::PhantomData,
                };

                {
                    let mut workflow_state = workflow_state_for_callback.lock().unwrap();
                    workflow_state.current_claims = new_claims.clone();
                    workflow_state.current_claim_point = new_claim_point.clone();
                    workflow_state.current_batching_challenge = next_batching_challenge;
                    workflow_state.seed = state.seed;
                    workflow_state.proofs.insert(layer_idx, proof.clone());
                    workflow_state
                        .claims_for_layers
                        .insert(layer_idx, new_claims.clone());
                    workflow_state
                        .points_for_claims_at_layer
                        .insert(layer_idx, new_claim_point.clone());
                }

                state.result = Some(GpuGKRDimensionReducingLayerExecution {
                    proof,
                    new_claims,
                    new_claim_point,
                    next_batching_challenge,
                    updated_seed: state.seed,
                });
            },
            stream,
        )?;
        layer_range.end(stream)?;
        tracing_ranges.push(layer_range);

        drop(claim_point_host);
        Ok(GpuGKRDimensionReducingScheduledLayerExecution {
            tracing_ranges,
            start_callbacks,
            static_spill_upload,
            round_challenge_buffers,
            reduction_states,
            final_readback: {
                drop(final_evaluations);
                ScheduledDimensionReducingFinalReadback {
                    callbacks: final_readback_callbacks,
                    _phantom: std::marker::PhantomData,
                }
            },
            shared_state,
            _phantom: std::marker::PhantomData,
        })
    }
}

impl<B, E: FieldExtension<BF> + Field> GpuGKRDimensionReducingScheduledLayerExecution<B, E> {
    pub(crate) fn into_host_keepalive(self) -> GpuGKRDimensionReducingHostKeepalive<B, E> {
        let Self {
            tracing_ranges,
            start_callbacks,
            static_spill_upload,
            round_challenge_buffers,
            reduction_states,
            final_readback,
            shared_state,
            _phantom: _,
        } = self;
        GpuGKRDimensionReducingHostKeepalive {
            tracing_ranges,
            start_callbacks,
            static_spill_upload: static_spill_upload.map(upload_into_host_keepalive),
            round_challenge_buffers: round_challenge_buffers
                .into_iter()
                .map(challenge_buffer_into_host_keepalive)
                .collect(),
            reduction_states,
            final_readback,
            shared_state,
            _phantom: std::marker::PhantomData,
        }
    }

    pub(crate) fn into_execution(self) -> GpuGKRDimensionReducingLayerExecution<E> {
        self.shared_state
            .lock()
            .unwrap()
            .result
            .take()
            .expect("dimension-reducing layer execution is not ready yet")
    }
}

impl<E: 'static> GpuGKRMainLayerSumcheckLayerPlan<E>
where
    E: Field + FieldExtension<BF> + Reduce + GpuMainLayerKernelSet,
    Mul: BinaryOp<E, E, E>,
    [(); E::DEGREE]: Sized,
{
    fn compute_combined_claim(&self, output_claims: &BTreeMap<GKRAddress, E>) -> E {
        let mut result = E::ZERO;
        for kernel in self.kernel_plans.iter() {
            if kernel.kind == GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic {
                continue;
            }
            for (output, challenge) in kernel
                .inputs
                .outputs_in_base
                .iter()
                .chain(kernel.inputs.outputs_in_extension.iter())
                .zip(kernel.batch_challenges.iter())
            {
                let mut term = output_claims
                    .get(output)
                    .copied()
                    .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                term.mul_assign(challenge);
                result.add_assign(&term);
            }
        }

        result
    }

    fn compute_combined_claim_with_batch_base(
        &self,
        output_claims: &BTreeMap<GKRAddress, E>,
        batch_challenge_base: E,
    ) -> E {
        let mut result = E::ZERO;
        for kernel in self.kernel_plans.iter() {
            if kernel.kind == GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic {
                continue;
            }
            let mut challenge = field_pow(batch_challenge_base, kernel.batch_challenge_offset);
            for output in kernel
                .inputs
                .outputs_in_base
                .iter()
                .chain(kernel.inputs.outputs_in_extension.iter())
            {
                let mut term = output_claims
                    .get(output)
                    .copied()
                    .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                term.mul_assign(&challenge);
                result.add_assign(&term);
                challenge.mul_assign(&batch_challenge_base);
            }
        }

        result
    }

    fn batch_challenge_base_ptr(&self) -> *const E {
        // SAFETY: `claim_point` is allocated with `folding_steps + 1` elements in preparation.
        unsafe {
            self.round_scratch
                .claim_point
                .as_ptr()
                .add(self.folding_steps)
        }
    }

    fn launch_round0_kernels(
        &mut self,
        acc_size: usize,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.round0_batch_template;
        batch.claim_point = self.round_scratch.claim_point.as_ptr();
        batch.batch_challenge_base = self.batch_challenge_base_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.spill_payload = static_spill_upload
            .map(|upload| upload.device.as_ptr())
            .unwrap_or(null());
        launch_main_round0_batched(&batch, acc_size, context)
    }

    fn launch_round1_kernels(
        &mut self,
        folding_challenge: &ScheduledChallengeBuffer<E>,
        acc_size: usize,
        explicit_form: bool,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.round1_batch_template;
        batch.claim_point = self.round_scratch.claim_point.as_ptr();
        batch.batch_challenge_base = self.batch_challenge_base_ptr();
        batch.folding_challenge = folding_challenge.as_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.spill_payload = static_spill_upload
            .map(|upload| upload.device.as_ptr())
            .unwrap_or(null());
        batch.explicit_form = explicit_form;
        launch_main_round1_batched(&batch, acc_size, context)
    }

    fn launch_round2_kernels(
        &mut self,
        folding_challenges: &ScheduledChallengeBuffer<E>,
        acc_size: usize,
        explicit_form: bool,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self.round2_batch_template;
        batch.claim_point = self.round_scratch.claim_point.as_ptr();
        batch.batch_challenge_base = self.batch_challenge_base_ptr();
        batch.folding_challenges = folding_challenges.as_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.spill_payload = static_spill_upload
            .map(|upload| upload.device.as_ptr())
            .unwrap_or(null());
        batch.explicit_form = explicit_form;
        launch_main_round2_batched(&batch, acc_size, context)
    }

    fn launch_round3_kernels(
        &mut self,
        step: usize,
        folding_challenge: &ScheduledChallengeBuffer<E>,
        acc_size: usize,
        explicit_form: bool,
        static_spill_upload: Option<&ScheduledUpload<u8>>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let mut batch = self
            .round3_batch_templates
            .iter()
            .find(|template| template.step == step)
            .unwrap_or_else(|| panic!("missing round 3 template for step {step}"))
            .batch;
        batch.claim_point = self.round_scratch.claim_point.as_ptr();
        batch.batch_challenge_base = self.batch_challenge_base_ptr();
        batch.folding_challenge = folding_challenge.as_ptr();
        batch.contributions = self.round_scratch.accumulator.as_mut_ptr();
        batch.spill_payload = static_spill_upload
            .map(|upload| upload.device.as_ptr())
            .unwrap_or(null());
        batch.explicit_form = explicit_form;
        launch_main_round3_batched(&batch, acc_size, context)
    }

    fn schedule_round_coefficients_reduction(
        &mut self,
        step: usize,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
        let challenge_offset = step + 1;
        let challenge_count = self.folding_steps - step - 1;
        assert_eq!(acc_size, 1usize << challenge_count);
        let _ = (challenge_offset, challenge_count);
        let stream = context.get_exec_stream();
        let reduction_temp = unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.round_scratch.reduction_temp_storage.as_mut_ptr(),
                self.round_scratch.reduction_temp_storage.len(),
            )
        };
        {
            let low_half = DeviceVectorChunk::new(&self.round_scratch.accumulator, 0, acc_size);
            reduce(
                ReduceOperation::Sum,
                reduction_temp,
                &low_half,
                &mut self.round_scratch.reduction_output[0],
                stream,
            )?;
        }
        {
            let high_half =
                DeviceVectorChunk::new(&self.round_scratch.accumulator, acc_size, acc_size);
            reduce(
                ReduceOperation::Sum,
                reduction_temp,
                &high_half,
                &mut self.round_scratch.reduction_output[1],
                stream,
            )?;
        }

        let mut reduction_host = unsafe { context.alloc_host_uninit_slice(2) };
        memory_copy_async(
            &mut reduction_host,
            &self.round_scratch.reduction_output,
            context.get_exec_stream(),
        )?;
        Ok(reduction_host)
    }

    fn schedule_device_values_readback_from_raw_ptr(
        &self,
        ptr: *const E,
        len: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
        let device = unsafe { DeviceSlice::from_raw_parts(ptr, len) };
        let mut host = unsafe { context.alloc_host_uninit_slice(len) };
        memory_copy_async(&mut host, device, context.get_exec_stream())?;
        Ok(host)
    }

    fn final_evaluation_sources_for_last_step(
        &self,
        last_step: usize,
    ) -> BTreeMap<GKRAddress, *const E> {
        assert!(last_step >= 3, "main-layer final step must be in round 3+");
        let mut result = BTreeMap::new();
        for kernel in self.kernel_plans.iter() {
            let prepared = &kernel
                .round3_and_beyond_prepared
                .iter()
                .find(|prepared| prepared.step == last_step)
                .unwrap_or_else(|| panic!("missing round 3+ prepared storage for step {last_step}"))
                .prepared;
            for (address, source) in kernel
                .inputs
                .inputs_in_base
                .iter()
                .zip(prepared.base_field_inputs.iter())
            {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                result.insert(*address, source.this_layer_start.cast_const());
            }
            for (address, source) in kernel
                .inputs
                .inputs_in_extension
                .iter()
                .zip(prepared.extension_field_inputs.iter())
            {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                result.insert(*address, source.this_layer_start.cast_const());
            }
        }

        result
    }

    fn schedule_last_evaluations_readback(
        &self,
        last_step: usize,
        context: &ProverContext,
    ) -> CudaResult<BTreeMap<GKRAddress, HostAllocation<[E]>>> {
        let mut result = BTreeMap::new();
        for (address, ptr) in self.final_evaluation_sources_for_last_step(last_step) {
            result.insert(
                address,
                self.schedule_device_values_readback_from_raw_ptr(ptr, 2, context)?,
            );
        }
        Ok(result)
    }

    fn interpolate_linear(f0: E, f1: E, r: &E) -> E {
        let mut result = f1;
        result.sub_assign(&f0);
        result.mul_assign(r);
        result.add_assign(&f0);
        result
    }

    pub(crate) fn schedule_execute_main_layer(
        &mut self,
        output_layer_claims: &BTreeMap<GKRAddress, E>,
        previous_claim_point: &[E],
        seed: Seed,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerScheduledLayerExecution<E>> {
        assert_eq!(
            previous_claim_point.len(),
            self.folding_steps,
            "main-layer claim point must match folding steps"
        );

        let last_step = self.folding_steps - 1;
        assert!(last_step >= 3);
        let static_spill_upload = schedule_static_spill_upload(context, &self.static_spill_bytes)?;
        let mut round_challenge_buffers = Vec::with_capacity(last_step);
        let round_challenge_len = (1..=last_step)
            .map(main_layer_round_challenge_len)
            .sum::<usize>();
        let round_challenge_device = Arc::new(SharedChallengeDevice::new(
            context.alloc(round_challenge_len, AllocationPlacement::Top)?,
        ));
        let mut next_round_challenge_offset = 0usize;
        let mut start_callbacks = Callbacks::new();
        let mut start_state_values = previous_claim_point.to_vec();
        start_state_values.push(
            self.batch_challenge_base
                .expect("direct main-layer execution requires a prepared batching challenge base"),
        );
        let claim_point_host =
            alloc_host_and_schedule_copy(context, &mut start_callbacks, start_state_values);
        memory_copy_async(
            &mut self.round_scratch.claim_point,
            &claim_point_host,
            context.get_exec_stream(),
        )?;
        drop(claim_point_host);

        let shared_state = Arc::new(Mutex::new(ScheduledMainLayerExecutionState {
            seed,
            claim: self.compute_combined_claim(output_layer_claims),
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps),
            internal_round_coefficients: Vec::with_capacity(self.folding_steps - 1),
            result: None,
        }));
        let mut reduction_states = Vec::with_capacity(last_step);

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(acc_size, static_spill_upload.as_ref(), context)?;
            } else {
                match step {
                    1 => self.launch_round1_kernels(
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    2 => self.launch_round2_kernels(
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    _ => self.launch_round3_kernels(
                        step,
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                }
            }

            let reduction_output =
                self.schedule_round_coefficients_reduction(step, acc_size, context)?;
            let reduction_accessor = reduction_output.get_accessor();
            let next_round_len =
                (step < last_step).then(|| main_layer_round_challenge_len(step + 1));
            let shared_state_for_callback = Arc::clone(&shared_state);
            let previous_claim_coord = previous_claim_point[step];
            let callback = move |dst: &mut [E]| unsafe {
                let reduction = reduction_accessor.get();
                let c0 = reduction[0];
                let c2 = reduction[1];
                let mut state = shared_state_for_callback.lock().unwrap();
                let mut normalized_claim = state.claim;
                normalized_claim.mul_assign(
                    &state
                        .eq_prefactor
                        .inverse()
                        .expect("eq prefactor must be non-zero"),
                );
                let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E>(
                    previous_claim_coord,
                    normalized_claim,
                    c0,
                    c2,
                );
                commit_field_els(&mut state.seed, &coeffs);
                state.internal_round_coefficients.push(coeffs);

                let folding_challenge = draw_random_field_els::<BF, E>(&mut state.seed, 1)[0];
                state.claim =
                    evaluate_small_univariate_poly::<BF, E, _>(&coeffs, &folding_challenge);
                state.eq_prefactor =
                    evaluate_eq_poly::<BF, E>(&folding_challenge, &previous_claim_coord);
                state.folding_challenges.push(folding_challenge);
                match step + 1 {
                    1 => dst[0] = state.folding_challenges[0],
                    2 => {
                        dst[0] = state.folding_challenges[0];
                        dst[1] = state.folding_challenges[1];
                    }
                    _ => dst[0] = *state.folding_challenges.last().unwrap(),
                }
            };
            let callbacks = if let Some(len) = next_round_len {
                let offset = next_round_challenge_offset;
                next_round_challenge_offset += len;
                round_challenge_buffers.push(schedule_packed_round_challenge_upload(
                    context,
                    Arc::clone(&round_challenge_device),
                    offset,
                    len,
                    callback,
                )?);
                Callbacks::new()
            } else {
                let mut callbacks = Callbacks::new();
                callbacks.schedule(
                    move || {
                        let mut tmp = [E::ZERO; 2];
                        callback(&mut tmp[..main_layer_round_challenge_len(step + 1)]);
                    },
                    context.get_exec_stream(),
                )?;
                callbacks
            };
            drop(reduction_output);
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks,
                _phantom: std::marker::PhantomData,
            });
        }

        self.launch_round3_kernels(
            last_step,
            &round_challenge_buffers[last_step - 1],
            1,
            true,
            static_spill_upload.as_ref(),
            context,
        )?;
        let final_evaluations = self.schedule_last_evaluations_readback(last_step, context)?;
        let final_evaluation_accessors: Vec<_> = final_evaluations
            .iter()
            .map(|(addr, values)| (*addr, values.get_accessor()))
            .collect();
        let shared_state_for_callback = Arc::clone(&shared_state);
        let folding_steps = self.folding_steps;
        let mut final_readback_callbacks = Callbacks::new();
        final_readback_callbacks.schedule(
            move || unsafe {
                let mut last_evaluations = BTreeMap::new();
                for (address, accessor) in final_evaluation_accessors.iter() {
                    let values: [E; 2] = accessor.get().try_into().unwrap();
                    last_evaluations.insert(*address, values);
                }

                let transcript_inputs: Vec<E> = last_evaluations
                    .values()
                    .flat_map(|values| values.iter().copied())
                    .collect();
                let mut state = shared_state_for_callback.lock().unwrap();
                commit_field_els(&mut state.seed, &transcript_inputs);

                let challenges = draw_random_field_els::<BF, E>(&mut state.seed, 2);
                let [last_r, next_batching_challenge]: [E; 2] = challenges.try_into().unwrap();
                let mut new_claim_point = state.folding_challenges.clone();
                new_claim_point.push(last_r);
                let new_claims = last_evaluations
                    .iter()
                    .map(|(addr, [f0, f1])| (*addr, Self::interpolate_linear(*f0, *f1, &last_r)))
                    .collect();
                let proof = SumcheckIntermediateProofValues::<BF, E> {
                    sumcheck_num_rounds: folding_steps,
                    internal_round_coefficients: state.internal_round_coefficients.clone(),
                    final_step_evaluations: last_evaluations
                        .iter()
                        .map(|(addr, values)| (*addr, values.to_vec()))
                        .collect(),
                    extra_evaluations_from_caching_relations: BTreeMap::new(),
                    _marker: core::marker::PhantomData,
                };

                state.result = Some(GpuGKRMainLayerExecution {
                    proof,
                    new_claims,
                    new_claim_point,
                    next_batching_challenge,
                    updated_seed: state.seed,
                });
            },
            context.get_exec_stream(),
        )?;

        Ok(GpuGKRMainLayerScheduledLayerExecution {
            tracing_ranges: Vec::new(),
            start_callbacks,
            static_spill_upload,
            round_challenge_buffers,
            reduction_states,
            final_readback: {
                drop(final_evaluations);
                ScheduledDimensionReducingFinalReadback {
                    callbacks: final_readback_callbacks,
                    _phantom: std::marker::PhantomData,
                }
            },
            shared_state,
        })
    }

    pub(crate) fn schedule_execute_main_layer_from_workflow_state(
        &mut self,
        workflow_state: Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRMainLayerScheduledLayerExecution<E>> {
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let layer_name = format!("gkr.backward.main.layer.{}", self.layer_idx);
        let layer_range = Range::new(layer_name.clone())?;
        layer_range.start(stream)?;
        let last_step = self.folding_steps - 1;
        assert!(last_step >= 3);
        let mut start_callbacks = Callbacks::new();
        let static_spill_upload = schedule_static_spill_upload(context, &self.static_spill_bytes)?;
        let shared_state = Arc::new(Mutex::new(ScheduledMainLayerExecutionState {
            seed: Seed::default(),
            claim: E::ZERO,
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps),
            internal_round_coefficients: Vec::with_capacity(self.folding_steps - 1),
            result: None,
        }));

        let mut claim_point_host =
            unsafe { context.alloc_host_uninit_slice(self.folding_steps + 1) };
        let claim_point_accessor = claim_point_host.get_mut_accessor();
        let workflow_state_for_start = Arc::clone(&workflow_state);
        let shared_state_for_start = Arc::clone(&shared_state);
        let layer_claim_callback = self
            .kernel_plans
            .iter()
            .filter(|kernel| {
                kernel.kind != GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic
            })
            .map(|kernel| {
                (
                    kernel.batch_challenge_offset,
                    kernel
                        .inputs
                        .outputs_in_base
                        .iter()
                        .chain(kernel.inputs.outputs_in_extension.iter())
                        .copied()
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>();
        start_callbacks.schedule(
            move || unsafe {
                let workflow_state = workflow_state_for_start.lock().unwrap();
                let dst = claim_point_accessor.get_mut();
                let claim_len = dst.len() - 1;
                dst[..claim_len].copy_from_slice(&workflow_state.current_claim_point);
                dst[claim_len] = workflow_state.current_batching_challenge;
                let mut layer_state = shared_state_for_start.lock().unwrap();
                layer_state.seed = workflow_state.seed;
                layer_state.claim = {
                    let mut result = E::ZERO;
                    for (offset, outputs) in layer_claim_callback.iter() {
                        let mut challenge =
                            field_pow(workflow_state.current_batching_challenge, *offset);
                        for output in outputs.iter() {
                            let mut term = workflow_state
                                .current_claims
                                .get(output)
                                .copied()
                                .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                            term.mul_assign(&challenge);
                            result.add_assign(&term);
                            challenge.mul_assign(&workflow_state.current_batching_challenge);
                        }
                    }
                    result
                };
                layer_state.eq_prefactor = E::ONE;
                layer_state.folding_challenges.clear();
                layer_state.internal_round_coefficients.clear();
            },
            stream,
        )?;
        memory_copy_async(
            &mut self.round_scratch.claim_point,
            &claim_point_host,
            stream,
        )?;
        let mut round_challenge_buffers = Vec::with_capacity(last_step);
        let round_challenge_len = (1..=last_step)
            .map(main_layer_round_challenge_len)
            .sum::<usize>();
        let round_challenge_device = Arc::new(SharedChallengeDevice::new(
            context.alloc(round_challenge_len, AllocationPlacement::Top)?,
        ));
        let mut next_round_challenge_offset = 0usize;
        let mut reduction_states = Vec::with_capacity(last_step);

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(acc_size, static_spill_upload.as_ref(), context)?;
            } else {
                match step {
                    1 => self.launch_round1_kernels(
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    2 => self.launch_round2_kernels(
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                    _ => self.launch_round3_kernels(
                        step,
                        &round_challenge_buffers[step - 1],
                        acc_size,
                        false,
                        static_spill_upload.as_ref(),
                        context,
                    )?,
                }
            }

            let reduction_output =
                self.schedule_round_coefficients_reduction(step, acc_size, context)?;
            let reduction_accessor = reduction_output.get_accessor();
            let next_round_len =
                (step < last_step).then(|| main_layer_round_challenge_len(step + 1));
            let shared_state_for_callback = Arc::clone(&shared_state);
            let previous_claim_coord_idx = step;
            let claim_point_for_callback = Arc::clone(&workflow_state);
            let callback = move |dst: &mut [E]| unsafe {
                let reduction = reduction_accessor.get();
                let c0 = reduction[0];
                let c2 = reduction[1];
                let previous_claim_coord =
                    claim_point_for_callback.lock().unwrap().current_claim_point
                        [previous_claim_coord_idx];
                let mut state = shared_state_for_callback.lock().unwrap();
                let mut normalized_claim = state.claim;
                normalized_claim.mul_assign(
                    &state
                        .eq_prefactor
                        .inverse()
                        .expect("eq prefactor must be non-zero"),
                );
                let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E>(
                    previous_claim_coord,
                    normalized_claim,
                    c0,
                    c2,
                );
                commit_field_els(&mut state.seed, &coeffs);
                state.internal_round_coefficients.push(coeffs);

                let folding_challenge = draw_random_field_els::<BF, E>(&mut state.seed, 1)[0];
                state.claim =
                    evaluate_small_univariate_poly::<BF, E, _>(&coeffs, &folding_challenge);
                state.eq_prefactor =
                    evaluate_eq_poly::<BF, E>(&folding_challenge, &previous_claim_coord);
                state.folding_challenges.push(folding_challenge);
                match step + 1 {
                    1 => dst[0] = state.folding_challenges[0],
                    2 => {
                        dst[0] = state.folding_challenges[0];
                        dst[1] = state.folding_challenges[1];
                    }
                    _ => dst[0] = *state.folding_challenges.last().unwrap(),
                }
            };
            let callbacks = if let Some(len) = next_round_len {
                let offset = next_round_challenge_offset;
                next_round_challenge_offset += len;
                round_challenge_buffers.push(schedule_packed_round_challenge_upload(
                    context,
                    Arc::clone(&round_challenge_device),
                    offset,
                    len,
                    callback,
                )?);
                Callbacks::new()
            } else {
                let mut callbacks = Callbacks::new();
                callbacks.schedule(
                    move || {
                        let mut tmp = [E::ZERO; 2];
                        callback(&mut tmp[..main_layer_round_challenge_len(step + 1)]);
                    },
                    stream,
                )?;
                callbacks
            };
            drop(reduction_output);
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks,
                _phantom: std::marker::PhantomData,
            });
        }
        self.launch_round3_kernels(
            last_step,
            &round_challenge_buffers[last_step - 1],
            1,
            true,
            static_spill_upload.as_ref(),
            context,
        )?;
        let final_evaluations = self.schedule_last_evaluations_readback(last_step, context)?;
        let final_evaluation_accessors: Vec<_> = final_evaluations
            .iter()
            .map(|(addr, values)| (*addr, values.get_accessor()))
            .collect();
        let shared_state_for_callback = Arc::clone(&shared_state);
        let workflow_state_for_callback = Arc::clone(&workflow_state);
        let folding_steps = self.folding_steps;
        let layer_idx = self.layer_idx;
        let mut final_readback_callbacks = Callbacks::new();
        final_readback_callbacks.schedule(
            move || unsafe {
                let mut last_evaluations = BTreeMap::new();
                for (address, accessor) in final_evaluation_accessors.iter() {
                    let values: [E; 2] = accessor.get().try_into().unwrap();
                    last_evaluations.insert(*address, values);
                }

                let transcript_inputs: Vec<E> = last_evaluations
                    .values()
                    .flat_map(|values| values.iter().copied())
                    .collect();
                let mut state = shared_state_for_callback.lock().unwrap();
                commit_field_els(&mut state.seed, &transcript_inputs);

                let challenges = draw_random_field_els::<BF, E>(&mut state.seed, 2);
                let [last_r, next_batching_challenge]: [E; 2] = challenges.try_into().unwrap();
                let mut new_claim_point = state.folding_challenges.clone();
                new_claim_point.push(last_r);
                let new_claims = last_evaluations
                    .iter()
                    .map(|(addr, [f0, f1])| (*addr, Self::interpolate_linear(*f0, *f1, &last_r)))
                    .collect::<BTreeMap<_, _>>();
                let proof = SumcheckIntermediateProofValues::<BF, E> {
                    sumcheck_num_rounds: folding_steps,
                    internal_round_coefficients: state.internal_round_coefficients.clone(),
                    final_step_evaluations: last_evaluations
                        .iter()
                        .map(|(addr, values)| (*addr, values.to_vec()))
                        .collect(),
                    extra_evaluations_from_caching_relations: BTreeMap::new(),
                    _marker: core::marker::PhantomData,
                };

                {
                    let mut workflow_state = workflow_state_for_callback.lock().unwrap();
                    workflow_state.current_claims = new_claims.clone();
                    workflow_state.current_claim_point = new_claim_point.clone();
                    workflow_state.current_batching_challenge = next_batching_challenge;
                    workflow_state.seed = state.seed;
                    workflow_state.proofs.insert(layer_idx, proof.clone());
                    workflow_state
                        .claims_for_layers
                        .insert(layer_idx, new_claims.clone());
                    workflow_state
                        .points_for_claims_at_layer
                        .insert(layer_idx, new_claim_point.clone());
                }

                state.result = Some(GpuGKRMainLayerExecution {
                    proof,
                    new_claims,
                    new_claim_point,
                    next_batching_challenge,
                    updated_seed: state.seed,
                });
            },
            stream,
        )?;
        layer_range.end(stream)?;
        tracing_ranges.push(layer_range);

        drop(claim_point_host);
        Ok(GpuGKRMainLayerScheduledLayerExecution {
            tracing_ranges,
            start_callbacks,
            static_spill_upload,
            round_challenge_buffers,
            reduction_states,
            final_readback: {
                drop(final_evaluations);
                ScheduledDimensionReducingFinalReadback {
                    callbacks: final_readback_callbacks,
                    _phantom: std::marker::PhantomData,
                }
            },
            shared_state,
        })
    }
}

impl<E: FieldExtension<BF> + Field> GpuGKRMainLayerScheduledLayerExecution<E> {
    pub(crate) fn into_host_keepalive(self) -> GpuGKRMainLayerHostKeepalive<E> {
        let Self {
            tracing_ranges,
            start_callbacks,
            static_spill_upload,
            round_challenge_buffers,
            reduction_states,
            final_readback,
            shared_state,
        } = self;
        GpuGKRMainLayerHostKeepalive {
            tracing_ranges,
            start_callbacks,
            static_spill_upload: static_spill_upload.map(upload_into_host_keepalive),
            round_challenge_buffers: round_challenge_buffers
                .into_iter()
                .map(challenge_buffer_into_host_keepalive)
                .collect(),
            reduction_states,
            final_readback,
            shared_state,
        }
    }

    pub(crate) fn into_execution(self) -> GpuGKRMainLayerExecution<E> {
        self.shared_state
            .lock()
            .unwrap()
            .result
            .take()
            .expect("main-layer execution is not ready yet")
    }
}

impl<B, E> GpuGKRBackwardScheduledExecution<B, E>
where
    E: FieldExtension<BF> + Field,
{
    pub(crate) fn into_host_keepalive(self) -> GpuGKRBackwardHostKeepalive<B, E> {
        let Self {
            tracing_ranges,
            dimension_reducing_layers,
            main_layers,
            shared_state,
        } = self;
        GpuGKRBackwardHostKeepalive {
            tracing_ranges,
            dimension_reducing_layers: dimension_reducing_layers
                .into_iter()
                .map(GpuGKRDimensionReducingScheduledLayerExecution::into_host_keepalive)
                .collect(),
            main_layers: main_layers
                .into_iter()
                .map(GpuGKRMainLayerScheduledLayerExecution::into_host_keepalive)
                .collect(),
            shared_state,
        }
    }

    pub(crate) fn shared_state_handle(&self) -> Arc<Mutex<ScheduledBackwardWorkflowState<E>>> {
        Arc::clone(&self.shared_state)
    }

    pub(crate) fn wait(self, context: &ProverContext) -> CudaResult<GpuGKRBackwardExecution<E>> {
        context.get_exec_stream().synchronize()?;
        let mut state = self.shared_state.lock().unwrap();
        Ok(GpuGKRBackwardExecution {
            proofs: std::mem::take(&mut state.proofs),
            claims_for_layers: std::mem::take(&mut state.claims_for_layers),
            points_for_claims_at_layer: std::mem::take(&mut state.points_for_claims_at_layer),
            next_batching_challenge: state.current_batching_challenge,
            updated_seed: state.seed,
        })
    }
}

impl<E> GpuGKRDimensionReducingBackwardState<BF, E>
where
    E: Field + FieldExtension<BF> + Reduce + GpuMainLayerKernelSet + 'static,
    Mul: BinaryOp<E, E, E>,
    [(); E::DEGREE]: Sized,
{
    pub(crate) fn schedule_execute_backward_workflow_from_shared_state(
        mut self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        shared_state: Arc<Mutex<ScheduledBackwardWorkflowState<E>>>,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRBackwardScheduledExecution<BF, E>> {
        let stream = context.get_exec_stream();
        let mut tracing_ranges = Vec::new();
        let workflow_range = Range::new("gkr.backward.schedule")?;
        workflow_range.start(stream)?;
        let mut dimension_reducing_layers = Vec::new();
        let dimension_reducing_layers_range = Range::new("gkr.backward.dimension_reducing_layers")?;
        dimension_reducing_layers_range.start(stream)?;
        while let Some(mut prepared_layer) = self.prepare_next_layer_static(context)? {
            let layer_idx = prepared_layer.layer_idx;
            dimension_reducing_layers.push(
                prepared_layer.schedule_execute_dimension_reducing_layer_from_workflow_state(
                    Arc::clone(&shared_state),
                    context,
                )?,
            );
            // Stream-ordered storage can be dropped once the layer's uploads and kernels have
            // been fully enqueued on exec_stream.
            self.purge_up_to_layer(layer_idx);
        }
        dimension_reducing_layers_range.end(stream)?;
        tracing_ranges.push(dimension_reducing_layers_range);

        let (lookup_additive_challenge, constraint_batch_challenge) = {
            let workflow_state = shared_state.lock().unwrap();
            (
                workflow_state.lookup_additive_challenge,
                workflow_state.constraint_batch_challenge,
            )
        };
        let mut main_backward_state = self.into_main_layer_backward_state(
            compiled_circuit,
            lookup_additive_challenge,
            constraint_batch_challenge,
        );
        let mut main_layers = Vec::new();
        let main_layers_range = Range::new("gkr.backward.main_layers")?;
        main_layers_range.start(stream)?;
        while let Some(mut prepared_layer) =
            main_backward_state.prepare_next_layer_static(context)?
        {
            let layer_idx = prepared_layer.layer_idx;
            main_layers.push(
                prepared_layer.schedule_execute_main_layer_from_workflow_state(
                    Arc::clone(&shared_state),
                    context,
                )?,
            );
            main_backward_state.purge_up_to_layer(layer_idx);
        }
        main_layers_range.end(stream)?;
        tracing_ranges.push(main_layers_range);

        let GpuGKRMainLayerBackwardState { storage: _, .. } = main_backward_state;
        // Remaining main-layer storage drops here after all exec-stream work has been scheduled.
        workflow_range.end(stream)?;
        tracing_ranges.push(workflow_range);

        Ok(GpuGKRBackwardScheduledExecution {
            tracing_ranges,
            dimension_reducing_layers,
            main_layers,
            shared_state,
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn schedule_execute_backward_workflow(
        self,
        compiled_circuit: GKRCircuitArtifact<BF>,
        initial_output_layer_idx: usize,
        top_layer_claims: BTreeMap<GKRAddress, E>,
        evaluation_point: Vec<E>,
        seed: Seed,
        batching_challenge: E,
        lookup_additive_challenge: E,
        constraint_batch_challenge: E,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRBackwardScheduledExecution<BF, E>> {
        let shared_state = Arc::new(Mutex::new(ScheduledBackwardWorkflowState {
            claims_for_layers: BTreeMap::from([(
                initial_output_layer_idx,
                top_layer_claims.clone(),
            )]),
            points_for_claims_at_layer: BTreeMap::from([(
                initial_output_layer_idx,
                evaluation_point.clone(),
            )]),
            current_claims: top_layer_claims,
            current_claim_point: evaluation_point,
            current_batching_challenge: batching_challenge,
            lookup_additive_challenge,
            constraint_batch_challenge,
            seed,
            proofs: BTreeMap::new(),
        }));
        self.schedule_execute_backward_workflow_from_shared_state(
            compiled_circuit,
            shared_state,
            context,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::{
        build_dimension_reducing_kernel_blueprints, build_main_layer_kernel_blueprints,
        launch_build_eq_values, launch_lookup_continuation, launch_lookup_round0,
        launch_main_round0, launch_pairwise_continuation, launch_pairwise_round0,
        make_deferred_backward_workflow_state, populate_backward_workflow_state,
        GKRCircuitArtifact, GpuGKRDimensionReducingBackwardState,
        GpuGKRMainLayerConstraintLinearTerm, GpuGKRMainLayerConstraintQuadraticTerm,
        GpuGKRMainLayerKernelKind,
    };
    use crate::allocator::tracker::AllocationPlacement;
    use crate::ops::cub::device_reduce::{get_reduce_temp_storage_bytes, ReduceOperation};
    use crate::primitives::callbacks::Callbacks;
    use crate::primitives::context::{DeviceAllocation, ProverContext};
    use crate::primitives::field::{BF, E4};
    use crate::prover::gkr::{
        GpuBaseFieldPolySource, GpuExtensionFieldPolyContinuingLaunchDescriptor,
        GpuExtensionFieldPolyInitialSource, GpuSumcheckRound0DeviceLaunchDescriptors,
        GpuSumcheckRound0HostLaunchDescriptors, GpuSumcheckRound0ScheduledLaunchDescriptors,
    };
    use crate::prover::test_utils::make_test_context;
    use cs::definitions::GKRAddress;
    use cs::gkr_compiler::{
        GKRLayerDescription, GateArtifacts, NoFieldGKRRelation,
        NoFieldMaxQuadraticConstraintsGKRRelation, OutputType,
    };
    use era_cudart::memory::memory_copy_async;
    use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
    use field::{Field, FieldExtension};
    use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
    use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
    use prover::gkr::sumcheck::evaluation_kernels::{
        BatchConstraintEvalGKRRelation, BatchedGKRKernel,
    };
    use prover::gkr::sumcheck::output_univariate_monomial_form_max_quadratic;
    use prover::transcript::Seed;
    use serial_test::serial;
    use std::collections::BTreeMap;

    fn sample_ext(seed: u32) -> E4 {
        E4::from_array_of_base([
            BF::new(seed),
            BF::new(seed + 1),
            BF::new(seed + 2),
            BF::new(seed + 3),
        ])
    }

    fn successive_powers<E: Field>(base: E, count: usize) -> Vec<E> {
        let mut current = E::ONE;
        (0..count)
            .map(|_| {
                let result = current;
                current.mul_assign(&base);
                result
            })
            .collect()
    }

    fn interleaved_pairs_to_strided<T: Copy>(values: &[T]) -> Vec<T> {
        assert_eq!(values.len() % 2, 0);
        let pair_count = values.len() / 2;
        let mut result = Vec::with_capacity(values.len());
        for idx in 0..pair_count {
            result.push(values[idx * 2]);
        }
        for idx in 0..pair_count {
            result.push(values[idx * 2 + 1]);
        }
        result
    }

    fn alloc_and_copy<T: Copy>(context: &ProverContext, values: &[T]) -> DeviceAllocation<T> {
        let mut allocation = context
            .alloc(values.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
        allocation
    }

    fn copy_device_values<T: Copy>(context: &ProverContext, values: &DeviceSlice<T>) -> Vec<T> {
        let mut allocation = unsafe { context.alloc_host_uninit_slice(values.len()) };
        memory_copy_async(&mut allocation, values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        unsafe { allocation.get_accessor().get().to_vec() }
    }

    fn payload_slice<'a, T: Copy>(
        inline_payload: &'a [u8],
        spill_payload: &'a [u8],
        range: super::GpuGKRMainLayerPayloadRange,
        from_inline: bool,
    ) -> &'a [T] {
        if range.count == 0 {
            return &[];
        }
        let bytes = if from_inline {
            inline_payload
        } else {
            spill_payload
        };
        let start = range.offset as usize;
        let len = range.count as usize;
        // SAFETY: the payload builders align and serialize typed slices into these byte buffers,
        // and tests decode them with the exact same element type and count.
        unsafe { std::slice::from_raw_parts(bytes.as_ptr().add(start).cast::<T>(), len) }
    }

    fn assert_base_poly_source_slice_eq(
        actual: &[GpuBaseFieldPolySource<BF>],
        expected: &[GpuBaseFieldPolySource<BF>],
        message: &str,
    ) {
        assert_eq!(actual.len(), expected.len(), "{message}: len mismatch");
        for (idx, (actual, expected)) in actual.iter().zip(expected.iter()).enumerate() {
            assert_eq!(
                actual.start, expected.start,
                "{message}: start mismatch at index {idx}"
            );
            assert_eq!(
                actual.next_layer_size, expected.next_layer_size,
                "{message}: next_layer_size mismatch at index {idx}"
            );
        }
    }

    fn assert_extension_poly_source_slice_eq(
        actual: &[GpuExtensionFieldPolyInitialSource<E4>],
        expected: &[GpuExtensionFieldPolyInitialSource<E4>],
        message: &str,
    ) {
        assert_eq!(actual.len(), expected.len(), "{message}: len mismatch");
        for (idx, (actual, expected)) in actual.iter().zip(expected.iter()).enumerate() {
            assert_eq!(
                actual.start, expected.start,
                "{message}: start mismatch at index {idx}"
            );
            assert_eq!(
                actual.next_layer_size, expected.next_layer_size,
                "{message}: next_layer_size mismatch at index {idx}"
            );
        }
    }

    fn assert_extension_poly_continuing_slice_eq(
        actual: &[GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>],
        expected: &[GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>],
        message: &str,
    ) {
        assert_eq!(actual.len(), expected.len(), "{message}: len mismatch");
        for (idx, (actual, expected)) in actual.iter().zip(expected.iter()).enumerate() {
            assert_eq!(
                actual.previous_layer_start, expected.previous_layer_start,
                "{message}: previous_layer_start mismatch at index {idx}"
            );
            assert_eq!(
                actual.this_layer_start, expected.this_layer_start,
                "{message}: this_layer_start mismatch at index {idx}"
            );
            assert_eq!(
                actual.this_layer_size, expected.this_layer_size,
                "{message}: this_layer_size mismatch at index {idx}"
            );
            assert_eq!(
                actual.next_layer_size, expected.next_layer_size,
                "{message}: next_layer_size mismatch at index {idx}"
            );
            assert_eq!(
                actual.first_access, expected.first_access,
                "{message}: first_access mismatch at index {idx}"
            );
        }
    }

    fn eq_weights_for_binary_tail(challenge: E4) -> [E4; 2] {
        let mut one_minus = E4::ONE;
        one_minus.sub_assign(&challenge);
        [one_minus, challenge]
    }

    fn fold_continuing_value(values: &[E4], challenge: E4, idx: usize) -> E4 {
        let half = values.len() / 2;
        let mut delta = values[half + idx];
        delta.sub_assign(&values[idx]);
        let mut result = challenge;
        result.mul_assign(&delta);
        result.add_assign(&values[idx]);
        result
    }

    #[test]
    #[serial]
    fn shared_state_dimension_reduction_purges_storage_after_each_layer() {
        let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
        let context = &fixture.context;
        let expected_dimension_reducing_layers =
            fixture.initial_output_layer_idx - fixture.compiled_circuit.layers.len();
        assert!(
            expected_dimension_reducing_layers >= 2,
            "fixture must include multiple dimension-reducing layers"
        );

        let mut backward_state = fixture.gpu_backward_state;
        let shared_state = make_deferred_backward_workflow_state();
        populate_backward_workflow_state(
            &shared_state,
            fixture.initial_output_layer_idx,
            fixture.top_layer_claims,
            fixture.evaluation_point,
            fixture.seed,
            fixture.batching_challenge,
            fixture.lookup_additive_part,
            fixture.constraints_batch_challenge,
        );

        let mut dimension_reducing_layers = Vec::new();
        let mut purged_layers = 0usize;
        while let Some(mut prepared_layer) =
            backward_state.prepare_next_layer_static(context).unwrap()
        {
            let layer_idx = prepared_layer.layer_idx;
            let scheduled = prepared_layer
                .schedule_execute_dimension_reducing_layer_from_workflow_state(
                    std::sync::Arc::clone(&shared_state),
                    context,
                )
                .unwrap();
            dimension_reducing_layers.push(scheduled);
            backward_state.purge_up_to_layer(layer_idx);
            purged_layers += 1;

            assert_eq!(
                backward_state.storage().layers.len(),
                layer_idx + 1,
                "storage should be truncated through scheduled dimension-reducing layer {layer_idx}"
            );
            assert!(
                backward_state.storage().layers.get(layer_idx + 1).is_none(),
                "layers above {layer_idx} should be purged after scheduling"
            );
        }

        assert_eq!(purged_layers, expected_dimension_reducing_layers);

        let mut main_state = backward_state.into_main_layer_backward_state(
            fixture.compiled_circuit,
            E4::ZERO,
            E4::ZERO,
        );
        let mut first_main_layer = main_state
            .prepare_next_layer_static(context)
            .unwrap()
            .expect("expected first main-layer plan after dimension reduction");
        let first_main_layer_idx = first_main_layer.layer_idx;
        let _first_main_layer_execution = first_main_layer
            .schedule_execute_main_layer_from_workflow_state(
                std::sync::Arc::clone(&shared_state),
                context,
            )
            .unwrap();

        context.get_exec_stream().synchronize().unwrap();

        let execution = super::take_backward_execution_from_shared_state(&shared_state);
        assert!(
            execution.proofs.contains_key(&first_main_layer_idx),
            "shared-state workflow should still schedule the first main layer after purging"
        );
    }

    #[test]
    #[serial]
    fn first_dimension_reducing_static_batch_templates_match_expected_values() {
        let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
        let context = &fixture.context;
        let mut backward_state = fixture.gpu_backward_state;

        let static_plan = backward_state
            .prepare_next_layer_static(context)
            .unwrap()
            .expect("expected first dimension-reducing layer");

        assert!(
            static_plan.batch_challenge_base.is_none(),
            "static dimension-reducing preparation should defer the batching challenge base",
        );

        let static_spill_upload =
            super::schedule_static_spill_upload(context, &static_plan.static_spill_bytes).unwrap();
        if let Some(upload) = static_spill_upload.as_ref() {
            assert_eq!(
                copy_device_values(context, &upload.device),
                static_plan.static_spill_bytes,
                "static spill upload must match the single packed spill blob",
            );
        } else {
            assert!(
                static_plan.static_spill_bytes.is_empty(),
                "empty spill bytes should not schedule a spill upload",
            );
        }

        let round0_batch = &static_plan.round0_batch_template;
        assert_eq!(
            round0_batch.record_count as usize,
            static_plan.kernel_plans.len()
        );
        assert_eq!(round0_batch.challenge_offset as usize, 1);
        assert_eq!(
            round0_batch.challenge_count as usize,
            static_plan.folding_steps - 1
        );

        for (idx, kernel_plan) in static_plan.kernel_plans.iter().enumerate() {
            let record = &round0_batch.records[idx];
            let descriptors_inline = record.record_mode
                == super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32();
            assert_eq!(record.kind, kernel_plan.kind.as_u32());
            assert_eq!(
                record.batch_challenge_offset as usize,
                kernel_plan.batch_challenge_offset
            );
            assert_eq!(
                record.batch_challenge_count as usize,
                kernel_plan.batch_challenge_count
            );
            let round0 = &static_plan.round0_descriptors[idx];
            assert_extension_poly_source_slice_eq(
                payload_slice::<GpuExtensionFieldPolyInitialSource<E4>>(
                    &round0_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.extension_inputs,
                    descriptors_inline,
                ),
                round0.extension_field_inputs.as_slice(),
                &format!("kernel {idx} round0 extension input descriptors mismatch"),
            );
            assert_extension_poly_source_slice_eq(
                payload_slice::<GpuExtensionFieldPolyInitialSource<E4>>(
                    &round0_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.extension_outputs,
                    descriptors_inline,
                ),
                round0.extension_field_outputs.as_slice(),
                &format!("kernel {idx} round0 extension output descriptors mismatch"),
            );
        }

        let round1_batch = &static_plan.round1_batch_template;
        assert_eq!(
            round1_batch.record_count as usize,
            static_plan.kernel_plans.len()
        );
        assert_eq!(round1_batch.challenge_offset as usize, 2);
        assert_eq!(
            round1_batch.challenge_count as usize,
            static_plan.folding_steps - 2
        );
        for (idx, kernel_plan) in static_plan.kernel_plans.iter().enumerate() {
            let record = &round1_batch.records[idx];
            let descriptors_inline = record.record_mode
                == super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32();
            assert_eq!(record.kind, kernel_plan.kind.as_u32());
            let round1 = kernel_plan.round1_prepared.build_launch_descriptors();
            assert_extension_poly_continuing_slice_eq(
                payload_slice::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                    &round1_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.extension_inputs,
                    descriptors_inline,
                ),
                round1.extension_field_inputs.as_slice(),
                &format!("kernel {idx} round1 extension input descriptors mismatch"),
            );
        }

        if let Some(round2_batch) = static_plan.round2_batch_template.as_ref() {
            assert_eq!(
                round2_batch.record_count as usize,
                static_plan.kernel_plans.len()
            );
            assert_eq!(round2_batch.challenge_offset as usize, 3);
            assert_eq!(
                round2_batch.challenge_count as usize,
                static_plan.folding_steps - 3
            );
            for (idx, kernel_plan) in static_plan.kernel_plans.iter().enumerate() {
                let record = &round2_batch.records[idx];
                let descriptors_inline = record.record_mode
                    == super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32();
                assert_eq!(record.kind, kernel_plan.kind.as_u32());
                let round2 = kernel_plan
                    .round2_prepared
                    .as_ref()
                    .expect("round2 descriptors should be present")
                    .build_launch_descriptors();
                assert_extension_poly_continuing_slice_eq(
                    payload_slice::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                        &round2_batch.inline_payload,
                        &static_plan.static_spill_bytes,
                        record.extension_inputs,
                        descriptors_inline,
                    ),
                    round2.extension_field_inputs.as_slice(),
                    &format!("kernel {idx} round2 extension input descriptors mismatch"),
                );
            }
        }

        for round3_template in static_plan.round3_batch_templates.iter() {
            let step = round3_template.step;
            let batch = &round3_template.batch;
            assert_eq!(batch.record_count as usize, static_plan.kernel_plans.len());
            assert_eq!(batch.challenge_offset as usize, step + 1);
            assert_eq!(
                batch.challenge_count as usize,
                static_plan.folding_steps - step - 1
            );
            for (idx, kernel_plan) in static_plan.kernel_plans.iter().enumerate() {
                let record = &batch.records[idx];
                let descriptors_inline = record.record_mode
                    == super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32();
                assert_eq!(record.kind, kernel_plan.kind.as_u32());
                let round3 = kernel_plan
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|prepared| prepared.step == step)
                    .unwrap_or_else(|| panic!("missing round3 descriptors for step {step}"))
                    .prepared
                    .build_launch_descriptors();
                assert_extension_poly_continuing_slice_eq(
                    payload_slice::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                        &batch.inline_payload,
                        &static_plan.static_spill_bytes,
                        record.extension_inputs,
                        descriptors_inline,
                    ),
                    round3.extension_field_inputs.as_slice(),
                    &format!(
                        "kernel {idx} round3 step {step} extension input descriptors mismatch"
                    ),
                );
            }
        }
    }

    #[test]
    #[serial]
    fn first_main_layer_static_batch_templates_match_expected_values() {
        fn advance_dimension_reduction(
            mut state: GpuGKRDimensionReducingBackwardState<BF, E4>,
            compiled_circuit: &GKRCircuitArtifact<BF>,
            mut current_claims: BTreeMap<GKRAddress, E4>,
            mut current_point: Vec<E4>,
            mut seed: Seed,
            mut batching_challenge: E4,
            lookup_additive_part: E4,
            constraints_batch_challenge: E4,
            context: &ProverContext,
        ) -> (
            crate::prover::gkr::backward::GpuGKRMainLayerBackwardState<E4>,
            BTreeMap<GKRAddress, E4>,
            Vec<E4>,
            Seed,
            E4,
        ) {
            while let Some(mut plan) = state
                .prepare_next_layer(batching_challenge, context)
                .unwrap()
            {
                let scheduled = plan
                    .schedule_execute_dimension_reducing_layer(
                        &current_claims,
                        &current_point,
                        seed,
                        batching_challenge,
                        context,
                    )
                    .unwrap();
                context.get_exec_stream().synchronize().unwrap();
                let execution = scheduled.into_execution();
                current_claims = execution.new_claims;
                current_point = execution.new_claim_point;
                seed = execution.updated_seed;
                batching_challenge = execution.next_batching_challenge;
            }

            (
                state.into_main_layer_backward_state(
                    compiled_circuit.clone(),
                    lookup_additive_part,
                    constraints_batch_challenge,
                ),
                current_claims,
                current_point,
                seed,
                batching_challenge,
            )
        }

        let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
        let context = &fixture.context;
        let (mut main_state, current_claims, current_point, seed, batching_challenge) =
            advance_dimension_reduction(
                fixture.gpu_backward_state,
                &fixture.compiled_circuit,
                fixture.top_layer_claims,
                fixture.evaluation_point,
                fixture.seed,
                fixture.batching_challenge,
                fixture.lookup_additive_part,
                fixture.constraints_batch_challenge,
                context,
            );

        let static_plan = main_state
            .prepare_next_layer_static(context)
            .unwrap()
            .expect("expected first main-layer plan");
        let expected = crate::prover::tests::expected_main_layer_kernel_specs_for_test(
            &fixture.compiled_circuit.layers[static_plan.layer_idx],
            static_plan.layer_idx,
            main_state.storage(),
            batching_challenge,
            fixture.lookup_additive_part,
            fixture.constraints_batch_challenge,
            fixture.compiled_circuit.memory_layout.total_width,
            fixture.compiled_circuit.witness_layout.total_width,
        );
        assert_eq!(static_plan.kernel_plans.len(), expected.len());

        let shared_state = make_deferred_backward_workflow_state();
        populate_backward_workflow_state(
            &shared_state,
            static_plan.layer_idx + 1,
            current_claims,
            current_point,
            seed,
            batching_challenge,
            fixture.lookup_additive_part,
            fixture.constraints_batch_challenge,
        );

        assert!(
            static_plan.batch_challenge_base.is_none(),
            "workflow/static preparation should defer the batching-challenge base to layer start"
        );

        let static_spill_upload =
            super::schedule_static_spill_upload(context, &static_plan.static_spill_bytes).unwrap();
        if let Some(upload) = static_spill_upload.as_ref() {
            assert_eq!(
                copy_device_values(context, &upload.device),
                static_plan.static_spill_bytes,
                "static spill upload must match the single packed spill blob",
            );
        } else {
            assert!(
                static_plan.static_spill_bytes.is_empty(),
                "empty spill bytes should not schedule a spill upload",
            );
        }

        let round0_batch = &static_plan.round0_batch_template;
        assert_eq!(round0_batch.record_count as usize, expected.len());
        assert_eq!(
            round0_batch.challenge_offset as usize, 1,
            "round0 should skip the first claim-point coordinate when building eq weights",
        );
        assert_eq!(
            round0_batch.challenge_count as usize,
            static_plan.folding_steps - 1
        );

        for (idx, expected_kernel) in expected.iter().enumerate() {
            let kernel_plan = &static_plan.kernel_plans[idx];
            let record = &round0_batch.records[idx];
            let descriptors_inline = record.record_mode
                != super::GpuGKRMainLayerBatchRecordMode::PointerDescriptors.as_u32();

            assert_eq!(record.kind, expected_kernel.kind.as_u32());
            assert_eq!(
                record.batch_challenge_offset as usize, kernel_plan.batch_challenge_offset,
                "kernel {idx} batch challenge offset mismatch",
            );
            assert_eq!(
                record.batch_challenge_count as usize, kernel_plan.batch_challenge_count,
                "kernel {idx} batch challenge count mismatch",
            );
            assert_eq!(
                record.auxiliary_challenge, expected_kernel.auxiliary_challenge,
                "kernel {idx} auxiliary challenge mismatch",
            );

            let round0 = &static_plan.round0_descriptors[idx];
            assert_base_poly_source_slice_eq(
                payload_slice::<GpuBaseFieldPolySource<BF>>(
                    &round0_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.base_inputs,
                    descriptors_inline,
                ),
                round0.base_field_inputs.as_slice(),
                &format!("kernel {idx} round0 base input descriptors mismatch"),
            );
            assert_extension_poly_source_slice_eq(
                payload_slice::<GpuExtensionFieldPolyInitialSource<E4>>(
                    &round0_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.extension_inputs,
                    descriptors_inline,
                ),
                round0.extension_field_inputs.as_slice(),
                &format!("kernel {idx} round0 extension input descriptors mismatch"),
            );
            assert_base_poly_source_slice_eq(
                payload_slice::<GpuBaseFieldPolySource<BF>>(
                    &round0_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.base_outputs,
                    descriptors_inline,
                ),
                round0.base_field_outputs.as_slice(),
                &format!("kernel {idx} round0 base output descriptors mismatch"),
            );
            assert_extension_poly_source_slice_eq(
                payload_slice::<GpuExtensionFieldPolyInitialSource<E4>>(
                    &round0_batch.inline_payload,
                    &static_plan.static_spill_bytes,
                    record.extension_outputs,
                    descriptors_inline,
                ),
                round0.extension_field_outputs.as_slice(),
                &format!("kernel {idx} round0 extension output descriptors mismatch"),
            );

            let metadata_inline = record.metadata_inline != 0;
            match &expected_kernel.constraint_metadata {
                None => {
                    assert_eq!(record.quadratic_terms.count, 0);
                    assert_eq!(record.linear_terms.count, 0);
                    assert_eq!(record.constant_offset, E4::ZERO);
                }
                Some(expected_metadata) => {
                    assert_eq!(
                        payload_slice::<GpuGKRMainLayerConstraintQuadraticTerm<E4>>(
                            &round0_batch.inline_payload,
                            &static_plan.static_spill_bytes,
                            record.quadratic_terms,
                            metadata_inline,
                        ),
                        expected_metadata.quadratic_terms.as_slice(),
                        "kernel {idx} quadratic metadata mismatch",
                    );
                    assert_eq!(
                        payload_slice::<GpuGKRMainLayerConstraintLinearTerm<E4>>(
                            &round0_batch.inline_payload,
                            &static_plan.static_spill_bytes,
                            record.linear_terms,
                            metadata_inline,
                        ),
                        expected_metadata.linear_terms.as_slice(),
                        "kernel {idx} linear metadata mismatch",
                    );
                    assert_eq!(
                        record.constant_offset, expected_metadata.constant_offset,
                        "kernel {idx} constant offset mismatch",
                    );
                }
            }
        }
    }

    #[test]
    #[serial]
    fn main_layer0_round_coefficients_match_cpu_reference() {
        let fixture = crate::prover::tests::prepare_basic_unrolled_async_backward_fixture(8);
        let cpu_fixture = crate::prover::tests::prepare_basic_unrolled_proof_fixture();
        let expected_layer0 = cpu_fixture
            .expected_cpu_proof
            .sumcheck_intermediate_values
            .get(&0)
            .expect("CPU proof must contain layer 0");
        let context = &fixture.context;

        let mut backward_state = fixture.gpu_backward_state;
        let mut current_claims = fixture.top_layer_claims;
        let mut current_point = fixture.evaluation_point;
        let mut seed = fixture.seed;
        let mut batching_challenge = fixture.batching_challenge;

        while let Some(mut plan) = backward_state
            .prepare_next_layer(batching_challenge, context)
            .unwrap()
        {
            let scheduled = plan
                .schedule_execute_dimension_reducing_layer(
                    &current_claims,
                    &current_point,
                    seed,
                    batching_challenge,
                    context,
                )
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let execution = scheduled.into_execution();
            current_claims = execution.new_claims;
            current_point = execution.new_claim_point;
            seed = execution.updated_seed;
            batching_challenge = execution.next_batching_challenge;
        }

        let mut main_state = backward_state.into_main_layer_backward_state(
            fixture.compiled_circuit,
            fixture.lookup_additive_part,
            fixture.constraints_batch_challenge,
        );

        let mut layer0_plan = loop {
            let Some(mut plan) = main_state
                .prepare_next_layer(batching_challenge, context)
                .unwrap()
            else {
                panic!("expected to reach main layer 0");
            };
            let layer_idx = plan.layer_idx;
            if layer_idx == 0 {
                break plan;
            }
            let scheduled = plan
                .schedule_execute_main_layer(&current_claims, &current_point, seed, context)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let execution = scheduled.into_execution();
            current_claims = execution.new_claims;
            current_point = execution.new_claim_point;
            seed = execution.updated_seed;
            batching_challenge = execution.next_batching_challenge;
            main_state.purge_up_to_layer(layer_idx);
        };

        let static_spill_upload =
            super::schedule_static_spill_upload(context, &layer0_plan.static_spill_bytes).unwrap();
        let mut start_state_host =
            unsafe { context.alloc_host_uninit_slice(current_point.len() + 1) };
        unsafe {
            let batch_challenge_base = layer0_plan
                .batch_challenge_base
                .expect("direct main-layer plan must store the batching challenge base");
            start_state_host
                .get_mut_accessor()
                .get_mut()
                .copy_from_slice(
                    &current_point
                        .iter()
                        .copied()
                        .chain(std::iter::once(batch_challenge_base))
                        .collect::<Vec<_>>(),
                );
        }
        memory_copy_async(
            &mut layer0_plan.round_scratch.claim_point,
            &start_state_host,
            context.get_exec_stream(),
        )
        .unwrap();

        let mut probe_seed = seed;
        let mut probe_claim = layer0_plan.compute_combined_claim(&current_claims);
        let mut eq_prefactor = E4::ONE;
        let mut folding_challenges = Vec::with_capacity(layer0_plan.folding_steps);

        for step in 0..(layer0_plan.folding_steps - 1) {
            let acc_size = 1usize << (layer0_plan.folding_steps - step - 1);
            match step {
                0 => {
                    layer0_plan
                        .launch_round0_kernels(acc_size, static_spill_upload.as_ref(), context)
                        .unwrap();
                }
                1 => {
                    let folding_buffer = super::schedule_immediate_field_upload(
                        context,
                        1,
                        &[folding_challenges[0]],
                    )
                    .unwrap();
                    layer0_plan
                        .launch_round1_kernels(
                            &folding_buffer,
                            acc_size,
                            false,
                            static_spill_upload.as_ref(),
                            context,
                        )
                        .unwrap();
                }
                2 => {
                    let folding_buffer = super::schedule_immediate_field_upload(
                        context,
                        2,
                        &[folding_challenges[0], folding_challenges[1]],
                    )
                    .unwrap();
                    layer0_plan
                        .launch_round2_kernels(
                            &folding_buffer,
                            acc_size,
                            false,
                            static_spill_upload.as_ref(),
                            context,
                        )
                        .unwrap();
                }
                _ => {
                    let folding_buffer = super::schedule_immediate_field_upload(
                        context,
                        1,
                        &[*folding_challenges.last().unwrap()],
                    )
                    .unwrap();
                    layer0_plan
                        .launch_round3_kernels(
                            step,
                            &folding_buffer,
                            acc_size,
                            false,
                            static_spill_upload.as_ref(),
                            context,
                        )
                        .unwrap();
                }
            }

            let reduction_output = layer0_plan
                .schedule_round_coefficients_reduction(step, acc_size, context)
                .unwrap();
            context.get_exec_stream().synchronize().unwrap();
            let reduction_values: [E4; 2] =
                unsafe { reduction_output.get_accessor().get().try_into().unwrap() };

            let mut normalized_claim = probe_claim;
            normalized_claim.mul_assign(
                &eq_prefactor
                    .inverse()
                    .expect("eq prefactor must be non-zero"),
            );
            let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E4>(
                current_point[step],
                normalized_claim,
                reduction_values[0],
                reduction_values[1],
            );
            assert_eq!(
                coeffs, expected_layer0.internal_round_coefficients[step],
                "layer 0 round {step} coeffs diverged: reduction={reduction_values:?}, normalized_claim={normalized_claim:?}, eq_prefactor={eq_prefactor:?}"
            );

            commit_field_els::<BF, E4>(&mut probe_seed, &coeffs);
            let folding_challenge = draw_random_field_els::<BF, E4>(&mut probe_seed, 1)[0];
            probe_claim = prover::gkr::sumcheck::evaluate_small_univariate_poly::<BF, E4, _>(
                &coeffs,
                &folding_challenge,
            );
            eq_prefactor = prover::gkr::sumcheck::evaluate_eq_poly::<BF, E4>(
                &folding_challenge,
                &current_point[step],
            );
            folding_challenges.push(folding_challenge);
        }
    }

    #[test]
    fn dimension_reducing_kernel_blueprints_match_cpu_order_and_challenges() {
        let layer = BTreeMap::from([
            (
                OutputType::PermutationProduct,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 0,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 1,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 0,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 1,
                        },
                    ],
                },
            ),
            (
                OutputType::Lookup16Bits,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 2,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 3,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 2,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 3,
                        },
                    ],
                },
            ),
            (
                OutputType::LookupTimestamps,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 4,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 5,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 4,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 5,
                        },
                    ],
                },
            ),
            (
                OutputType::GenericLookup,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 6,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 7,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 6,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 7,
                        },
                    ],
                },
            ),
        ]);

        let batch_challenge_base = sample_ext(10);
        let blueprints = build_dimension_reducing_kernel_blueprints(&layer, batch_challenge_base);
        let powers = successive_powers(batch_challenge_base, 8);

        assert_eq!(blueprints.len(), 5);
        assert_eq!(
            blueprints[0].inputs.inputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].inputs[0]]
        );
        assert_eq!(
            blueprints[0].inputs.outputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].output[0]]
        );
        assert_eq!(blueprints[0].batch_challenges, vec![powers[0]]);

        assert_eq!(
            blueprints[1].inputs.inputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].inputs[1]]
        );
        assert_eq!(
            blueprints[1].inputs.outputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].output[1]]
        );
        assert_eq!(blueprints[1].batch_challenges, vec![powers[1]]);

        assert_eq!(
            blueprints[2].inputs.inputs_in_extension,
            layer[&OutputType::Lookup16Bits].inputs
        );
        assert_eq!(
            blueprints[2].inputs.outputs_in_extension,
            layer[&OutputType::Lookup16Bits].output
        );
        assert_eq!(blueprints[2].batch_challenges, vec![powers[2], powers[3]]);

        assert_eq!(
            blueprints[3].inputs.inputs_in_extension,
            layer[&OutputType::LookupTimestamps].inputs
        );
        assert_eq!(
            blueprints[3].inputs.outputs_in_extension,
            layer[&OutputType::LookupTimestamps].output
        );
        assert_eq!(blueprints[3].batch_challenges, vec![powers[4], powers[5]]);

        assert_eq!(
            blueprints[4].inputs.inputs_in_extension,
            layer[&OutputType::GenericLookup].inputs
        );
        assert_eq!(
            blueprints[4].inputs.outputs_in_extension,
            layer[&OutputType::GenericLookup].output
        );
        assert_eq!(blueprints[4].batch_challenges, vec![powers[6], powers[7]]);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_round0_batched_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let output_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(50), sample_ext(60)];
        let input = alloc_and_copy(&context, &input_values);
        let output = alloc_and_copy(&context, &output_values);
        let claim_point_dev = alloc_and_copy(&context, &claim_point);
        let batch_challenge_base = sample_ext(200);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge_base]);
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let extension_inputs = inline_builder
            .try_push_copy(&[GpuExtensionFieldPolyInitialSource {
                start: input.as_ptr(),
                next_layer_size: 4,
            }])
            .unwrap();
        let extension_outputs = inline_builder
            .try_push_copy(&[GpuExtensionFieldPolyInitialSource {
                start: output.as_ptr(),
                next_layer_size: 2,
            }])
            .unwrap();

        let mut batch = super::GpuGKRDimensionReducingRound0Batch::default();
        batch.record_count = 1;
        batch.challenge_offset = 1;
        batch.challenge_count = 1;
        batch.claim_point = claim_point_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.inline_payload = inline_builder.into_bytes();
        batch.records[0] = super::GpuGKRDimensionReducingRound0BatchRecord {
            kind: super::GpuGKRDimensionReducingKernelKind::Pairwise.as_u32(),
            record_mode: super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            extension_outputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 1,
        };

        super::launch_dim_reducing_round0_batched(&batch, 2, &context).unwrap();
        let actual = copy_device_values(&context, &contributions);

        let eq = eq_weights_for_binary_tail(claim_point[1]);
        let mut expected = Vec::new();
        for gid in 0..2 {
            let index = gid * 2;
            let mut c0 = batch_challenge_base;
            c0.mul_assign(&output_values[gid]);
            c0.mul_assign(&eq[gid]);

            let mut lhs = input_values[4 + index];
            lhs.sub_assign(&input_values[index]);
            let mut rhs = input_values[4 + index + 1];
            rhs.sub_assign(&input_values[index + 1]);
            let mut c1 = lhs;
            c1.mul_assign(&rhs);
            c1.mul_assign(&batch_challenge_base);
            c1.mul_assign(&eq[gid]);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_round0_batched_matches_cpu() {
        let context = make_test_context(64, 8);
        let input0_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let input1_values = (0..8).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let output_num_values = (0..4).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();
        let output_den_values = (0..4).map(|i| sample_ext(300 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(40), sample_ext(41)];
        let input0 = alloc_and_copy(&context, &input0_values);
        let input1 = alloc_and_copy(&context, &input1_values);
        let output_num = alloc_and_copy(&context, &output_num_values);
        let output_den = alloc_and_copy(&context, &output_den_values);
        let claim_point_dev = alloc_and_copy(&context, &claim_point);
        let batch_challenge_base = sample_ext(400);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge_base]);
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let extension_inputs = inline_builder
            .try_push_copy(&[
                GpuExtensionFieldPolyInitialSource {
                    start: input0.as_ptr(),
                    next_layer_size: 4,
                },
                GpuExtensionFieldPolyInitialSource {
                    start: input1.as_ptr(),
                    next_layer_size: 4,
                },
            ])
            .unwrap();
        let extension_outputs = inline_builder
            .try_push_copy(&[
                GpuExtensionFieldPolyInitialSource {
                    start: output_num.as_ptr(),
                    next_layer_size: 2,
                },
                GpuExtensionFieldPolyInitialSource {
                    start: output_den.as_ptr(),
                    next_layer_size: 2,
                },
            ])
            .unwrap();

        let mut batch = super::GpuGKRDimensionReducingRound0Batch::default();
        batch.record_count = 1;
        batch.challenge_offset = 1;
        batch.challenge_count = 1;
        batch.claim_point = claim_point_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.inline_payload = inline_builder.into_bytes();
        batch.records[0] = super::GpuGKRDimensionReducingRound0BatchRecord {
            kind: super::GpuGKRDimensionReducingKernelKind::Lookup.as_u32(),
            record_mode: super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            extension_outputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 2,
        };

        super::launch_dim_reducing_round0_batched(&batch, 2, &context).unwrap();
        let actual = copy_device_values(&context, &contributions);

        let eq = eq_weights_for_binary_tail(claim_point[1]);
        let batch0 = batch_challenge_base;
        let batch1 = super::field_pow(batch_challenge_base, 2);
        let mut expected = Vec::new();
        for gid in 0..2 {
            let index = gid * 2;
            let pair_index = index + 1;

            let mut a = input0_values[4 + index];
            a.sub_assign(&input0_values[index]);
            let mut b = input1_values[4 + index];
            b.sub_assign(&input1_values[index]);
            let mut c = input0_values[4 + pair_index];
            c.sub_assign(&input0_values[pair_index]);
            let mut d = input1_values[4 + pair_index];
            d.sub_assign(&input1_values[pair_index]);

            let mut num = a;
            num.mul_assign(&d);
            let mut t = c;
            t.mul_assign(&b);
            num.add_assign(&t);

            let mut den = b;
            den.mul_assign(&d);

            let mut c0 = batch0;
            c0.mul_assign(&output_num_values[gid]);
            let mut den_out = batch1;
            den_out.mul_assign(&output_den_values[gid]);
            c0.add_assign(&den_out);
            c0.mul_assign(&eq[gid]);

            let mut c1 = batch0;
            c1.mul_assign(&num);
            let mut den_term = batch1;
            den_term.mul_assign(&den);
            c1.add_assign(&den_term);
            c1.mul_assign(&eq[gid]);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_round1_batched_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(40), sample_ext(41), sample_ext(42)];
        let folding_challenge = sample_ext(300);
        let batch_challenge_base = sample_ext(400);
        let prev_dev = alloc_and_copy(&context, &prev);
        let claim_point_dev = alloc_and_copy(&context, &claim_point);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge_base]);
        let cache: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let extension_inputs = inline_builder
            .try_push_copy(&[GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: prev_dev.as_ptr(),
                this_layer_start: cache.as_ptr().cast_mut(),
                this_layer_size: 8,
                next_layer_size: 4,
                first_access: true,
            }])
            .unwrap();

        let mut batch = super::GpuGKRDimensionReducingRound1Batch::default();
        batch.record_count = 1;
        batch.challenge_offset = 2;
        batch.challenge_count = 1;
        batch.claim_point = claim_point_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.folding_challenge = folding_challenge_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.inline_payload = inline_builder.into_bytes();
        batch.records[0] = super::GpuGKRDimensionReducingContinuationBatchRecord {
            kind: super::GpuGKRDimensionReducingKernelKind::Pairwise.as_u32(),
            record_mode: super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 1,
        };

        super::launch_dim_reducing_round1_batched(&batch, 2, &context).unwrap();
        let actual = copy_device_values(&context, &contributions);

        let eq = eq_weights_for_binary_tail(claim_point[2]);
        let mut expected = Vec::new();
        for gid in 0..2 {
            let even_index = gid * 2;
            let odd_index = even_index + 1;
            let even0 = fold_continuing_value(&prev, folding_challenge, even_index);
            let even1 = fold_continuing_value(&prev, folding_challenge, even_index + 4);
            let mut even_delta = even1;
            even_delta.sub_assign(&even0);

            let odd0 = fold_continuing_value(&prev, folding_challenge, odd_index);
            let odd1 = fold_continuing_value(&prev, folding_challenge, odd_index + 4);
            let mut odd_delta = odd1;
            odd_delta.sub_assign(&odd0);

            let mut c0 = even0;
            c0.mul_assign(&odd0);
            c0.mul_assign(&batch_challenge_base);
            c0.mul_assign(&eq[gid]);

            let mut c1 = even_delta;
            c1.mul_assign(&odd_delta);
            c1.mul_assign(&batch_challenge_base);
            c1.mul_assign(&eq[gid]);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_round1_batched_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev0 = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let prev1 = (0..16).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(50), sample_ext(51), sample_ext(52)];
        let folding_challenge = sample_ext(300);
        let batch_challenge_base = sample_ext(400);
        let prev0_dev = alloc_and_copy(&context, &prev0);
        let prev1_dev = alloc_and_copy(&context, &prev1);
        let claim_point_dev = alloc_and_copy(&context, &claim_point);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge_base]);
        let cache0: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let cache1: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let extension_inputs = inline_builder
            .try_push_copy(&[
                GpuExtensionFieldPolyContinuingLaunchDescriptor {
                    previous_layer_start: prev0_dev.as_ptr(),
                    this_layer_start: cache0.as_ptr().cast_mut(),
                    this_layer_size: 8,
                    next_layer_size: 4,
                    first_access: true,
                },
                GpuExtensionFieldPolyContinuingLaunchDescriptor {
                    previous_layer_start: prev1_dev.as_ptr(),
                    this_layer_start: cache1.as_ptr().cast_mut(),
                    this_layer_size: 8,
                    next_layer_size: 4,
                    first_access: true,
                },
            ])
            .unwrap();

        let mut batch = super::GpuGKRDimensionReducingRound1Batch::default();
        batch.record_count = 1;
        batch.challenge_offset = 2;
        batch.challenge_count = 1;
        batch.claim_point = claim_point_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.folding_challenge = folding_challenge_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.inline_payload = inline_builder.into_bytes();
        batch.records[0] = super::GpuGKRDimensionReducingContinuationBatchRecord {
            kind: super::GpuGKRDimensionReducingKernelKind::Lookup.as_u32(),
            record_mode: super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 2,
        };

        super::launch_dim_reducing_round1_batched(&batch, 2, &context).unwrap();
        let actual = copy_device_values(&context, &contributions);

        let eq = eq_weights_for_binary_tail(claim_point[2]);
        let batch0 = batch_challenge_base;
        let batch1 = super::field_pow(batch_challenge_base, 2);
        let mut expected = Vec::new();
        for gid in 0..2 {
            let even_index = gid * 2;
            let odd_index = even_index + 1;

            let a0 = fold_continuing_value(&prev0, folding_challenge, even_index);
            let a1_full = fold_continuing_value(&prev0, folding_challenge, even_index + 4);
            let mut da = a1_full;
            da.sub_assign(&a0);
            let b0 = fold_continuing_value(&prev1, folding_challenge, even_index);
            let b1_full = fold_continuing_value(&prev1, folding_challenge, even_index + 4);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0 = fold_continuing_value(&prev0, folding_challenge, odd_index);
            let c1_full = fold_continuing_value(&prev0, folding_challenge, odd_index + 4);
            let mut dc = c1_full;
            dc.sub_assign(&c0);
            let d0 = fold_continuing_value(&prev1, folding_challenge, odd_index);
            let d1_full = fold_continuing_value(&prev1, folding_challenge, odd_index + 4);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut num0 = a0;
            num0.mul_assign(&d0);
            let mut t0 = c0;
            t0.mul_assign(&b0);
            num0.add_assign(&t0);
            let mut den0 = b0;
            den0.mul_assign(&d0);

            let mut num1 = da;
            num1.mul_assign(&dd);
            let mut t1 = dc;
            t1.mul_assign(&db);
            num1.add_assign(&t1);
            let mut den1 = db;
            den1.mul_assign(&dd);

            let mut out0 = batch0;
            out0.mul_assign(&num0);
            let mut out0_den = batch1;
            out0_den.mul_assign(&den0);
            out0.add_assign(&out0_den);
            out0.mul_assign(&eq[gid]);

            let mut out1 = batch0;
            out1.mul_assign(&num1);
            let mut out1_den = batch1;
            out1_den.mul_assign(&den1);
            out1.add_assign(&out1_den);
            out1.mul_assign(&eq[gid]);

            expected.push(out0);
            expected.push(out1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_round2_batched_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let claim_point = [
            sample_ext(40),
            sample_ext(41),
            sample_ext(42),
            sample_ext(43),
        ];
        let folding_challenge = sample_ext(300);
        let batch_challenge_base = sample_ext(400);
        let prev_dev = alloc_and_copy(&context, &prev);
        let claim_point_dev = alloc_and_copy(&context, &claim_point);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge_base]);
        let cache: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let extension_inputs = inline_builder
            .try_push_copy(&[GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: prev_dev.as_ptr(),
                this_layer_start: cache.as_ptr().cast_mut(),
                this_layer_size: 8,
                next_layer_size: 4,
                first_access: true,
            }])
            .unwrap();

        let mut batch = super::GpuGKRDimensionReducingRound2Batch::default();
        batch.record_count = 1;
        batch.challenge_offset = 3;
        batch.challenge_count = 1;
        batch.claim_point = claim_point_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.folding_challenge = folding_challenge_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.inline_payload = inline_builder.into_bytes();
        batch.records[0] = super::GpuGKRDimensionReducingContinuationBatchRecord {
            kind: super::GpuGKRDimensionReducingKernelKind::Pairwise.as_u32(),
            record_mode: super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 1,
        };

        super::launch_dim_reducing_round2_batched(&batch, 2, &context).unwrap();
        let actual = copy_device_values(&context, &contributions);

        let eq = eq_weights_for_binary_tail(claim_point[3]);
        let mut expected = Vec::new();
        for gid in 0..2 {
            let even_index = gid * 2;
            let odd_index = even_index + 1;
            let even0 = fold_continuing_value(&prev, folding_challenge, even_index);
            let even1 = fold_continuing_value(&prev, folding_challenge, even_index + 4);
            let mut even_delta = even1;
            even_delta.sub_assign(&even0);

            let odd0 = fold_continuing_value(&prev, folding_challenge, odd_index);
            let odd1 = fold_continuing_value(&prev, folding_challenge, odd_index + 4);
            let mut odd_delta = odd1;
            odd_delta.sub_assign(&odd0);

            let mut c0 = even0;
            c0.mul_assign(&odd0);
            c0.mul_assign(&batch_challenge_base);
            c0.mul_assign(&eq[gid]);

            let mut c1 = even_delta;
            c1.mul_assign(&odd_delta);
            c1.mul_assign(&batch_challenge_base);
            c1.mul_assign(&eq[gid]);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_round3_batched_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev0 = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let prev1 = (0..16).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let claim_point = [
            sample_ext(50),
            sample_ext(51),
            sample_ext(52),
            sample_ext(53),
            sample_ext(54),
        ];
        let folding_challenge = sample_ext(300);
        let batch_challenge_base = sample_ext(400);
        let prev0_dev = alloc_and_copy(&context, &prev0);
        let prev1_dev = alloc_and_copy(&context, &prev1);
        let claim_point_dev = alloc_and_copy(&context, &claim_point);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge_base]);
        let cache0: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let cache1: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut inline_builder = super::InlinePayloadBuilder::new();
        let extension_inputs = inline_builder
            .try_push_copy(&[
                GpuExtensionFieldPolyContinuingLaunchDescriptor {
                    previous_layer_start: prev0_dev.as_ptr(),
                    this_layer_start: cache0.as_ptr().cast_mut(),
                    this_layer_size: 8,
                    next_layer_size: 4,
                    first_access: true,
                },
                GpuExtensionFieldPolyContinuingLaunchDescriptor {
                    previous_layer_start: prev1_dev.as_ptr(),
                    this_layer_start: cache1.as_ptr().cast_mut(),
                    this_layer_size: 8,
                    next_layer_size: 4,
                    first_access: true,
                },
            ])
            .unwrap();

        let mut batch = super::GpuGKRDimensionReducingRound3Batch::default();
        batch.record_count = 1;
        batch.challenge_offset = 4;
        batch.challenge_count = 1;
        batch.claim_point = claim_point_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.folding_challenge = folding_challenge_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.inline_payload = inline_builder.into_bytes();
        batch.records[0] = super::GpuGKRDimensionReducingContinuationBatchRecord {
            kind: super::GpuGKRDimensionReducingKernelKind::Lookup.as_u32(),
            record_mode: super::GpuGKRDimensionReducingBatchRecordMode::InlineDescriptors.as_u32(),
            _reserved0: 0,
            _reserved1: 0,
            extension_inputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 2,
        };

        super::launch_dim_reducing_round3_batched(&batch, 2, &context).unwrap();
        let actual = copy_device_values(&context, &contributions);

        let eq = eq_weights_for_binary_tail(claim_point[4]);
        let batch0 = batch_challenge_base;
        let batch1 = super::field_pow(batch_challenge_base, 2);
        let mut expected = Vec::new();
        for gid in 0..2 {
            let even_index = gid * 2;
            let odd_index = even_index + 1;

            let a0 = fold_continuing_value(&prev0, folding_challenge, even_index);
            let a1_full = fold_continuing_value(&prev0, folding_challenge, even_index + 4);
            let mut da = a1_full;
            da.sub_assign(&a0);
            let b0 = fold_continuing_value(&prev1, folding_challenge, even_index);
            let b1_full = fold_continuing_value(&prev1, folding_challenge, even_index + 4);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0 = fold_continuing_value(&prev0, folding_challenge, odd_index);
            let c1_full = fold_continuing_value(&prev0, folding_challenge, odd_index + 4);
            let mut dc = c1_full;
            dc.sub_assign(&c0);
            let d0 = fold_continuing_value(&prev1, folding_challenge, odd_index);
            let d1_full = fold_continuing_value(&prev1, folding_challenge, odd_index + 4);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut num0 = a0;
            num0.mul_assign(&d0);
            let mut t0 = c0;
            t0.mul_assign(&b0);
            num0.add_assign(&t0);
            let mut den0 = b0;
            den0.mul_assign(&d0);

            let mut num1 = da;
            num1.mul_assign(&dd);
            let mut t1 = dc;
            t1.mul_assign(&db);
            num1.add_assign(&t1);
            let mut den1 = db;
            den1.mul_assign(&dd);

            let mut out0 = batch0;
            out0.mul_assign(&num0);
            let mut out0_den = batch1;
            out0_den.mul_assign(&den0);
            out0.add_assign(&out0_den);
            out0.mul_assign(&eq[gid]);

            let mut out1 = batch0;
            out1.mul_assign(&num1);
            let mut out1_den = batch1;
            out1_den.mul_assign(&den1);
            out1.add_assign(&out1_den);
            out1.mul_assign(&eq[gid]);

            expected.push(out0);
            expected.push(out1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_round0_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let output_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let batch_challenge = sample_ext(200);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge]);
        let input = alloc_and_copy(&context, &input_values);
        let output = alloc_and_copy(&context, &output_values);
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: input.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: output.as_ptr(),
                next_layer_size: 2,
            };
        }
        memory_copy_async(
            &mut round0.device.extension_field_inputs,
            &round0.host.extension_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.extension_field_outputs,
            &round0.host.extension_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_pairwise_round0::<E4>(
            &round0,
            batch_challenges_dev.as_ptr(),
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let index = output_index * 2;
            let mut c0 = batch_challenge;
            c0.mul_assign(&output_values[output_index]);
            let mut a = input_values[4 + index];
            a.sub_assign(&input_values[index]);
            let mut b = input_values[4 + index + 1];
            b.sub_assign(&input_values[index + 1]);
            let mut c1 = a;
            c1.mul_assign(&b);
            c1.mul_assign(&batch_challenge);
            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_round0_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let input0_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let input1_values = (0..8).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let output_num_values = (0..4).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();
        let output_den_values = (0..4).map(|i| sample_ext(300 + i)).collect::<Vec<_>>();
        let input0 = alloc_and_copy(&context, &input0_values);
        let input1 = alloc_and_copy(&context, &input1_values);
        let output_num = alloc_and_copy(&context, &output_num_values);
        let output_den = alloc_and_copy(&context, &output_den_values);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(2)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(2)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(2, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(2, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: input0.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[1] = GpuExtensionFieldPolyInitialSource {
                start: input1.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: output_num.as_ptr(),
                next_layer_size: 2,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[1] = GpuExtensionFieldPolyInitialSource {
                start: output_den.as_ptr(),
                next_layer_size: 2,
            };
        }
        memory_copy_async(
            &mut round0.device.extension_field_inputs,
            &round0.host.extension_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.extension_field_outputs,
            &round0.host.extension_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_lookup_round0::<E4>(
            &round0,
            batch_challenges_dev.as_ptr(),
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let index = output_index * 2;
            let pair_index = index + 1;

            let mut a = input0_values[4 + index];
            a.sub_assign(&input0_values[index]);
            let mut b = input1_values[4 + index];
            b.sub_assign(&input1_values[index]);
            let mut c = input0_values[4 + pair_index];
            c.sub_assign(&input0_values[pair_index]);
            let mut d = input1_values[4 + pair_index];
            d.sub_assign(&input1_values[pair_index]);

            let mut num = a;
            num.mul_assign(&d);
            let mut t = c;
            t.mul_assign(&b);
            num.add_assign(&t);

            let mut den = b;
            den.mul_assign(&d);

            let mut c0 = batch0;
            c0.mul_assign(&output_num_values[output_index]);
            let mut output_den_term = batch1;
            output_den_term.mul_assign(&output_den_values[output_index]);
            c0.add_assign(&output_den_term);

            let mut c1 = batch0;
            c1.mul_assign(&num);
            let mut den_term = batch1;
            den_term.mul_assign(&den);
            c1.add_assign(&den_term);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_continuation_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev0 = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let prev1 = (0..16).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let challenge = sample_ext(300);
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let prev0_dev = alloc_and_copy(&context, &prev0);
        let prev1_dev = alloc_and_copy(&context, &prev1);
        let cache0: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let cache1: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let folding_challenge_dev = alloc_and_copy(&context, &[challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let descriptors = [
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: prev0_dev.as_ptr(),
                this_layer_start: cache0.as_ptr().cast_mut(),
                this_layer_size: 8,
                next_layer_size: 4,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: prev1_dev.as_ptr(),
                this_layer_start: cache1.as_ptr().cast_mut(),
                this_layer_size: 8,
                next_layer_size: 4,
                first_access: true,
            },
        ];
        let descriptors_dev = alloc_and_copy(&context, &descriptors);
        let contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        launch_lookup_continuation::<E4>(
            descriptors_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            batch_challenges_dev.as_ptr(),
            false,
            contributions.as_ptr().cast_mut(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold = |values: &[E4], idx: usize| {
            let mut delta = values[8 + idx];
            delta.sub_assign(&values[idx]);
            let mut result = challenge;
            result.mul_assign(&delta);
            result.add_assign(&values[idx]);
            result
        };
        let mut expected = Vec::new();
        for output_index in 0..2 {
            let idx = output_index * 2;
            let a0 = fold(&prev0, idx);
            let a1_full = fold(&prev0, idx + 4);
            let mut da = a1_full;
            da.sub_assign(&a0);
            let b0 = fold(&prev1, idx);
            let b1_full = fold(&prev1, idx + 4);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0 = fold(&prev0, idx + 1);
            let c1_full = fold(&prev0, idx + 5);
            let mut dc = c1_full;
            dc.sub_assign(&c0);
            let d0 = fold(&prev1, idx + 1);
            let d1_full = fold(&prev1, idx + 5);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut num0 = a0;
            num0.mul_assign(&d0);
            let mut t0 = c0;
            t0.mul_assign(&b0);
            num0.add_assign(&t0);
            let mut den0 = b0;
            den0.mul_assign(&d0);

            let mut num1 = da;
            num1.mul_assign(&dd);
            let mut t1 = dc;
            t1.mul_assign(&db);
            num1.add_assign(&t1);
            let mut den1 = db;
            den1.mul_assign(&dd);

            let mut e0 = batch0;
            e0.mul_assign(&num0);
            let mut e0_den = batch1;
            e0_den.mul_assign(&den0);
            e0.add_assign(&e0_den);

            let mut e1 = batch0;
            e1.mul_assign(&num1);
            let mut e1_den = batch1;
            e1_den.mul_assign(&den1);
            e1.add_assign(&e1_den);

            expected.push(e0);
            expected.push(e1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_continuation_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let challenge = sample_ext(300);
        let batch = sample_ext(400);
        let prev_dev = alloc_and_copy(&context, &prev);
        let cache: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let folding_challenge_dev = alloc_and_copy(&context, &[challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch]);
        let descriptors = [GpuExtensionFieldPolyContinuingLaunchDescriptor {
            previous_layer_start: prev_dev.as_ptr(),
            this_layer_start: cache.as_ptr().cast_mut(),
            this_layer_size: 8,
            next_layer_size: 4,
            first_access: true,
        }];
        let descriptors_dev = alloc_and_copy(&context, &descriptors);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        launch_pairwise_continuation::<E4>(
            descriptors_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            batch_challenges_dev.as_ptr(),
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold = |values: &[E4], idx: usize| {
            let mut delta = values[8 + idx];
            delta.sub_assign(&values[idx]);
            let mut result = challenge;
            result.mul_assign(&delta);
            result.add_assign(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let idx = output_index * 2;
            let even0 = fold(&prev, idx);
            let even1 = fold(&prev, idx + 4);
            let mut even_delta = even1;
            even_delta.sub_assign(&even0);

            let odd0 = fold(&prev, idx + 1);
            let odd1 = fold(&prev, idx + 5);
            let mut odd_delta = odd1;
            odd_delta.sub_assign(&odd0);

            let mut c0 = even0;
            c0.mul_assign(&odd0);
            c0.mul_assign(&batch);

            let mut c1 = even_delta;
            c1.mul_assign(&odd_delta);
            c1.mul_assign(&batch);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn accumulator_eq_multiply_and_reduce_match_cpu() {
        let context = make_test_context(64, 8);
        let accumulator = vec![
            sample_ext(10),
            sample_ext(20),
            sample_ext(11),
            sample_ext(21),
        ];
        let eq = vec![sample_ext(30), sample_ext(31)];
        let eq_dev = alloc_and_copy(&context, &eq);
        let mut accumulator_dev = alloc_and_copy(&context, &accumulator);
        let temp_bytes = get_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, 2).unwrap();
        let mut temp = context.alloc(temp_bytes, AllocationPlacement::Top).unwrap();
        let mut reduced = context.alloc(2, AllocationPlacement::Top).unwrap();

        super::apply_eq_and_reduce_accumulator(
            &eq_dev,
            &mut accumulator_dev,
            &mut reduced,
            &mut temp,
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(2) };
        memory_copy_async(&mut host, &reduced, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = [E4::ZERO; 2];
        for row in 0..2 {
            let mut row0 = accumulator[row];
            row0.mul_assign(&eq[row]);
            expected[0].add_assign(&row0);

            let mut row1 = accumulator[2 + row];
            row1.mul_assign(&eq[row]);
            expected[1].add_assign(&row1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_round0_kernel_accumulates_into_existing_buffer() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let output_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let batch_challenge = sample_ext(200);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge]);
        let input = alloc_and_copy(&context, &input_values);
        let output = alloc_and_copy(&context, &output_values);
        let initial = vec![
            sample_ext(300),
            sample_ext(301),
            sample_ext(302),
            sample_ext(303),
        ];
        let mut contributions = alloc_and_copy(&context, &initial);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: input.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: output.as_ptr(),
                next_layer_size: 2,
            };
        }
        memory_copy_async(
            &mut round0.device.extension_field_inputs,
            &round0.host.extension_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.extension_field_outputs,
            &round0.host.extension_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_pairwise_round0::<E4>(
            &round0,
            batch_challenges_dev.as_ptr(),
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = initial;
        for output_index in 0..2 {
            let index = output_index * 2;
            let mut c0 = batch_challenge;
            c0.mul_assign(&output_values[output_index]);
            expected[output_index].add_assign(&c0);

            let mut a = input_values[4 + index];
            a.sub_assign(&input_values[index]);
            let mut b = input_values[4 + index + 1];
            b.sub_assign(&input_values[index + 1]);
            let mut c1 = a;
            c1.mul_assign(&b);
            c1.mul_assign(&batch_challenge);
            expected[2 + output_index].add_assign(&c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn build_eq_values_matches_cpu() {
        let context = make_test_context(64, 8);
        let claim_point = vec![
            sample_ext(40),
            sample_ext(50),
            sample_ext(60),
            sample_ext(70),
        ];
        let claim_point_dev = alloc_and_copy(&context, &claim_point);
        let mut eq_values = context.alloc(4, AllocationPlacement::Top).unwrap();

        launch_build_eq_values::<E4>(
            claim_point_dev.as_ptr(),
            1,
            2,
            eq_values.as_mut_ptr(),
            4,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &eq_values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let r0 = claim_point[1];
        let r1 = claim_point[2];
        let mut one_minus_r0 = E4::ONE;
        one_minus_r0.sub_assign(&r0);
        let mut one_minus_r1 = E4::ONE;
        one_minus_r1.sub_assign(&r1);

        let mut expected_00 = one_minus_r0;
        expected_00.mul_assign(&one_minus_r1);
        let mut expected_01 = one_minus_r0;
        expected_01.mul_assign(&r1);
        let mut expected_10 = r0;
        expected_10.mul_assign(&one_minus_r1);
        let mut expected_11 = r0;
        expected_11.mul_assign(&r1);

        let expected = vec![expected_00, expected_01, expected_10, expected_11];

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round0_base_copy_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..4).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let output_values = (0..4).map(|i| BF::new(100 + i)).collect::<Vec<_>>();
        let input = alloc_and_copy(&context, &input_values);
        let output = alloc_and_copy(&context, &output_values);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let batch_challenge = sample_ext(200);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(1)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(0)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(1)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(0)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(1, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(0, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(1, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(0, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0.host.base_field_inputs.get_mut_accessor().get_mut()[0] =
                GpuBaseFieldPolySource {
                    start: input.as_ptr(),
                    next_layer_size: 2,
                };
            round0.host.base_field_outputs.get_mut_accessor().get_mut()[0] =
                GpuBaseFieldPolySource {
                    start: output.as_ptr(),
                    next_layer_size: 2,
                };
        }
        memory_copy_async(
            &mut round0.device.base_field_inputs,
            &round0.host.base_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.base_field_outputs,
            &round0.host.base_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_main_round0(
            GpuGKRMainLayerKernelKind::BaseCopy,
            &round0,
            batch_challenges_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let mut c0 = batch_challenge;
            c0.mul_assign_by_base(&output_values[output_index]);
            expected.push(c0);
            expected.push(E4::ZERO);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round0_batched_base_copy_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..4).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let output_values = (0..4).map(|i| BF::new(100 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(50), sample_ext(60)];
        let input = alloc_and_copy(&context, &input_values);
        let output = alloc_and_copy(&context, &output_values);
        let claim_point_dev = alloc_and_copy(&context, &claim_point);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let batch_challenge = sample_ext(200);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge]);
        let mut inline_builder = super::InlinePayloadBuilder::new();
        let base_inputs = inline_builder
            .try_push_copy(&[GpuBaseFieldPolySource {
                start: input.as_ptr(),
                next_layer_size: 2,
            }])
            .unwrap();
        let extension_inputs = super::GpuGKRMainLayerPayloadRange::default();
        let base_outputs = inline_builder
            .try_push_copy(&[GpuBaseFieldPolySource {
                start: output.as_ptr(),
                next_layer_size: 2,
            }])
            .unwrap();
        let extension_outputs = super::GpuGKRMainLayerPayloadRange::default();

        let mut batch = super::GpuGKRMainRound0Batch::default();
        batch.record_count = 1;
        batch.challenge_offset = 1;
        batch.challenge_count = 1;
        batch.claim_point = claim_point_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.inline_payload = inline_builder.into_bytes();
        batch.records[0] = super::GpuGKRMainRound0BatchRecord {
            kind: GpuGKRMainLayerKernelKind::BaseCopy.as_u32(),
            record_mode: super::GpuGKRMainLayerBatchRecordMode::InlineAll.as_u32(),
            metadata_inline: 1,
            _reserved: 0,
            base_inputs,
            extension_inputs,
            base_outputs,
            extension_outputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 1,
            quadratic_terms: super::GpuGKRMainLayerPayloadRange::default(),
            linear_terms: super::GpuGKRMainLayerPayloadRange::default(),
            auxiliary_challenge: E4::ZERO,
            constant_offset: E4::ZERO,
        };

        super::launch_main_round0_batched(&batch, 2, &context).unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let r = claim_point[1];
        let mut one_minus_r = E4::ONE;
        one_minus_r.sub_assign(&r);
        let eq = [one_minus_r, r];

        let mut expected = Vec::new();
        for gid in 0..2 {
            let mut c0 = batch_challenge;
            c0.mul_assign_by_base(&output_values[gid]);
            c0.mul_assign(&eq[gid]);
            expected.push(c0);
            expected.push(E4::ZERO);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_base_copy_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input = alloc_and_copy(&context, &input_values);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input.as_ptr(),
                _marker: core::marker::PhantomData,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = context
            .alloc::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                0,
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::BaseCopy,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let mut c0 = batch_challenge;
            c0.mul_assign(&fold_base(&input_values, gid));
            expected.push(c0);
            expected.push(E4::ZERO);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_ext_copy_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let input = alloc_and_copy(&context, &input_values);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);
        let cache: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_descriptors_dev = context
            .alloc::<crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<BF, E4>>(0, AllocationPlacement::Top)
            .unwrap();
        let ext_descriptors = [GpuExtensionFieldPolyContinuingLaunchDescriptor {
            previous_layer_start: input.as_ptr(),
            this_layer_start: cache.as_ptr().cast_mut(),
            this_layer_size: 4,
            next_layer_size: 2,
            first_access: true,
        }];
        let ext_descriptors_dev = alloc_and_copy(&context, &ext_descriptors);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::ExtCopy,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_ext = |values: &[E4], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign(&diff);
            result.add_assign(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let mut c0 = batch_challenge;
            c0.mul_assign(&fold_ext(&input_values, gid));
            expected.push(c0);
            expected.push(E4::ZERO);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_product_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_a_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let input_b_values = (0..8).map(|i| sample_ext(30 + i)).collect::<Vec<_>>();
        let input_a = alloc_and_copy(&context, &input_a_values);
        let input_b = alloc_and_copy(&context, &input_b_values);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);
        let cache_a: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let cache_b: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_descriptors_dev = context
            .alloc::<crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor<BF, E4>>(0, AllocationPlacement::Top)
            .unwrap();
        let ext_descriptors = [
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: input_a.as_ptr(),
                this_layer_start: cache_a.as_ptr().cast_mut(),
                this_layer_size: 4,
                next_layer_size: 2,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: input_b.as_ptr(),
                this_layer_start: cache_b.as_ptr().cast_mut(),
                this_layer_size: 4,
                next_layer_size: 2,
                first_access: true,
            },
        ];
        let ext_descriptors_dev = alloc_and_copy(&context, &ext_descriptors);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::Product,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_ext = |values: &[E4], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign(&diff);
            result.add_assign(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let a0 = fold_ext(&input_a_values, gid);
            let a1_full = fold_ext(&input_a_values, gid + 2);
            let mut da = a1_full;
            da.sub_assign(&a0);

            let b0 = fold_ext(&input_b_values, gid);
            let b1_full = fold_ext(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let mut c0 = batch_challenge;
            let mut eval0 = a0;
            eval0.mul_assign(&b0);
            c0.mul_assign(&eval0);

            let mut c1 = batch_challenge;
            let mut eval1 = da;
            eval1.mul_assign(&db);
            c1.mul_assign(&eval1);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_enforce_constraints_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_a_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_b_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let input_c_values = (0..8).map(|i| BF::new(50 + i)).collect::<Vec<_>>();
        let input_a = alloc_and_copy(&context, &input_a_values);
        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_c = alloc_and_copy(&context, &input_c_values);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let constant_offset = sample_ext(400);
        let quadratic_terms = vec![
            GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: 0,
                rhs: 1,
                challenge: sample_ext(500),
            },
            GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: 1,
                rhs: 2,
                challenge: sample_ext(600),
            },
        ];
        let linear_terms = vec![GpuGKRMainLayerConstraintLinearTerm {
            input: 2,
            challenge: sample_ext(700),
        }];
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch_challenge, E4::ZERO]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[E4::ZERO]);

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_a.as_ptr(),
                _marker: core::marker::PhantomData::<E4>,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_b.as_ptr(),
                _marker: core::marker::PhantomData::<E4>,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_c.as_ptr(),
                _marker: core::marker::PhantomData::<E4>,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = context
            .alloc::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                0,
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let constraint_upload = super::ScheduledMainLayerConstraintMetadataUpload {
            callbacks: Callbacks::new(),
            quadratic_terms: super::ScheduledUpload {
                callbacks: Callbacks::new(),
                device: alloc_and_copy(&context, &quadratic_terms),
            },
            linear_terms: super::ScheduledUpload {
                callbacks: Callbacks::new(),
                device: alloc_and_copy(&context, &linear_terms),
            },
            constant_offset: super::ScheduledUpload {
                callbacks: Callbacks::new(),
                device: alloc_and_copy(&context, &[constant_offset]),
            },
            constant_offset_value: constant_offset,
        };

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            Some(&constraint_upload),
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let a0 = fold_base(&input_a_values, gid);
            let a1_full = fold_base(&input_a_values, gid + 2);
            let mut da = a1_full;
            da.sub_assign(&a0);

            let b0 = fold_base(&input_b_values, gid);
            let b1_full = fold_base(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0_in = fold_base(&input_c_values, gid);

            let mut eval0 = constant_offset;
            let mut term0 = a0;
            term0.mul_assign(&b0);
            term0.mul_assign(&quadratic_terms[0].challenge);
            eval0.add_assign(&term0);
            let mut term1 = b0;
            term1.mul_assign(&c0_in);
            term1.mul_assign(&quadratic_terms[1].challenge);
            eval0.add_assign(&term1);
            let mut linear = c0_in;
            linear.mul_assign(&linear_terms[0].challenge);
            eval0.add_assign(&linear);

            let mut eval1 = E4::ZERO;
            let mut delta0 = da;
            delta0.mul_assign(&db);
            delta0.mul_assign(&quadratic_terms[0].challenge);
            eval1.add_assign(&delta0);

            let c1_full = fold_base(&input_c_values, gid + 2);
            let mut dc = c1_full;
            dc.sub_assign(&c0_in);
            let mut delta1 = db;
            delta1.mul_assign(&dc);
            delta1.mul_assign(&quadratic_terms[1].challenge);
            eval1.add_assign(&delta1);

            let mut c0 = batch_challenge;
            c0.mul_assign(&eval0);
            let mut c1 = batch_challenge;
            c1.mul_assign(&eval1);
            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_batched_enforce_constraints_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_a_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_b_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let input_c_values = (0..8).map(|i| BF::new(50 + i)).collect::<Vec<_>>();
        let claim_point = [sample_ext(90), sample_ext(91), sample_ext(92)];
        let input_a = alloc_and_copy(&context, &input_a_values);
        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_c = alloc_and_copy(&context, &input_c_values);
        let claim_point_dev = alloc_and_copy(&context, &claim_point);

        let folding_challenge = sample_ext(200);
        let batch_challenge = sample_ext(300);
        let constant_offset = sample_ext(400);
        let quadratic_terms = vec![
            GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: 0,
                rhs: 1,
                challenge: sample_ext(500),
            },
            GpuGKRMainLayerConstraintQuadraticTerm {
                lhs: 1,
                rhs: 2,
                challenge: sample_ext(600),
            },
        ];
        let linear_terms = vec![GpuGKRMainLayerConstraintLinearTerm {
            input: 2,
            challenge: sample_ext(700),
        }];
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenge_base_dev = alloc_and_copy(&context, &[batch_challenge]);

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_a.as_ptr(),
                _marker: core::marker::PhantomData::<E4>,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_b.as_ptr(),
                _marker: core::marker::PhantomData::<E4>,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_c.as_ptr(),
                _marker: core::marker::PhantomData::<E4>,
            },
        ];
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let mut spill_builder = super::SpillPayloadBuilder::default();
        let base_inputs = spill_builder.push_copy(&base_descriptors);
        let extension_inputs = super::GpuGKRMainLayerPayloadRange::default();
        let quadratic_terms_range = spill_builder.push_copy(&quadratic_terms);
        let linear_terms_range = spill_builder.push_copy(&linear_terms);
        let spill_payload_dev = alloc_and_copy(&context, spill_builder.bytes.as_slice());

        let mut batch = super::GpuGKRMainRound1Batch::default();
        batch.record_count = 1;
        batch.challenge_offset = 2;
        batch.challenge_count = 1;
        batch.claim_point = claim_point_dev.as_ptr();
        batch.batch_challenge_base = batch_challenge_base_dev.as_ptr();
        batch.folding_challenge = folding_challenge_dev.as_ptr();
        batch.contributions = contributions.as_mut_ptr();
        batch.spill_payload = spill_payload_dev.as_ptr();
        batch.explicit_form = false;
        batch.records[0] = super::GpuGKRMainRound1BatchRecord {
            kind: GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic.as_u32(),
            record_mode: super::GpuGKRMainLayerBatchRecordMode::PointerDescriptors.as_u32(),
            metadata_inline: 0,
            _reserved: 0,
            base_inputs,
            extension_inputs,
            batch_challenge_offset: 1,
            batch_challenge_count: 1,
            quadratic_terms: quadratic_terms_range,
            linear_terms: linear_terms_range,
            auxiliary_challenge: E4::ZERO,
            constant_offset,
        };

        super::launch_main_round1_batched(&batch, 2, &context).unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let r = claim_point[2];
        let mut one_minus_r = E4::ONE;
        one_minus_r.sub_assign(&r);
        let eq = [one_minus_r, r];

        let mut expected = Vec::new();
        for gid in 0..2 {
            let a0 = fold_base(&input_a_values, gid);
            let a1_full = fold_base(&input_a_values, gid + 2);
            let mut da = a1_full;
            da.sub_assign(&a0);

            let b0 = fold_base(&input_b_values, gid);
            let b1_full = fold_base(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0_in = fold_base(&input_c_values, gid);

            let mut eval0 = constant_offset;
            let mut term0 = a0;
            term0.mul_assign(&b0);
            term0.mul_assign(&quadratic_terms[0].challenge);
            eval0.add_assign(&term0);
            let mut term1 = b0;
            term1.mul_assign(&c0_in);
            term1.mul_assign(&quadratic_terms[1].challenge);
            eval0.add_assign(&term1);
            let mut linear = c0_in;
            linear.mul_assign(&linear_terms[0].challenge);
            eval0.add_assign(&linear);

            let mut eval1 = E4::ZERO;
            let mut delta0 = da;
            delta0.mul_assign(&db);
            delta0.mul_assign(&quadratic_terms[0].challenge);
            eval1.add_assign(&delta0);

            let c1_full = fold_base(&input_c_values, gid + 2);
            let mut dc = c1_full;
            dc.sub_assign(&c0_in);
            let mut delta1 = db;
            delta1.mul_assign(&dc);
            delta1.mul_assign(&quadratic_terms[1].challenge);
            eval1.add_assign(&delta1);

            let mut c0 = batch_challenge;
            c0.mul_assign(&eval0);
            c0.mul_assign(&eq[gid]);
            let mut c1 = batch_challenge;
            c1.mul_assign(&eval1);
            c1.mul_assign(&eq[gid]);
            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round0_lookup_base_pair_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_b_values = (0..4).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_d_values = (0..4).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let output_num_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let output_den_values = (0..4).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();
        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_d = alloc_and_copy(&context, &input_d_values);
        let output_num = alloc_and_copy(&context, &output_num_values);
        let output_den = alloc_and_copy(&context, &output_den_values);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let batch0 = sample_ext(300);
        let batch1 = sample_ext(400);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let lookup_additive_challenge = sample_ext(500);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[lookup_additive_challenge]);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            callbacks: Callbacks::new(),
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(2)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(0)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(2)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(2, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(0, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(2, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0.host.base_field_inputs.get_mut_accessor().get_mut()[0] =
                GpuBaseFieldPolySource {
                    start: input_b.as_ptr(),
                    next_layer_size: 2,
                };
            round0.host.base_field_inputs.get_mut_accessor().get_mut()[1] =
                GpuBaseFieldPolySource {
                    start: input_d.as_ptr(),
                    next_layer_size: 2,
                };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: output_num.as_ptr(),
                next_layer_size: 2,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[1] = GpuExtensionFieldPolyInitialSource {
                start: output_den.as_ptr(),
                next_layer_size: 2,
            };
        }
        memory_copy_async(
            &mut round0.device.base_field_inputs,
            &round0.host.base_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.extension_field_outputs,
            &round0.host.extension_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_main_round0(
            GpuGKRMainLayerKernelKind::LookupBasePair,
            &round0,
            batch_challenges_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let mut c0 = batch0;
            c0.mul_assign(&output_num_values[output_index]);
            let mut output_den_term = batch1;
            output_den_term.mul_assign(&output_den_values[output_index]);
            c0.add_assign(&output_den_term);

            let mut b1 = input_b_values[2 + output_index];
            b1.sub_assign(&input_b_values[output_index]);
            let mut d1 = input_d_values[2 + output_index];
            d1.sub_assign(&input_d_values[output_index]);
            let mut den = b1;
            den.mul_assign(&d1);

            let mut c1 = batch1;
            c1.mul_assign_by_base(&den);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_lookup_with_cached_dens_and_setup_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_a_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_c_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let input_b_values = (0..8).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let input_d_values = (0..8).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();

        let input_a = alloc_and_copy(&context, &input_a_values);
        let input_c = alloc_and_copy(&context, &input_c_values);
        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_d = alloc_and_copy(&context, &input_d_values);

        let folding_challenge = sample_ext(300);
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let lookup_additive_challenge = sample_ext(600);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[lookup_additive_challenge]);
        let cache_b: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
        let cache_d: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_a.as_ptr(),
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_c.as_ptr(),
                _marker: core::marker::PhantomData,
            },
        ];
        let ext_descriptors = [
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: input_b.as_ptr(),
                this_layer_start: cache_b.as_ptr().cast_mut(),
                this_layer_size: 4,
                next_layer_size: 2,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: input_d.as_ptr(),
                this_layer_start: cache_d.as_ptr().cast_mut(),
                this_layer_size: 4,
                next_layer_size: 2,
                first_access: true,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = alloc_and_copy(&context, &ext_descriptors);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };
        let fold_ext = |values: &[E4], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign(&diff);
            result.add_assign(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let a0 = fold_base(&input_a_values, gid);
            let a1_full = fold_base(&input_a_values, gid + 2);
            let mut da = a1_full;
            da.sub_assign(&a0);

            let c0_in = fold_base(&input_c_values, gid);
            let c1_full = fold_base(&input_c_values, gid + 2);
            let mut dc = c1_full;
            dc.sub_assign(&c0_in);

            let b0 = fold_ext(&input_b_values, gid);
            let b1_full = fold_ext(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let d0 = fold_ext(&input_d_values, gid);
            let d1_full = fold_ext(&input_d_values, gid + 2);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut shifted_b0 = b0;
            shifted_b0.add_assign(&lookup_additive_challenge);
            let mut shifted_d0 = d0;
            shifted_d0.add_assign(&lookup_additive_challenge);
            let mut num0 = a0;
            num0.mul_assign(&shifted_d0);
            let mut t0 = c0_in;
            t0.mul_assign(&shifted_b0);
            num0.sub_assign(&t0);
            let mut den0 = shifted_b0;
            den0.mul_assign(&shifted_d0);

            let mut num1 = da;
            num1.mul_assign(&dd);
            let mut t1 = dc;
            t1.mul_assign(&db);
            num1.sub_assign(&t1);
            let mut den1 = db;
            den1.mul_assign(&dd);

            let mut c0 = batch0;
            c0.mul_assign(&num0);
            let mut c0_den = batch1;
            c0_den.mul_assign(&den0);
            c0.add_assign(&c0_den);

            let mut c1 = batch0;
            c1.mul_assign(&num1);
            let mut c1_den = batch1;
            c1_den.mul_assign(&den1);
            c1.add_assign(&c1_den);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_lookup_base_pair_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_b_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_d_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();

        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_d = alloc_and_copy(&context, &input_d_values);

        let folding_challenge = sample_ext(300);
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let lookup_additive_challenge = sample_ext(600);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[lookup_additive_challenge]);

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_b.as_ptr(),
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_d.as_ptr(),
                _marker: core::marker::PhantomData,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = context
            .alloc::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                0,
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::LookupBasePair,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let b0 = fold_base(&input_b_values, gid);
            let b1_full = fold_base(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let d0 = fold_base(&input_d_values, gid);
            let d1_full = fold_base(&input_d_values, gid + 2);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut shifted_b0 = b0;
            shifted_b0.add_assign(&lookup_additive_challenge);
            let mut shifted_d0 = d0;
            shifted_d0.add_assign(&lookup_additive_challenge);

            let mut num0 = shifted_b0;
            num0.add_assign(&shifted_d0);
            let mut den0 = shifted_b0;
            den0.mul_assign(&shifted_d0);

            let num1 = E4::ZERO;
            let mut den1 = db;
            den1.mul_assign(&dd);

            let mut c0 = batch0;
            c0.mul_assign(&num0);
            let mut c0_den = batch1;
            c0_den.mul_assign(&den0);
            c0.add_assign(&c0_den);

            let mut c1 = batch0;
            c1.mul_assign(&num1);
            let mut c1_den = batch1;
            c1_den.mul_assign(&den1);
            c1.add_assign(&c1_den);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn main_round1_lookup_base_minus_multiplicity_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_b_values = (0..8).map(|i| BF::new(10 + i)).collect::<Vec<_>>();
        let input_c_values = (0..8).map(|i| BF::new(30 + i)).collect::<Vec<_>>();
        let input_d_values = (0..8).map(|i| BF::new(50 + i)).collect::<Vec<_>>();

        let input_b = alloc_and_copy(&context, &input_b_values);
        let input_c = alloc_and_copy(&context, &input_c_values);
        let input_d = alloc_and_copy(&context, &input_d_values);

        let folding_challenge = sample_ext(300);
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let lookup_additive_challenge = sample_ext(600);
        let folding_challenge_dev = alloc_and_copy(&context, &[folding_challenge]);
        let batch_challenges_dev = alloc_and_copy(&context, &[batch0, batch1]);
        let auxiliary_challenge_dev = alloc_and_copy(&context, &[lookup_additive_challenge]);

        let base_descriptors = [
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_b.as_ptr(),
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_c.as_ptr(),
                _marker: core::marker::PhantomData,
            },
            crate::prover::gkr::GpuBaseFieldPolySourceAfterOneFoldingLaunchDescriptor {
                base_layer_half_size: 4,
                next_layer_size: 2,
                base_input_start: input_d.as_ptr(),
                _marker: core::marker::PhantomData,
            },
        ];
        let base_descriptors_dev = alloc_and_copy(&context, &base_descriptors);
        let ext_descriptors_dev = context
            .alloc::<GpuExtensionFieldPolyContinuingLaunchDescriptor<E4>>(
                0,
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        let scheduled = crate::prover::gkr::GpuSumcheckRound1ScheduledLaunchDescriptors {
            device: crate::prover::gkr::GpuSumcheckRound1DeviceLaunchDescriptors {
                base_field_inputs: base_descriptors_dev,
                extension_field_inputs: ext_descriptors_dev,
            },
        };

        super::launch_main_round1(
            GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
            &scheduled,
            batch_challenges_dev.as_ptr(),
            folding_challenge_dev.as_ptr(),
            auxiliary_challenge_dev.as_ptr(),
            None,
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy_async(&mut host, &contributions, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold_base = |values: &[BF], idx: usize| {
            let mut diff = values[4 + idx];
            diff.sub_assign(&values[idx]);
            let mut result = folding_challenge;
            result.mul_assign_by_base(&diff);
            result.add_assign_base(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for gid in 0..2 {
            let b0 = fold_base(&input_b_values, gid);
            let b1_full = fold_base(&input_b_values, gid + 2);
            let mut db = b1_full;
            db.sub_assign(&b0);

            let c0_in = fold_base(&input_c_values, gid);
            let c1_full = fold_base(&input_c_values, gid + 2);
            let mut dc = c1_full;
            dc.sub_assign(&c0_in);

            let d0 = fold_base(&input_d_values, gid);
            let d1_full = fold_base(&input_d_values, gid + 2);
            let mut dd = d1_full;
            dd.sub_assign(&d0);

            let mut shifted_b0 = b0;
            shifted_b0.add_assign(&lookup_additive_challenge);
            let mut shifted_d0 = d0;
            shifted_d0.add_assign(&lookup_additive_challenge);

            let mut num0 = shifted_d0;
            let mut t0 = c0_in;
            t0.mul_assign(&shifted_b0);
            num0.sub_assign(&t0);
            let mut den0 = shifted_b0;
            den0.mul_assign(&shifted_d0);

            let mut num1 = dc;
            num1.mul_assign(&db);
            num1.negate();
            let mut den1 = db;
            den1.mul_assign(&dd);

            let mut c0 = batch0;
            c0.mul_assign(&num0);
            let mut c0_den = batch1;
            c0_den.mul_assign(&den0);
            c0.add_assign(&c0_den);

            let mut c1 = batch0;
            c1.mul_assign(&num1);
            let mut c1_den = batch1;
            c1_den.mul_assign(&den1);
            c1.add_assign(&c1_den);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, interleaved_pairs_to_strided(&expected));
    }

    #[test]
    fn main_layer_constraint_blueprint_metadata_matches_cpu() {
        let storage = crate::prover::gkr::GpuGKRStorage::<BF, E4> {
            layers: vec![Default::default()],
        };
        let constraint_input = NoFieldMaxQuadraticConstraintsGKRRelation {
            quadratic_terms: vec![
                (
                    (
                        GKRAddress::BaseLayerMemory(0),
                        GKRAddress::BaseLayerWitness(1),
                    ),
                    vec![(2u32, 0usize), (3u32, 2usize)].into_boxed_slice(),
                ),
                (
                    (
                        GKRAddress::BaseLayerWitness(1),
                        GKRAddress::BaseLayerWitness(1),
                    ),
                    vec![(5u32, 1usize)].into_boxed_slice(),
                ),
            ]
            .into_boxed_slice(),
            linear_terms: vec![(
                GKRAddress::BaseLayerMemory(1),
                vec![(7u32, 0usize)].into_boxed_slice(),
            )]
            .into_boxed_slice(),
            constants: vec![(11u32, 0usize), (13u32, 1usize)].into_boxed_slice(),
        };
        let layer = GKRLayerDescription {
            layer: 0,
            gates_with_external_connections: Vec::new(),
            cached_relations: BTreeMap::new(),
            gates: vec![GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::EnforceConstraintsMaxQuadratic {
                    input: constraint_input.clone(),
                },
            }],
            additional_base_layer_openings: Vec::new(),
        };
        let constraint_batch_challenge = sample_ext(20);
        let blueprints = build_main_layer_kernel_blueprints(
            &layer,
            0,
            &storage,
            sample_ext(10),
            sample_ext(30),
            constraint_batch_challenge,
            2,
            2,
        );

        assert_eq!(blueprints.len(), 1);
        let blueprint = &blueprints[0];
        let relation = BatchConstraintEvalGKRRelation::<BF, E4>::new(
            &constraint_input,
            2,
            2,
            constraint_batch_challenge,
        );

        assert_eq!(
            blueprint.kind,
            GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic
        );
        assert_eq!(blueprint.batch_challenges, vec![E4::ONE]);
        assert_eq!(
            blueprint.inputs,
            <BatchConstraintEvalGKRRelation<BF, E4> as BatchedGKRKernel<BF, E4>>::get_inputs(
                &relation,
            )
        );

        let metadata = blueprint
            .constraint_metadata_source
            .as_ref()
            .expect("constraint metadata must be present");
        let metadata = match metadata {
            super::GpuGKRMainLayerConstraintMetadataSource::Immediate(metadata) => metadata,
            super::GpuGKRMainLayerConstraintMetadataSource::Deferred(..) => {
                panic!("dynamic blueprint must materialize immediate constraint metadata")
            }
        };
        assert_eq!(metadata.constant_offset, relation.kernel.constant_offset);
        assert_eq!(
            metadata.quadratic_terms.len(),
            relation.kernel.quadratic_parts.len()
        );
        assert_eq!(
            metadata.linear_terms.len(),
            relation.kernel.linear_parts.len()
        );
        assert_eq!(
            metadata.quadratic_terms,
            relation
                .kernel
                .quadratic_parts
                .iter()
                .map(
                    |((lhs, rhs), challenge)| GpuGKRMainLayerConstraintQuadraticTerm {
                        lhs: *lhs as u32,
                        rhs: *rhs as u32,
                        challenge: *challenge,
                    }
                )
                .collect::<Vec<_>>()
        );
        assert_eq!(
            metadata.linear_terms,
            relation
                .kernel
                .linear_parts
                .iter()
                .map(|(input, challenge)| GpuGKRMainLayerConstraintLinearTerm {
                    input: *input as u32,
                    challenge: *challenge,
                })
                .collect::<Vec<_>>()
        );
    }
}
