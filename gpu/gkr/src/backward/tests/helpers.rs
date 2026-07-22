use super::super::*;
use crate::GpuSumcheckRound1ScheduledLaunchDescriptors;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::field::BF;
use gpu_prover_context::ProverContext;

use era_cudart::slice::CudaSlice;

use std::collections::BTreeMap;

use super::lookup_builders::build_materialized_vector_lookup_input_inputs_and_metadata;
use crate::upstream::{
    DimensionReducingInputOutput, Field, FieldExtension, GKRAddress, GKRExternalChallenges,
    GKRLayerDescription, NoFieldGKRRelation, OutputType,
};

fn fill_round0_eq_pair_values<E: Field>(dst: &mut [E], claim_point: &[E]) {
    assert_eq!(
        dst.len(),
        round0_eq_pair_values_len(claim_point.len()),
        "round-0 eq pair buffer must match the claim-point suffix length"
    );
    for (pair, challenge) in dst
        .chunks_exact_mut(2)
        .zip(claim_point.iter().skip(1).copied())
    {
        let mut one_minus = E::ONE;
        one_minus.sub_assign(&challenge);
        pair[0] = one_minus;
        pair[1] = challenge;
    }
}

pub(in crate::backward::tests) fn make_round0_eq_pair_values<E: Field>(
    claim_point: &[E],
) -> Vec<E> {
    let mut result = vec![E::ZERO; round0_eq_pair_values_len(claim_point.len())];
    fill_round0_eq_pair_values(&mut result, claim_point);
    result
}

pub(in crate::backward::tests) fn build_dimension_reducing_kernel_blueprints<E: Field>(
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
        // Both passes iterate `BTreeMap<OutputType>` by the derived `Ord`, so
        // `InitsAndTeardownsProduct` (the last discriminant in cs's OutputType enum)
        // always squeezes its 2 pairwise records / 2 challenges after the
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
