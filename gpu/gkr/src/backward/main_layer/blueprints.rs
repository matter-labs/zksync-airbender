use std::collections::BTreeMap;

use crate::upstream::{DimensionReducingInputOutput, GKRAddress, GKRInputs, OutputType};

use super::super::kernels::{GpuGKRDimensionReducingKernelKind, GpuGKRDimensionReducingKernelPlan};

pub(in crate::backward) fn build_dimension_reducing_kernel_blueprints_static(
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
) -> Vec<GpuGKRDimensionReducingKernelPlan> {
    let mut next_batch_challenge_offset = 0;
    let mut blueprints = Vec::new();
    for (output_type, reduced) in layer {
        match output_type {
            OutputType::PermutationProduct | OutputType::InitsAndTeardownsProduct => {
                for (input, output) in reduced.inputs.iter().zip(&reduced.output) {
                    blueprints.push(GpuGKRDimensionReducingKernelPlan {
                        kind: GpuGKRDimensionReducingKernelKind::Pairwise,
                        inputs: GKRInputs {
                            inputs_in_base: Vec::new(),
                            inputs_in_extension: vec![*input],
                            outputs_in_base: Vec::new(),
                            outputs_in_extension: vec![*output],
                        },
                        batch_challenge_offset: next_batch_challenge_offset,
                    });
                    next_batch_challenge_offset += 1;
                }
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let inputs: [GKRAddress; 2] = reduced
                    .inputs
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup expects two inputs");
                let outputs: [GKRAddress; 2] = reduced
                    .output
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup expects two outputs");
                blueprints.push(GpuGKRDimensionReducingKernelPlan {
                    kind: GpuGKRDimensionReducingKernelKind::Lookup,
                    inputs: GKRInputs {
                        inputs_in_base: Vec::new(),
                        inputs_in_extension: inputs.to_vec(),
                        outputs_in_base: Vec::new(),
                        outputs_in_extension: outputs.to_vec(),
                    },
                    batch_challenge_offset: next_batch_challenge_offset,
                });
                next_batch_challenge_offset += 2;
            }
        }
    }
    blueprints
}
