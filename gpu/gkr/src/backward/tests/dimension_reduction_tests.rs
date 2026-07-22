use super::super::*;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::E4;

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::CudaSlice;

use std::collections::BTreeMap;

use super::{build_dimension_reducing_kernel_blueprints, sample_ext, successive_powers};
use crate::upstream::{DimensionReducingInputOutput, Field, OutputType};

#[test]
fn main_layer_kind_batch_challenge_count_matches_all_supported_kinds() {
    let one_challenge_kinds = [
        GpuGKRMainLayerKernelKind::BaseCopy,
        GpuGKRMainLayerKernelKind::ExtCopy,
        GpuGKRMainLayerKernelKind::Product,
        GpuGKRMainLayerKernelKind::MaskIdentity,
        GpuGKRMainLayerKernelKind::EnforceConstraintsMaxQuadratic,
        GpuGKRMainLayerKernelKind::MaxQuadraticBaseOutput,
        GpuGKRMainLayerKernelKind::LinearBaseOutput,
        GpuGKRMainLayerKernelKind::InitsAndTeardownsInitialPair,
        GpuGKRMainLayerKernelKind::InitialGrandProductWithoutCaches,
        GpuGKRMainLayerKernelKind::MaterializeGrandProductTermExpression,
    ];
    let two_challenge_kinds = [
        GpuGKRMainLayerKernelKind::LookupPair,
        GpuGKRMainLayerKernelKind::LookupBasePair,
        GpuGKRMainLayerKernelKind::LookupBaseMinusMultiplicityByBase,
        GpuGKRMainLayerKernelKind::LookupExtMinusMultiplicityByExt,
        GpuGKRMainLayerKernelKind::LookupUnbalanced,
        GpuGKRMainLayerKernelKind::LookupWithCachedDensAndSetup,
        GpuGKRMainLayerKernelKind::LookupPairFromBaseInputs,
        GpuGKRMainLayerKernelKind::LookupWithDensAndSetupExpressions,
        GpuGKRMainLayerKernelKind::LookupPairFromVectorInputs,
        GpuGKRMainLayerKernelKind::LookupFromVectorInputWithSetup,
        GpuGKRMainLayerKernelKind::LookupUnbalancedPairWithVectorInputs,
        GpuGKRMainLayerKernelKind::LookupExtPair,
        GpuGKRMainLayerKernelKind::LookupUnbalancedExtension,
    ];

    for kind in one_challenge_kinds {
        assert_eq!(super::main_layer_kind_batch_challenge_count(kind), 1);
    }
    for kind in two_challenge_kinds {
        assert_eq!(super::main_layer_kind_batch_challenge_count(kind), 2);
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
