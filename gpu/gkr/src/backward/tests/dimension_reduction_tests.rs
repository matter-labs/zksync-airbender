use std::collections::BTreeMap;

use crate::backward::kernels::GpuGKRDimensionReducingKernelKind;
use crate::backward::main_layer::blueprints::build_dimension_reducing_kernel_blueprints_static;
use crate::upstream::{DimensionReducingInputOutput, OutputType};

#[test]
fn dimension_reducing_kernel_blueprints_match_protocol_order() {
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

    let blueprints = build_dimension_reducing_kernel_blueprints_static(&layer);

    assert_eq!(blueprints.len(), 5);
    assert_eq!(
        blueprints[0].inputs.inputs_in_extension,
        vec![layer[&OutputType::PermutationProduct].inputs[0]]
    );
    assert_eq!(
        blueprints[0].inputs.outputs_in_extension,
        vec![layer[&OutputType::PermutationProduct].output[0]]
    );
    assert_eq!(
        blueprints[0].kind,
        GpuGKRDimensionReducingKernelKind::Pairwise
    );
    assert_eq!(blueprints[0].batch_challenge_offset, 0);

    assert_eq!(
        blueprints[1].inputs.inputs_in_extension,
        vec![layer[&OutputType::PermutationProduct].inputs[1]]
    );
    assert_eq!(
        blueprints[1].inputs.outputs_in_extension,
        vec![layer[&OutputType::PermutationProduct].output[1]]
    );
    assert_eq!(
        blueprints[1].kind,
        GpuGKRDimensionReducingKernelKind::Pairwise
    );
    assert_eq!(blueprints[1].batch_challenge_offset, 1);

    assert_eq!(
        blueprints[2].inputs.inputs_in_extension,
        layer[&OutputType::Lookup16Bits].inputs
    );
    assert_eq!(
        blueprints[2].inputs.outputs_in_extension,
        layer[&OutputType::Lookup16Bits].output
    );
    assert_eq!(
        blueprints[2].kind,
        GpuGKRDimensionReducingKernelKind::Lookup
    );
    assert_eq!(blueprints[2].batch_challenge_offset, 2);

    assert_eq!(
        blueprints[3].inputs.inputs_in_extension,
        layer[&OutputType::LookupTimestamps].inputs
    );
    assert_eq!(
        blueprints[3].inputs.outputs_in_extension,
        layer[&OutputType::LookupTimestamps].output
    );
    assert_eq!(
        blueprints[3].kind,
        GpuGKRDimensionReducingKernelKind::Lookup
    );
    assert_eq!(blueprints[3].batch_challenge_offset, 4);

    assert_eq!(
        blueprints[4].inputs.inputs_in_extension,
        layer[&OutputType::GenericLookup].inputs
    );
    assert_eq!(
        blueprints[4].inputs.outputs_in_extension,
        layer[&OutputType::GenericLookup].output
    );
    assert_eq!(
        blueprints[4].kind,
        GpuGKRDimensionReducingKernelKind::Lookup
    );
    assert_eq!(blueprints[4].batch_challenge_offset, 6);
}
