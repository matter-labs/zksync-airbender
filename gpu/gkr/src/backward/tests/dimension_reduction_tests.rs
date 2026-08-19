use std::collections::BTreeMap;

use crate::backward::kernels::dim_reducing_slot_index;
use crate::backward::main_layer::blueprints::build_dimension_reducing_slots_static;
use crate::upstream::{DimensionReducingInputOutput, OutputType};

#[test]
fn dimension_reducing_slots_match_protocol_order() {
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

    let layer_slots = build_dimension_reducing_slots_static(&layer);

    // The fixture omits InitsAndTeardownsProduct, so exponents must pack densely
    // across the four present types rather than leaving a hole at its slot.
    assert_eq!(layer_slots.enabled_mask(), 0b0_1111);
    for (output_type, expected_exp) in [
        (OutputType::PermutationProduct, [0u16, 1]),
        (OutputType::Lookup16Bits, [2, 3]),
        (OutputType::LookupTimestamps, [4, 5]),
        (OutputType::GenericLookup, [6, 7]),
    ] {
        let slot = layer_slots.slots[dim_reducing_slot_index(output_type)]
            .as_ref()
            .unwrap_or_else(|| panic!("{output_type:?} slot must be enabled"));
        assert_eq!(slot.inputs.as_slice(), layer[&output_type].inputs);
        assert_eq!(slot.outputs.as_slice(), layer[&output_type].output);
        assert_eq!(slot.batch_exp, expected_exp, "{output_type:?}");
    }
}
