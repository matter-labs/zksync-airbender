use std::collections::BTreeMap;

use crate::upstream::{DimensionReducingInputOutput, GKRAddress, OutputType};

use super::super::kernels::{
    dim_reducing_slot_index, GpuGKRDimensionReducingLayerSlots, GpuGKRDimensionReducingSlotPlan,
    GKR_DIM_REDUCING_INPUTS_PER_SLOT, GKR_DIM_REDUCING_OUTPUTS_PER_SLOT,
};

/// Lowers a layer's `OutputType`-keyed IO map onto the fixed slot table; absent
/// output types leave their slot disabled.
///
/// Exponents are packed densely, two per enabled slot. `BTreeMap` iterates in
/// `OutputType` `Ord` order and slot index is monotonic in that order, so this
/// reproduces the numbering the generated verifier derives by walking its own
/// present output groups.
pub(in crate::backward) fn build_dimension_reducing_slots_static(
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
) -> GpuGKRDimensionReducingLayerSlots {
    let mut layer_slots = GpuGKRDimensionReducingLayerSlots::default();
    let mut next_batch_exp = 0u16;

    for (output_type, reduced) in layer {
        let inputs: [GKRAddress; GKR_DIM_REDUCING_INPUTS_PER_SLOT] =
            reduced.inputs.clone().try_into().unwrap_or_else(|_| {
                panic!("dimension-reducing {output_type:?} expects two inputs")
            });
        let outputs: [GKRAddress; GKR_DIM_REDUCING_OUTPUTS_PER_SLOT] =
            reduced.output.clone().try_into().unwrap_or_else(|_| {
                panic!("dimension-reducing {output_type:?} expects two outputs")
            });

        let batch_exp = [next_batch_exp, next_batch_exp + 1];
        next_batch_exp += GKR_DIM_REDUCING_OUTPUTS_PER_SLOT as u16;

        let slot_idx = dim_reducing_slot_index(*output_type);
        let previous = layer_slots.slots[slot_idx].replace(GpuGKRDimensionReducingSlotPlan {
            inputs,
            outputs,
            batch_exp,
        });
        assert!(
            previous.is_none(),
            "duplicate dimension-reducing slot for {output_type:?}"
        );
    }

    layer_slots
}
