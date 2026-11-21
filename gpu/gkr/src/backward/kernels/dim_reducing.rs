use crate::{
    backward::kernels::shared::GKR_BACKWARD_MAX_TRACE_LEN_LOG2,
    upstream::{GKRAddress, OutputType},
};

// Dim-reducing layers carry one slot per OutputType, in OutputType discriminant
// order, each with 2 inputs / 2 outputs / 2 batch challenges. MUST stay in
// lockstep with the native mirror in native/gkr/support/descriptors.cuh.
pub(crate) const GKR_DIM_REDUCING_SLOTS: usize = 5;
pub(crate) const GKR_DIM_REDUCING_INPUTS_PER_SLOT: usize = 2;
pub(crate) const GKR_DIM_REDUCING_OUTPUTS_PER_SLOT: usize = 2;
pub(crate) const GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN: usize =
    GKR_DIM_REDUCING_SLOTS * GKR_DIM_REDUCING_OUTPUTS_PER_SLOT;

/// Wire slot index for an output type. The device derives each slot's kind from
/// this index at compile time, and exponents are packed densely in this order,
/// which must stay the `OutputType` `Ord` order the generated verifier walks.
pub(crate) const fn dim_reducing_slot_index(output_type: OutputType) -> usize {
    match output_type {
        OutputType::PermutationProduct => 0,
        OutputType::Lookup16Bits => 1,
        OutputType::LookupTimestamps => 2,
        OutputType::GenericLookup => 3,
        OutputType::InitsAndTeardownsProduct => 4,
    }
}

/// Dim-reducing next-layer state stores `(folding_steps - 1)` per-round
/// challenges plus 3 transcript-squeezed values:
/// `[folding_challenges, r_before_last, r_last, next_batching]`.
pub(crate) const MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN: usize =
    GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 2;

/// Host-side plan for one enabled slot: its 2 input and 2 output addresses, and
/// the batch-challenge table index carried by each output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct GpuGKRDimensionReducingSlotPlan {
    pub(crate) inputs: [GKRAddress; GKR_DIM_REDUCING_INPUTS_PER_SLOT],
    pub(crate) outputs: [GKRAddress; GKR_DIM_REDUCING_OUTPUTS_PER_SLOT],
    pub(crate) batch_exp: [u16; GKR_DIM_REDUCING_OUTPUTS_PER_SLOT],
}

/// The fixed slot table for one dim-reducing layer. `None` means the circuit
/// does not use that output type.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct GpuGKRDimensionReducingLayerSlots {
    pub(crate) slots: [Option<GpuGKRDimensionReducingSlotPlan>; GKR_DIM_REDUCING_SLOTS],
}

impl GpuGKRDimensionReducingLayerSlots {
    pub(crate) fn enabled_mask(&self) -> u32 {
        self.slots
            .iter()
            .enumerate()
            .filter(|(_, slot)| slot.is_some())
            .fold(0u32, |mask, (idx, _)| mask | (1u32 << idx))
    }

    /// Enabled slots in wire order, paired with their slot index.
    pub(crate) fn iter_enabled(
        &self,
    ) -> impl Iterator<Item = (usize, &GpuGKRDimensionReducingSlotPlan)> {
        self.slots
            .iter()
            .enumerate()
            .filter_map(|(idx, slot)| slot.as_ref().map(|slot| (idx, slot)))
    }

    /// Every input address read by this layer, in wire order.
    pub(crate) fn input_addresses(&self) -> impl Iterator<Item = GKRAddress> + '_ {
        self.iter_enabled()
            .flat_map(|(_, slot)| slot.inputs.iter().copied())
    }
}
