use super::super::kernels::{make_eq_sizes, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS};

const E4_BYTES: usize = 16;
const EQ_GROUP_BITS: usize = 8;
const MAX_CANONICAL_SOURCES: usize = 10;
const MAX_ENTRY_ROUND: usize = 15;

const _: () = assert!(GKR_EQ_GROUP_TABLE_LEN == 1 << EQ_GROUP_BITS);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrTailCapacityRequest {
    pub(crate) folding_steps: usize,
    pub(crate) entry_round: usize,
    pub(crate) canonical_sources: usize,
    pub(crate) static_smem_bytes: usize,
    pub(crate) device_cap_bytes: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrTailCapacityDecision {
    pub(crate) entry_round: usize,
    pub(crate) remaining_rounds: usize,
    pub(crate) entry_cells_per_source: usize,
    pub(crate) state_bytes: usize,
    pub(crate) eq_suffix_offset: usize,
    pub(crate) eq_suffix_bits: usize,
    pub(crate) eq_group_count: usize,
    pub(crate) factored_eq_bytes: usize,
    pub(crate) dynamic_smem_bytes: usize,
    pub(crate) static_smem_bytes: usize,
    pub(crate) total_smem_bytes: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DrTailCapacityRejection {
    FoldingStepsTooSmall,
    EntryBeforeFirstWindow,
    EntryNotWidthThreeBoundary,
    EntryAtOrAfterFinalRound,
    CanonicalSourceCountOutOfRange,
    EqSuffixExceedsStrictThreeSlotGeometry,
    InconsistentEqSizes,
    ArithmeticOverflow,
    DeviceCapacityExceeded {
        required_bytes: usize,
        cap_bytes: usize,
    },
}

impl core::fmt::Display for DrTailCapacityRejection {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for DrTailCapacityRejection {}

pub(crate) fn portable_entry(folding_steps: usize) -> Result<usize, DrTailCapacityRejection> {
    let completed = folding_steps
        .checked_sub(1)
        .ok_or(DrTailCapacityRejection::FoldingStepsTooSmall)?
        / 3;
    let entry = completed
        .checked_mul(3)
        .ok_or(DrTailCapacityRejection::ArithmeticOverflow)?
        .min(MAX_ENTRY_ROUND);
    if entry < 3 || entry >= folding_steps {
        return Err(DrTailCapacityRejection::FoldingStepsTooSmall);
    }
    Ok(entry)
}

impl DrTailCapacityRequest {
    pub(crate) fn decide(self) -> Result<DrTailCapacityDecision, DrTailCapacityRejection> {
        if self.entry_round < 3 {
            return Err(DrTailCapacityRejection::EntryBeforeFirstWindow);
        }
        if self.entry_round % 3 != 0 {
            return Err(DrTailCapacityRejection::EntryNotWidthThreeBoundary);
        }
        if self.entry_round >= self.folding_steps {
            return Err(DrTailCapacityRejection::EntryAtOrAfterFinalRound);
        }
        if !(1..=MAX_CANONICAL_SOURCES).contains(&self.canonical_sources) {
            return Err(DrTailCapacityRejection::CanonicalSourceCountOutOfRange);
        }

        let remaining_rounds = self
            .folding_steps
            .checked_sub(self.entry_round)
            .ok_or(DrTailCapacityRejection::ArithmeticOverflow)?;
        let eq_suffix_offset = self
            .entry_round
            .checked_add(1)
            .ok_or(DrTailCapacityRejection::ArithmeticOverflow)?;
        let eq_suffix_bits = self
            .folding_steps
            .checked_sub(eq_suffix_offset)
            .ok_or(DrTailCapacityRejection::ArithmeticOverflow)?;
        let max_eq_bits = (GKR_EQ_HIGH_SLOTS + 1)
            .checked_mul(EQ_GROUP_BITS)
            .ok_or(DrTailCapacityRejection::ArithmeticOverflow)?;
        if eq_suffix_bits > max_eq_bits {
            return Err(DrTailCapacityRejection::EqSuffixExceedsStrictThreeSlotGeometry);
        }

        let eq_sizes = make_eq_sizes(eq_suffix_bits);
        let represented_bits = eq_sizes
            .high
            .iter()
            .try_fold(eq_sizes.low as usize, |sum, size| {
                sum.checked_add(*size as usize)
            });
        if represented_bits != Some(eq_suffix_bits) {
            return Err(DrTailCapacityRejection::InconsistentEqSizes);
        }

        let eq_group_count = eq_suffix_bits
            .checked_add(EQ_GROUP_BITS - 1)
            .ok_or(DrTailCapacityRejection::ArithmeticOverflow)?
            / EQ_GROUP_BITS;
        let entry_cell_bits = remaining_rounds
            .checked_add(1)
            .ok_or(DrTailCapacityRejection::ArithmeticOverflow)?;
        let entry_cells_per_source = 1usize
            .checked_shl(
                entry_cell_bits
                    .try_into()
                    .map_err(|_| DrTailCapacityRejection::ArithmeticOverflow)?,
            )
            .ok_or(DrTailCapacityRejection::ArithmeticOverflow)?;
        let state_bytes = entry_cells_per_source
            .checked_mul(self.canonical_sources)
            .and_then(|cells| cells.checked_mul(E4_BYTES))
            .ok_or(DrTailCapacityRejection::ArithmeticOverflow)?;
        let factored_eq_bytes = eq_group_count
            .checked_mul(GKR_EQ_GROUP_TABLE_LEN)
            .and_then(|cells| cells.checked_mul(E4_BYTES))
            .ok_or(DrTailCapacityRejection::ArithmeticOverflow)?;
        let dynamic_smem_bytes = state_bytes
            .checked_add(factored_eq_bytes)
            .ok_or(DrTailCapacityRejection::ArithmeticOverflow)?;
        let total_smem_bytes = dynamic_smem_bytes
            .checked_add(self.static_smem_bytes)
            .ok_or(DrTailCapacityRejection::ArithmeticOverflow)?;
        if total_smem_bytes > self.device_cap_bytes {
            return Err(DrTailCapacityRejection::DeviceCapacityExceeded {
                required_bytes: total_smem_bytes,
                cap_bytes: self.device_cap_bytes,
            });
        }

        Ok(DrTailCapacityDecision {
            entry_round: self.entry_round,
            remaining_rounds,
            entry_cells_per_source,
            state_bytes,
            eq_suffix_offset,
            eq_suffix_bits,
            eq_group_count,
            factored_eq_bytes,
            dynamic_smem_bytes,
            static_smem_bytes: self.static_smem_bytes,
            total_smem_bytes,
        })
    }
}
