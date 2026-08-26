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
}

impl DrTailCapacityDecision {
    pub(crate) const fn entry_round(&self) -> usize {
        self.entry_round
    }

    pub(crate) const fn dynamic_smem_bytes(&self) -> usize {
        self.dynamic_smem_bytes
    }
}

pub(crate) fn portable_entry(folding_steps: usize) -> usize {
    let completed = folding_steps
        .checked_sub(1)
        .expect("DR layer must contain at least one round")
        / 3;
    let entry = completed
        .checked_mul(3)
        .expect("DR-tail entry round overflowed")
        .min(MAX_ENTRY_ROUND);
    assert!((3..folding_steps).contains(&entry));
    entry
}

impl DrTailCapacityRequest {
    pub(crate) fn decide(self) -> DrTailCapacityDecision {
        assert!(self.entry_round >= 3);
        assert!(self.entry_round.is_multiple_of(3));
        assert!(self.entry_round < self.folding_steps);
        assert!((1..=MAX_CANONICAL_SOURCES).contains(&self.canonical_sources));

        let remaining_rounds = self.folding_steps.checked_sub(self.entry_round).unwrap();
        let eq_suffix_offset = self
            .entry_round
            .checked_add(1)
            .expect("DR-tail Eq suffix offset overflowed");
        let eq_suffix_bits = self.folding_steps.checked_sub(eq_suffix_offset).unwrap();
        let max_eq_bits = (GKR_EQ_HIGH_SLOTS + 1)
            .checked_mul(EQ_GROUP_BITS)
            .expect("DR-tail Eq capacity overflowed");
        assert!(eq_suffix_bits <= max_eq_bits);

        let eq_sizes = make_eq_sizes(eq_suffix_bits);
        let represented_bits = eq_sizes
            .high
            .iter()
            .try_fold(eq_sizes.low as usize, |sum, size| {
                sum.checked_add(*size as usize)
            });
        assert_eq!(represented_bits, Some(eq_suffix_bits));

        let eq_group_count = eq_suffix_bits
            .checked_add(EQ_GROUP_BITS - 1)
            .expect("DR-tail Eq group count overflowed")
            / EQ_GROUP_BITS;
        let entry_cell_bits = remaining_rounds
            .checked_add(1)
            .expect("DR-tail entry cell count overflowed");
        let entry_cells_per_source = 1usize
            .checked_shl(entry_cell_bits.try_into().unwrap())
            .expect("DR-tail entry cell count overflowed");
        let state_bytes = entry_cells_per_source
            .checked_mul(self.canonical_sources)
            .and_then(|cells| cells.checked_mul(E4_BYTES))
            .expect("DR-tail state size overflowed");
        let factored_eq_bytes = eq_group_count
            .checked_mul(GKR_EQ_GROUP_TABLE_LEN)
            .and_then(|cells| cells.checked_mul(E4_BYTES))
            .expect("DR-tail Eq size overflowed");
        let dynamic_smem_bytes = state_bytes
            .checked_add(factored_eq_bytes)
            .expect("DR-tail dynamic shared-memory size overflowed");
        let total_smem_bytes = dynamic_smem_bytes
            .checked_add(self.static_smem_bytes)
            .expect("DR-tail shared-memory size overflowed");
        assert!(total_smem_bytes <= self.device_cap_bytes);

        DrTailCapacityDecision {
            entry_round: self.entry_round,
            remaining_rounds,
            entry_cells_per_source,
            state_bytes,
            eq_suffix_offset,
            eq_suffix_bits,
            eq_group_count,
            factored_eq_bytes,
            dynamic_smem_bytes,
        }
    }
}
