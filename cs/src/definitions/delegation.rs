use super::*;

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct DelegationRequestLayout {
    pub multiplicity: ColumnSet<1>,
    pub delegation_type: ColumnSet<1>,
    pub abi_mem_offset_high: ColumnSet<1>,
    // write timestamps come from in-cycle index and setup's provided timestamps
    // for every cycle
    pub in_cycle_write_index: u16,
}

impl DelegationRequestLayout {
    pub const fn empty() -> Self {
        Self {
            multiplicity: ColumnSet::empty(),
            delegation_type: ColumnSet::empty(),
            abi_mem_offset_high: ColumnSet::empty(),
            in_cycle_write_index: 0,
        }
    }
}

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct DelegationProcessingLayout {
    pub multiplicity: ColumnSet<1>,
    pub abi_mem_offset_high: ColumnSet<1>,
    pub write_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
}

impl DelegationProcessingLayout {
    pub const fn empty() -> Self {
        Self {
            multiplicity: ColumnSet::empty(),
            abi_mem_offset_high: ColumnSet::empty(),
            write_timestamp: ColumnSet::empty(),
        }
    }
}
