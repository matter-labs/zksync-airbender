use super::column::*;
pub const SHUFFLE_RAM_INIT_AND_TEARDOWN_LAYOUT_WIDTH: usize =
    REGISTER_SIZE * 2 + NUM_TIMESTAMP_COLUMNS_FOR_RAM;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct ShuffleRamInitAndTeardownLayout {
    pub lazy_init_addresses_columns: ColumnSet<REGISTER_SIZE>,
    pub lazy_teardown_values_columns: ColumnSet<REGISTER_SIZE>,
    pub lazy_teardown_timestamps_columns: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
}

impl From<cs::definitions::ShuffleRamInitAndTeardownLayout> for ShuffleRamInitAndTeardownLayout {
    fn from(value: cs::definitions::ShuffleRamInitAndTeardownLayout) -> Self {
        Self {
            lazy_init_addresses_columns: value.lazy_init_addresses_columns.into(),
            lazy_teardown_values_columns: value.lazy_teardown_values_columns.into(),
            lazy_teardown_timestamps_columns: value.lazy_teardown_timestamps_columns.into(),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct DelegationRequestLayout {
    pub multiplicity: ColumnSet<1>,
    pub delegation_type: ColumnSet<1>,
    pub abi_mem_offset_high: ColumnSet<1>,
}

impl From<cs::definitions::DelegationRequestLayout> for DelegationRequestLayout {
    fn from(value: cs::definitions::DelegationRequestLayout) -> Self {
        Self {
            multiplicity: value.multiplicity.into(),
            delegation_type: value.delegation_type.into(),
            abi_mem_offset_high: value.abi_mem_offset_high.into(),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct DelegationProcessingLayout {
    pub multiplicity: ColumnSet<1>,
    pub abi_mem_offset_high: ColumnSet<1>,
    pub write_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
}

impl From<cs::definitions::DelegationProcessingLayout> for DelegationProcessingLayout {
    fn from(value: cs::definitions::DelegationProcessingLayout) -> Self {
        Self {
            multiplicity: value.multiplicity.into(),
            abi_mem_offset_high: value.abi_mem_offset_high.into(),
            write_timestamp: value.write_timestamp.into(),
        }
    }
}
