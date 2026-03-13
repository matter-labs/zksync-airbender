use cs::definitions::TimestampData;

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C)]
pub struct RegisterOrIndirectReadData {
    pub read_value: u32,
    pub timestamp: TimestampData,
}

impl RegisterOrIndirectReadData {
    pub const EMPTY: Self = Self {
        read_value: 0,
        timestamp: TimestampData::EMPTY,
    };
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C)]
pub struct RegisterOrIndirectReadWriteData {
    pub read_value: u32,
    pub write_value: u32,
    pub timestamp: TimestampData,
}

impl RegisterOrIndirectReadWriteData {
    pub const EMPTY: Self = Self {
        read_value: 0,
        write_value: 0,
        timestamp: TimestampData::EMPTY,
    };
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C)]
pub struct RegisterOrIndirectVariableOffsetData {
    pub variable_offset_value: u16,
}

impl RegisterOrIndirectVariableOffsetData {
    pub const EMPTY: Self = Self {
        variable_offset_value: 0,
    };
}

impl From<u16> for RegisterOrIndirectVariableOffsetData {
    fn from(value: u16) -> Self {
        Self {
            variable_offset_value: value,
        }
    }
}
