use super::option::u32::*;
use crate::upstream::{NUM_TIMESTAMP_COLUMNS_FOR_RAM, REGISTER_SIZE};
use crate::witness::Address;

use crate::upstream::{
    CSIndirectRamAccessAddress, CSRamAddress, CSRamAuxComparisonSet, CSRamQuery, CSRamReadQuery,
    CSRamWordRepresentation, CSRamWriteQuery, CSRegisterOnlyAccessAddress,
    CSRegisterOrRamAccessAddress, CSRegisterOrRamAddressSpace,
};

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct RamWordU16Limbs {
    pub limbs: [u32; REGISTER_SIZE],
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct RamWordU8Limbs {
    pub limbs: [u32; REGISTER_SIZE * 2],
}

// FFI: payload limbs are consumed by GPU code via the `#[repr(C, u32)]` layout
// rather than read from Rust; suppress the per-variant dead_code lint.
#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub(crate) enum RamWordRepresentation {
    Zero,
    U16Limbs(RamWordU16Limbs),
    U8Limbs(RamWordU8Limbs),
}

impl Default for RamWordRepresentation {
    fn default() -> Self {
        Self::Zero
    }
}

impl From<CSRamWordRepresentation> for RamWordRepresentation {
    fn from(value: CSRamWordRepresentation) -> Self {
        match value {
            CSRamWordRepresentation::Zero => Self::Zero,
            CSRamWordRepresentation::U16Limbs(value) => Self::U16Limbs(RamWordU16Limbs {
                limbs: value.map(|x| x as u32),
            }),
            CSRamWordRepresentation::U8Limbs(value) => Self::U8Limbs(RamWordU8Limbs {
                limbs: value.map(|x| x as u32),
            }),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct RegisterOnlyAccessAddress {
    pub register_index: u32,
}

impl From<CSRegisterOnlyAccessAddress> for RegisterOnlyAccessAddress {
    fn from(value: CSRegisterOnlyAccessAddress) -> Self {
        Self {
            register_index: value.register_index as u32,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct IndirectRamVariableOffset {
    pub offset: u32,
    pub variable: u32,
}

impl From<(u16, usize)> for IndirectRamVariableOffset {
    fn from(value: (u16, usize)) -> Self {
        Self {
            offset: value.0 as u32,
            variable: value.1 as u32,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct IndirectRamAccessAddress {
    pub base_register_value: [u32; REGISTER_SIZE],
    pub base_register_index: u32,
    pub constant_offset: u32,
    pub indirect_access_idx_for_register: u32,
    pub variable_offset: Option<IndirectRamVariableOffset>,
}

impl From<CSIndirectRamAccessAddress> for IndirectRamAccessAddress {
    fn from(value: CSIndirectRamAccessAddress) -> Self {
        Self {
            base_register_value: value.base_register_value.map(|x| x as u32),
            base_register_index: value.base_register_index as u32,
            constant_offset: value.constant_offset as u32,
            indirect_access_idx_for_register: value.indirect_access_idx_for_register as u32,
            variable_offset: value.variable_offset.into(),
        }
    }
}

// FFI: payload is consumed by GPU code via the `#[repr(C, u32)]` layout.
#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub(crate) enum RegisterOrRamAddressSpace {
    RegisterAddressSpace(u32),
    RamAddressSpace(u32),
}

impl Default for RegisterOrRamAddressSpace {
    fn default() -> Self {
        Self::RegisterAddressSpace(0)
    }
}

impl From<CSRegisterOrRamAddressSpace> for RegisterOrRamAddressSpace {
    fn from(value: CSRegisterOrRamAddressSpace) -> Self {
        match value {
            CSRegisterOrRamAddressSpace::RegisterAddressSpace(x) => {
                Self::RegisterAddressSpace(x as u32)
            }
            CSRegisterOrRamAddressSpace::RamAddressSpace(x) => Self::RamAddressSpace(x as u32),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct RegisterOrRamAccessAddress {
    pub address_space: RegisterOrRamAddressSpace,
    pub address: [u32; REGISTER_SIZE],
}

impl From<CSRegisterOrRamAccessAddress> for RegisterOrRamAccessAddress {
    fn from(value: CSRegisterOrRamAccessAddress) -> Self {
        Self {
            address_space: value.address_space.into(),
            address: value.address.map(|x| x as u32),
        }
    }
}

// FFI: payload is consumed by GPU code via the `#[repr(C, u32)]` layout.
#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub(crate) enum RamAddress {
    ConstantRegister(u32),
    RegisterOnly(RegisterOnlyAccessAddress),
    RegisterOrRam(RegisterOrRamAccessAddress),
    IndirectRam(IndirectRamAccessAddress),
}

impl Default for RamAddress {
    fn default() -> Self {
        Self::RegisterOnly(RegisterOnlyAccessAddress::default())
    }
}

impl From<CSRamAddress> for RamAddress {
    fn from(value: CSRamAddress) -> Self {
        match value {
            CSRamAddress::ConstantRegister(register_index) => {
                Self::ConstantRegister(register_index as u32)
            }
            CSRamAddress::RegisterOnly(addr) => Self::RegisterOnly(addr.into()),
            CSRamAddress::RegisterOrRam(addr) => Self::RegisterOrRam(addr.into()),
            CSRamAddress::IndirectRam(addr) => Self::IndirectRam(addr.into()),
        }
    }
}

impl From<CSRegisterOrRamAccessAddress> for RamAddress {
    fn from(value: CSRegisterOrRamAccessAddress) -> Self {
        Self::RegisterOrRam(RegisterOrRamAccessAddress {
            address_space: value.address_space.into(),
            address: value.address.map(|x| x as u32),
        })
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct RamReadQuery {
    pub in_cycle_write_index: u32,
    pub address: RamAddress,
    pub read_timestamp: [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub read_value: RamWordRepresentation,
}

impl From<CSRamReadQuery> for RamReadQuery {
    fn from(value: CSRamReadQuery) -> Self {
        Self {
            in_cycle_write_index: value.in_cycle_write_index as u32,
            address: value.address.into(),
            read_timestamp: value.read_timestamp.map(|x| x as u32),
            read_value: value.read_value.into(),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct RamWriteQuery {
    pub in_cycle_write_index: u32,
    pub address: RamAddress,
    pub read_timestamp: [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub read_value: RamWordRepresentation,
    pub write_value: RamWordRepresentation,
}

impl From<CSRamWriteQuery> for RamWriteQuery {
    fn from(value: CSRamWriteQuery) -> Self {
        Self {
            in_cycle_write_index: value.in_cycle_write_index as u32,
            address: value.address.into(),
            read_timestamp: value.read_timestamp.map(|x| x as u32),
            read_value: value.read_value.into(),
            write_value: value.write_value.into(),
        }
    }
}

// FFI: payload is consumed by GPU code via the `#[repr(C, u32)]` layout.
#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub(crate) enum RamQuery {
    Readonly(RamReadQuery),
    Write(RamWriteQuery),
}

impl Default for RamQuery {
    fn default() -> Self {
        RamQuery::Readonly(RamReadQuery::default())
    }
}

impl From<CSRamQuery> for RamQuery {
    fn from(value: CSRamQuery) -> Self {
        match value {
            CSRamQuery::Readonly(query) => Self::Readonly(query.into()),
            CSRamQuery::Write(query) => Self::Write(query.into()),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct RamAuxComparisonSet {
    pub intermediate_borrow: Address,
}

impl From<CSRamAuxComparisonSet> for RamAuxComparisonSet {
    fn from(value: CSRamAuxComparisonSet) -> Self {
        Self {
            intermediate_borrow: value.intermediate_borrow.into(),
        }
    }
}
