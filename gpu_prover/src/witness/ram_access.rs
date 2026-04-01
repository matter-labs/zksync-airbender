use super::option::u32::*;
use crate::witness::Address;
use cs::definitions::{GKRAddress, NUM_TIMESTAMP_COLUMNS_FOR_RAM, REGISTER_SIZE};

type CSRegisterOnlyAccessAddress = cs::definitions::gkr::RegisterOnlyAccessAddress;
type CSIsRegisterAddress = cs::definitions::gkr::IsRegisterAddress;
type CSRamAddress = cs::definitions::gkr::RamAddress;
type CSRegisterOrRamAccessAddress = cs::definitions::gkr::RegisterOrRamAccessAddress;
type CSRamWordRepresentation = cs::definitions::gkr::RamWordRepresentation;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct RamWordU16Limbs {
    pub limbs: [u32; REGISTER_SIZE],
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct RamWordU8Limbs {
    pub limbs: [u32; REGISTER_SIZE * 2],
}

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
pub enum RamWordRepresentation {
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
pub struct RegisterOnlyAccessAddress {
    pub register_index: u32,
}

impl From<CSRegisterOnlyAccessAddress> for RegisterOnlyAccessAddress {
    fn from(value: CSRegisterOnlyAccessAddress) -> Self {
        Self {
            register_index: value.register_index as u32,
        }
    }
}

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
pub enum IsRegisterAddress {
    Is(u32),
    Not(u32),
}

impl Default for IsRegisterAddress {
    fn default() -> Self {
        Self::Is(0)
    }
}

impl From<CSIsRegisterAddress> for IsRegisterAddress {
    fn from(value: CSIsRegisterAddress) -> Self {
        match value {
            CSIsRegisterAddress::Is(x) => Self::Is(x as u32),
            CSIsRegisterAddress::Not(x) => Self::Not(x as u32),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct RegisterOrRamAccessAddress {
    pub is_register: IsRegisterAddress,
    pub address: [u32; REGISTER_SIZE],
}

impl From<CSRegisterOrRamAccessAddress> for RegisterOrRamAccessAddress {
    fn from(value: CSRegisterOrRamAccessAddress) -> Self {
        Self {
            is_register: value.is_register.into(),
            address: value.address.map(|x| x as u32),
        }
    }
}

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
pub enum RamAddress {
    RegisterOnly(RegisterOnlyAccessAddress),
    RegisterOrRam(RegisterOrRamAccessAddress),
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
                Self::RegisterOnly(RegisterOnlyAccessAddress {
                    register_index: register_index as u32,
                })
            }
            CSRamAddress::RegisterOnly(addr) => Self::RegisterOnly(addr.into()),
            CSRamAddress::RegisterOrRam(addr) => Self::RegisterOrRam(addr.into()),
            CSRamAddress::IndirectRam(_) => {
                unimplemented!("GPU witness generation does not yet support indirect RAM addresses")
            }
        }
    }
}

impl From<CSRegisterOrRamAccessAddress> for RamAddress {
    fn from(value: CSRegisterOrRamAccessAddress) -> Self {
        Self::RegisterOrRam(RegisterOrRamAccessAddress {
            is_register: value.is_register.into(),
            address: value.address.map(|x| x as u32),
        })
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct RamReadQuery {
    pub in_cycle_write_index: u32,
    pub address: RamAddress,
    pub read_timestamp: [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub read_value: RamWordRepresentation,
}

impl From<cs::definitions::gkr::RamReadQuery> for RamReadQuery {
    fn from(value: cs::definitions::gkr::RamReadQuery) -> Self {
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
pub struct RamWriteQuery {
    pub in_cycle_write_index: u32,
    pub address: RamAddress,
    pub read_timestamp: [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub read_value: RamWordRepresentation,
    pub write_value: RamWordRepresentation,
}

impl From<cs::definitions::gkr::RamWriteQuery> for RamWriteQuery {
    fn from(value: cs::definitions::gkr::RamWriteQuery) -> Self {
        Self {
            in_cycle_write_index: value.in_cycle_write_index as u32,
            address: value.address.into(),
            read_timestamp: value.read_timestamp.map(|x| x as u32),
            read_value: value.read_value.into(),
            write_value: value.write_value.into(),
        }
    }
}

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
pub enum RamQuery {
    Readonly(RamReadQuery),
    Write(RamWriteQuery),
}

impl Default for RamQuery {
    fn default() -> Self {
        RamQuery::Readonly(RamReadQuery::default())
    }
}

impl From<cs::definitions::gkr::RamQuery> for RamQuery {
    fn from(value: cs::definitions::gkr::RamQuery) -> Self {
        match value {
            cs::definitions::gkr::RamQuery::Readonly(query) => Self::Readonly(query.into()),
            cs::definitions::gkr::RamQuery::Write(query) => Self::Write(query.into()),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct RamAuxComparisonSet {
    pub intermediate_borrow: Address,
}

impl From<cs::definitions::gkr::RamAuxComparisonSet> for RamAuxComparisonSet {
    fn from(value: cs::definitions::gkr::RamAuxComparisonSet) -> Self {
        Self {
            intermediate_borrow: value.intermediate_borrow.into(),
        }
    }
}

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
pub enum RegisterAccessColumns {
    ReadAccess {
        register_index: u32,
        read_timestamp: [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
        read_value: [u32; REGISTER_SIZE],
    },
    WriteAccess {
        register_index: u32,
        read_timestamp: [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
        read_value: [u32; REGISTER_SIZE],
        write_value: [u32; REGISTER_SIZE],
    },
}

impl Default for RegisterAccessColumns {
    fn default() -> Self {
        Self::ReadAccess {
            register_index: 0,
            read_timestamp: [0; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
            read_value: [0; REGISTER_SIZE],
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct IndirectAccessVariableDependency {
    pub offset: u32,
    pub variable: u32,
    pub index: u32,
}

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
pub enum IndirectAccess {
    ReadAccess {
        read_timestamp: [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
        read_value: [u32; REGISTER_SIZE],
        address_derivation_carry_bit: Option<u32>,
        variable_dependent: Option<IndirectAccessVariableDependency>,
        offset_constant: u32,
    },
    WriteAccess {
        read_timestamp: [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
        read_value: [u32; REGISTER_SIZE],
        write_value: [u32; REGISTER_SIZE],
        address_derivation_carry_bit: Option<u32>,
        variable_dependent: Option<IndirectAccessVariableDependency>,
        offset_constant: u32,
    },
}

impl Default for IndirectAccess {
    fn default() -> Self {
        Self::ReadAccess {
            read_timestamp: [0; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
            read_value: [0; REGISTER_SIZE],
            address_derivation_carry_bit: Option::None,
            variable_dependent: Option::None,
            offset_constant: 0,
        }
    }
}

pub const MAX_INDIRECT_ACCESSES_COUNT: usize = 32;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct RegisterAndIndirectAccessDescription {
    pub register_access: RegisterAccessColumns,
    pub indirect_accesses_count: u32,
    pub indirect_accesses: [IndirectAccess; MAX_INDIRECT_ACCESSES_COUNT],
}

pub const MAX_AUX_BORROW_SET_INDIRECTS_COUNT: usize = 24;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct AuxBorrowSet {
    pub borrow: Address,
    pub indirects_count: u32,
    pub indirects: [Address; MAX_AUX_BORROW_SET_INDIRECTS_COUNT],
}

pub const MAX_AUX_BORROW_SETS_COUNT: usize = 4;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct RegisterAndIndirectAccessTimestampComparisonAuxVars {
    pub predicate: Address,
    pub write_timestamp_columns: [Address; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub write_timestamp: [Address; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub aux_borrow_sets: [AuxBorrowSet; MAX_AUX_BORROW_SETS_COUNT],
}
