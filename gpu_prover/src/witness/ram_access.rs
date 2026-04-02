use super::option::u32::*;
use crate::witness::Address;
use cs::definitions::{NUM_TIMESTAMP_COLUMNS_FOR_RAM, REGISTER_SIZE};

type CSRegisterOnlyAccessAddress = cs::definitions::gkr::RegisterOnlyAccessAddress;
type CSIndirectRamAccessAddress = cs::definitions::gkr::IndirectRamAccessAddress;
type CSIsRegisterAddress = cs::definitions::gkr::IsRegisterAddress;
type CSRamAddress = cs::definitions::gkr::RamAddress;
type CSRegisterAccessColumns = cs::definitions::gkr::RegisterAccessColumns;
type CSIndirectAccess = cs::definitions::gkr::IndirectAccess;
type CSRegisterAndIndirectAccessDescription =
    cs::definitions::gkr::RegisterAndIndirectAccessDescription;
type CSRegisterAndIndirectAccessTimestampComparisonAuxVars =
    cs::definitions::gkr::RegisterAndIndirectAccessTimestampComparisonAuxVars;
type CSRegisterOrRamAccessAddress = cs::definitions::gkr::RegisterOrRamAccessAddress;
type CSRamWordRepresentation = cs::definitions::gkr::RamWordRepresentation;
type CSRamAuxComparisonSet = cs::definitions::gkr::RamAuxComparisonSet;

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

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct IndirectRamVariableOffset {
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
pub struct IndirectRamAccessAddress {
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

impl From<CSRegisterAccessColumns> for RegisterAccessColumns {
    fn from(value: CSRegisterAccessColumns) -> Self {
        match value {
            CSRegisterAccessColumns::ReadAccess {
                register_index,
                read_timestamp,
                read_value,
            } => Self::ReadAccess {
                register_index: register_index as u32,
                read_timestamp: read_timestamp.map(|x| x as u32),
                read_value: read_value.map(|x| x as u32),
            },
            CSRegisterAccessColumns::WriteAccess {
                register_index,
                read_timestamp,
                read_value,
                write_value,
            } => Self::WriteAccess {
                register_index: register_index as u32,
                read_timestamp: read_timestamp.map(|x| x as u32),
                read_value: read_value.map(|x| x as u32),
                write_value: write_value.map(|x| x as u32),
            },
        }
    }
}

impl From<CSIndirectAccess> for IndirectAccess {
    fn from(value: CSIndirectAccess) -> Self {
        match value {
            CSIndirectAccess::ReadAccess {
                read_timestamp,
                read_value,
                address_derivation_carry_bit,
                variable_dependent,
                offset_constant,
            } => Self::ReadAccess {
                read_timestamp: read_timestamp.map(|x| x as u32),
                read_value: read_value.map(|x| x as u32),
                address_derivation_carry_bit: address_derivation_carry_bit.map(|x| x as u32).into(),
                variable_dependent: variable_dependent
                    .map(
                        |(offset, variable, index)| IndirectAccessVariableDependency {
                            offset,
                            variable: variable as u32,
                            index: index as u32,
                        },
                    )
                    .into(),
                offset_constant,
            },
            CSIndirectAccess::WriteAccess {
                read_timestamp,
                read_value,
                write_value,
                address_derivation_carry_bit,
                variable_dependent,
                offset_constant,
            } => Self::WriteAccess {
                read_timestamp: read_timestamp.map(|x| x as u32),
                read_value: read_value.map(|x| x as u32),
                write_value: write_value.map(|x| x as u32),
                address_derivation_carry_bit: address_derivation_carry_bit.map(|x| x as u32).into(),
                variable_dependent: variable_dependent
                    .map(
                        |(offset, variable, index)| IndirectAccessVariableDependency {
                            offset,
                            variable: variable as u32,
                            index: index as u32,
                        },
                    )
                    .into(),
                offset_constant,
            },
        }
    }
}

impl From<CSRegisterAndIndirectAccessDescription> for RegisterAndIndirectAccessDescription {
    fn from(value: CSRegisterAndIndirectAccessDescription) -> Self {
        let indirect_accesses_count = value.indirect_accesses.len();
        assert!(indirect_accesses_count <= MAX_INDIRECT_ACCESSES_COUNT);
        let mut indirect_accesses = [IndirectAccess::default(); MAX_INDIRECT_ACCESSES_COUNT];
        for (src, dst) in value
            .indirect_accesses
            .into_iter()
            .zip(indirect_accesses.iter_mut())
        {
            *dst = src.into();
        }
        Self {
            register_access: value.register_access.into(),
            indirect_accesses_count: indirect_accesses_count as u32,
            indirect_accesses,
        }
    }
}

impl From<CSRegisterAndIndirectAccessTimestampComparisonAuxVars>
    for RegisterAndIndirectAccessTimestampComparisonAuxVars
{
    fn from(value: CSRegisterAndIndirectAccessTimestampComparisonAuxVars) -> Self {
        let aux_borrow_sets = value.aux_borrow_sets;
        let len = aux_borrow_sets.len();
        assert!(len <= MAX_AUX_BORROW_SETS_COUNT);
        let mut dst = [AuxBorrowSet::default(); MAX_AUX_BORROW_SETS_COUNT];
        for ((borrow, indirects), slot) in aux_borrow_sets.into_iter().zip(dst.iter_mut()) {
            let indirects_len = indirects.len();
            assert!(indirects_len <= MAX_AUX_BORROW_SET_INDIRECTS_COUNT);
            let mut indirects_dst = [Address::default(); MAX_AUX_BORROW_SET_INDIRECTS_COUNT];
            for (src, dst) in indirects.into_iter().zip(indirects_dst.iter_mut()) {
                *dst = src.into();
            }
            *slot = AuxBorrowSet {
                borrow: borrow.into(),
                indirects_count: indirects_len as u32,
                indirects: indirects_dst,
            };
        }
        Self {
            predicate: value.predicate.into(),
            write_timestamp_columns: value.write_timestamp_columns.map(Into::into),
            write_timestamp: value.write_timestamp.map(Into::into),
            aux_borrow_sets: dst,
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
