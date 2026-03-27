use super::*;

use crate::definitions::constants::*;
use crate::definitions::GKRAddress;

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct RegisterOnlyAccessAddress {
    pub register_index: usize,
}

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub enum IsRegisterAddress {
    Is(usize),
    Not(usize),
}

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct RegisterOrRamAccessAddress {
    pub is_register: IsRegisterAddress,
    pub address: [usize; REGISTER_SIZE],
}

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct IndirectRamAccessAddress {
    pub base_register_value: [usize; REGISTER_SIZE],
    pub base_register_index: u16,
    pub constant_offset: u16,
    pub indirect_access_idx_for_register: usize,
    pub variable_offset: Option<(u16, usize)>,
}

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub enum RamAddress {
    ConstantRegister(u16),
    RegisterOnly(RegisterOnlyAccessAddress),
    RegisterOrRam(RegisterOrRamAccessAddress),
    IndirectRam(IndirectRamAccessAddress),
}

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct RamReadQuery {
    pub in_cycle_write_index: u32,
    pub address: RamAddress,
    pub read_timestamp: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub read_value: RamWordRepresentation,
}

#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum RamWordRepresentation {
    Zero,
    U16Limbs([usize; REGISTER_SIZE]),
    U8Limbs([usize; REGISTER_SIZE * 2]),
}

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct RamWriteQuery {
    pub in_cycle_write_index: u32,
    pub address: RamAddress,
    pub read_timestamp: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub read_value: RamWordRepresentation,
    pub write_value: RamWordRepresentation,
}

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub enum RamQuery {
    Readonly(RamReadQuery),
    Write(RamWriteQuery),
}

impl RamQuery {
    pub fn local_timestamp_in_cycle(&self) -> u32 {
        match self {
            Self::Readonly(el) => el.in_cycle_write_index,
            Self::Write(el) => el.in_cycle_write_index,
        }
    }

    pub const fn get_read_timestamp_columns(&self) -> [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM] {
        match self {
            Self::Readonly(el) => el.read_timestamp,
            Self::Write(el) => el.read_timestamp,
        }
    }

    pub const fn get_read_value_columns(&self) -> RamWordRepresentation {
        match self {
            Self::Readonly(el) => el.read_value,
            Self::Write(el) => el.read_value,
        }
    }

    pub const fn get_address(&self) -> RamAddress {
        match self {
            Self::Readonly(el) => el.address,
            Self::Write(el) => el.address,
        }
    }
}

// NOTE: to sort lazy init addresses we will materialize intermediate subtraction values to avoid extending
// lookup expressions to span >1 row

#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RamAuxComparisonSet {
    pub intermediate_borrow: GKRAddress,
}

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub enum RegisterAccessColumns {
    ReadAccess {
        register_index: u32,
        read_timestamp: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
        // write timestamp comes from the delegation request
        read_value: [usize; REGISTER_SIZE],
    },
    WriteAccess {
        register_index: u32,
        read_timestamp: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
        // write timestamp comes from the delegation request
        read_value: [usize; REGISTER_SIZE],
        write_value: [usize; REGISTER_SIZE],
    },
}

impl RegisterAccessColumns {
    pub const fn get_register_index(&self) -> u32 {
        match self {
            Self::ReadAccess { register_index, .. } => *register_index,
            Self::WriteAccess { register_index, .. } => *register_index,
        }
    }

    pub const fn get_read_value_columns(&self) -> [usize; REGISTER_SIZE] {
        match self {
            Self::ReadAccess { read_value, .. } => *read_value,
            Self::WriteAccess { read_value, .. } => *read_value,
        }
    }

    pub const fn get_read_timestamp_columns(&self) -> [usize; REGISTER_SIZE] {
        match self {
            Self::ReadAccess { read_timestamp, .. } => *read_timestamp,
            Self::WriteAccess { read_timestamp, .. } => *read_timestamp,
        }
    }
}

#[derive(Clone, Copy, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub enum IndirectAccess {
    ReadAccess {
        read_timestamp: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
        // write timestamp comes from the delegation request
        read_value: [usize; REGISTER_SIZE],
        // this value will be a part of the expression to accumulate grand product,
        // so it must be in the memory tree and not the witness tree
        address_derivation_carry_bit: Option<usize>,
        variable_dependent: Option<(u32, usize, usize)>,
        offset_constant: u32,
    },
    WriteAccess {
        read_timestamp: [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
        // write timestamp comes from the delegation request
        read_value: [usize; REGISTER_SIZE],
        write_value: [usize; REGISTER_SIZE],
        // this value will be a part of the expression to accumulate grand product,
        // so it must be in the memory tree and not the witness tree
        address_derivation_carry_bit: Option<usize>,
        variable_dependent: Option<(u32, usize, usize)>,
        offset_constant: u32,
    },
}

impl IndirectAccess {
    pub const fn offset_constant(&self) -> u32 {
        match self {
            Self::ReadAccess {
                offset_constant, ..
            } => *offset_constant,
            Self::WriteAccess {
                offset_constant, ..
            } => *offset_constant,
        }
    }

    pub const fn variable_dependent(&self) -> Option<(u32, usize, usize)> {
        match self {
            Self::ReadAccess {
                variable_dependent, ..
            } => *variable_dependent,
            Self::WriteAccess {
                variable_dependent, ..
            } => *variable_dependent,
        }
    }

    pub const fn get_address_derivation_carry_bit_column(&self) -> Option<usize> {
        match self {
            Self::ReadAccess {
                address_derivation_carry_bit,
                ..
            } => *address_derivation_carry_bit,
            Self::WriteAccess {
                address_derivation_carry_bit,
                ..
            } => *address_derivation_carry_bit,
        }
    }

    pub const fn get_read_value_columns(&self) -> [usize; REGISTER_SIZE] {
        match self {
            Self::ReadAccess { read_value, .. } => *read_value,
            Self::WriteAccess { read_value, .. } => *read_value,
        }
    }

    pub const fn get_read_timestamp_columns(&self) -> [usize; NUM_TIMESTAMP_COLUMNS_FOR_RAM] {
        match self {
            Self::ReadAccess { read_timestamp, .. } => *read_timestamp,
            Self::WriteAccess { read_timestamp, .. } => *read_timestamp,
        }
    }
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct RegisterAndIndirectAccessDescription {
    pub register_access: RegisterAccessColumns,
    pub indirect_accesses: Vec<IndirectAccess>,
}

impl RegisterAndIndirectAccessDescription {
    pub fn as_compiled<'a>(&'a self) -> CompiledRegisterAndIndirectAccessDescription<'a> {
        CompiledRegisterAndIndirectAccessDescription {
            register_access: self.register_access,
            indirect_accesses: &self.indirect_accesses,
        }
    }
}

#[derive(Clone, Copy, Hash, Debug)]
pub struct CompiledRegisterAndIndirectAccessDescription<'a> {
    pub register_access: RegisterAccessColumns,
    pub indirect_accesses: &'a [IndirectAccess],
}

#[derive(Clone, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct RegisterAndIndirectAccessTimestampComparisonAuxVars {
    pub predicate: GKRAddress,
    pub write_timestamp_columns: [GKRAddress; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub write_timestamp: [GKRAddress; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    pub aux_borrow_sets: Vec<(GKRAddress, Vec<GKRAddress>)>,
}
