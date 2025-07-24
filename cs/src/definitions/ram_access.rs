use super::*;

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub struct RegisterOnlyAccessAddress {
    pub register_index: ColumnSet<1>,
}

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub struct RegisterOrRamAccessAddress {
    pub is_register: ColumnSet<1>,
    pub address: ColumnSet<REGISTER_SIZE>,
}

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub enum ShuffleRamAddress {
    RegisterOnly(RegisterOnlyAccessAddress),
    RegisterOrRam(RegisterOrRamAccessAddress),
}

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub struct ShuffleRamQueryReadColumns {
    pub in_cycle_write_index: u32,
    pub address: ShuffleRamAddress,
    pub read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    // // write timestamp will be made form setup
    // pub write_timestamp: Range<usize>,
    pub read_value: ColumnSet<REGISTER_SIZE>,
}

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub struct ShuffleRamQueryWriteColumns {
    pub in_cycle_write_index: u32,
    pub address: ShuffleRamAddress,
    pub read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    // // write timestamp will be made form setup
    // pub write_timestamp: Range<usize>,
    pub read_value: ColumnSet<REGISTER_SIZE>,
    pub write_value: ColumnSet<REGISTER_SIZE>,
}

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub enum ShuffleRamQueryColumns {
    Readonly(ShuffleRamQueryReadColumns),
    Write(ShuffleRamQueryWriteColumns),
}

impl ShuffleRamQueryColumns {
    pub const fn max_offset(&self) -> usize {
        match self {
            Self::Readonly(el) => el.read_value.start + REGISTER_SIZE,
            Self::Write(el) => el.write_value.start + REGISTER_SIZE,
        }
    }

    pub const fn get_read_timestamp_columns(&self) -> ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> {
        match self {
            Self::Readonly(el) => el.read_timestamp,
            Self::Write(el) => el.read_timestamp,
        }
    }

    pub const fn get_read_value_columns(&self) -> ColumnSet<REGISTER_SIZE> {
        match self {
            Self::Readonly(el) => el.read_value,
            Self::Write(el) => el.read_value,
        }
    }

    pub const fn get_address(&self) -> ShuffleRamAddress {
        match self {
            Self::Readonly(el) => el.address,
            Self::Write(el) => el.address,
        }
    }
}

// NOTE: to sort lazy init addresses we will materialize intermediate subtraction values to avoid extending
// lookup expressions to span >1 row

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub struct ShuffleRamAuxComparisonSet {
    pub aux_low_high: [ColumnAddress; 2],
    pub intermediate_borrow: ColumnAddress,
    pub final_borrow: ColumnAddress,
}

// NOTE: for this kind of memory access we will need to compare that read timestamp < write timestamp,
// but using lookup expressions we do not need to make any extra description for it - lookup expression contains
// all the information

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub enum BatchedRamAccessColumns {
    ReadAccess {
        read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
        // write timestamp comes from the delegation request
        read_value: ColumnSet<REGISTER_SIZE>,
    },
    WriteAccess {
        read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
        // write timestamp comes from the delegation request
        read_value: ColumnSet<REGISTER_SIZE>,
        write_value: ColumnSet<REGISTER_SIZE>,
    },
}

impl BatchedRamAccessColumns {
    pub const fn get_read_value_columns(&self) -> ColumnSet<REGISTER_SIZE> {
        match self {
            Self::ReadAccess { read_value, .. } => *read_value,
            Self::WriteAccess { read_value, .. } => *read_value,
        }
    }

    pub const fn get_read_timestamp_columns(&self) -> ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> {
        match self {
            Self::ReadAccess { read_timestamp, .. } => *read_timestamp,
            Self::WriteAccess { read_timestamp, .. } => *read_timestamp,
        }
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct BatchedRamTimestampComparisonAuxVars {
    pub predicate: ColumnAddress,
    pub write_timestamp_columns: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    pub write_timestamp: [ColumnAddress; 2],
    pub aux_borrow_vars: Vec<ColumnAddress>,
}

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub enum RegisterAccessColumns {
    ReadAccess {
        register_index: u32,
        read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
        // write timestamp comes from the delegation request
        read_value: ColumnSet<REGISTER_SIZE>,
    },
    WriteAccess {
        register_index: u32,
        read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
        // write timestamp comes from the delegation request
        read_value: ColumnSet<REGISTER_SIZE>,
        write_value: ColumnSet<REGISTER_SIZE>,
    },
}

impl RegisterAccessColumns {
    pub const fn get_register_index(&self) -> u32 {
        match self {
            Self::ReadAccess { register_index, .. } => *register_index,
            Self::WriteAccess { register_index, .. } => *register_index,
        }
    }

    pub const fn get_read_value_columns(&self) -> ColumnSet<REGISTER_SIZE> {
        match self {
            Self::ReadAccess { read_value, .. } => *read_value,
            Self::WriteAccess { read_value, .. } => *read_value,
        }
    }

    pub const fn get_read_timestamp_columns(&self) -> ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> {
        match self {
            Self::ReadAccess { read_timestamp, .. } => *read_timestamp,
            Self::WriteAccess { read_timestamp, .. } => *read_timestamp,
        }
    }
}

#[derive(Clone, Copy, Debug, serde::Serialize, serde::Deserialize)]
pub enum IndirectAccessColumns {
    ReadAccess {
        read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
        // write timestamp comes from the delegation request
        read_value: ColumnSet<REGISTER_SIZE>,
        // this value will be a part of the expression to accumulate grand product,
        // so it must be in the memory tree and not the witness tree
        address_derivation_carry_bit: ColumnSet<1>,
        variable_dependent: Option<(u32, ColumnSet<1>)>,
        offset_constant: u32,
    },
    WriteAccess {
        read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
        // write timestamp comes from the delegation request
        read_value: ColumnSet<REGISTER_SIZE>,
        write_value: ColumnSet<REGISTER_SIZE>,
        // this value will be a part of the expression to accumulate grand product,
        // so it must be in the memory tree and not the witness tree
        address_derivation_carry_bit: ColumnSet<1>,
        variable_dependent: Option<(u32, ColumnSet<1>)>,
        offset_constant: u32,
    },
}

impl IndirectAccessColumns {
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

    pub const fn variable_dependent(&self) -> Option<(u32, ColumnSet<1>)> {
        match self {
            Self::ReadAccess {
                variable_dependent, ..
            } => *variable_dependent,
            Self::WriteAccess {
                variable_dependent, ..
            } => *variable_dependent,
        }
    }

    pub const fn get_address_derivation_carry_bit_column(&self) -> ColumnSet<1> {
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

    pub const fn get_read_value_columns(&self) -> ColumnSet<REGISTER_SIZE> {
        match self {
            Self::ReadAccess { read_value, .. } => *read_value,
            Self::WriteAccess { read_value, .. } => *read_value,
        }
    }

    pub const fn get_read_timestamp_columns(&self) -> ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM> {
        match self {
            Self::ReadAccess { read_timestamp, .. } => *read_timestamp,
            Self::WriteAccess { read_timestamp, .. } => *read_timestamp,
        }
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RegisterAndIndirectAccessDescription {
    pub register_access: RegisterAccessColumns,
    pub indirect_accesses: Vec<IndirectAccessColumns>,
}

impl RegisterAndIndirectAccessDescription {
    pub fn as_compiled<'a>(&'a self) -> CompiledRegisterAndIndirectAccessDescription<'a> {
        CompiledRegisterAndIndirectAccessDescription {
            register_access: self.register_access,
            indirect_accesses: &self.indirect_accesses,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct CompiledRegisterAndIndirectAccessDescription<'a> {
    pub register_access: RegisterAccessColumns,
    pub indirect_accesses: &'a [IndirectAccessColumns],
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RegisterAndIndirectAccessTimestampComparisonAuxVars {
    pub predicate: ColumnAddress,
    pub write_timestamp_columns: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    pub write_timestamp: [ColumnAddress; 2],
    pub aux_borrow_sets: Vec<(ColumnAddress, Vec<ColumnAddress>)>,
}
