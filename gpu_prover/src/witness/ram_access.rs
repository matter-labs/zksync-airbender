use super::column::*;
use super::option::*;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct RegisterOnlyAccessAddress {
    pub register_index: ColumnSet<1>,
}

impl From<cs::definitions::RegisterOnlyAccessAddress> for RegisterOnlyAccessAddress {
    fn from(value: cs::definitions::RegisterOnlyAccessAddress) -> Self {
        Self {
            register_index: value.register_index.into(),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct RegisterOrRamAccessAddress {
    pub is_register: ColumnSet<1>,
    pub address: ColumnSet<REGISTER_SIZE>,
}

impl From<cs::definitions::RegisterOrRamAccessAddress> for RegisterOrRamAccessAddress {
    fn from(value: cs::definitions::RegisterOrRamAccessAddress) -> Self {
        Self {
            is_register: value.is_register.into(),
            address: value.address.into(),
        }
    }
}

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub enum ShuffleRamAddress {
    RegisterOnly(RegisterOnlyAccessAddress),
    RegisterOrRam(RegisterOrRamAccessAddress),
}

impl Default for ShuffleRamAddress {
    fn default() -> Self {
        Self::RegisterOnly(RegisterOnlyAccessAddress::default())
    }
}

impl From<cs::definitions::ShuffleRamAddress> for ShuffleRamAddress {
    fn from(value: cs::definitions::ShuffleRamAddress) -> Self {
        match value {
            cs::definitions::ShuffleRamAddress::RegisterOnly(x) => Self::RegisterOnly(x.into()),
            cs::definitions::ShuffleRamAddress::RegisterOrRam(x) => Self::RegisterOrRam(x.into()),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct ShuffleRamQueryReadColumns {
    pub in_cycle_write_index: u32,
    pub address: ShuffleRamAddress,
    pub read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    pub read_value: ColumnSet<REGISTER_SIZE>,
}

impl From<cs::definitions::ShuffleRamQueryReadColumns> for ShuffleRamQueryReadColumns {
    fn from(value: cs::definitions::ShuffleRamQueryReadColumns) -> Self {
        Self {
            in_cycle_write_index: value.in_cycle_write_index,
            address: value.address.into(),
            read_timestamp: value.read_timestamp.into(),
            read_value: value.read_value.into(),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct ShuffleRamQueryWriteColumns {
    pub in_cycle_write_index: u32,
    pub address: ShuffleRamAddress,
    pub read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    pub read_value: ColumnSet<REGISTER_SIZE>,
    pub write_value: ColumnSet<REGISTER_SIZE>,
}

impl From<cs::definitions::ShuffleRamQueryWriteColumns> for ShuffleRamQueryWriteColumns {
    fn from(value: cs::definitions::ShuffleRamQueryWriteColumns) -> Self {
        Self {
            in_cycle_write_index: value.in_cycle_write_index,
            address: value.address.into(),
            read_timestamp: value.read_timestamp.into(),
            read_value: value.read_value.into(),
            write_value: value.write_value.into(),
        }
    }
}

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub enum ShuffleRamQueryColumns {
    Readonly(ShuffleRamQueryReadColumns),
    Write(ShuffleRamQueryWriteColumns),
}

impl Default for ShuffleRamQueryColumns {
    fn default() -> Self {
        Self::Readonly(ShuffleRamQueryReadColumns::default())
    }
}

impl From<cs::definitions::ShuffleRamQueryColumns> for ShuffleRamQueryColumns {
    fn from(value: cs::definitions::ShuffleRamQueryColumns) -> Self {
        match value {
            cs::definitions::ShuffleRamQueryColumns::Readonly(x) => Self::Readonly(x.into()),
            cs::definitions::ShuffleRamQueryColumns::Write(x) => Self::Write(x.into()),
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct ShuffleRamAuxComparisonSet {
    pub aux_low_high: [ColumnAddress; 2],
    pub intermediate_borrow: ColumnAddress,
    pub final_borrow: ColumnAddress,
}

impl From<&cs::definitions::ShuffleRamAuxComparisonSet> for ShuffleRamAuxComparisonSet {
    fn from(value: &cs::definitions::ShuffleRamAuxComparisonSet) -> Self {
        Self {
            aux_low_high: [value.aux_low_high[0].into(), value.aux_low_high[1].into()],
            intermediate_borrow: value.intermediate_borrow.into(),
            final_borrow: value.final_borrow.into(),
        }
    }
}

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub enum BatchedRamAccessColumns {
    ReadAccess {
        read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
        read_value: ColumnSet<REGISTER_SIZE>,
    },
    WriteAccess {
        read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
        read_value: ColumnSet<REGISTER_SIZE>,
        write_value: ColumnSet<REGISTER_SIZE>,
    },
}

impl Default for BatchedRamAccessColumns {
    fn default() -> Self {
        Self::ReadAccess {
            read_timestamp: ColumnSet::default(),
            read_value: ColumnSet::default(),
        }
    }
}

impl From<cs::definitions::BatchedRamAccessColumns> for BatchedRamAccessColumns {
    fn from(value: cs::definitions::BatchedRamAccessColumns) -> Self {
        match value {
            cs::definitions::BatchedRamAccessColumns::ReadAccess {
                read_timestamp,
                read_value,
            } => Self::ReadAccess {
                read_timestamp: read_timestamp.into(),
                read_value: read_value.into(),
            },
            cs::definitions::BatchedRamAccessColumns::WriteAccess {
                read_timestamp,
                read_value,
                write_value,
            } => Self::WriteAccess {
                read_timestamp: read_timestamp.into(),
                read_value: read_value.into(),
                write_value: write_value.into(),
            },
        }
    }
}

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub enum RegisterAccessColumns {
    ReadAccess {
        register_index: u32,
        read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
        read_value: ColumnSet<REGISTER_SIZE>,
    },
    WriteAccess {
        register_index: u32,
        read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
        read_value: ColumnSet<REGISTER_SIZE>,
        write_value: ColumnSet<REGISTER_SIZE>,
    },
}

impl Default for RegisterAccessColumns {
    fn default() -> Self {
        Self::ReadAccess {
            register_index: 0,
            read_timestamp: ColumnSet::default(),
            read_value: ColumnSet::default(),
        }
    }
}

impl From<cs::definitions::RegisterAccessColumns> for RegisterAccessColumns {
    fn from(value: cs::definitions::RegisterAccessColumns) -> Self {
        match value {
            cs::definitions::RegisterAccessColumns::ReadAccess {
                register_index,
                read_timestamp,
                read_value,
            } => Self::ReadAccess {
                register_index,
                read_timestamp: read_timestamp.into(),
                read_value: read_value.into(),
            },
            cs::definitions::RegisterAccessColumns::WriteAccess {
                register_index,
                read_timestamp,
                read_value,
                write_value,
            } => Self::WriteAccess {
                register_index,
                read_timestamp: read_timestamp.into(),
                read_value: read_value.into(),
                write_value: write_value.into(),
            },
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub struct IndirectAccessVariableDependency {
    pub offset: u32,
    pub variable: ColumnSet<1>,
    pub index: u32,
}

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub enum IndirectAccessColumns {
    ReadAccess {
        read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
        read_value: ColumnSet<REGISTER_SIZE>,
        address_derivation_carry_bit: ColumnSet<1>,
        variable_dependent: Option<IndirectAccessVariableDependency>,
        offset_constant: u32,
    },
    WriteAccess {
        read_timestamp: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
        read_value: ColumnSet<REGISTER_SIZE>,
        write_value: ColumnSet<REGISTER_SIZE>,
        address_derivation_carry_bit: ColumnSet<1>,
        variable_dependent: Option<IndirectAccessVariableDependency>,
        offset_constant: u32,
    },
}

impl Default for IndirectAccessColumns {
    fn default() -> Self {
        Self::ReadAccess {
            read_timestamp: ColumnSet::default(),
            read_value: ColumnSet::default(),
            address_derivation_carry_bit: ColumnSet::default(),
            variable_dependent: Option::None,
            offset_constant: 0,
        }
    }
}

impl From<cs::definitions::IndirectAccessColumns> for IndirectAccessColumns {
    fn from(value: cs::definitions::IndirectAccessColumns) -> Self {
        match value {
            cs::definitions::IndirectAccessColumns::ReadAccess {
                read_timestamp,
                read_value,
                address_derivation_carry_bit,
                variable_dependent,
                offset_constant,
            } => Self::ReadAccess {
                read_timestamp: read_timestamp.into(),
                read_value: read_value.into(),
                address_derivation_carry_bit: address_derivation_carry_bit.into(),
                variable_dependent: variable_dependent
                    .map(
                        |(offset, variable, index)| IndirectAccessVariableDependency {
                            offset,
                            variable: variable.into(),
                            index: index as u32,
                        },
                    )
                    .into(),
                offset_constant,
            },
            cs::definitions::IndirectAccessColumns::WriteAccess {
                read_timestamp,
                read_value,
                write_value,
                address_derivation_carry_bit,
                variable_dependent,
                offset_constant,
            } => Self::WriteAccess {
                read_timestamp: read_timestamp.into(),
                read_value: read_value.into(),
                write_value: write_value.into(),
                address_derivation_carry_bit: address_derivation_carry_bit.into(),
                variable_dependent: variable_dependent
                    .map(
                        |(offset, variable, index)| IndirectAccessVariableDependency {
                            offset,
                            variable: variable.into(),
                            index: index as u32,
                        },
                    )
                    .into(),
                offset_constant,
            },
        }
    }
}

pub const MAX_INDIRECT_ACCESS_DESCRIPTION_INDIRECT_ACCESSES_COUNT: usize = 32;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct RegisterAndIndirectAccessDescription {
    pub register_access: RegisterAccessColumns,
    pub indirect_accesses_count: u32,
    pub indirect_accesses:
        [IndirectAccessColumns; MAX_INDIRECT_ACCESS_DESCRIPTION_INDIRECT_ACCESSES_COUNT],
}

impl From<cs::definitions::RegisterAndIndirectAccessDescription>
    for RegisterAndIndirectAccessDescription
{
    fn from(value: cs::definitions::RegisterAndIndirectAccessDescription) -> Self {
        let indirect_accesses_count = value.indirect_accesses.len() as u32;
        assert!(
            indirect_accesses_count
                <= MAX_INDIRECT_ACCESS_DESCRIPTION_INDIRECT_ACCESSES_COUNT as u32
        );
        let mut indirect_accesses = [IndirectAccessColumns::default();
            MAX_INDIRECT_ACCESS_DESCRIPTION_INDIRECT_ACCESSES_COUNT];
        for (i, value) in value.indirect_accesses.into_iter().enumerate() {
            indirect_accesses[i] = value.into();
        }
        Self {
            register_access: value.register_access.into(),
            indirect_accesses_count,
            indirect_accesses,
        }
    }
}

pub const MAX_AUX_BORROW_SET_INDIRECTS_COUNT: usize = 24;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct AuxBorrowSet {
    pub borrow: ColumnAddress,
    pub indirects_count: u32,
    pub indirects: [ColumnAddress; MAX_AUX_BORROW_SET_INDIRECTS_COUNT],
}

impl
    From<(
        cs::definitions::ColumnAddress,
        Vec<cs::definitions::ColumnAddress>,
    )> for AuxBorrowSet
{
    fn from(
        value: (
            cs::definitions::ColumnAddress,
            Vec<cs::definitions::ColumnAddress>,
        ),
    ) -> Self {
        let (value_borrow, value_indirects) = value;
        let indirects_count = value_indirects.len() as u32;
        assert!(indirects_count <= MAX_AUX_BORROW_SET_INDIRECTS_COUNT as u32);
        let mut indirects = [ColumnAddress::default(); MAX_AUX_BORROW_SET_INDIRECTS_COUNT];
        for (i, value) in value_indirects.into_iter().enumerate() {
            indirects[i] = value.into();
        }
        Self {
            borrow: value_borrow.into(),
            indirects_count,
            indirects,
        }
    }
}

pub const MAX_AUX_BORROW_SETS_COUNT: usize = 4;

#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct RegisterAndIndirectAccessTimestampComparisonAuxVars {
    pub predicate: ColumnAddress,
    pub write_timestamp_columns: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
    pub write_timestamp: [ColumnAddress; 2],
    pub aux_borrow_sets_count: u32,
    pub aux_borrow_sets: [AuxBorrowSet; MAX_AUX_BORROW_SETS_COUNT],
}

impl From<&cs::definitions::RegisterAndIndirectAccessTimestampComparisonAuxVars>
    for RegisterAndIndirectAccessTimestampComparisonAuxVars
{
    fn from(value: &cs::definitions::RegisterAndIndirectAccessTimestampComparisonAuxVars) -> Self {
        let aux_borrow_sets_count = value.aux_borrow_sets.len() as u32;
        assert!(aux_borrow_sets_count <= MAX_AUX_BORROW_SETS_COUNT as u32);
        let mut aux_borrow_sets = [AuxBorrowSet::default(); MAX_AUX_BORROW_SETS_COUNT];
        for (i, value) in value.aux_borrow_sets.iter().enumerate() {
            aux_borrow_sets[i] = value.clone().into();
        }
        Self {
            predicate: value.predicate.into(),
            write_timestamp_columns: value.write_timestamp_columns.into(),
            write_timestamp: [
                value.write_timestamp[0].into(),
                value.write_timestamp[1].into(),
            ],
            aux_borrow_sets_count,
            aux_borrow_sets,
        }
    }
}
