// zero_entry table should have id = 0 (this is a strict requirement!)
pub const ZERO_ENTRY_TABLE_ID: u32 = 0;

// max table width including(!) table ID
pub const MAX_TABLE_WIDTH: usize = 16;

// and, or, xor table should have id to match corresponding funct3 for these opcodes
pub const AND_TABLE_ID: u32 = 7;
pub const XOR_TABLE_ID: u32 = 4;
pub const OR_TABLE_ID: u32 = 6;

#[derive(
    Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug, serde::Serialize, serde::Deserialize,
)]
#[repr(u32)]
pub enum TableType {
    ZeroEntry = 0,
    RegIsZero,
    JumpCleanupOffset,
    GetSignExtensionByte,
    Xor = 4,
    U16GetSign,
    Or = 6,
    And = 7,
    TruncateShiftAmountAndRangeCheck8,
    ShiftImplementationOverBytes,
    RangeCheck8x8,
    AndNot,
    U16GetSignAndHighByte,
    MemoryOffsetGetBits,
    MemoryLoadGetSigns,
    RomAddressSpaceSeparator,
    RomRead,
    Xor3,
    Xor4,
    Xor7,
    Xor9,
    Xor12,
    RangeCheck9x9,
    RangeCheck10x10,
    RangeCheck11,
    RangeCheck12,
    RangeCheck13,
    U16SelectByteAndGetByteSign,
    ExtendLoadedValue,
    StoreByteSourceContribution,
    StoreByteExistingContribution,
    ConditionalJmpBranchSlt,
    MemoryGetOffsetAndMaskWithTrap,
    MemoryLoadHalfwordOrByte,
    AlignedRomRead,
    MemStoreClearOriginalRamValueLimb,
    MemStoreClearWrittenValueLimb,
    KeccakPermutationIndices,
    XorSpecialIota,
    AndN,
    RotL,
    U16GetLowByte,
    LoadHalfwordSignextend,
    LoadByteSignextend,
    LoadHalfwordRomRead,
    LoadByteRomRead,
    Decoder,
    DynamicPlaceholder, // MUST be the last
}

pub const COMMON_TABLE_WIDTH: usize = 3;
pub const NUM_COLUMNS_FOR_COMMON_TABLE_WIDTH_SETUP: usize = COMMON_TABLE_WIDTH + 1;
pub const SMALL_RANGE_CHECK_TABLE_WIDTH: usize = 8;
pub const LARGE_RANGE_CHECK_TABLE_WIDTH: usize = 16;

pub const SMALL_RANGE_CHECK_TABLE_ID: u32 = TableType::RangeCheck8x8 as u32;
