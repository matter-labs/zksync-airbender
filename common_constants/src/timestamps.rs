// Various constants that non-workspace crates may want to import
pub const NUM_TIMESTAMP_DATA_LIMBS: usize = 3;
pub type TimestampScalar = u64;

pub const INITIAL_TIMESTAMP: TimestampScalar = 4;

pub const NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP: u32 = 2; // we need 3 accesses for the cycle if bytecode is in ROM

pub const INITIAL_TIMESTAMP_AT_CHUNK_START: TimestampScalar = 4;
pub const TIMESTAMP_STEP: TimestampScalar = 1 << NUM_EMPTY_BITS_FOR_RAM_TIMESTAMP;

pub const NUM_TIMESTAMP_COLUMNS_FOR_RAM: usize = 2;
pub const NUM_TIMESTAMP_COLUMNS_FOR_RAM_IN_SETUP: usize = NUM_TIMESTAMP_COLUMNS_FOR_RAM;

pub const TIMESTAMP_COLUMNS_NUM_BITS: u32 = 19;

pub const TOTAL_TIMESTAMP_BITS: u32 =
    TIMESTAMP_COLUMNS_NUM_BITS * NUM_TIMESTAMP_COLUMNS_FOR_RAM as u32;
pub const MAX_INITIAL_TIMESTAMP: TimestampScalar = (1 << TOTAL_TIMESTAMP_BITS) - TIMESTAMP_STEP * 2;
