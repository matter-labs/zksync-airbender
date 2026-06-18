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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct TimestampData(pub [u16; NUM_TIMESTAMP_DATA_LIMBS]);

const _: () = const {
    assert!(core::mem::align_of::<TimestampData>() == 2);
    assert!(core::mem::size_of::<TimestampData>() == 6);

    ()
};

impl Default for TimestampData {
    #[inline(always)]
    fn default() -> Self {
        Self([0; NUM_TIMESTAMP_DATA_LIMBS])
    }
}

impl TimestampData {
    pub const EMPTY: Self = Self([0u16; NUM_TIMESTAMP_DATA_LIMBS]);

    #[inline(always)]
    pub const fn from_scalar(ts: TimestampScalar) -> Self {
        let l0 = ts as u16;
        let l1 = (ts >> 16) as u16;
        let l2 = (ts >> 32) as u16;

        Self([l0, l1, l2])
    }

    pub const fn as_scalar(&self) -> TimestampScalar {
        (self.0[0] as u64) | ((self.0[1] as u64) << 16) | ((self.0[2] as u64) << 32)
    }
}
