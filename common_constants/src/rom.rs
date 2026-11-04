pub const ROM_BYTE_SIZE_LOG2: usize = 22; // 4Mb
pub const ROM_BYTE_SIZE: usize = 1 << ROM_BYTE_SIZE_LOG2; // 4Mb
pub const ROM_SECOND_WORD_BITS: usize = ROM_BYTE_SIZE_LOG2 - 16;
pub const ROM_WORD_SIZE: usize = ROM_BYTE_SIZE / core::mem::size_of::<u32>();
