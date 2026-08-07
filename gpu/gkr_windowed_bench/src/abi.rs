use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;

pub type BF = BabyBearField;
pub type E4 = BabyBearExt4;

pub const WARPS_PER_BLOCK: u32 = 9;
pub const THREADS_PER_BLOCK: u32 = 32 * WARPS_PER_BLOCK;
pub const WINDOW_CELLS: u32 = 27;
pub const SOURCE_NONE: u16 = u16::MAX;
pub const PROGRAM_CAPACITY: usize = 175;
pub const SOURCE_CAPACITY: usize = 59;
pub const SLOT_CAPACITY: usize = 6;
pub const IMMEDIATE_CAPACITY: usize = 7;
pub const KERNEL_ARGUMENT_CEILING_BYTES: usize = 32_764;

pub const ORIGIN_READ_BASE: u8 = 0;
pub const ORIGIN_READ_EXT: u8 = 1;
pub const ORIGIN_PROCEDURAL: u8 = 2;
pub const PROCEDURAL_NONE: u8 = u8::MAX;

pub const SOURCE_CLASS_BF_DIRECT: u8 = 0;
pub const SOURCE_CLASS_E4_DIRECT: u8 = 3;
pub const SOURCE_CLASS_PROCEDURAL: u8 = 4;
pub const C_INIT_NONE: u32 = u32::MAX;

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WindowEqSizes {
    pub high: [u32; 2],
    pub low: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct WindowAddrSlot {
    pub base: *const u8,
    pub log2_stride: u8,
    pub origin: u8,
    pub procedural_kind: u8,
    pub reserved: [u8; 5],
}

impl Default for WindowAddrSlot {
    fn default() -> Self {
        Self {
            base: core::ptr::null(),
            log2_stride: 0,
            origin: ORIGIN_READ_BASE,
            procedural_kind: PROCEDURAL_NONE,
            reserved: [0; 5],
        }
    }
}

#[repr(C, align(4))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WindowSourceRecord {
    pub packed: u32,
}

impl WindowSourceRecord {
    pub const fn new(window: u16, column: u16) -> Self {
        Self {
            packed: (window as u32) | ((column as u32) << 16),
        }
    }

    pub const fn window(self) -> u16 {
        self.packed as u16
    }

    pub const fn column(self) -> u16 {
        (self.packed >> 16) as u16
    }
}

#[repr(C, align(8))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WindowBaseRecord {
    pub base: *const u8,
}

impl Default for WindowBaseRecord {
    fn default() -> Self {
        Self {
            base: core::ptr::null(),
        }
    }
}

#[repr(C, align(8))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct WindowInstruction {
    pub term_class: u16,
    pub factor: u16,
    pub source_a: u16,
    pub source_b: u16,
}

#[repr(C, align(16))]
#[derive(Clone, Copy, Debug)]
pub struct WindowVmDesc {
    pub program: [WindowInstruction; PROGRAM_CAPACITY],
    pub sources: [WindowSourceRecord; SOURCE_CAPACITY],
    pub window_bases: [WindowBaseRecord; SLOT_CAPACITY],
    pub immediates: [u32; IMMEDIATE_CAPACITY],
    pub eq_low: *const E4,
    pub partials: *mut E4,
    pub program_records: u32,
    pub term_count: u32,
    pub record_count: u32,
    pub num_sources: u32,
    pub num_immediates: u32,
    pub num_coefficients: u32,
    pub c_init_coeff: u32,
    pub log_rows: u32,
    pub eq_sizes: WindowEqSizes,
}

const _: () = {
    use core::mem::{align_of, offset_of, size_of};

    assert!(size_of::<BF>() == 4);
    assert!(size_of::<E4>() == 16);
    assert!(size_of::<WindowEqSizes>() == 12);
    assert!(size_of::<WindowAddrSlot>() == 16);
    assert!(align_of::<WindowAddrSlot>() == 8);
    assert!(offset_of!(WindowAddrSlot, base) == 0);
    assert!(offset_of!(WindowAddrSlot, log2_stride) == 8);
    assert!(offset_of!(WindowAddrSlot, origin) == 9);
    assert!(offset_of!(WindowAddrSlot, procedural_kind) == 10);
    assert!(offset_of!(WindowAddrSlot, reserved) == 11);
    assert!(size_of::<WindowSourceRecord>() == 4);
    assert!(align_of::<WindowSourceRecord>() == 4);
    assert!(offset_of!(WindowSourceRecord, packed) == 0);
    assert!(size_of::<WindowBaseRecord>() == 8);
    assert!(align_of::<WindowBaseRecord>() == 8);
    assert!(offset_of!(WindowBaseRecord, base) == 0);
    assert!(size_of::<WindowInstruction>() == 8);
    assert!(align_of::<WindowInstruction>() == 8);
    assert!(offset_of!(WindowInstruction, term_class) == 0);
    assert!(offset_of!(WindowInstruction, factor) == 2);
    assert!(offset_of!(WindowInstruction, source_a) == 4);
    assert!(offset_of!(WindowInstruction, source_b) == 6);
    assert!(PROGRAM_CAPACITY == 175);
    assert!(SOURCE_CAPACITY == 59);
    assert!(SLOT_CAPACITY == 6);
    assert!(IMMEDIATE_CAPACITY == 7);
    assert!(size_of::<WindowVmDesc>() == 1_792);
    assert!(size_of::<WindowVmDesc>() <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(align_of::<WindowVmDesc>() == 16);
    assert!(offset_of!(WindowVmDesc, program) == 0);
    assert!(offset_of!(WindowVmDesc, sources) == 1_400);
    assert!(offset_of!(WindowVmDesc, window_bases) == 1_640);
    assert!(offset_of!(WindowVmDesc, immediates) == 1_688);
    assert!(offset_of!(WindowVmDesc, eq_low) == 1_720);
    assert!(offset_of!(WindowVmDesc, partials) == 1_728);
    assert!(offset_of!(WindowVmDesc, program_records) == 1_736);
    assert!(offset_of!(WindowVmDesc, term_count) == 1_740);
    assert!(offset_of!(WindowVmDesc, record_count) == 1_744);
    assert!(offset_of!(WindowVmDesc, num_sources) == 1_748);
    assert!(offset_of!(WindowVmDesc, num_immediates) == 1_752);
    assert!(offset_of!(WindowVmDesc, num_coefficients) == 1_756);
    assert!(offset_of!(WindowVmDesc, c_init_coeff) == 1_760);
    assert!(offset_of!(WindowVmDesc, log_rows) == 1_764);
    assert!(offset_of!(WindowVmDesc, eq_sizes) == 1_768);
    assert!(THREADS_PER_BLOCK == 288);
    assert!(WINDOW_CELLS == 3 * WARPS_PER_BLOCK);
};

#[cfg(test)]
mod tests {
    use core::mem::{align_of, offset_of, size_of};

    use super::*;

    #[test]
    fn instruction_is_one_aligned_eight_byte_record() {
        assert_eq!(size_of::<WindowInstruction>(), 8);
        assert_eq!(align_of::<WindowInstruction>(), 8);
        assert_eq!(offset_of!(WindowInstruction, term_class), 0);
        assert_eq!(offset_of!(WindowInstruction, factor), 2);
        assert_eq!(offset_of!(WindowInstruction, source_a), 4);
        assert_eq!(offset_of!(WindowInstruction, source_b), 6);
        assert_eq!(PROGRAM_CAPACITY, 175);
    }

    #[test]
    fn address_slot_matches_the_segmented_vm_layout() {
        assert_eq!(size_of::<WindowAddrSlot>(), 16);
        assert_eq!(align_of::<WindowAddrSlot>(), 8);
        assert_eq!(offset_of!(WindowAddrSlot, base), 0);
        assert_eq!(offset_of!(WindowAddrSlot, log2_stride), 8);
        assert_eq!(offset_of!(WindowAddrSlot, origin), 9);
        assert_eq!(offset_of!(WindowAddrSlot, procedural_kind), 10);
        assert_eq!(offset_of!(WindowAddrSlot, reserved), 11);
    }

    #[test]
    fn source_record_is_a_compact_window_column_pair() {
        assert_eq!(size_of::<WindowSourceRecord>(), 4);
        assert_eq!(align_of::<WindowSourceRecord>(), 4);
        assert_eq!(offset_of!(WindowSourceRecord, packed), 0);
        let record = WindowSourceRecord::new(0x1234, 0xabcd);
        assert_eq!(record.window(), 0x1234);
        assert_eq!(record.column(), 0xabcd);
        assert_eq!(size_of::<WindowBaseRecord>(), 8);
        assert_eq!(align_of::<WindowBaseRecord>(), 8);
        assert_eq!(offset_of!(WindowBaseRecord, base), 0);
    }

    #[test]
    fn descriptor_layout_is_pinned() {
        assert_eq!(size_of::<WindowEqSizes>(), 12);
        assert_eq!(PROGRAM_CAPACITY, 175);
        assert_eq!(SOURCE_CAPACITY, 59);
        assert_eq!(SLOT_CAPACITY, 6);
        assert_eq!(IMMEDIATE_CAPACITY, 7);
        assert_eq!(size_of::<WindowVmDesc>(), 1_792);
        assert!(size_of::<WindowVmDesc>() <= KERNEL_ARGUMENT_CEILING_BYTES);
        assert_eq!(align_of::<WindowVmDesc>(), 16);
        assert_eq!(offset_of!(WindowVmDesc, program), 0);
        assert_eq!(offset_of!(WindowVmDesc, sources), 1_400);
        assert_eq!(offset_of!(WindowVmDesc, window_bases), 1_640);
        assert_eq!(offset_of!(WindowVmDesc, immediates), 1_688);
        assert_eq!(offset_of!(WindowVmDesc, eq_low), 1_720);
        assert_eq!(offset_of!(WindowVmDesc, partials), 1_728);
        assert_eq!(offset_of!(WindowVmDesc, program_records), 1_736);
        assert_eq!(offset_of!(WindowVmDesc, term_count), 1_740);
        assert_eq!(offset_of!(WindowVmDesc, record_count), 1_744);
        assert_eq!(offset_of!(WindowVmDesc, num_sources), 1_748);
        assert_eq!(offset_of!(WindowVmDesc, num_immediates), 1_752);
        assert_eq!(offset_of!(WindowVmDesc, num_coefficients), 1_756);
        assert_eq!(offset_of!(WindowVmDesc, c_init_coeff), 1_760);
        assert_eq!(offset_of!(WindowVmDesc, log_rows), 1_764);
        assert_eq!(offset_of!(WindowVmDesc, eq_sizes), 1_768);
    }

    #[test]
    fn launch_geometry_is_one_warp_per_output_triplet() {
        assert_eq!(WARPS_PER_BLOCK, 9);
        assert_eq!(THREADS_PER_BLOCK, 288);
        assert_eq!(WINDOW_CELLS, 27);
    }
}
