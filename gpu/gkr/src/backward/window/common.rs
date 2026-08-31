use core::mem::{align_of, size_of};

use gpu_gkr_compiler::{
    CoefficientRecipeId, KIND_ORDER, MAX_BACKWARD_COEFFICIENT_RECIPES, MAX_COEFFICIENT_ENCODINGS,
    MAX_SOURCE_WINDOWS, SOURCE_NONE, SOURCE_WINDOW_COLUMNS, WINDOW_COEFFICIENT_BANK_BIAS,
    WINDOW_MAX_COEFFICIENT_PLANS,
};

pub(crate) const BWD_COEFF_BANK_CAPACITY: usize = 1_792;
pub(crate) const BWD_COEFF_NONE: u32 = u32::MAX;
pub(crate) const BWD_SOURCE_WINDOW_SLOTS: usize = 64;
pub(crate) const BWD_FOLD_WEIGHT_SLOTS: usize = 11;

const _: () = {
    assert!(BWD_SOURCE_WINDOW_SLOTS == MAX_SOURCE_WINDOWS);
    assert!(
        BWD_COEFF_BANK_CAPACITY
            >= MAX_BACKWARD_COEFFICIENT_RECIPES + CoefficientRecipeId::RESERVED as usize
    );
    assert!(
        BWD_COEFF_BANK_CAPACITY
            >= WINDOW_MAX_COEFFICIENT_PLANS + WINDOW_COEFFICIENT_BANK_BIAS as usize
    );
    assert!(BWD_COEFF_BANK_CAPACITY <= MAX_COEFFICIENT_ENCODINGS);
    assert!(BWD_COEFF_BANK_CAPACITY * size_of::<gpu_core::primitives::field::E4>() == 28 * 1_024);
};

pub(crate) const BWD_COEFF_ORIGIN_READ_BASE: u8 = 0;
pub(crate) const BWD_COEFF_ORIGIN_READ_EXT: u8 = 1;
pub(crate) const BWD_COEFF_ORIGIN_PROCEDURAL: u8 = 2;
pub(crate) const BWD_COEFF_PROCEDURAL_NONE: u8 = 0xff;
pub(crate) const BWD_COEFF_PROCEDURAL_KINDS: usize = KIND_ORDER.len();

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct BwdSourceWindow {
    pub base: *const u8,
    pub log2_stride: u8,
    pub origin: u8,
    pub procedural_kind: u8,
    pub reserved: [u8; 5],
}

const _: () = {
    use core::mem::offset_of;

    assert!(size_of::<BwdSourceWindow>() == 16);
    assert!(align_of::<BwdSourceWindow>() == 8);
    assert!(offset_of!(BwdSourceWindow, base) == 0);
    assert!(offset_of!(BwdSourceWindow, log2_stride) == 8);
    assert!(offset_of!(BwdSourceWindow, origin) == 9);
    assert!(offset_of!(BwdSourceWindow, procedural_kind) == 10);
    assert!(offset_of!(BwdSourceWindow, reserved) == 11);
};

pub(crate) const BWD_SOURCE_LANE_COLUMN_BITS: u32 = 7;
pub(crate) const BWD_SOURCE_LANE_NONE: u16 = SOURCE_NONE;

pub(crate) fn bwd_source_lane(slot: usize, column: usize) -> Option<u16> {
    if slot >= BWD_SOURCE_WINDOW_SLOTS || column >= SOURCE_WINDOW_COLUMNS {
        return None;
    }
    Some(((slot << BWD_SOURCE_LANE_COLUMN_BITS) | column) as u16)
}

const _: () = {
    assert!(SOURCE_WINDOW_COLUMNS == 1 << BWD_SOURCE_LANE_COLUMN_BITS);
    assert!(
        (BWD_SOURCE_WINDOW_SLOTS << BWD_SOURCE_LANE_COLUMN_BITS) <= BWD_SOURCE_LANE_NONE as usize
    );
};
