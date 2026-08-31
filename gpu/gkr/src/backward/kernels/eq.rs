use super::launchers::{GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS};
use gpu_core::primitives::field::E4;

pub(crate) fn max_partials_len(max_acc_size: usize) -> usize {
    2 * max_acc_size.div_ceil(32).max(1)
}

pub(crate) fn resolve_active_eq_slot(eq_sizes: &GkrEqSizes, eq_low: *mut E4) -> (*mut E4, u32) {
    if eq_sizes.low > 0 {
        (eq_low, eq_sizes.low)
    } else if eq_sizes.high[1] > 0 {
        const { assert!(GKR_EQ_HIGH_SLOTS >= 2) };
        let base = unsafe {
            super::launchers::get_eq_high_constant_device_ptr().add(GKR_EQ_GROUP_TABLE_LEN)
        };
        (base, eq_sizes.high[1])
    } else {
        debug_assert!(eq_sizes.high[0] >= 1);
        (
            super::launchers::get_eq_high_constant_device_ptr(),
            eq_sizes.high[0],
        )
    }
}

pub(crate) fn record_active_eq_slot_fold(eq_sizes: &mut GkrEqSizes) {
    if eq_sizes.low > 0 {
        eq_sizes.low -= 1;
    } else if eq_sizes.high[1] > 0 {
        eq_sizes.high[1] -= 1;
    } else {
        debug_assert!(eq_sizes.high[0] >= 1, "the factored eq drained past empty");
        eq_sizes.high[0] -= 1;
    }
}
