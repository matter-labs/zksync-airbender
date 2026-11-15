use gpu_core::primitives::field::E4;

use crate::backward::kernels::launchers::{GkrEqSizes, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS};

pub(crate) fn resolve_active_eq_slot(eq_sizes: &GkrEqSizes, eq_low: *mut E4) -> (*mut E4, u32) {
    if eq_sizes.low > 0 {
        (eq_low, eq_sizes.low)
    } else if eq_sizes.high[1] > 0 {
        const { assert!(GKR_EQ_HIGH_SLOTS >= 2) };
        let base = unsafe {
            crate::baby_bear::backward::kernels::launchers::get_eq_high_constant_device_ptr()
                .add(GKR_EQ_GROUP_TABLE_LEN)
        };
        (base, eq_sizes.high[1])
    } else {
        debug_assert!(eq_sizes.high[0] >= 1);
        (
            crate::baby_bear::backward::kernels::launchers::get_eq_high_constant_device_ptr(),
            eq_sizes.high[0],
        )
    }
}
