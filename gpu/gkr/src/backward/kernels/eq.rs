use crate::backward::kernels::launchers::GkrEqSizes;

pub(crate) fn max_partials_len(max_acc_size: usize) -> usize {
    2 * max_acc_size.div_ceil(32).max(1)
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
