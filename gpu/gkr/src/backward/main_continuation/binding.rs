//! Runtime storage binding for the width-three MAIN continuation window.

pub(crate) fn pointer_ranges_overlap(
    first: *const u8,
    first_bytes: usize,
    second: *const u8,
    second_bytes: usize,
) -> bool {
    let first_start = first as usize;
    let second_start = second as usize;
    let Some(first_end) = first_start.checked_add(first_bytes) else {
        return true;
    };
    let Some(second_end) = second_start.checked_add(second_bytes) else {
        return true;
    };
    first_start < second_end && second_start < first_end
}
