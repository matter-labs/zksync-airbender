pub mod context;
pub mod hypercube;
pub mod lde;
pub mod pack;

pub use context::{DeviceContext, TwiddleDescriptor};
pub use hypercube::hypercube_evals_to_monomials;
pub use lde::{lde_coset, lde_cosets_batched};
pub use pack::pack_hypercubes_to_monomials;

use era_cudart::slice::DeviceSlice;
use gpu_core::primitives::device_structures::DeviceMatrixChunkImpl;
use gpu_core::primitives::field::PR;
use std::ops::Range;

pub(crate) fn validate_slice(values: &DeviceSlice<PR>, name: &str) -> Range<usize> {
    let start = values.as_ptr() as usize;
    assert_eq!(
        start % 16,
        0,
        "{name}: base pointer must be 16-byte aligned"
    );
    let bytes = values
        .len()
        .checked_mul(size_of::<PR>())
        .unwrap_or_else(|| panic!("{name}: byte length overflow"));
    let end = start
        .checked_add(bytes)
        .unwrap_or_else(|| panic!("{name}: address overflow"));
    start..end
}

pub(crate) fn validate_matrix(
    values: &(impl DeviceMatrixChunkImpl<PR> + ?Sized),
    min_log: u32,
    max_log: u32,
    name: &str,
) -> (u32, Range<usize>) {
    assert!(
        values.rows().is_power_of_two(),
        "{name}: rows must be a power of two"
    );
    let log_n = values.rows().trailing_zeros();
    assert!(
        (min_log..=max_log).contains(&log_n),
        "{name}: log_n {log_n} outside {min_log}..={max_log}"
    );
    assert!(
        values.stride() >= values.rows(),
        "{name}: stride is smaller than rows"
    );
    let row_end = values
        .offset()
        .checked_add(values.rows())
        .unwrap_or_else(|| panic!("{name}: row offset overflow"));
    assert!(
        row_end <= values.stride(),
        "{name}: rows extend beyond stride"
    );
    let backing = validate_slice(values.slice(), name);
    let cols = values.cols();
    let end = if cols == 0 {
        values.offset()
    } else {
        (cols - 1)
            .checked_mul(values.stride())
            .and_then(|column| column.checked_add(row_end))
            .unwrap_or_else(|| panic!("{name}: matrix span overflow"))
    };
    assert!(
        end <= values.slice().len(),
        "{name}: matrix span exceeds backing slice"
    );
    let start_bytes = values
        .offset()
        .checked_mul(size_of::<PR>())
        .unwrap_or_else(|| panic!("{name}: byte offset overflow"));
    let end_bytes = end
        .checked_mul(size_of::<PR>())
        .unwrap_or_else(|| panic!("{name}: byte span overflow"));
    let start = backing
        .start
        .checked_add(start_bytes)
        .unwrap_or_else(|| panic!("{name}: start address overflow"));
    let end = backing
        .start
        .checked_add(end_bytes)
        .unwrap_or_else(|| panic!("{name}: end address overflow"));
    (log_n, start..end)
}

pub(crate) fn validate_disjoint(left: &Range<usize>, right: &Range<usize>, message: &str) {
    assert!(
        left.is_empty() || right.is_empty() || left.end <= right.start || right.end <= left.start,
        "{message}"
    );
}

pub(crate) fn validate_context_log(context: &DeviceContext, log_n: u32) {
    let domain_log = context.log_max_domain();
    assert!(
        log_n <= domain_log,
        "Proth120 NTT: log_n {log_n} exceeds context log_max_domain {domain_log}"
    );
}

#[cfg(test)]
mod tests;
