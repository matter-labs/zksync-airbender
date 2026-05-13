pub mod device_radix_sort;
pub mod device_reduce;
pub mod device_run_length_encode;

// Match the strong alignment callers typically get from raw CUDA allocations for opaque temp
// storage that CUB or vectorized device code may reinterpret internally.
pub(crate) const CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2: u32 = 8;
