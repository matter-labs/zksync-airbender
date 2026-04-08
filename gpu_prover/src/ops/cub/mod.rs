pub mod device_radix_sort;
pub mod device_reduce;
pub mod device_run_length_encode;
pub mod device_scan;

// Match the strong alignment callers typically get from raw CUDA allocations for opaque temp
// storage that CUB or vectorized device code may reinterpret internally.
pub const CUB_TEMP_STORAGE_EXTRA_ALIGNMENT_LOG2: u32 = 8;
