fn main() {
    // export_include(true): whir's kernels (still in gpu_circuit_prover) include
    // this crate's `gkr/support/{eq_inline,kernel_helpers}.cuh` (which pull in
    // `descriptors.cuh`) via DEP_GPU_GKR_NATIVE_INCLUDE. The gkr archive itself
    // owns all 8 `__constant__` symbols; nothing device-side crosses the archive
    // boundary (whir reads only the pointer-based inline helpers + compile-time
    // constants, never a `__constant__` symbol).
    gpu_native_build::CudaArchive::new("gpu_gkr_native", "GPU_GKR")
        .export_include(true)
        .build();
}
