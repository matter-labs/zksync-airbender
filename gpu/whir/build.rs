fn main() {
    // The WHIR/PoW protocol kernels. `accumulate_eq.cu` includes gpu_gkr's
    // `gkr/support/{eq_inline,kernel_helpers}.cuh` via DEP_GPU_GKR_NATIVE_INCLUDE
    // (gpu_gkr's build.rs `export_include(true)` emits it, auto-forwarded as a
    // CMake -D by gpu_native_build). `leaves.cu` includes gpu_hash's `hash.cuh`
    // and gpu_ntt's reusable WHIR leaf transform via their exported include
    // directories. `deterministic_pow` is not defined here:
    // the PoW search kernel lives in gpu_hash, so gpu_whir/deterministic_pow
    // forwards to gpu_hash/deterministic_pow instead of an AB_DETERMINISTIC_POW
    // define on this archive.
    gpu_native_build::CudaArchive::new("gpu_whir_native", "GPU_WHIR").build();
}
