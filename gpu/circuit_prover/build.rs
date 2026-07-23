fn main() {
    // No native archive anymore — the kernels live in gpu_trace/gpu_gkr/gpu_whir.
    // Apex tests still carry #[cfg(not(no_cuda))] sites, so declare the cfg here.
    gpu_native_build::emit_no_cuda_cfg();
}
