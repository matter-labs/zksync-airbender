fn main() {
    // `gpu_trace_native` is the witness-generation CUDA archive (the `airbender::
    // trace::witness::*` kernels). It is fully self-contained: it needs only the
    // gpu_core base headers (forwarded as `DEP_GPU_CORE_NATIVE_INCLUDE`) plus its
    // own local headers and the committed generated witness bodies under
    // `circuit_defs/**/generated/`. No `export_include` — nothing includes the
    // witness headers cross-crate; no `deterministic_pow` — this archive has no
    // PoW kernel (that lives in gpu_hash).
    gpu_native_build::CudaArchive::new("gpu_trace_native", "GPU_TRACE").build();
}
