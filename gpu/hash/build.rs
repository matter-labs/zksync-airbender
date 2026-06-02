fn main() {
    // `export_include(true)`: emit `cargo:include` for `native/hash.cuh` so the
    // blake2s-dependent kernels that stayed in `circuit_prover` (`gkr_ops.cu`,
    // `leaves.cu`) resolve `#include "hash.cuh"` via `DEP_GPU_HASH_NATIVE_INCLUDE`.
    // `deterministic_pow(true)`: honor `CARGO_FEATURE_DETERMINISTIC_POW` so the
    // GPU PoW search matches the host verifier's (mirrors `circuit_prover`).
    gpu_native_build::CudaArchive::new("gpu_hash_native", "GPU_HASH")
        .export_include(true)
        .deterministic_pow(true)
        .build();
}
