fn main() {
    // The build script lives under `build/`; once any `rerun-if-changed` is
    // emitted (the shared helper emits them for `native/`), Cargo tracks only
    // the declared paths — so watch the build dir explicitly too.
    println!("cargo:rerun-if-changed=build");
    // `circuit_prover_native` links blake2s-dependent kernels (`ops/gkr_ops*`,
    // `whir/leaves`) that `#include "hash.cuh"`; the helper auto-forwards
    // `DEP_GPU_HASH_NATIVE_INCLUDE` (and `DEP_GPU_CORE_NATIVE_INCLUDE`) as CMake
    // include defines. `deterministic_pow` propagates to `AB_DETERMINISTIC_POW`
    // so the GPU PoW search matches the host verifier (proof parity).
    let archive = gpu_native_build::CudaArchive::new("circuit_prover_native", "GPU_PROVER")
        .deterministic_pow(true);
    // The Rust `bench` feature (cfg(all(test, feature = "bench"))) gates the
    // GKR eval-ISA A/B bench harness (`prover::gkr::forward::bench_interp` +
    // `vm::gpu_tests`), which drives the production v2 fwd-VM kernels — no
    // bench-only native sources remain, so this feature has no CMake side.
    archive.build();
}
