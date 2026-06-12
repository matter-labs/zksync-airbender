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
    let mut archive = gpu_native_build::CudaArchive::new("circuit_prover_native", "GPU_PROVER")
        .deterministic_pow(true);
    // The `bench` feature compiles the GKR eval-ISA bench kernels
    // (`native/bench/`) into `circuit_prover_native` itself (same archive,
    // gated contents). They must share the
    // device-link module with the production kernels (the interpreter reads
    // `__constant__` symbols like `ab_gkr_lookup_gamma_consts` defined there),
    // so this is a CMake option on `circuit_prover_native`, not a separate
    // archive.
    if std::env::var_os("CARGO_FEATURE_BENCH").is_some() {
        archive = archive.define("AB_GKR_BENCH", "ON");
    }
    archive.build();
}
