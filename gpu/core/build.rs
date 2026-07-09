/// Build script for gpu_core.
///
/// Always compiles the NVTX C wrapper (`native/nvtx.c`) so that the
/// `#[link(name = "gpu_core_nvtx")]` directive in `primitives/nvtx.rs` resolves
/// when gpu_core is tested or used standalone — plain C, no CUDA.
///
/// Under the `bench` feature it additionally builds the field micro-benchmark
/// CUDA archive (`native/bench/field.cu` → `gpu_core_bench_native`). gpu_core
/// has no production kernels, so this is the crate's only CUDA compilation and
/// is entirely bench-gated.
fn main() {
    use std::env;

    // NVTX headers live in the CUDA include tree.
    let cuda_include = env::var("CUDA_PATH")
        .map(|p| format!("{p}/include"))
        .unwrap_or_else(|_| "/usr/local/cuda/include".to_owned());

    cc::Build::new()
        .file("native/nvtx.c")
        .include(&cuda_include)
        .compile("gpu_core_nvtx");

    println!("cargo:rerun-if-changed=native/nvtx.c");

    let headers = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("native_headers");
    println!("cargo:include={}", headers.display());
    println!("cargo:rerun-if-changed=native_headers");

    // The bench kernels `#include "primitives/field.cuh"`, so the archive needs
    // gpu_core's own `native_headers` on its include path — there is no
    // `DEP_GPU_CORE_NATIVE_INCLUDE` for gpu_core itself, so pass it explicitly.
    if env::var_os("CARGO_FEATURE_BENCH").is_some() {
        gpu_native_build::CudaArchive::new("gpu_core_bench_native", "GPU_CORE")
            .define(
                "GPU_CORE_NATIVE_INCLUDE",
                headers
                    .to_str()
                    .expect("native_headers path must be valid UTF-8"),
            )
            .build();
    }
}
