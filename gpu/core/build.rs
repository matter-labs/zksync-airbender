/// Build script for gpu_core.
///
/// Compiles the NVTX C wrapper (`native/nvtx.c`) so that the
/// `#[link(name = "gpu_core_nvtx")]` directive in `primitives/nvtx.rs` resolves
/// when gpu_core is tested or used standalone. Plain C, but not CUDA-free: it
/// includes `nvtx3/nvToolsExt.h` from the Toolkit, hence the `no_cuda` skip.
///
/// gpu_core has no production kernels. Its CUDA archive (`gpu_core_native`)
/// holds the Proth120 field-header probes that its tests launch and, under the
/// `bench` feature, the BabyBear field micro-benchmark kernels.
fn main() {
    use std::env;

    // Toolkit absent → the wrapper cannot compile; `primitives/nvtx.rs` swaps the
    // `#[link]`ed externs for stubs, so nothing references the archive.
    if !gpu_native_build::is_no_cuda() {
        // NVTX headers live in the CUDA include tree.
        let cuda_include = env::var("CUDA_PATH")
            .map(|p| format!("{p}/include"))
            .unwrap_or_else(|_| "/usr/local/cuda/include".to_owned());

        cc::Build::new()
            .file("native/nvtx.c")
            .include(&cuda_include)
            .compile("gpu_core_nvtx");
    }

    println!("cargo:rerun-if-changed=native/nvtx.c");

    let headers = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("native_headers");
    println!("cargo:include={}", headers.display());
    println!("cargo:rerun-if-changed=native_headers");

    // The archive's kernels include gpu_core's own headers; there is no
    // `DEP_GPU_CORE_NATIVE_INCLUDE` for gpu_core itself, so pass it explicitly.
    let mut archive = gpu_native_build::CudaArchive::new("gpu_core_native", "GPU_CORE").define(
        "GPU_CORE_NATIVE_INCLUDE",
        headers
            .to_str()
            .expect("native_headers path must be valid UTF-8"),
    );
    if env::var_os("CARGO_FEATURE_BENCH").is_some() {
        archive = archive.define("GPU_CORE_BUILD_BENCH", "ON");
    }
    archive.build();
}
