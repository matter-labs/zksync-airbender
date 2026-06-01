/// Minimal build script for gpu_core.
///
/// Compiles the NVTX C wrapper (`native/nvtx.c`) so that the
/// `#[link(name = "gpu_prover_nvtx")]` directive in `primitives/nvtx.rs`
/// resolves when gpu_core is tested or used standalone.  No CUDA kernel
/// compilation occurs here; this is plain C only.
fn main() {
    use std::env;

    // NVTX headers live in the CUDA include tree.
    let cuda_include = env::var("CUDA_PATH")
        .map(|p| format!("{p}/include"))
        .unwrap_or_else(|_| "/usr/local/cuda/include".to_owned());

    cc::Build::new()
        .file("native/nvtx.c")
        .include(&cuda_include)
        .compile("gpu_prover_nvtx");

    println!("cargo:rerun-if-changed=native/nvtx.c");

    let headers = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("native_headers");
    println!("cargo:include={}", headers.display());
    println!("cargo:rerun-if-changed=native_headers");
}
