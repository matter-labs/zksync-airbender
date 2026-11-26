fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    let macos = std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("macos");
    let gpu = std::env::var_os("CARGO_FEATURE_GPU").is_some();
    assert!(
        !(macos && gpu),
        "prover_pipeline: feature gpu requires CUDA, which is unavailable on macOS"
    );
}
