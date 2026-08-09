use std::path::Path;

fn main() {
    // gpu_core is a dev-dependency here (crate-root serial guard only), so there is
    // no DEP_GPU_CORE_NATIVE_INCLUDE to auto-forward — pass the header dir directly.
    let native_headers = Path::new(env!("CARGO_MANIFEST_DIR")).join("../core/native_headers");
    // gpu_native_build only tracks this crate's own `native/` tree, so without this
    // an edit to a shared gpu_core header would leave a stale CUDA archive linked.
    // Emitted per file: a bare directory path catches entry add/remove, not content edits.
    rerun_if_changed_recursive(&native_headers);
    // Window diagnostics (chain-execution counter + slot poison) are compile-gated OFF:
    // the shipped build must emit the same SASS as without them.
    println!("cargo:rerun-if-env-changed=GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG");
    println!("cargo:rustc-check-cfg=cfg(window_diag)");
    // ALWAYS passed, "ON" or "OFF": a define that is only passed when set STICKS in the
    // CMake cache, so an env-unset rebuild after a diagnostic one would keep compiling the
    // counter atomic while the host side (gated by the cfg below) refuses the probes — a
    // binary that looks shipped, times like a diagnostic build, and puts `w` in the wrong
    // occupancy class. CMake reads "OFF" as false, so the cache is always truthful.
    let diag = std::env::var_os("GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG").is_some();
    if diag {
        println!("cargo:rustc-cfg=window_diag");
    }
    gpu_native_build::CudaArchive::new("gpu_gkr_uniskip_bench_native", "GPU_GKR_UNISKIP_BENCH")
        .define("GPU_CORE_NATIVE_INCLUDE", native_headers.to_str().unwrap())
        .define("AB_UNISKIP_WINDOW_DIAG", if diag { "ON" } else { "OFF" })
        .build();
}

fn rerun_if_changed_recursive(path: &Path) {
    println!("cargo:rerun-if-changed={}", path.display());
    if path.is_dir() {
        let mut entries = std::fs::read_dir(path)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()))
            .collect::<Result<Vec<_>, _>>()
            .unwrap_or_else(|err| panic!("failed to enumerate {}: {err}", path.display()));
        entries.sort_by_key(|entry| entry.path());
        for entry in entries {
            rerun_if_changed_recursive(&entry.path());
        }
    }
}
