#![allow(unexpected_cfgs)]

use era_cudart_sys::{
    get_cuda_include_path, get_cuda_lib_path, get_cuda_version, is_no_cuda, no_cuda_message,
};
use std::fs;
use std::path::Path;

fn emit_rerun_if_changed_recursive(path: &Path) {
    println!("cargo:rerun-if-changed={}", path.display());
    if path.is_dir() {
        let mut entries = fs::read_dir(path)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()))
            .collect::<Result<Vec<_>, _>>()
            .unwrap_or_else(|err| panic!("failed to enumerate {}: {err}", path.display()));
        entries.sort_by_key(|entry| entry.path());
        for entry in entries {
            emit_rerun_if_changed_recursive(&entry.path());
        }
    }
}

fn main() {
    println!("cargo::rustc-check-cfg=cfg(no_cuda)");

    // Export the include dir holding `hash.cuh` so downstream crates that keep
    // blake2s-dependent kernels (e.g. `circuit_prover`'s `gkr_ops`) can resolve
    // `#include "hash.cuh"` via `DEP_GPU_HASH_NATIVE_INCLUDE`.
    let native = Path::new(env!("CARGO_MANIFEST_DIR")).join("native");
    println!("cargo:include={}", native.display());

    let enable_lineinfo = std::env::var_os("GPU_HASH_ENABLE_LINEINFO").is_some();
    println!("cargo:rerun-if-env-changed=GPU_HASH_ENABLE_LINEINFO");
    emit_rerun_if_changed_recursive(Path::new("native"));
    if is_no_cuda() {
        println!("cargo::warning={}", no_cuda_message!());
        println!("cargo::rustc-cfg=no_cuda");
    } else {
        use std::env::var;
        let _cuda_include_path =
            get_cuda_include_path().expect("Failed to determine the CUDA Toolkit include path.");
        const SUPPORTED_CUDA_MAJOR_PREFIXES: &[&str] = &["12.", "13."];
        let cuda_version =
            get_cuda_version().expect("Failed to determine the CUDA Toolkit version.");
        if !SUPPORTED_CUDA_MAJOR_PREFIXES
            .iter()
            .any(|p| cuda_version.starts_with(p))
        {
            println!("cargo::warning=CUDA Toolkit version {cuda_version} detected. This crate is only tested with CUDA Toolkit versions 12.* and 13.*.");
        }
        let cudaarchs = var("CUDAARCHS").unwrap_or("native".to_string());
        let mut config = cmake::Config::new("native");
        config.profile("Release");
        config.define("CMAKE_CUDA_ARCHITECTURES", cudaarchs);
        if let Ok(inc) = std::env::var("DEP_GPU_CORE_NATIVE_INCLUDE") {
            config.define("GPU_CORE_NATIVE_INCLUDE", &inc);
        }
        config.define(
            "GPU_HASH_ENABLE_LINEINFO",
            if enable_lineinfo { "ON" } else { "OFF" },
        );
        // The `ab_blake2s_pow_kernel` in `native/hash.cu` is `#ifdef
        // AB_DETERMINISTIC_POW`-gated; mirror `circuit_prover`'s deterministic-PoW
        // feature so the GPU PoW search matches the host verifier's.
        if std::env::var_os("CARGO_FEATURE_DETERMINISTIC_POW").is_some() {
            config.define("AB_DETERMINISTIC_POW", "ON");
        }
        let dst = config.build();
        let gpu_hash_native_path = dst.to_str().unwrap();
        println!("cargo:rustc-link-search=native={gpu_hash_native_path}");
        println!("cargo:rustc-link-lib=static=gpu_hash_archive");
        let cuda_lib_path = get_cuda_lib_path().unwrap();
        let cuda_lib_path_str = cuda_lib_path.to_str().unwrap();
        println!("cargo:rustc-link-search=native={cuda_lib_path_str}");
        println!("cargo:rustc-link-lib=cudart");
        #[cfg(target_os = "linux")]
        println!("cargo:rustc-link-lib=stdc++");
    }
}
