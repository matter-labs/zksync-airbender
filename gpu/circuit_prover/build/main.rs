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
    let deterministic_pow = std::env::var_os("CARGO_FEATURE_DETERMINISTIC_POW").is_some();
    let enable_lineinfo = std::env::var_os("GPU_PROVER_ENABLE_LINEINFO").is_some();
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_BENCH");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_DETERMINISTIC_POW");
    println!("cargo:rerun-if-env-changed=GPU_PROVER_ENABLE_LINEINFO");
    emit_rerun_if_changed_recursive(Path::new("build"));
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
        // nvtx.c is now compiled by gpu_core's build.rs (gpu_core owns nvtx.rs).
        // gpu_core emits cargo:rustc-link-lib=static=gpu_prover_nvtx which Cargo
        // propagates to circuit_prover; no duplicate compilation needed here.
        let cudaarchs = var("CUDAARCHS").unwrap_or("native".to_string());
        let mut config = cmake::Config::new("native");
        config.profile("Release");
        config.define("CMAKE_CUDA_ARCHITECTURES", cudaarchs);
        if let Ok(inc) = std::env::var("DEP_GPU_CORE_NATIVE_INCLUDE") {
            config.define("GPU_CORE_NATIVE_INCLUDE", &inc);
        }
        // gpu_hash exports `hash.cuh`; the remaining blake2s-dependent kernels
        // here (`ops/gkr_ops*`) `#include "hash.cuh"`.
        if let Ok(inc) = std::env::var("DEP_GPU_HASH_NATIVE_INCLUDE") {
            config.define("GPU_HASH_NATIVE_INCLUDE", &inc);
        }
        let build_bench = if var("CARGO_FEATURE_BENCH").is_ok() {
            "ON"
        } else {
            "OFF"
        };
        config.define("GPU_PROVER_BUILD_BENCH", build_bench);
        config.define(
            "GPU_PROVER_ENABLE_LINEINFO",
            if enable_lineinfo { "ON" } else { "OFF" },
        );
        if deterministic_pow {
            config.define("AB_DETERMINISTIC_POW", "ON");
        }
        let dst = config.build();
        let circuit_prover_native_path = dst.to_str().unwrap();
        println!("cargo:rustc-link-search=native={circuit_prover_native_path}");
        println!("cargo:rustc-link-lib=static=circuit_prover_native");
        let cuda_lib_path = get_cuda_lib_path().unwrap();
        let cuda_lib_path_str = cuda_lib_path.to_str().unwrap();
        println!("cargo:rustc-link-search=native={cuda_lib_path_str}");
        println!("cargo:rustc-link-lib=cudart");
        #[cfg(target_os = "linux")]
        println!("cargo:rustc-link-lib=stdc++");
    }
}
