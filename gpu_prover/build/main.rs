#![allow(unexpected_cfgs)]

use era_cudart_sys::{get_cuda_lib_path, get_cuda_version, is_no_cuda, no_cuda_message};
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
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_BENCH");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_DETERMINISTIC_POW");
    emit_rerun_if_changed_recursive(Path::new("build"));
    emit_rerun_if_changed_recursive(Path::new("native"));
    if is_no_cuda() {
        println!("cargo::warning={}", no_cuda_message!());
        println!("cargo::rustc-cfg=no_cuda");
    } else {
        use std::env::var;
        let cuda_version =
            get_cuda_version().expect("Failed to determine the CUDA Toolkit version.");
        if !(cuda_version.starts_with("12.") || cuda_version.starts_with("13.")) {
            println!("cargo::warning=CUDA Toolkit version {cuda_version} detected. This crate is only tested with CUDA Toolkit versions 12.* and 13.*.");
        }
        let cudaarchs = var("CUDAARCHS").unwrap_or("native".to_string());
        let mut config = cmake::Config::new("native");
        config.profile("Release");
        config.define("CMAKE_CUDA_ARCHITECTURES", cudaarchs);
        let build_bench = if var("CARGO_FEATURE_BENCH").is_ok() {
            "ON"
        } else {
            "OFF"
        };
        config.define("GPU_PROVER_BUILD_BENCH", build_bench);
        if deterministic_pow {
            config.define("AB_DETERMINISTIC_POW", "ON");
        }
        let dst = config.build();
        let gpu_prover_native_path = dst.to_str().unwrap();
        println!("cargo:rustc-link-search=native={gpu_prover_native_path}");
        println!("cargo:rustc-link-lib=static=gpu_prover_native");
        let cuda_lib_path = get_cuda_lib_path().unwrap();
        let cuda_lib_path_str = cuda_lib_path.to_str().unwrap();
        println!("cargo:rustc-link-search=native={cuda_lib_path_str}");
        println!("cargo:rustc-link-lib=cudart");
        #[cfg(target_os = "linux")]
        println!("cargo:rustc-link-lib=stdc++");
    }
}
