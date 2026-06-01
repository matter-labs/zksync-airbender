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
    let enable_lineinfo = std::env::var_os("GPU_OPS_ENABLE_LINEINFO").is_some();
    println!("cargo:rerun-if-env-changed=GPU_OPS_ENABLE_LINEINFO");
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
            "GPU_OPS_ENABLE_LINEINFO",
            if enable_lineinfo { "ON" } else { "OFF" },
        );
        let dst = config.build();
        let gpu_ops_native_path = dst.to_str().unwrap();
        println!("cargo:rustc-link-search=native={gpu_ops_native_path}");
        println!("cargo:rustc-link-lib=static=gpu_ops_archive");
        let cuda_lib_path = get_cuda_lib_path().unwrap();
        let cuda_lib_path_str = cuda_lib_path.to_str().unwrap();
        println!("cargo:rustc-link-search=native={cuda_lib_path_str}");
        println!("cargo:rustc-link-lib=cudart");
        #[cfg(target_os = "linux")]
        println!("cargo:rustc-link-lib=stdc++");
    }
}
