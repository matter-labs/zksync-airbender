#![allow(unexpected_cfgs)]

fn main() {
    println!("cargo::rustc-check-cfg=cfg(no_cuda)");
    #[cfg(no_cuda)]
    {
        println!("cargo::warning={}", era_cudart_sys::no_cuda_message!());
    }
    #[cfg(not(no_cuda))]
    {
        use era_cudart_sys::{get_cuda_lib_path, get_cuda_version};
        use std::env::var;
        let cuda_version =
            get_cuda_version().expect("Failed to determine the CUDA Toolkit version.");
        if !(cuda_version.starts_with("12.") || cuda_version.starts_with("13.")) {
            println!("cargo::warning=CUDA Toolkit version {cuda_version} detected. This crate is only tested with CUDA Toolkit versions 12.* and 13.*.");
        }
        let cudaarchs = var("CUDAARCHS").unwrap_or("native".to_string());
        let dst = cmake::Config::new("native")
            .profile("Release")
            .define("CMAKE_CUDA_ARCHITECTURES", cudaarchs)
            .build();
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
