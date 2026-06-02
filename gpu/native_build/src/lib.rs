//! Shared build-script helper for the GPU kernel crates.
//!
//! `gpu_ntt`, `gpu_ops`, `gpu_hash`, `gpu_cub` (and, under its `bench` feature,
//! `gpu_core`) each compile a CUDA static archive from their `native/`
//! directory via CMake and emit the link directives. That logic is identical
//! across crates except for the archive/target name, the `*_ENABLE_LINEINFO`
//! env-var prefix, and two optional behaviors (exporting the native include
//! dir; the deterministic-PoW feature gate). This crate centralizes it so each
//! `build.rs` is a single [`CudaArchive`] call.
//!
//! The behavior is intentionally identical to the per-crate scripts it
//! replaced — only the duplication is removed.

use era_cudart_sys::{
    get_cuda_include_path, get_cuda_lib_path, get_cuda_version, is_no_cuda, no_cuda_message,
};
use std::env;
use std::fs;
use std::path::Path;

/// CUDA Toolkit major versions this build path is tested against.
const SUPPORTED_CUDA_MAJOR_PREFIXES: &[&str] = &["12.", "13."];

/// Describes a single CUDA static archive built from the calling crate's
/// `native/` directory.
pub struct CudaArchive {
    lib_name: String,
    env_prefix: String,
    export_include: bool,
    deterministic_pow: bool,
    extra_defines: Vec<(String, String)>,
}

impl CudaArchive {
    /// Create a builder.
    ///
    /// * `lib_name` — the CMake `add_library`/`install` target, also the static
    ///   library linked via `cargo:rustc-link-lib=static=<lib_name>` (e.g.
    ///   `"gpu_ntt_native"`).
    /// * `env_prefix` — prefix of the lineinfo toggle env var and matching
    ///   CMake `-D` (e.g. `"GPU_NTT"` → `GPU_NTT_ENABLE_LINEINFO`).
    pub fn new(lib_name: impl Into<String>, env_prefix: impl Into<String>) -> Self {
        Self {
            lib_name: lib_name.into(),
            env_prefix: env_prefix.into(),
            export_include: false,
            deterministic_pow: false,
            extra_defines: Vec::new(),
        }
    }

    /// Export the crate's `native/` directory as `cargo:include` so downstream
    /// crates can resolve `#include`s of its headers via `DEP_<LINKS>_INCLUDE`.
    /// Emitted unconditionally (even in `no_cuda` mode), matching the prior
    /// `gpu_hash` build script.
    pub fn export_include(mut self, yes: bool) -> Self {
        self.export_include = yes;
        self
    }

    /// When `true`, honor `CARGO_FEATURE_DETERMINISTIC_POW` by defining
    /// `AB_DETERMINISTIC_POW` for the CMake build.
    pub fn deterministic_pow(mut self, yes: bool) -> Self {
        self.deterministic_pow = yes;
        self
    }

    /// Forward an extra `-D<key>=<value>` to CMake — e.g. an include directory
    /// the crate provides itself rather than via a `DEP_*` env var (used by
    /// `gpu_core`'s own bench archive, which has no `DEP_GPU_CORE_NATIVE_INCLUDE`).
    pub fn define(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.extra_defines.push((key.into(), value.into()));
        self
    }

    /// Emit rerun directives, handle `no_cuda`, configure and build the CMake
    /// project under `native/`, and emit the link directives.
    pub fn build(self) {
        println!("cargo::rustc-check-cfg=cfg(no_cuda)");

        let lineinfo_var = format!("{}_ENABLE_LINEINFO", self.env_prefix);
        let enable_lineinfo = env::var_os(&lineinfo_var).is_some();
        println!("cargo:rerun-if-env-changed={lineinfo_var}");

        emit_rerun_if_changed_recursive(Path::new("native"));

        if self.export_include {
            // Runtime `CARGO_MANIFEST_DIR` (the calling crate's dir), not the
            // compile-time `env!` of this helper crate.
            let manifest = env::var("CARGO_MANIFEST_DIR")
                .expect("CARGO_MANIFEST_DIR not set in build script");
            let native = Path::new(&manifest).join("native");
            println!("cargo:include={}", native.display());
        }

        if is_no_cuda() {
            println!("cargo::warning={}", no_cuda_message!());
            println!("cargo::rustc-cfg=no_cuda");
            return;
        }

        get_cuda_include_path().expect("Failed to determine the CUDA Toolkit include path.");
        let cuda_version =
            get_cuda_version().expect("Failed to determine the CUDA Toolkit version.");
        if !SUPPORTED_CUDA_MAJOR_PREFIXES
            .iter()
            .any(|p| cuda_version.starts_with(p))
        {
            println!("cargo::warning=CUDA Toolkit version {cuda_version} detected. This crate is only tested with CUDA Toolkit versions 12.* and 13.*.");
        }

        let cudaarchs = env::var("CUDAARCHS").unwrap_or_else(|_| "native".to_string());
        let mut config = cmake::Config::new("native");
        config.profile("Release");
        config.define("CMAKE_CUDA_ARCHITECTURES", cudaarchs);
        // Forward every `DEP_<crate>_INCLUDE` (set by a dependency that emits
        // `cargo:include=`) as a CMake `-D<crate>_INCLUDE`. gpu_core →
        // `GPU_CORE_NATIVE_INCLUDE`; gpu_hash → `GPU_HASH_NATIVE_INCLUDE`; etc.
        // Kernel crates see only `GPU_CORE`; `circuit_prover` sees both.
        for (key, value) in env::vars() {
            if let Some(cmake_var) = key.strip_prefix("DEP_") {
                if cmake_var.ends_with("_INCLUDE") {
                    config.define(cmake_var, value);
                }
            }
        }
        config.define(
            &lineinfo_var,
            if enable_lineinfo { "ON" } else { "OFF" },
        );
        if self.deterministic_pow && env::var_os("CARGO_FEATURE_DETERMINISTIC_POW").is_some() {
            config.define("AB_DETERMINISTIC_POW", "ON");
        }
        for (key, value) in &self.extra_defines {
            config.define(key, value);
        }
        let dst = config.build();

        println!("cargo:rustc-link-search=native={}", dst.display());
        println!("cargo:rustc-link-lib=static={}", self.lib_name);
        let cuda_lib_path = get_cuda_lib_path().unwrap();
        println!(
            "cargo:rustc-link-search=native={}",
            cuda_lib_path.to_str().unwrap()
        );
        println!("cargo:rustc-link-lib=cudart");
        #[cfg(target_os = "linux")]
        println!("cargo:rustc-link-lib=stdc++");
    }
}

/// Emit `cargo:rerun-if-changed` for `path` and, recursively, every entry
/// beneath it (deterministically ordered).
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
