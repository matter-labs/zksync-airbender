//! Shared build-script helper for the GPU kernel crates.
//!
//! `gpu_ntt`, `gpu_ops`, `gpu_hash` (and, under its `bench` feature,
//! `gpu_core`) each compile a CUDA static archive from their `native/`
//! directory via CMake and emit the link directives. That logic is identical
//! across crates except for the archive/target name, the `*_ENABLE_LINEINFO`
//! env-var prefix, and two optional behaviors (exporting the native include
//! dir; the deterministic-PoW feature gate). This crate centralizes it so each
//! `build.rs` is a single [`CudaArchive`] call.
//!
//! It also ships the shared CMake module `cmake/ab_cuda_target.cmake` (the
//! `ab_cuda_configure_target` function that owns the common target
//! configuration), whose directory is passed to CMake as `AB_CUDA_CMAKE_DIR`.

use era_cudart_sys::{get_cuda_include_path, get_cuda_lib_path, get_cuda_version, no_cuda_message};

/// Re-exported so a kernel `build.rs` can skip Toolkit-dependent steps — including a
/// host `cc` compile, like `gpu_core`'s NVTX wrapper — without its own
/// `era_cudart_sys` build-dependency.
pub use era_cudart_sys::is_no_cuda;
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
    /// * `env_prefix` — prefix of the diagnostics toggle env vars and matching
    ///   CMake `-D`s (e.g. `"GPU_NTT"` → `GPU_NTT_ENABLE_LINEINFO`). Both
    ///   toggles are off by default; presence of the env var (any value) means
    ///   ON:
    ///     - `<PREFIX>_ENABLE_LINEINFO` — nvcc `-lineinfo` (ncu source
    ///       correlation; alters device code).
    ///     - `<PREFIX>_ENABLE_BUILD_DIAG` — nvcc `--ptxas-options=-v` +
    ///       `--keep` (per-kernel register/spill report + retained PTX/cubin
    ///       intermediates).
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
    /// Emitted unconditionally (even in `no_cuda` mode).
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
        emit_no_cuda_cfg();

        let lineinfo_var = format!("{}_ENABLE_LINEINFO", self.env_prefix);
        let enable_lineinfo = env::var_os(&lineinfo_var).is_some();
        println!("cargo:rerun-if-env-changed={lineinfo_var}");

        let build_diag_var = format!("{}_ENABLE_BUILD_DIAG", self.env_prefix);
        let enable_build_diag = env::var_os(&build_diag_var).is_some();
        println!("cargo:rerun-if-env-changed={build_diag_var}");

        emit_rerun_if_changed_recursive(Path::new("native"));

        // The shared CMake module ships with this helper crate, outside the calling
        // crate's `native/` — track it per file so edits retrigger consumers (a bare
        // directory path would only catch entry add/remove, not content edits).
        let cmake_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("cmake");
        emit_rerun_if_changed_recursive(&cmake_dir);

        if self.export_include {
            // Runtime `CARGO_MANIFEST_DIR` (the calling crate's dir), not the
            // compile-time `env!` of this helper crate.
            let manifest =
                env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR not set in build script");
            let native = Path::new(&manifest).join("native");
            println!("cargo:include={}", native.display());
        }

        if is_no_cuda() {
            println!("cargo::warning={}", no_cuda_message!());
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

        println!("cargo:rerun-if-env-changed=CUDAARCHS");
        let cudaarchs = env::var("CUDAARCHS").unwrap_or_else(|_| "native".to_string());
        let mut config = cmake::Config::new("native");
        config.profile("Release");
        config.define("CMAKE_CUDA_ARCHITECTURES", cudaarchs);
        // Forward every `DEP_<crate>_INCLUDE` (set by a dependency that emits
        // `cargo:include=`) as a CMake `-D<crate>_INCLUDE`. gpu_core →
        // `GPU_CORE_NATIVE_INCLUDE`; gpu_hash → `GPU_HASH_NATIVE_INCLUDE`; etc.
        // Kernel crates see only `GPU_CORE`; `gpu_circuit_prover` sees both.
        for (key, value) in env::vars() {
            if let Some(cmake_var) = key.strip_prefix("DEP_") {
                if cmake_var.ends_with("_INCLUDE") {
                    config.define(cmake_var, value);
                }
            }
        }
        config.define(&lineinfo_var, if enable_lineinfo { "ON" } else { "OFF" });
        config.define(
            "AB_CUDA_CMAKE_DIR",
            cmake_dir
                .to_str()
                .expect("cmake module dir must be valid UTF-8")
                // CMake include() wants forward slashes; backslashes break on Windows.
                .replace('\\', "/"),
        );
        config.define(
            &build_diag_var,
            if enable_build_diag { "ON" } else { "OFF" },
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

/// Declare (and, in no-CUDA mode, set) the `no_cuda` cfg WITHOUT building any native archive.
/// For crates that have `#[cfg(no_cuda)]`/`#[cfg(not(no_cuda))]` sites but own no CUDA code —
/// build-script cfgs do not propagate from dependencies.
pub fn emit_no_cuda_cfg() {
    println!("cargo::rustc-check-cfg=cfg(no_cuda)");
    if is_no_cuda() {
        println!("cargo::rustc-cfg=no_cuda");
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
