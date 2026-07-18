//! Pre-main guard forcing plain `cargo test` (libtest) to run single-threaded.
//!
//! The GPU crates carry no `#[serial]` annotations since the cargo-nextest
//! migration: under nextest, serialization comes from the `gpu-serial` test
//! group in the workspace `.config/nextest.toml`. Plain `cargo test` knows
//! nothing about that config and would run tests concurrently in threads,
//! racing the GPU. [`force_serial_libtest!`] closes that hole, fail-closed:
//! a pre-set `RUST_TEST_THREADS` is overridden, and a `--test-threads` flag
//! other than 1 aborts the binary (libtest gives the flag precedence over the
//! env var, so it cannot be neutralized any other way). Set
//! [`ALLOW_PARALLEL_ENV`] to bypass both — a deliberate, spelled-out act.
//!
//! GPU test execution in this repo is Linux-only; on other targets the macro
//! expands to nothing (there is no CUDA to race there).

/// Escape hatch: set (to any value) to run a guarded test binary with libtest
/// parallelism anyway. You are asserting that nothing in the run touches the
/// GPU concurrently.
pub const ALLOW_PARALLEL_ENV: &str = "AB_GPU_TESTS_ALLOW_PARALLEL";

#[doc(hidden)]
pub fn enforce_serial_libtest() {
    if std::env::var_os(ALLOW_PARALLEL_ENV).is_some() {
        return;
    }
    // Pre-main is single-threaded: set_var cannot race. Deliberately
    // overrides any inherited value — the GPU-serial invariant outranks
    // ambient environment configuration.
    std::env::set_var("RUST_TEST_THREADS", "1");
    // libtest prefers the CLI flag over the env var, so a parallel
    // --test-threads request must be refused outright. (If std's argv capture
    // has not run yet, args() is empty and only the env enforcement applies.)
    let mut args = std::env::args();
    while let Some(arg) = args.next() {
        let value = if arg == "--test-threads" {
            args.next()
        } else {
            arg.strip_prefix("--test-threads=").map(str::to_owned)
        };
        if let Some(value) = value {
            if value.trim() != "1" {
                eprintln!(
                    "this test binary drives the single local GPU and is serialized: \
                     --test-threads={value} is refused (set {ALLOW_PARALLEL_ENV}=1 to override)"
                );
                std::process::exit(101);
            }
        }
    }
}

/// Force plain `cargo test` to run this crate's tests single-threaded.
///
/// Plants a `.init_array` constructor in the test binary that calls
/// `enforce_serial_libtest` before libtest reads its configuration — the
/// serialization `#[serial]` used to provide, but fail-closed. Inert under
/// nextest (each process runs a single test).
///
/// Invoke once at the crate root of every GPU crate:
///
/// ```ignore
/// #[cfg(test)]
/// gpu_core::force_serial_libtest!();
/// ```
///
/// Unit tests in the crate's lib are covered. A `tests/` integration target
/// would NOT be — its root must invoke the macro itself (no `#[cfg(test)]`
/// needed there) — and runnable doctests are never covered; keep GPU
/// doctests `ignore`/`no_run`.
#[macro_export]
macro_rules! force_serial_libtest {
    () => {
        #[cfg(target_os = "linux")]
        #[used]
        #[link_section = ".init_array"]
        static __FORCE_SERIAL_LIBTEST: extern "C" fn() = {
            extern "C" fn force_serial_libtest() {
                $crate::serial_guard::enforce_serial_libtest();
            }
            force_serial_libtest
        };
    };
}

#[cfg(test)]
mod tests {
    /// Drift guard: both GPU-safety classifications fail open on omission (a
    /// new `gpu/` crate is parallel under nextest until listed, and unguarded
    /// under plain `cargo test` until it invokes the macro), so this test
    /// fails closed instead: every `gpu/` workspace crate must be in the
    /// `gpu-serial` filter and invoke `force_serial_libtest!`, or be
    /// explicitly exempted here with a reason.
    #[test]
    fn cpu_nextest_config_covers_all_gpu_crates() {
        // No GPU tests to serialize: build-script helper / pure-CPU codegen.
        const FILTER_EXEMPT: &[&str] = &["gpu_native_build", "gpu_witness_eval_generator"];
        // Additionally guard-exempt: pure-CPU model crate without a gpu_core
        // dep; its tests never touch CUDA (nextest still serializes them via
        // the gpu-serial group).
        const GUARD_EXEMPT: &[&str] = &[
            "gpu_native_build",
            "gpu_witness_eval_generator",
            "gpu_gkr_model",
        ];
        let gpu_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .to_path_buf();
        let config =
            std::fs::read_to_string(gpu_dir.parent().unwrap().join(".config/nextest.toml"))
                .expect("workspace .config/nextest.toml must exist");
        let mut crates_seen = 0;
        for entry in std::fs::read_dir(&gpu_dir).unwrap() {
            let dir = entry.unwrap().path();
            let manifest_path = dir.join("Cargo.toml");
            let Ok(manifest) = std::fs::read_to_string(&manifest_path) else {
                continue;
            };
            let name = manifest
                .lines()
                .find_map(|line| line.strip_prefix("name = "))
                .map(|s| s.trim().trim_matches('"').to_string())
                .unwrap_or_else(|| panic!("no package name in {manifest_path:?}"));
            crates_seen += 1;
            if !FILTER_EXEMPT.contains(&name.as_str()) {
                assert!(
                    config.contains(&format!("package({name})")),
                    "{name} is missing from the gpu-serial filter in .config/nextest.toml \
                     — its tests would run in parallel under nextest"
                );
            }
            if !GUARD_EXEMPT.contains(&name.as_str()) {
                let lib = std::fs::read_to_string(dir.join("src/lib.rs")).unwrap();
                assert!(
                    lib.contains("force_serial_libtest!"),
                    "{name} does not invoke gpu_core::force_serial_libtest!() at its crate \
                     root — its tests would run in parallel under plain cargo test"
                );
            }
            // Integration-test targets are separate crates that do NOT
            // inherit the lib's #[cfg(test)] guard: each top-level file must
            // invoke the macro itself.
            if let Ok(entries) = std::fs::read_dir(dir.join("tests")) {
                for entry in entries {
                    let path = entry.unwrap().path();
                    if path.extension().is_some_and(|e| e == "rs") {
                        let src = std::fs::read_to_string(&path).unwrap();
                        assert!(
                            src.contains("force_serial_libtest!"),
                            "integration-test target {path:?} does not invoke \
                             gpu_core::force_serial_libtest!() at its root — it is not \
                             covered by {name}'s lib guard"
                        );
                    }
                }
            }
        }
        assert!(
            crates_seen >= 9,
            "gpu/ crate scan looks broken ({crates_seen} crates found)"
        );
    }

    /// Mechanism check: the constructor ran before libtest started and forced
    /// the serial value (unless the escape hatch is deliberately set).
    #[cfg(target_os = "linux")]
    #[test]
    fn guard_engaged_before_libtest() {
        if std::env::var_os(super::ALLOW_PARALLEL_ENV).is_some() {
            return;
        }
        assert_eq!(
            std::env::var("RUST_TEST_THREADS").as_deref(),
            Ok("1"),
            "force_serial_libtest! constructor did not force RUST_TEST_THREADS=1"
        );
    }
}
