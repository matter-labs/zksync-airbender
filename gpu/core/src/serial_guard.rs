//! Pre-main guard forcing plain `cargo test` (libtest) to run single-threaded.
//!
//! The GPU crates carry no `#[serial]` annotations since the cargo-nextest
//! migration: under nextest, serialization comes from the `gpu-serial` test
//! group in the workspace `.config/nextest.toml`. Plain `cargo test` knows
//! nothing about that config and would run tests concurrently in threads,
//! racing the GPU. [`force_serial_libtest!`] closes that hole.

/// Force plain `cargo test` to run this crate's tests single-threaded.
///
/// Plants a `.init_array` constructor in the test binary that sets
/// `RUST_TEST_THREADS=1` before libtest reads it — the semantics `#[serial]`
/// used to provide. Inert under nextest (each process runs a single test),
/// and explicit intent still wins: a pre-set `RUST_TEST_THREADS` is left
/// alone, and a `--test-threads` CLI flag takes precedence over the env var
/// in libtest anyway.
///
/// Invoke once at the crate root of every GPU crate:
///
/// ```ignore
/// #[cfg(test)]
/// gpu_core::force_serial_libtest!();
/// ```
#[macro_export]
macro_rules! force_serial_libtest {
    () => {
        #[cfg(target_os = "linux")]
        #[used]
        #[link_section = ".init_array"]
        static __FORCE_SERIAL_LIBTEST: extern "C" fn() = {
            extern "C" fn force_serial_libtest() {
                // Pre-main is single-threaded: set_var cannot race.
                if std::env::var_os("RUST_TEST_THREADS").is_none() {
                    std::env::set_var("RUST_TEST_THREADS", "1");
                }
            }
            force_serial_libtest
        };
    };
}

#[cfg(test)]
mod tests {
    /// Mechanism check: the constructor ran before libtest started, so the
    /// variable is always present in a test process (either pre-set by the
    /// caller or "1" from the guard).
    #[cfg(target_os = "linux")]
    #[test]
    fn guard_engaged_before_libtest() {
        assert!(
            std::env::var_os("RUST_TEST_THREADS").is_some(),
            "force_serial_libtest! constructor did not run pre-main"
        );
    }
}
