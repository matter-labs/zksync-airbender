use clap::ValueEnum;

pub use crate::rv32im::unicorn::run_on_unicorn;
pub use crate::rv32im::vm::run_vm as run_on_airbender;
pub use crate::rv32im::vm::VM;

pub(crate) mod binary;
mod common;
#[cfg(feature = "prover")]
pub(crate) mod prover;
mod types;
mod unicorn;
pub(crate) mod vm;

/// Available fuzzing modes
#[derive(ValueEnum, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// Dumb fuzzing that runs the prover with random binary inputs.
    Dumb,
    /// Runs the input against the target and an unicorn VM, comparing the results.
    Unicorn,
}

/// Configures the fuzzer to expect only one input and stop after that regardless of status.
fn configure_singleton_test_mode() {
    std::env::set_var("AFL_FUZZER_LOOPCOUNT", "1");
}

pub fn run(mode: Mode, test_one: bool) {
    if cfg!(debug_assertions) {
        let _ = ();
        log::info!("Debug assertions are enabled!");
    }
    if test_one {
        configure_singleton_test_mode();
    }

    match mode {
        Mode::Dumb => dumb_fuzzer(test_one),
        Mode::Unicorn => oracle_fuzzer(test_one),
    }
}

/// Default amount of cycles, taken from `tools/cli/src/prover_utils.rs`.
const DEFAULT_CYCLES: usize = 32_000_000;
const ENTRYPOINT: u32 = 0;

type GuestResult = [u32; 8];

macro_rules! log_result {
    ($enabled:expr, $fmt:expr $(,$args:expr)* $(,)?) => {
        if $enabled {
            log::info!($fmt, $( $args, )*);
        }
    };
}

fn dumb_fuzzer(print_result: bool) {
    crate::afl::fuzz!(|data| {
        let result = vm::run_vm::<true>(data, None);
        log_result!(print_result, "result = {result:?}");
    })
}

fn oracle_fuzzer(print_result: bool) {
    crate::afl::fuzz_nohook!(|data| {
        let oracle_result = match run_on_unicorn(data, None) {
            Ok(or) => or,
            Err(err) => {
                // Stop if the oracle failed.
                if print_result {
                    log::info!("Oracle failed. Skipping...");
                    log::info!("Oracle failure: {err}");
                }
                return;
            }
        };
        log_result!(print_result, "Oracle: {oracle_result:?}");
        let target_result = vm::run_vm::<true>(data, None);
        log_result!(print_result, "Target: {target_result:?}");

        if oracle_result != target_result {
            eprintln!("Oracle and result produced different register outputs!");
            eprintln!("oracle: {oracle_result:?}");
            eprintln!("target: {target_result:?}");
            std::process::abort();
        }
    })
}
