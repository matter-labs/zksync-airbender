#![feature(allocator_api)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

mod afl;
#[cfg(feature = "prover")]
pub mod prover;
pub mod rv32im;
mod utils;
pub mod witgen;

pub fn setup_logging() {
    #![allow(unexpected_cfgs)]
    #[cfg(not(fuzzing))]
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info"))
        .format_timestamp_millis()
        .format_module_path(false)
        .format_target(false)
        .init();
}
