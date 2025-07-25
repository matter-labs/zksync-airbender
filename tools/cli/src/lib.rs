#![feature(allocator_api)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

pub mod generate_constants;
pub mod prover_utils;
pub mod setup;
pub mod vk;

use clap::ValueEnum;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, ValueEnum, Serialize, Deserialize)]
pub enum Machine {
    Standard,
    Reduced,
    // Final reduced machine, used to generate a single proof at the end.
    ReducedFinal,
}
