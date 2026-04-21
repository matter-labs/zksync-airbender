#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]

#[path = "../../../../verifier/src/generated/blake2_with_extended_control/mod.rs"]
mod generated_gkr;

include!("../common.rs");
