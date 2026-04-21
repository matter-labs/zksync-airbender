#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]

#[path = "../../../../verifier/src/generated/jump_branch_slt/mod.rs"]
mod generated_gkr;

include!("../common.rs");
