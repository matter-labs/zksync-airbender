#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]

#[path = "../../../../verifier/src/generated/add_sub_lui_auipc_mop/mod.rs"]
mod generated_gkr;

include!("../common.rs");
