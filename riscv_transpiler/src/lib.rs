#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(vec_push_within_capacity)]
#![feature(allocator_api)]
#![feature(bigint_helper_methods)]
#![feature(ptr_as_ref_unchecked)]
#![feature(maybe_uninit_array_assume_init)]

// In the first take over the compiler and the corresponding simulator we will first
// preprocess the bytecode into fixed-width format, and then will do very simple and execution loop
// that just dispatches a function pointer

pub mod ir;
pub mod replayer;
pub mod vm;
pub mod witness;
