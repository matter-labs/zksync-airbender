#![allow(internal_features)]
#![feature(vec_push_within_capacity)]
#![feature(allocator_api)]
#![feature(likely_unlikely)]
#![feature(pointer_is_aligned_to)]
#![feature(const_cmp)]
#![feature(const_trait_impl)]
#![feature(core_intrinsics)]

// In the first take over the compiler and the corresponding simulator we will first
// preprocess the bytecode into fixed-width format, and then will do very simple and execution loop
// that just dispatches a function pointer

pub mod abstractions;
pub mod cycle;
pub mod ir;
pub mod jit;
pub mod replayer;
pub mod vm;
pub mod witness;

pub use ::common_constants;

#[cfg(test)]
mod tests;
