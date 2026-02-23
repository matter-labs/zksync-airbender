#![cfg_attr(not(test), no_std)]

//! The Poseidon2 permutation.
//!
//! This implementation was based upon the following resources:
//! - <https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2.rs>
//! - <https://eprint.iacr.org/2023/323.pdf>
//! - <https://github.com/Plonky3/Plonky3/blob/main/mersenne-31/src/poseidon2.rs> for parameters

pub mod m31;
