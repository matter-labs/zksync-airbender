#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(allocator_api)]

pub use ::prover;
pub use ::setups;
use prover::field::*;
use prover::*;

#[cfg(feature = "gpu")]
pub mod gpu;

pub mod unified;
pub mod unrolled;

pub const LDE_FACTOR_LOG2: usize = 1;
pub const NUM_FOLDINGS: usize = 5; // same for all circuits we use here
pub const SECURITY_CONFIG: verifier_common::SizedProofSecurityConfig<NUM_FOLDINGS> =
    verifier_common::SizedProofSecurityConfig::<NUM_FOLDINGS>::worst_case_config();
pub const MEMORY_DELEGATION_POW_BITS: usize = verifier_common::MEMORY_DELEGATION_POW_BITS;

#[cfg(not(feature = "precheck_satisfied"))]
const PRECHECK_SATISFIED: bool = false;

#[cfg(feature = "precheck_satisfied")]
const PRECHECK_SATISFIED: bool = true;

const DUMP_WITNESS_VAR: &str = "DUMP_WITNESS";

#[allow(dead_code)]
fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
}

#[allow(dead_code)]
fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    serde_json::from_reader(src).unwrap()
}

#[allow(dead_code)]
fn bincode_serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::fs::File::create(filename).unwrap();
    bincode::serialize_into(&mut dst, el).unwrap();
}

#[allow(dead_code)]
fn bincode_deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::fs::File::open(filename).unwrap();
    bincode::deserialize_from(src).unwrap()
}

fn u32_from_field_elems(src: &[Mersenne31Field; 2]) -> u32 {
    use prover::field::PrimeField;

    let low = u16::try_from(src[0].as_u64_reduced()).expect("read value is not 16 bit long") as u32;
    let high =
        u16::try_from(src[1].as_u64_reduced()).expect("read value is not 16 bit long") as u32;
    low + (high << 16)
}
