#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(allocator_api)]

pub use ::prover;
pub use ::setups;

#[cfg(feature = "gpu")]
pub mod gpu;

pub mod unified;
pub mod unrolled;

mod recursion;

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
fn try_deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> Result<T, ()> {
    let src = std::fs::File::open(filename).map_err(|_| ())?;
    Ok(serde_json::from_reader(src).unwrap())
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
