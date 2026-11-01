#![feature(allocator_api)]

pub use ::prover;
pub use ::setups;

pub mod bundle;

#[cfg(feature = "l1")]
pub mod compression;
#[cfg(feature = "l1")]
pub mod l1;
pub mod proof_assembly;
pub mod unified;
pub mod unified_transition;
pub mod unrolled;

pub use proof_assembly::{assemble_program_proof, program_setups};

const DUMP_WITNESS_VAR: &str = "DUMP_WITNESS";

pub fn serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::io::BufWriter::new(std::fs::File::create(filename).unwrap());
    serde_json::to_writer_pretty(&mut dst, el).unwrap();
    std::io::Write::flush(&mut dst).unwrap();
}

pub fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::io::BufReader::new(std::fs::File::open(filename).unwrap());
    serde_json::from_reader(src).unwrap()
}

pub fn try_deserialize_from_file<T: serde::de::DeserializeOwned>(
    filename: &str,
) -> std::io::Result<T> {
    let src = std::io::BufReader::new(std::fs::File::open(filename)?);
    Ok(serde_json::from_reader(src).unwrap())
}

pub fn bincode_serialize_to_file<T: serde::Serialize>(el: &T, filename: &str) {
    let mut dst = std::io::BufWriter::new(std::fs::File::create(filename).unwrap());
    bincode::serialize_into(&mut dst, el).unwrap();
    std::io::Write::flush(&mut dst).unwrap();
}

pub fn bincode_deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
    let src = std::io::BufReader::new(std::fs::File::open(filename).unwrap());
    bincode::deserialize_from(src).unwrap()
}

#[cfg(test)]
mod artifact_file_tests {
    use super::*;

    type Value = Vec<(String, Vec<u32>)>;

    fn value() -> Value {
        vec![("a".into(), vec![1, 2, 3]), ("b".into(), vec![])]
    }

    fn temp_path(name: &str) -> String {
        std::env::temp_dir()
            .join(format!("program_prover_{name}_{}", std::process::id()))
            .to_str()
            .unwrap()
            .to_owned()
    }

    #[test]
    fn json_files_hold_pretty_json_and_round_trip() {
        let path = temp_path("artifact_file.json");
        serialize_to_file(&value(), &path);
        let bytes = std::fs::read(&path).unwrap();
        let decoded: Value = deserialize_from_file(&path);
        let tried: Value = try_deserialize_from_file(&path).unwrap();
        std::fs::remove_file(&path).unwrap();
        assert_eq!(bytes, serde_json::to_vec_pretty(&value()).unwrap());
        assert_eq!(decoded, value());
        assert_eq!(tried, value());
    }

    #[test]
    fn bincode_files_hold_bincode_and_round_trip() {
        let path = temp_path("artifact_file.bin");
        bincode_serialize_to_file(&value(), &path);
        let bytes = std::fs::read(&path).unwrap();
        let decoded: Value = bincode_deserialize_from_file(&path);
        std::fs::remove_file(&path).unwrap();
        assert_eq!(bytes, bincode::serialize(&value()).unwrap());
        assert_eq!(decoded, value());
    }

    #[cfg(target_os = "linux")]
    #[test]
    #[should_panic(expected = "StorageFull")]
    fn json_write_errors_are_not_dropped() {
        serialize_to_file(&value(), "/dev/full");
    }

    #[cfg(target_os = "linux")]
    #[test]
    #[should_panic(expected = "StorageFull")]
    fn bincode_write_errors_are_not_dropped() {
        bincode_serialize_to_file(&value(), "/dev/full");
    }
}
