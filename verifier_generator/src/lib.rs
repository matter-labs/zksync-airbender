#![expect(warnings)]

use ::prover::*;
use prover::cs::one_row_compiler::*;
use prover::field::*;

mod utils;
use self::utils::*;

pub mod generator;
pub use self::generator::*;

pub mod inlining_generator;
pub use self::inlining_generator::*;

pub fn generate_from_reader<R: std::io::Read>(reader: R) -> (String, String) {
    let description = serde_json::from_reader(reader).unwrap();
    generate_for_description(description)
}

pub fn generate_for_description(
    description: CompiledCircuitArtifact<Mersenne31Field>,
) -> (String, String) {
    let layout = generate_from_parts(&description);

    let quotient = generate_inlined(description);

    (layout.to_string(), quotient.to_string())
}

// mod testing_file;
// mod testing_inlining_file;

#[cfg(test)]
mod test {
    use std::io::Write;

    use super::*;

    fn deserialize_from_file<T: serde::de::DeserializeOwned>(filename: &str) -> T {
        let src = std::fs::File::open(filename).unwrap();
        serde_json::from_reader(src).unwrap()
    }

    #[test]
    fn launch() {
        let compiled_circuit = deserialize_from_file("../prover/full_machine_layout.json");
        // let compiled_circuit = deserialize_from_file("../prover/layout");
        // let compiled_circuit = deserialize_from_file("../prover/blake2s_delegator_layout");

        let result = generate_from_parts(&compiled_circuit);

        let mut dst = std::fs::File::create("./src/generated.rs").unwrap();
        dst.write_all(&result.to_string().as_bytes()).unwrap();
    }

    #[test]
    fn launch_inlining() {
        let compiled_circuit = deserialize_from_file("../prover/full_machine_layout.json");
        // let compiled_circuit = deserialize_from_file("../prover/layout");
        // let compiled_circuit = deserialize_from_file("../prover/blake2s_delegator_layout");

        let result = generate_inlined(compiled_circuit);

        // let mut dst = std::fs::File::create("./src/generated_inlined_verifier.rs").unwrap();
        let mut dst = std::fs::File::create("./src/generated_inlined_verifier.rs").unwrap();
        dst.write_all(&result.to_string().as_bytes()).unwrap();
    }

    #[test]
    fn generate_reduced_machine() {
        let compiled_circuit = deserialize_from_file("../prover/reduced_machine_layout");

        let result = generate_from_parts(&compiled_circuit);
        let mut dst = std::fs::File::create("./src/generated.rs").unwrap();
        dst.write_all(&result.to_string().as_bytes()).unwrap();

        let result = generate_inlined(compiled_circuit);
        let mut dst = std::fs::File::create("./src/generated_inlined_verifier.rs").unwrap();
        dst.write_all(&result.to_string().as_bytes()).unwrap();
    }
}
