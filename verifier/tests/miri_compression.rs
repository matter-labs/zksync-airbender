//! The canonical fixed-workload compression fixture in the Software Blake multiproof layout.
#[path = "common/miri_circuit_stream.rs"]
mod miri_circuit_stream;

#[test]
fn compression_pessimistic_conjecture() {
    assert_eq!(
        verifier::verifier_common::BLAKE_MODE,
        verifier::verifier_common::BlakeMode::Software
    );
    miri_circuit_stream::check(
        "compression",
        0,
        include_bytes!(concat!(
            env!("AIRBENDER_MIRI_CIRCUIT_INPUT_DIR"),
            "/pessimistic_conjecture/compression.bin"
        )),
    );
}
