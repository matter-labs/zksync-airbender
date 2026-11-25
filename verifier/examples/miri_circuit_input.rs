//! Prepare one Sec100 canonical proof for static-input Miri verification.
//! Usage: miri_circuit_input CIRCUIT MODE OUTPUT_PATH
#[path = "../tests/common/miri_circuit_stream.rs"]
mod miri_circuit_stream;

use verifier::prover::definitions::SoundnessMode;
use verifier::verifier_common::{
    self,
    test_circuits::{SecurityLevel, CIRCUITS},
};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    assert_eq!(
        args.len(),
        3,
        "usage: miri_circuit_input CIRCUIT MODE OUTPUT_PATH"
    );
    let name = args[0].clone();
    let (mode, mode_id) = match args[1].as_str() {
        "pessimistic_conjecture" => (SoundnessMode::PessimisticConjecture, 0),
        "ethproofs_soundcalc" => (SoundnessMode::EthproofsSoundnessCalc, 1),
        _ => panic!("unknown soundness mode"),
    };
    let output = std::path::absolute(&args[2]).unwrap();
    std::env::set_current_dir(env!("CARGO_MANIFEST_DIR")).unwrap();
    let circuit = if name == "compression" {
        assert_eq!(
            verifier_common::BLAKE_MODE,
            verifier_common::BlakeMode::Software
        );
        #[cfg(feature = "miri_compression_coverage")]
        {
            &*verifier_common::test_circuits::COMPRESSION
        }
        #[cfg(not(feature = "miri_compression_coverage"))]
        panic!("compression input preparation needs --features miri_compression_coverage");
    } else {
        assert_eq!(
            verifier_common::BLAKE_MODE,
            verifier_common::BlakeMode::Compression
        );
        CIRCUITS
            .iter()
            .find(|c| c.name == name)
            .expect("canonical circuit")
    };
    let (nds, challenges) =
        circuit.load_nds_for_mode(SecurityLevel::Sec100, mode, verifier_common::BLAKE_MODE);
    let mut payload = Vec::new();
    challenges.flatten_into_buffer(&mut payload);
    let challenge_words = payload.len();
    payload.extend(&nds);
    let bytes = std::thread::Builder::new().stack_size(1 << 27).spawn(move || {
        #[cfg(feature = "miri_compression_coverage")]
        verifier_common::multiproof_coverage::reset();
        let expected = miri_circuit_stream::verify(&name, mode_id, &mut payload.iter().copied());
        #[cfg(feature = "miri_compression_coverage")]
        if name == "compression" {
            use verifier::compression::{ethproofs_soundcalc, pessimistic_conjecture};
            let (queries_per_round, cap_size) = match mode {
                SoundnessMode::PessimisticConjecture => (
                    pessimistic_conjecture::constants::WHIR_QUERIES.as_slice(),
                    pessimistic_conjecture::constants::WHIR_CAP_SIZE,
                ),
                SoundnessMode::EthproofsSoundnessCalc => (
                    ethproofs_soundcalc::constants::WHIR_QUERIES.as_slice(),
                    ethproofs_soundcalc::constants::WHIR_CAP_SIZE,
                ),
            };
            let counts = verifier_common::multiproof_coverage::counts();
            for (round, &queries) in queries_per_round.iter().enumerate() {
                let executed = counts.get(round).copied().unwrap_or(0);
                let expected = if verifier_common::BlakeMode::Software.merkle_multiproofs(queries, cap_size) { queries } else { 0 };
                println!("compression round {round}: queries={queries}, cap_size={cap_size}, executed_multiproof_queries={executed}");
                assert_eq!(executed, expected, "multiproof branch coverage in round {round}");
            }
            assert!(counts.iter().sum::<usize>() > 0, "compression must execute multiproofs");
        }
        let bytes = miri_circuit_stream::encode(&expected, &payload);
        println!("{name}: natively verified {} NDS words + {challenge_words} challenge words; {} output words; {} bytes", nds.len(), expected.len(), bytes.len());
        bytes
    }).unwrap().join().expect("native verification failed");
    std::fs::write(output, bytes).unwrap();
}
