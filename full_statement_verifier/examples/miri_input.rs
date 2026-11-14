//! Verify a committed chain natively and record inner outputs for statement-only Miri.
//! Usage: miri_input OUTPUT MODE CHAIN
//! MODE: pessimistic_conjecture or ethproofs_soundcalc.
//! CHAIN: base, unrolled, unified, unrolled_unified or compression.
#[path = "../tests/common/miri_stream.rs"]
mod miri_stream;

use full_statement_verifier::host_utils::{
    build_unified_stream, build_unrolled_stream, fixture_artifact::ChainArtifact,
};
use full_statement_verifier::verifier_common::{
    self, prover::definitions::SoundnessMode, BlakeMode,
};
use miri_stream::{Chain, Selection};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    assert_eq!(args.len(), 3, "usage: miri_input OUTPUT MODE CHAIN");
    let mode = match args[1].as_str() {
        "pessimistic_conjecture" => SoundnessMode::PessimisticConjecture,
        "ethproofs_soundcalc" => SoundnessMode::EthproofsSoundnessCalc,
        _ => panic!("unsupported soundness mode"),
    };
    let chain = args[2].as_str();
    let selection = Selection {
        mode,
        chain: match chain {
            "base" => Chain::Base,
            "unrolled" => Chain::Unrolled,
            "unified" => Chain::Unified,
            "unrolled_unified" => Chain::UnrolledUnified,
            "compression" => Chain::Compression,
            _ => panic!("unsupported chain"),
        },
    };
    assert_eq!(verifier_common::BLAKE_MODE, BlakeMode::Compression);
    let artifact = ChainArtifact::load(mode, chain);
    let nds = match selection.chain {
        Chain::Base | Chain::Unrolled => build_unrolled_stream(
            &artifact.setups,
            &artifact.proof,
            verifier_common::BLAKE_MODE,
        ),
        Chain::Unified | Chain::UnrolledUnified | Chain::Compression => build_unified_stream(
            &artifact.setups,
            &artifact.proof,
            verifier_common::BLAKE_MODE,
        ),
    };
    let input = std::thread::Builder::new()
        .stack_size(1 << 27)
        .spawn(move || {
            let expected = selection.verify(&mut nds.iter().copied());
            assert_eq!(expected[8..16], artifact.chain_hash);
            let (recorded_output, statement) = selection.record(nds.iter().copied());
            assert_eq!(recorded_output, expected);
            assert_eq!(selection.verify_mocked(statement.iter().copied()), expected);
            let input = miri_stream::encode(&expected, &statement);
            println!(
                "verified {} NDS words; recorded {} statement words; wrote {} bytes",
                nds.len(),
                statement.len(),
                input.len()
            );
            input
        })
        .unwrap()
        .join()
        .expect("native verification failed");
    // A rejected artifact never produces a static Miri input.
    std::fs::write(&args[0], input).unwrap();
}
