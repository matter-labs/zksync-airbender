//! Prepare a committed chain artifact outside Miri and verify the selected entry point.
//! Usage: miri_input OUTPUT CHAIN ENTRY
//! CHAIN / ENTRY: base / unrolled_base, unrolled / unrolled_recursion,
//! unified / recursion_dispatch. Uses pessimistic_conjecture.
#[path = "../tests/common/miri_stream.rs"]
mod miri_stream;

use full_statement_verifier::host_utils::{
    build_unified_stream, build_unrolled_stream, fixture_artifact::ChainArtifact,
};
use full_statement_verifier::verifier_common::{
    self, prover::definitions::SoundnessMode, BlakeMode,
};
use miri_stream::Selection;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    assert_eq!(args.len(), 3, "usage: miri_input OUTPUT CHAIN ENTRY");
    let chain = args[1].as_str();
    let selection = match (chain, args[2].as_str()) {
        ("base", "unrolled_base") => Selection::UnrolledBase,
        ("unrolled", "unrolled_recursion") => Selection::UnrolledRecursion,
        ("unified", "recursion_dispatch") => Selection::RecursionDispatch,
        _ => panic!("unsupported chain/entry pair"),
    };
    assert_eq!(verifier_common::BLAKE_MODE, BlakeMode::Compression);
    let artifact = ChainArtifact::load(SoundnessMode::PessimisticConjecture, chain);
    let mut nds = if !matches!(selection, Selection::RecursionDispatch) {
        build_unrolled_stream(
            &artifact.setups,
            &artifact.proof,
            verifier_common::BLAKE_MODE,
        )
    } else {
        build_unified_stream(
            &artifact.setups,
            &artifact.proof,
            verifier_common::BLAKE_MODE,
        )
    };
    if matches!(selection, Selection::RecursionDispatch) {
        nds.insert(0, full_statement_verifier::definitions::OP_VERIFY_UNIFIED_RECURSION_LAYER_IN_UNIFIED_CIRCUIT);
    }
    let input = std::thread::Builder::new()
        .stack_size(1 << 27)
        .spawn(move || {
            let expected = selection.verify(&mut nds.iter().copied());
            assert_eq!(expected[8..16], artifact.chain_hash);
            let input = miri_stream::encode(&expected, &nds);
            println!(
                "verified full FSV output and {} NDS words; wrote {} bytes",
                nds.len(),
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
