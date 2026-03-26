#![cfg(feature = "gkr_verify")]

mod common;

use verifier_common::prover::nd_source_std::{set_iterator, ThreadLocalBasedSource};

#[test]
fn rejects_corrupted_proof() {
    let mut nds = common::load_nds("add_sub_lui_auipc_mop");

    // Corrupt a word in the GKR sumcheck region (past the transcript preamble).
    let corrupt_idx = verifier::add_sub_lui_auipc_mop::constants::GKR_TRANSCRIPT_U32 + 100;
    nds[corrupt_idx] ^= 1;

    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name("gkr verifier corrupted".to_string())
            .stack_size(1 << 27)
            .spawn_scoped(s, move || {
                set_iterator(nds.into_iter());
                verifier::add_sub_lui_auipc_mop::verify_all::<ThreadLocalBasedSource>()
            })
            .expect("failed to spawn thread");

        let result = handle.join().expect("verifier thread panicked");

        assert!(
            result.is_err(),
            "verifier should reject corrupted proof data"
        );
    });
}
