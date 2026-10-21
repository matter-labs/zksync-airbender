//! End-to-end check of the PACKED base commitment on the CPU verifier: the
//! generated `blake2_with_extended_control/sec_100_pack4` verifier (see
//! `generate_verifiers.rs::blake2_with_extended_control_pack4`) against the
//! `pack_log2 = 4` proof fixture. The generated module is included by path
//! (as `full_statement_verifier` does), so regenerate before running this.

// the generated code carries `verifier_stats` cfg gates this crate has no feature for
#![allow(unexpected_cfgs)]

use verifier_common::errors::DebugErrorCreator;
use verifier_common::test_circuits::packed_fixture;

#[path = "../../verifier/src/generated/blake2_with_extended_control/sec_100_pack4/mod.rs"]
#[allow(dead_code, unused_imports, clippy::all)]
mod packed_verifier;

const VERIFIER_STACK_SIZE: usize = 1 << 27;

#[test]
fn blake2_with_extended_control_pack4_proof_verifies() {
    let proof_path = packed_fixture::proof_path();
    assert!(
        std::path::Path::new(&proof_path).exists(),
        "packed proof fixture missing: {proof_path}"
    );
    // the fixture must have been proved with the config the verifier was generated from
    let proof = packed_fixture::proof();
    let config = packed_fixture::prover_config();
    assert_eq!(
        proof.whir_proof.whir_schedule, config.whir_schedule,
        "fixture WHIR schedule differs from the generated verifier's"
    );
    assert_eq!(
        packed_verifier::constants::PACK_LOG2,
        packed_fixture::PACK_LOG2
    );
    assert_eq!(
        packed_verifier::constants::TRACE_LEN_LOG2 as usize,
        config.trace_len_log2
    );

    let (nds, external_challenges) = packed_fixture::load_nds();
    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name("gkr packed verifier".into())
            .stack_size(VERIFIER_STACK_SIZE)
            .spawn_scoped(s, move || {
                let mut it = nds.into_iter();
                packed_verifier::verify::<_, DebugErrorCreator>(&external_challenges, &mut it)
                    .unwrap_or_else(|e| panic!("packed proof failed to verify: {e:?}"));
                assert_eq!(it.len(), 0, "the verifier must consume the whole proof");
            })
            .expect("failed to spawn verifier thread");
        handle.join().unwrap();
    });
}
