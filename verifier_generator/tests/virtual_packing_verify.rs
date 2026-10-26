//! End-to-end check of the VIRTUAL-PACKING base round on the CPU verifier: the
//! generated `blake2_with_extended_control/pessimistic_conjecture_virtual` verifier (see
//! `generate_verifiers.rs::blake2_with_extended_control_virtual`) against the
//! `fold_log2 = 0` proof fixture. The generated module is included by path
//! (as `full_statement_verifier` does), so regenerate before running this.

// the generated code carries `verifier_stats` cfg gates this crate has no feature for
#![allow(unexpected_cfgs)]

use verifier_common::errors::DebugErrorCreator;
use verifier_common::test_circuits::virtual_packing_fixture;

#[path = "../../verifier/src/generated/blake2_with_extended_control/pessimistic_conjecture_virtual/mod.rs"]
#[allow(dead_code, unused_imports, clippy::all)]
mod virtual_verifier;

const VERIFIER_STACK_SIZE: usize = 1 << 27;

#[test]
fn blake2_with_extended_control_virtual_packing_proof_verifies() {
    let proof_path = virtual_packing_fixture::proof_path();
    assert!(
        std::path::Path::new(&proof_path).exists(),
        "virtual-packing proof fixture missing: {proof_path}"
    );
    // the fixture must have been proved with the config the verifier was generated from
    let proof = virtual_packing_fixture::proof();
    let config = virtual_packing_fixture::prover_config();
    assert_eq!(
        proof.whir_proof.whir_schedule, config.whir_schedule,
        "fixture WHIR schedule differs from the generated verifier's"
    );
    assert!(proof.whir_proof.base_sumcheck_polys.is_empty());
    assert_eq!(virtual_verifier::constants::WHIR_FOLD_STEPS[0], 0);
    assert_eq!(
        virtual_verifier::constants::TRACE_LEN_LOG2 as usize,
        config.trace_len_log2
    );

    let (nds, external_challenges) = virtual_packing_fixture::load_nds();
    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name("gkr virtual-packing verifier".into())
            .stack_size(VERIFIER_STACK_SIZE)
            .spawn_scoped(s, move || {
                let mut it = nds.into_iter();
                virtual_verifier::verify::<_, DebugErrorCreator>(&external_challenges, &mut it)
                    .unwrap_or_else(|e| panic!("virtual-packing proof failed to verify: {e:?}"));
                assert_eq!(it.len(), 0, "the verifier must consume the whole proof");
            })
            .expect("failed to spawn verifier thread");
        handle.join().unwrap();
    });
}
