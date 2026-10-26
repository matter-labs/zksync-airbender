//! End-to-end checks of the blake base-round comparison sweep on the CPU
//! verifier: every generated `blake2_with_extended_control/pessimistic_conjecture{infix}`
//! verifier (see `generate_verifiers.rs::blake2_with_extended_control_variants`)
//! against its proof fixture (the prover's
//! `gkr_blake_delegation_variant_sweep_sec_100`). The generated modules are
//! included by path, so regenerate before running this.

// the generated code carries `verifier_stats` cfg gates this crate has no feature for
#![allow(unexpected_cfgs)]

use prover::field::baby_bear::base::BabyBearField;
use prover::field::baby_bear::ext4::BabyBearExt4;
use prover::definitions::GKRExternalChallenges;
use verifier_common::errors::DebugErrorCreator;
use verifier_common::test_circuits::blake_variants::BlakeVariant;

#[path = "../../verifier/src/generated/blake2_with_extended_control/pessimistic_conjecture_pack0/mod.rs"]
#[allow(dead_code, unused_imports, clippy::all)]
mod verifier_sec_100;
#[path = "../../verifier/src/generated/blake2_with_extended_control/pessimistic_conjecture_virtual/mod.rs"]
#[allow(dead_code, unused_imports, clippy::all)]
mod verifier_sec_100_virtual;
#[path = "../../verifier/src/generated/blake2_with_extended_control/pessimistic_conjecture_pack1/mod.rs"]
#[allow(dead_code, unused_imports, clippy::all)]
mod verifier_sec_100_pack1;
#[path = "../../verifier/src/generated/blake2_with_extended_control/pessimistic_conjecture_pack1_virtual/mod.rs"]
#[allow(dead_code, unused_imports, clippy::all)]
mod verifier_sec_100_pack1_virtual;
#[path = "../../verifier/src/generated/blake2_with_extended_control/pessimistic_conjecture_pack2/mod.rs"]
#[allow(dead_code, unused_imports, clippy::all)]
mod verifier_sec_100_pack2;
#[path = "../../verifier/src/generated/blake2_with_extended_control/pessimistic_conjecture_pack2_virtual/mod.rs"]
#[allow(dead_code, unused_imports, clippy::all)]
mod verifier_sec_100_pack2_virtual;
#[path = "../../verifier/src/generated/blake2_with_extended_control/pessimistic_conjecture_pack3/mod.rs"]
#[allow(dead_code, unused_imports, clippy::all)]
mod verifier_sec_100_pack3;
#[path = "../../verifier/src/generated/blake2_with_extended_control/pessimistic_conjecture_pack3_virtual/mod.rs"]
#[allow(dead_code, unused_imports, clippy::all)]
mod verifier_sec_100_pack3_virtual;
#[path = "../../verifier/src/generated/blake2_with_extended_control/pessimistic_conjecture_pack4/mod.rs"]
#[allow(dead_code, unused_imports, clippy::all)]
mod verifier_sec_100_pack4;
#[path = "../../verifier/src/generated/blake2_with_extended_control/pessimistic_conjecture_pack4_virtual/mod.rs"]
#[allow(dead_code, unused_imports, clippy::all)]
mod verifier_sec_100_pack4_virtual;

const VERIFIER_STACK_SIZE: usize = 1 << 27;

fn verify_variant<V>(
    variant: BlakeVariant,
    generated_fold_0: usize,
    generated_trace_len_log2: usize,
    verify: V,
) where
    V: FnOnce(
            &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
            &mut std::vec::IntoIter<u32>,
        ) -> Result<(), verifier_common::errors::VerificationError>
        + Send,
{
    let proof_path = variant.proof_path();
    assert!(
        std::path::Path::new(&proof_path).exists(),
        "{} proof fixture missing: {proof_path}",
        variant.name()
    );
    // the fixture must have been proved with the config the verifier was generated from
    let proof = variant.proof();
    let config = variant.prover_config();
    assert_eq!(
        proof.whir_proof.whir_schedule, config.whir_schedule,
        "{}: fixture WHIR schedule differs from the generated verifier's",
        variant.name()
    );
    assert_eq!(generated_fold_0, variant.fold_log2);
    assert_eq!(generated_trace_len_log2, config.trace_len_log2);
    assert_eq!(config.pack_log2(), variant.pack_log2);

    let (nds, external_challenges) = variant.load_nds();
    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(format!("gkr verifier {}", variant.name()))
            .stack_size(VERIFIER_STACK_SIZE)
            .spawn_scoped(s, move || {
                let mut it = nds.into_iter();
                verify(&external_challenges, &mut it)
                    .unwrap_or_else(|e| panic!("{} proof failed to verify: {e:?}", variant.name()));
                assert_eq!(it.len(), 0, "the verifier must consume the whole proof");
            })
            .expect("failed to spawn verifier thread");
        handle.join().unwrap();
    });
}

#[test]
fn blake2_with_extended_control_sec_100_proof_verifies() {
    verify_variant(
        BlakeVariant { pack_log2: 0, fold_log2: 1 },
        verifier_sec_100::constants::WHIR_FOLD_STEPS[0],
        verifier_sec_100::constants::TRACE_LEN_LOG2 as usize,
        |ext, it| verifier_sec_100::verify::<_, DebugErrorCreator>(ext, it).map(|_| ()),
    );
}
#[test]
fn blake2_with_extended_control_sec_100_virtual_proof_verifies() {
    verify_variant(
        BlakeVariant { pack_log2: 0, fold_log2: 0 },
        verifier_sec_100_virtual::constants::WHIR_FOLD_STEPS[0],
        verifier_sec_100_virtual::constants::TRACE_LEN_LOG2 as usize,
        |ext, it| verifier_sec_100_virtual::verify::<_, DebugErrorCreator>(ext, it).map(|_| ()),
    );
}
#[test]
fn blake2_with_extended_control_sec_100_pack1_proof_verifies() {
    verify_variant(
        BlakeVariant { pack_log2: 1, fold_log2: 1 },
        verifier_sec_100_pack1::constants::WHIR_FOLD_STEPS[0],
        verifier_sec_100_pack1::constants::TRACE_LEN_LOG2 as usize,
        |ext, it| verifier_sec_100_pack1::verify::<_, DebugErrorCreator>(ext, it).map(|_| ()),
    );
}
#[test]
fn blake2_with_extended_control_sec_100_pack1_virtual_proof_verifies() {
    verify_variant(
        BlakeVariant { pack_log2: 1, fold_log2: 0 },
        verifier_sec_100_pack1_virtual::constants::WHIR_FOLD_STEPS[0],
        verifier_sec_100_pack1_virtual::constants::TRACE_LEN_LOG2 as usize,
        |ext, it| verifier_sec_100_pack1_virtual::verify::<_, DebugErrorCreator>(ext, it).map(|_| ()),
    );
}
#[test]
fn blake2_with_extended_control_sec_100_pack2_proof_verifies() {
    verify_variant(
        BlakeVariant { pack_log2: 2, fold_log2: 1 },
        verifier_sec_100_pack2::constants::WHIR_FOLD_STEPS[0],
        verifier_sec_100_pack2::constants::TRACE_LEN_LOG2 as usize,
        |ext, it| verifier_sec_100_pack2::verify::<_, DebugErrorCreator>(ext, it).map(|_| ()),
    );
}
#[test]
fn blake2_with_extended_control_sec_100_pack2_virtual_proof_verifies() {
    verify_variant(
        BlakeVariant { pack_log2: 2, fold_log2: 0 },
        verifier_sec_100_pack2_virtual::constants::WHIR_FOLD_STEPS[0],
        verifier_sec_100_pack2_virtual::constants::TRACE_LEN_LOG2 as usize,
        |ext, it| verifier_sec_100_pack2_virtual::verify::<_, DebugErrorCreator>(ext, it).map(|_| ()),
    );
}
#[test]
fn blake2_with_extended_control_sec_100_pack3_proof_verifies() {
    verify_variant(
        BlakeVariant { pack_log2: 3, fold_log2: 1 },
        verifier_sec_100_pack3::constants::WHIR_FOLD_STEPS[0],
        verifier_sec_100_pack3::constants::TRACE_LEN_LOG2 as usize,
        |ext, it| verifier_sec_100_pack3::verify::<_, DebugErrorCreator>(ext, it).map(|_| ()),
    );
}
#[test]
fn blake2_with_extended_control_sec_100_pack3_virtual_proof_verifies() {
    verify_variant(
        BlakeVariant { pack_log2: 3, fold_log2: 0 },
        verifier_sec_100_pack3_virtual::constants::WHIR_FOLD_STEPS[0],
        verifier_sec_100_pack3_virtual::constants::TRACE_LEN_LOG2 as usize,
        |ext, it| verifier_sec_100_pack3_virtual::verify::<_, DebugErrorCreator>(ext, it).map(|_| ()),
    );
}
#[test]
fn blake2_with_extended_control_sec_100_pack4_proof_verifies() {
    verify_variant(
        BlakeVariant { pack_log2: 4, fold_log2: 1 },
        verifier_sec_100_pack4::constants::WHIR_FOLD_STEPS[0],
        verifier_sec_100_pack4::constants::TRACE_LEN_LOG2 as usize,
        |ext, it| verifier_sec_100_pack4::verify::<_, DebugErrorCreator>(ext, it).map(|_| ()),
    );
}
#[test]
fn blake2_with_extended_control_sec_100_pack4_virtual_proof_verifies() {
    verify_variant(
        BlakeVariant { pack_log2: 4, fold_log2: 0 },
        verifier_sec_100_pack4_virtual::constants::WHIR_FOLD_STEPS[0],
        verifier_sec_100_pack4_virtual::constants::TRACE_LEN_LOG2 as usize,
        |ext, it| verifier_sec_100_pack4_virtual::verify::<_, DebugErrorCreator>(ext, it).map(|_| ()),
    );
}
