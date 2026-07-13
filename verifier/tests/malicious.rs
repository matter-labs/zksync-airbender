#![cfg(feature = "security_80")]

#[macro_use]
mod common;

use common::SecurityLevel;
use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use prover::gkr::prover::GKRProof;
use prover::merkle_trees::DefaultTreeConstructor;
use verifier_common::errors::VerificationError;

const CIRCUIT_NAME: &str = "jump_branch_slt";

fn repo_root() -> String {
    format!("{}/..", env!("CARGO_MANIFEST_DIR"))
}

fn deserialize_from_file<T: serde::de::DeserializeOwned>(path: &str) -> T {
    let src = std::fs::File::open(path).unwrap_or_else(|e| {
        panic!(
            "failed to open {}: {} — did you run the malicious prover tests first?",
            path, e
        )
    });
    serde_json::from_reader(src).unwrap()
}

fn load_malicious_proof(
    variant: &str,
) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
    let path = format!(
        "{}/prover/test_proofs/malicious_{}_gkr_proof.json",
        repo_root(),
        variant
    );
    deserialize_from_file(&path)
}

fn assert_rejects(variant: &str, expected: impl FnOnce(&VerificationError) -> bool) {
    let proof = load_malicious_proof(variant);
    common::assert_rejects_with_variant(
        CIRCUIT_NAME,
        SecurityLevel::Sec80,
        variant,
        &proof,
        expected,
    );
}

fn assert_accepts(variant: &str) {
    let proof = load_malicious_proof(variant);
    let (nds, external_challenges) =
        common::proof_to_nds(CIRCUIT_NAME, SecurityLevel::Sec80, &proof);
    match common::verify_nds(
        CIRCUIT_NAME,
        SecurityLevel::Sec80,
        &external_challenges,
        nds,
    ) {
        Ok(()) => {}
        Err(r) => panic!(
            "{}: honest control proof unexpectedly REJECTED: {:?}",
            variant, r
        ),
    }
}

// ---- MemoryTuple cache must be bound to base columns ----
// Proofs produced by prover `generate_memtuple_regression_proofs` (run first, WITHOUT
// gkr_self_checks). These pin the generator-side MemoryTuple cache-binding fix.

/// Sanity: the honest control proof (no forge) is accepted
#[test]
#[ignore]
fn memtuple_control_accepts() {
    assert_accepts("memtuple_control");
}

/// forging the MemoryTuple cache poly (decoupling the memory-permutation grand
/// product from the committed base columns) must be rejected by the generated
/// MemoryTuple binding.
#[test]
#[ignore]
fn rejects_malicious_memtuple_cacheforge() {
    assert_rejects("memtuple_cacheforge", |e| {
        matches!(
            e,
            VerificationError::GkrPermutationCacheRelationFailed { .. }
        )
    });
}

/// an analogous forge of a BOUND SingleColumnLookup cache
#[test]
#[ignore]
fn rejects_malicious_lookup_cacheforge() {
    assert_rejects("lookup_cacheforge", |e| {
        matches!(
            e,
            VerificationError::GkrSingleLookupCacheRelationFailed { .. }
                | VerificationError::GkrVectorLookupCacheRelationFailed { .. }
                | VerificationError::GkrPermutationCacheRelationFailed { .. }
        )
    });
}

#[test]
#[ignore]
fn rejects_malicious_lookup_16bits() {
    assert_rejects("lookup_16bits", |e| {
        matches!(e, VerificationError::GkrLookupIdentityFailed { .. })
    });
}

#[test]
#[ignore]
fn rejects_malicious_lookup_timestamps() {
    assert_rejects("lookup_timestamps", |e| {
        matches!(e, VerificationError::GkrLookupIdentityFailed { .. })
    });
}

#[test]
#[ignore]
fn rejects_malicious_lookup_generic() {
    assert_rejects("lookup_generic", |e| {
        matches!(e, VerificationError::GkrLookupIdentityFailed { .. })
    });
}

#[test]
#[ignore]
fn rejects_malicious_witness_value() {
    assert_rejects("witness_value", |e| {
        matches!(
            e,
            VerificationError::GkrSumcheckRoundFailed { .. }
                | VerificationError::GkrFinalStepCheckFailed { .. }
        )
    });
}

#[test]
#[ignore]
fn rejects_malicious_memory_value() {
    // A corrupted memory-trace value breaks the memory consistency argument. Observed
    // rejection is GkrSingleLookupCacheRelationFailed (the value/timestamp cache); the other
    // cache-relation / sumcheck variants are kept as acceptable alternatives (matches the
    // cache-relation set in corruption.rs::test_rejects_corrupted_cache_relations).
    assert_rejects("memory_value", |e| {
        matches!(
            e,
            VerificationError::GkrSumcheckRoundFailed { .. }
                | VerificationError::GkrFinalStepCheckFailed { .. }
                | VerificationError::GkrSingleLookupCacheRelationFailed { .. }
                | VerificationError::GkrVectorLookupCacheRelationFailed { .. }
                | VerificationError::GkrPermutationCacheRelationFailed { .. }
        )
    });
}

// ---- subword address malleability ----
// Proof produced by prover `gkr_run_basic_unrolled_test_sec_80` with SUBWORD_ALIAS_FORGE=1,
// which trades the byte offset (b0,b1) against the word-cell address on an active byte-load
// row while preserving the address equation (all pre-fix constraints hold). The word-
// alignment constraint (cleanaddr_lo == 4*(cleanaddr_lo>>2), cleanaddr_lo>>2 range-checked)
// must reject the resulting non-word-aligned cleanaddr_lo.

const SUBWORD_CIRCUIT_NAME: &str = "mem_subword_only";

#[test]
#[ignore]
fn rejects_malicious_subword_alias() {
    let proof = load_malicious_proof("subword_alias");
    common::assert_rejects_with_variant(
        SUBWORD_CIRCUIT_NAME,
        SecurityLevel::Sec80,
        "subword_alias",
        &proof,
        |e| {
            matches!(
                e,
                VerificationError::GkrFinalStepCheckFailed { .. }
                    | VerificationError::GkrSumcheckRoundFailed { .. }
            )
        },
    );
}

// ---- Unified reduced machine proof-level negative tests ----
// Consume the proofs from `prover` `generate_malicious_unified_proofs` (run that first, WITHOUT gkr_self_checks)

const UNIFIED_CIRCUIT_NAME: &str = "unified_reduced_machine";

fn load_malicious_unified_proof(
    variant: &str,
) -> GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor> {
    let path = format!(
        "{}/prover/test_proofs/malicious_unified_{}_gkr_proof.json",
        repo_root(),
        variant
    );
    deserialize_from_file(&path)
}

fn assert_rejects_unified(variant: &str, expected: impl FnOnce(&VerificationError) -> bool) {
    let proof = load_malicious_unified_proof(variant);
    common::assert_rejects_with_variant(
        UNIFIED_CIRCUIT_NAME,
        SecurityLevel::Sec80,
        variant,
        &proof,
        expected,
    );
}

#[test]
#[ignore]
fn rejects_malicious_unified_rc16_overflow() {
    assert_rejects_unified("rc16_overflow", |e| {
        matches!(e, VerificationError::GkrLookupIdentityFailed { .. })
    });
}

#[test]
#[ignore]
fn rejects_malicious_unified_is_rom_forge() {
    assert_rejects_unified("is_rom_forge", |e| {
        matches!(
            e,
            VerificationError::GkrLookupIdentityFailed { .. }
                | VerificationError::GkrSumcheckRoundFailed { .. }
                | VerificationError::GkrFinalStepCheckFailed { .. }
        )
    });
}

#[test]
#[ignore]
fn rejects_malicious_unified_f4_sw_value() {
    assert_rejects_unified("f4_sw_value", |e| {
        matches!(
            e,
            VerificationError::GkrSumcheckRoundFailed { .. }
                | VerificationError::GkrFinalStepCheckFailed { .. }
                | VerificationError::GkrPermutationCacheRelationFailed { .. }
                | VerificationError::GkrGrandProductCheckFailed
        )
    });
}

#[test]
#[ignore]
fn rejects_malicious_unified_f4_lw_value() {
    assert_rejects_unified("f4_lw_value", |e| {
        matches!(
            e,
            VerificationError::GkrSumcheckRoundFailed { .. }
                | VerificationError::GkrFinalStepCheckFailed { .. }
                | VerificationError::GkrPermutationCacheRelationFailed { .. }
                | VerificationError::GkrGrandProductCheckFailed
        )
    });
}

#[test]
#[ignore]
fn rejects_malicious_unified_f3_pooled_lookup() {
    assert_rejects_unified("f3_pooled_lookup", |e| {
        matches!(
            e,
            VerificationError::GkrLookupIdentityFailed { .. }
                | VerificationError::GkrSingleLookupCacheRelationFailed { .. }
                | VerificationError::GkrVectorLookupCacheRelationFailed { .. }
                | VerificationError::GkrSumcheckRoundFailed { .. }
                | VerificationError::GkrFinalStepCheckFailed { .. }
        )
    });
}
