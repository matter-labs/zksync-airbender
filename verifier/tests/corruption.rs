// Corruption tests. The bulk of the suite is Sec80-only (it depends on the Sec80 NDS layout
// and the Sec80 generated verifier), so those tests are gated at their macro invocation below.
// The PoW-nonce tests run at *every* enabled security level: at Sec80 a tampered nonce is caught
// downstream (0-bit threshold is vacuous), while at Sec100 it is caught directly by `verify_pow`'s
// threshold check — so this is the coverage of the nonzero-bit rejection branch.

#[macro_use]
mod common;

use field::baby_bear::ext4::BabyBearExt4;
use field::Field;
use verifier_common::errors::VerificationError;

use common::{
    assert_rejects_any, assert_rejects_corrupted_nds, assert_rejects_via_panic,
    assert_rejects_with_variant, SecurityLevel, VerifyRejection,
};

fn test_rejects_garbage_proof(name: &str) {
    let nds_len = common::load_nds(name, SecurityLevel::Sec80).0.len();
    assert_rejects_corrupted_nds(
        name,
        SecurityLevel::Sec80,
        "garbage proof",
        |nds| {
            for i in 0..nds_len {
                nds[i] = (i as u32).wrapping_mul(2654435761);
            }
        },
        |r| matches!(r, VerifyRejection::Error(..)),
    );
}

fn test_rejects_corruption_at_fractions(name: &str) {
    let nds_len = common::load_nds(name, SecurityLevel::Sec80).0.len();
    for fraction in [0.25, 0.50, 0.75] {
        let label = format!("fraction {:.2}", fraction);
        let idx = (nds_len as f64 * fraction) as usize;
        assert_rejects_corrupted_nds(
            name,
            SecurityLevel::Sec80,
            &label,
            |nds| nds[idx] ^= 1,
            |r| matches!(r, VerifyRejection::Error(..)),
        );
    }
}

fn test_rejects_corrupted_gkr_region(name: &str) {
    with_circuit!(name, SecurityLevel::Sec80, |m| {
        type InitialTranscript = m::constants::ConcreteInitialTranscript;
        let initial_transcript_responses_offset = core::mem::offset_of!(InitialTranscript, _marker)
            - (core::mem::offset_of!(InitialTranscript, setup_caps)
                - core::mem::offset_of!(InitialTranscript, external_challenges_flattened));
        let gkr_off = initial_transcript_responses_offset / core::mem::size_of::<u32>();

        let gkr_evals = m::constants::GKR_EVALS;

        let cases: &[(usize, u32, &str)] = &[
            (10, 1, "transcript_start"),
            (gkr_off - 1, 0xFF, "transcript_end"),
            (gkr_off, 1, "first_eval"),
            (gkr_off + 50, 1, "mid_eval"),
            (gkr_off + gkr_evals * 4 + 10, 1, "sumcheck_coeffs"),
        ];

        for &(idx, mask, label) in cases {
            assert_rejects_corrupted_nds(
                name,
                SecurityLevel::Sec80,
                label,
                |nds| nds[idx] ^= mask,
                |r| matches!(r, VerifyRejection::Error(..)),
            );
        }
    });
}

fn test_rejects_corrupted_whir_region(name: &str) {
    let nds_len = common::load_nds(name, SecurityLevel::Sec80).0.len();

    let cases: &[(usize, &str)] = &[
        (nds_len / 2, "whir_early"),
        (nds_len - 100, "whir_late"),
        (nds_len - 1, "last_word"),
    ];

    for &(idx, label) in cases {
        assert_rejects_corrupted_nds(
            name,
            SecurityLevel::Sec80,
            label,
            |nds| nds[idx] ^= 1,
            |r| matches!(r, VerifyRejection::Error(..)),
        );
    }
}

fn test_rejects_zeroed_regions(name: &str) {
    with_circuit!(name, SecurityLevel::Sec80, |m| {
        type InitialTranscript = m::constants::ConcreteInitialTranscript;
        let initial_transcript_responses_offset = core::mem::offset_of!(InitialTranscript, _marker)
            - (core::mem::offset_of!(InitialTranscript, setup_caps)
                - core::mem::offset_of!(InitialTranscript, external_challenges_flattened));
        let gkr_off = initial_transcript_responses_offset / core::mem::size_of::<u32>();

        let nds_len = common::load_nds(name, SecurityLevel::Sec80).0.len();

        let cases: &[(usize, usize, &str)] = &[
            (gkr_off + 200, 32, "sumcheck_chunk"),
            (nds_len * 3 / 4, 64, "whir_chunk"),
        ];

        for &(start, count, label) in cases {
            assert_rejects_corrupted_nds(
                name,
                SecurityLevel::Sec80,
                label,
                |nds| {
                    let end = (start + count).min(nds.len());
                    for i in start..end {
                        nds[i] ^= 0xDEAD_BEEF;
                    }
                },
                |r| matches!(r, VerifyRejection::Error(..)),
            );
        }
    });
}

fn test_rejects_shifted_nds(name: &str) {
    assert_rejects_corrupted_nds(
        name,
        SecurityLevel::Sec80,
        "shifted by one word",
        |nds| nds.insert(0, 0),
        |r| matches!(r, VerifyRejection::Error(..)),
    );
}

fn test_rejects_corrupted_oracle_caps(name: &str) {
    with_circuit!(name, SecurityLevel::Sec80, |m| {
        type InitialTranscript = m::constants::ConcreteInitialTranscript;
        let setup_oracle_commit_offset = core::mem::offset_of!(InitialTranscript, setup_caps);
        let memory_oracle_commit_offset = core::mem::offset_of!(InitialTranscript, memory_caps);
        let witness_oracle_commit_offset = core::mem::offset_of!(InitialTranscript, witness_caps);
        let end_offset = core::mem::offset_of!(InitialTranscript, _marker);

        let setup_oracle_commit_size = memory_oracle_commit_offset - setup_oracle_commit_offset;
        let memory_oracle_commit_size = witness_oracle_commit_offset - memory_oracle_commit_offset;
        let witness_oracle_commit_size = end_offset - witness_oracle_commit_offset;

        let inits_and_teardowns_size =
            core::mem::offset_of!(InitialTranscript, external_challenges_flattened);

        for (cap_name, offset, size) in [
            (
                "setup",
                (inits_and_teardowns_size) / core::mem::size_of::<u32>(),
                setup_oracle_commit_size,
            ),
            (
                "memory",
                (inits_and_teardowns_size + setup_oracle_commit_size) / core::mem::size_of::<u32>(),
                memory_oracle_commit_size,
            ),
            (
                "witness",
                (inits_and_teardowns_size + setup_oracle_commit_size + memory_oracle_commit_size)
                    / core::mem::size_of::<u32>(),
                witness_oracle_commit_size,
            ),
        ] {
            if size == 0 {
                continue;
            }
            let label = format!("oracle_cap_{}", cap_name);
            assert_rejects_corrupted_nds(
                name,
                SecurityLevel::Sec80,
                &label,
                |nds| nds[offset] ^= 1,
                |r| {
                    matches!(
                        r,
                        VerifyRejection::Error(VerificationError::GkrSumcheckRoundFailed { .. })
                    )
                },
            );
        }
    });
}

fn test_rejects_truncated_nds(name: &str) {
    assert_rejects_corrupted_nds(
        name,
        SecurityLevel::Sec80,
        "truncated NDS",
        |nds| {
            let new_len = nds.len() * 9 / 10;
            nds.truncate(new_len);
        },
        |r| matches!(r, VerifyRejection::Panic(..)),
    );
}

fn test_rejects_corrupted_final_monomials(name: &str) {
    with_circuit!(name, SecurityLevel::Sec80, |m| {
        // NDS tail: [final_sumcheck_polys | final_monomials | pow_nonce | final_queries]
        // Compute monomials position by working backward from nds_len.
        let final_fold_steps = *m::constants::WHIR_FOLD_STEPS.last().unwrap();
        let final_num_queries = *m::constants::WHIR_QUERIES.last().unwrap();
        let final_oracle_depth = *m::constants::WHIR_ORACLE_DEPTHS.last().unwrap();
        let leaf_words = (1usize << final_fold_steps) * 4; // ext4 per leaf position
        let path_words = final_oracle_depth * 8; // blake2s digest size per sibling
        let queries_words = final_num_queries * (leaf_words + path_words);
        let pow_words = 2;
        let monomial_words = m::constants::FINAL_MONOMIALS_LEN * 4;
        let nds_len = common::load_nds(name, SecurityLevel::Sec80).0.len();
        let monomials_end = nds_len - queries_words - pow_words;
        let start = monomials_end - monomial_words;
        assert_rejects_corrupted_nds(
            name,
            SecurityLevel::Sec80,
            "corrupted final_monomials",
            |nds| {
                for word in &mut nds[start..monomials_end] {
                    *word ^= 0xDEAD_BEEF;
                }
            },
            |r| matches!(r, VerifyRejection::Panic(..)),
        );
    });
}

fn test_rejects_cross_circuit_nds(name: &str) {
    let other = common::CIRCUITS
        .iter()
        .find(|c| c.name != name)
        .expect("need at least two circuits");

    let other_nds = other.load_nds_for(SecurityLevel::Sec80).0;
    assert_rejects_corrupted_nds(
        name,
        SecurityLevel::Sec80,
        &format!("NDS from {}", other.name),
        |nds| {
            nds.clear();
            nds.extend_from_slice(&other_nds);
        },
        |r| matches!(r, VerifyRejection::Error(..)),
    );
}

fn test_rejects_corrupted_init_teardown_bits(name: &str) {
    let circuit_data = common::circuit_by_name(name);
    let compiled = circuit_data.compiled_circuit();
    let num_teardown_sets = compiled.memory_layout.teardown_sets.len();
    if num_teardown_sets == 0 {
        assert!(
            name != "inits_and_teardowns",
            "inits_and_teardowns circuit must have teardown sets"
        );
        return;
    }
    for i in 0..num_teardown_sets {
        let label = format!("teardown_top_bit_{}", i);
        assert_rejects_corrupted_nds(
            name,
            SecurityLevel::Sec80,
            &label,
            |nds| nds[i] ^= 0xFFFF_FFFF,
            |r| matches!(r, VerifyRejection::Error(..)),
        );
    }
}

fn test_rejects_non_canonical_field_element(name: &str) {
    with_circuit!(name, SecurityLevel::Sec80, |m| {
        type InitialTranscript = m::constants::ConcreteInitialTranscript;
        let initial_transcript_responses_offset = core::mem::offset_of!(InitialTranscript, _marker)
            - (core::mem::offset_of!(InitialTranscript, setup_caps)
                - core::mem::offset_of!(InitialTranscript, external_challenges_flattened));
        let gkr_off = initial_transcript_responses_offset / core::mem::size_of::<u32>();

        assert_rejects_corrupted_nds(
            name,
            SecurityLevel::Sec80,
            "non_canonical_field_element",
            |nds| {
                nds[gkr_off + 4] |= 0x8000_0000;
            },
            |r| {
                matches!(
                    r,
                    VerifyRejection::Error(
                        VerificationError::GkrSumcheckRoundFailed { .. }
                            | VerificationError::GkrFinalStepCheckFailed { .. }
                            | VerificationError::GkrGrandProductCheckFailed
                            | VerificationError::GkrPermutationCacheRelationFailed { .. }
                            | VerificationError::GkrSingleLookupCacheRelationFailed { .. }
                            | VerificationError::GkrVectorLookupCacheRelationFailed { .. }
                            | VerificationError::GkrLookupIdentityFailed { .. }
                            | VerificationError::GkrVirtualSetupEvalMismatch { .. }
                    )
                )
            },
        );
    });
}

fn test_rejects_corrupted_ood_sample(name: &str) {
    let circuit_data = common::circuit_by_name(name);
    let mut proof = circuit_data.proof_for(SecurityLevel::Sec80);
    assert!(
        !proof.whir_proof.ood_samples.is_empty(),
        "{}: proof must have OOD samples",
        name
    );
    proof.whir_proof.ood_samples[0].add_assign(&BabyBearExt4::ONE);
    assert_rejects_via_panic(name, SecurityLevel::Sec80, "corrupted OOD sample", &proof);
}

fn test_rejects_corrupted_pow_nonce(name: &str) {
    let circuit_data = common::circuit_by_name(name);
    let mut proof = circuit_data.proof_for(SecurityLevel::Sec80);
    assert!(
        !proof.whir_proof.pow_nonces.is_empty(),
        "{}: proof must have PoW nonces",
        name
    );
    proof.whir_proof.pow_nonces[0] ^= 1;
    assert_rejects_via_panic(name, SecurityLevel::Sec80, "corrupted PoW nonce", &proof);
}

fn test_rejects_corrupted_lookup_pow_nonce(name: &str, level: SecurityLevel) {
    let circuit_data = common::circuit_by_name(name);
    let mut proof = circuit_data.proof_for(level);
    // The lookup-challenge PoW nonce is bound into the transcript seed. Tampering with it
    // must be rejected — directly by `verify_pow` when the bit-count is non-zero (Sec100),
    // otherwise downstream once the diverged seed corrupts every later challenge (Sec80).
    proof.lookup_challenges_pow_nonce ^= 1;
    assert_rejects_any(name, level, "corrupted lookup PoW nonce", &proof);
}

fn test_rejects_corrupted_batched_proximity_pow_nonce(name: &str, level: SecurityLevel) {
    let circuit_data = common::circuit_by_name(name);
    let mut proof = circuit_data.proof_for(level);
    proof.batched_proximity_check_pow_nonce ^= 1;
    assert_rejects_any(name, level, "corrupted batched-proximity PoW nonce", &proof);
}

#[cfg(not(feature = "no_caches"))]
fn test_rejects_corrupted_cache_relations(name: &str) {
    let circuit_data = common::circuit_by_name(name);
    let mut proof = circuit_data.proof_for(SecurityLevel::Sec80);

    let base_layer = proof
        .sumcheck_intermediate_values
        .get_mut(&0)
        .expect("proof must have layer 0");
    if base_layer
        .extra_evaluations_from_caching_relations
        .is_empty()
    {
        // Circuit has no cached relations at the base layer; nothing to corrupt.
        return;
    }

    let (_addr, eval) = base_layer
        .extra_evaluations_from_caching_relations
        .iter_mut()
        .next()
        .unwrap();
    eval.add_assign(&BabyBearExt4::ONE);

    assert_rejects_with_variant(
        name,
        SecurityLevel::Sec80,
        "corrupted cache relation",
        &proof,
        |e| {
            matches!(
                e,
                VerificationError::GkrSingleLookupCacheRelationFailed { .. }
                    | VerificationError::GkrVectorLookupCacheRelationFailed { .. }
                    | VerificationError::GkrPermutationCacheRelationFailed { .. }
            )
        },
    );
}

fn test_rejects_corrupted_it_evals(name: &str) {
    with_circuit!(name, SecurityLevel::Sec80, |m| {
        type InitialTranscript = m::constants::ConcreteInitialTranscript;
        let initial_transcript_responses_offset = core::mem::offset_of!(InitialTranscript, _marker)
            - (core::mem::offset_of!(InitialTranscript, setup_caps)
                - core::mem::offset_of!(InitialTranscript, external_challenges_flattened));
        let gkr_off = initial_transcript_responses_offset / core::mem::size_of::<u32>();

        assert!(
            m::constants::GKR_EVALS >= 160,
            "{name} must have the 160-eval layout (i/t evals at [128..160])"
        );
        // First word of the first inits/teardowns ext4 eval (evals_slice[128]).
        let it_eval_off = gkr_off + 128 * 4;

        assert_rejects_corrupted_nds(
            name,
            SecurityLevel::Sec80,
            "it_evals",
            |nds| nds[it_eval_off] ^= 1,
            |r| {
                matches!(
                    r,
                    VerifyRejection::Error(
                        VerificationError::GkrSumcheckRoundFailed { .. }
                            | VerificationError::GkrFinalStepCheckFailed { .. }
                            | VerificationError::GkrGrandProductCheckFailed
                    )
                )
            },
        );
    });
}

#[test]
fn rejects_corrupted_it_evals_unified_reduced_machine_sec_80() {
    test_rejects_corrupted_it_evals("unified_reduced_machine");
}

macro_rules! generate_corruption_tests {
    ($($name:ident; $trace_len_log_2:expr; $layout_suffix:expr),* $(,)?) => {
        $(
            paste::paste! {
                #[test]
                fn [<rejects_garbage_proof_ $name _sec_80>]() {
                    test_rejects_garbage_proof(stringify!($name));
                }

                #[test]
                fn [<rejects_corruption_ $name _sec_80>]() {
                    test_rejects_corruption_at_fractions(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_gkr_region_ $name _sec_80>]() {
                    test_rejects_corrupted_gkr_region(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_whir_region_ $name _sec_80>]() {
                    test_rejects_corrupted_whir_region(stringify!($name));
                }

                #[test]
                fn [<rejects_zeroed_regions_ $name _sec_80>]() {
                    test_rejects_zeroed_regions(stringify!($name));
                }

                #[test]
                fn [<rejects_shifted_nds_ $name _sec_80>]() {
                    test_rejects_shifted_nds(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_oracle_caps_ $name _sec_80>]() {
                    test_rejects_corrupted_oracle_caps(stringify!($name));
                }

                #[test]
                fn [<rejects_truncated_nds_ $name _sec_80>]() {
                    test_rejects_truncated_nds(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_final_monomials_ $name _sec_80>]() {
                    test_rejects_corrupted_final_monomials(stringify!($name));
                }

                #[test]
                fn [<rejects_cross_circuit_nds_ $name _sec_80>]() {
                    test_rejects_cross_circuit_nds(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_init_teardown_bits_ $name _sec_80>]() {
                    test_rejects_corrupted_init_teardown_bits(stringify!($name));
                }

                #[test]
                fn [<rejects_non_canonical_field_element_ $name _sec_80>]() {
                    test_rejects_non_canonical_field_element(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_ood_sample_ $name _sec_80>]() {
                    test_rejects_corrupted_ood_sample(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_pow_nonce_ $name _sec_80>]() {
                    test_rejects_corrupted_pow_nonce(stringify!($name));
                }

                #[cfg(not(feature = "no_caches"))]
                #[test]
                fn [<rejects_corrupted_cache_relations_ $name _sec_80>]() {
                    test_rejects_corrupted_cache_relations(stringify!($name));
                }

            }
        )*
    };
}
// The bulk of the corruption suite is Sec80-only (Sec80 NDS layout + Sec80 verifier).
#[cfg(feature = "security_80")]
verifier_common::gkr_circuits!(generate_corruption_tests);

// PoW-nonce corruption runs at every enabled security level — the only corruption tests that
// exercise Sec100. At Sec100 (non-zero PoW bits) these hit `verify_pow`'s threshold-rejection
// branch directly; at Sec80 (0 bits) they verify the nonce is transcript-bound (downstream reject).
macro_rules! generate_pow_nonce_corruption_tests {
    ($($name:ident; $trace_len_log_2:expr; $layout_suffix:expr),* $(,)?) => {
        $(
            paste::paste! {
                #[cfg(feature = "security_80")]
                #[test]
                fn [<rejects_corrupted_lookup_pow_nonce_sec80_ $name>]() {
                    test_rejects_corrupted_lookup_pow_nonce(stringify!($name), SecurityLevel::Sec80);
                }
                #[cfg(feature = "security_100")]
                #[test]
                fn [<rejects_corrupted_lookup_pow_nonce_sec100_ $name>]() {
                    test_rejects_corrupted_lookup_pow_nonce(stringify!($name), SecurityLevel::Sec100);
                }
                #[cfg(feature = "security_80")]
                #[test]
                fn [<rejects_corrupted_batched_proximity_pow_nonce_sec80_ $name>]() {
                    test_rejects_corrupted_batched_proximity_pow_nonce(stringify!($name), SecurityLevel::Sec80);
                }
                #[cfg(feature = "security_100")]
                #[test]
                fn [<rejects_corrupted_batched_proximity_pow_nonce_sec100_ $name>]() {
                    test_rejects_corrupted_batched_proximity_pow_nonce(stringify!($name), SecurityLevel::Sec100);
                }
            }
        )*
    };
}
verifier_common::gkr_circuits!(generate_pow_nonce_corruption_tests);
