#![cfg(feature = "gkr_verify")]

#[macro_use]
mod common;

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::Field;
use prover::gkr::prover::GKRProof;
use prover::merkle_trees::DefaultTreeConstructor;
use verifier_common::gkr::flatten::flatten_gkr_proof_for_nds;

fn assert_rejects_corrupted_nds(name: &str, label: &str, corrupt: impl FnOnce(&mut Vec<u32>)) {
    let mut nds = common::load_nds(name);
    corrupt(&mut nds);
    assert!(
        !common::verify_nds(name, nds),
        "{}: should reject {}",
        name,
        label
    );
}

fn proof_to_nds(
    name: &str,
    proof: &GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>,
) -> Vec<u32> {
    let circuit_data = common::circuit_by_name(name);
    let compiled = circuit_data.compiled_circuit();
    flatten_gkr_proof_for_nds::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
        proof,
        &compiled,
        circuit_data.whir_schedule(),
        &[],
    )
}

fn test_rejects_garbage_proof(name: &str) {
    let nds_len = common::load_nds(name).len();
    assert_rejects_corrupted_nds(name, "garbage proof", |nds| {
        for i in 0..nds_len {
            nds[i] = (i as u32).wrapping_mul(2654435761);
        }
    });
}

fn test_rejects_corruption_at_fractions(name: &str) {
    let nds_len = common::load_nds(name).len();
    for fraction in [0.25, 0.50, 0.75] {
        let label = format!("fraction {:.2}", fraction);
        let idx = (nds_len as f64 * fraction) as usize;
        assert_rejects_corrupted_nds(name, &label, |nds| {
            nds[idx] ^= 1;
        });
    }
}

fn test_rejects_corrupted_gkr_region(name: &str) {
    with_circuit!(name, |m| {
        let gkr_off = m::constants::GKR_TRANSCRIPT_U32;
        let gkr_evals = m::constants::GKR_EVALS;

        let cases: &[(usize, u32, &str)] = &[
            (10, 1, "transcript_start"),
            (gkr_off - 1, 0xFF, "transcript_end"),
            (gkr_off, 1, "first_eval"),
            (gkr_off + 50, 1, "mid_eval"),
            (gkr_off + gkr_evals * 4 + 10, 1, "sumcheck_coeffs"),
        ];

        for &(idx, mask, label) in cases {
            assert_rejects_corrupted_nds(name, label, |nds| {
                nds[idx] ^= mask;
            });
        }
    });
}

fn test_rejects_corrupted_whir_region(name: &str) {
    let nds_len = common::load_nds(name).len();

    let cases: &[(usize, &str)] = &[
        (nds_len / 2, "whir_early"),
        (nds_len - 100, "whir_late"),
        (nds_len - 1, "last_word"),
    ];

    for &(idx, label) in cases {
        assert_rejects_corrupted_nds(name, label, |nds| {
            nds[idx] ^= 1;
        });
    }
}

fn test_rejects_zeroed_regions(name: &str) {
    with_circuit!(name, |m| {
        let gkr_off = m::constants::GKR_TRANSCRIPT_U32;
        let nds_len = common::load_nds(name).len();

        let cases: &[(usize, usize, &str)] = &[
            (gkr_off + 200, 32, "sumcheck_chunk"),
            (nds_len * 3 / 4, 64, "whir_chunk"),
        ];

        for &(start, count, label) in cases {
            assert_rejects_corrupted_nds(name, label, |nds| {
                let end = (start + count).min(nds.len());
                for i in start..end {
                    nds[i] ^= 0xDEAD_BEEF;
                }
            });
        }
    });
}

fn test_rejects_shifted_nds(name: &str) {
    assert_rejects_corrupted_nds(name, "shifted by one word", |nds| {
        nds.insert(0, 0);
    });
}

fn test_rejects_corrupted_oracle_caps(name: &str) {
    with_circuit!(name, |m| {
        let caps_offset = m::constants::CAPS_OFFSET_IN_TRANSCRIPT;
        let cap_offsets = m::constants::ORACLE_CAP_TRANSCRIPT_OFFSETS;

        for (i, &off) in cap_offsets.iter().enumerate() {
            let label = format!("oracle_cap_{}", i);
            assert_rejects_corrupted_nds(name, &label, |nds| {
                nds[caps_offset + off] ^= 1;
            });
        }
    });
}

fn test_rejects_truncated_nds(name: &str) {
    assert_rejects_corrupted_nds(name, "truncated NDS", |nds| {
        let new_len = nds.len() * 9 / 10;
        nds.truncate(new_len);
    });
}

fn test_rejects_corrupted_final_monomials(name: &str) {
    with_circuit!(name, |m| {
        let monomial_words = m::constants::FINAL_MONOMIALS_LEN * 4; // ext4 = 4 u32 per element
        let nds_len = common::load_nds(name).len();
        assert_rejects_corrupted_nds(name, "final_monomials", |nds| {
            let end = nds_len;
            let start = end - monomial_words;
            for i in start..end {
                nds[i] ^= 0xDEAD_BEEF;
            }
        });
    });
}

fn test_rejects_cross_circuit_nds(name: &str) {
    let other = common::CIRCUITS
        .iter()
        .find(|c| c.name != name)
        .expect("need at least two circuits");

    let other_nds = other.load_nds();
    assert_rejects_corrupted_nds(name, &format!("NDS from {}", other.name), |nds| {
        nds.clear();
        nds.extend_from_slice(&other_nds);
    });
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
        assert_rejects_corrupted_nds(name, &label, |nds| {
            nds[i] ^= 0xFFFF_FFFF;
        });
    }
}

fn test_rejects_non_canonical_field_element(name: &str) {
    with_circuit!(name, |m| {
        let gkr_off = m::constants::GKR_TRANSCRIPT_U32;
        assert_rejects_corrupted_nds(name, "non_canonical_field_element", |nds| {
            nds[gkr_off + 4] ^= 0x7800_0001;
        });
    });
}

fn test_rejects_corrupted_ood_sample(name: &str) {
    let circuit_data = common::circuit_by_name(name);
    let mut proof = circuit_data.proof();
    assert!(
        !proof.whir_proof.ood_samples.is_empty(),
        "{}: proof must have OOD samples",
        name
    );
    proof.whir_proof.ood_samples[0].add_assign(&BabyBearExt4::ONE);
    let nds = proof_to_nds(name, &proof);
    assert!(
        !common::verify_nds(name, nds),
        "{}: should reject corrupted OOD sample",
        name
    );
}

fn test_rejects_corrupted_pow_nonce(name: &str) {
    let circuit_data = common::circuit_by_name(name);
    let mut proof = circuit_data.proof();
    assert!(
        !proof.whir_proof.pow_nonces.is_empty(),
        "{}: proof must have PoW nonces",
        name
    );
    proof.whir_proof.pow_nonces[0] ^= 1;
    let nds = proof_to_nds(name, &proof);
    assert!(
        !common::verify_nds(name, nds),
        "{}: should reject corrupted PoW nonce",
        name
    );
}

#[cfg(not(feature = "no_caches"))]
fn test_rejects_corrupted_cache_relations(name: &str) {
    let circuit_data = common::circuit_by_name(name);
    let mut proof = circuit_data.proof();

    let base_layer = proof
        .sumcheck_intermediate_values
        .get_mut(&0)
        .expect("proof must have layer 0");
    assert!(
        !base_layer
            .extra_evaluations_from_caching_relations
            .is_empty(),
        "{}: base layer must have cached relations",
        name
    );

    let (_addr, eval) = base_layer
        .extra_evaluations_from_caching_relations
        .iter_mut()
        .next()
        .unwrap();
    eval.add_assign(&BabyBearExt4::ONE);

    let nds = proof_to_nds(name, &proof);
    assert!(
        !common::verify_nds(name, nds),
        "{}: should reject corrupted cache relation",
        name
    );
}

fn test_rejects_corrupted_grand_product(name: &str) {
    let circuit_data = common::circuit_by_name(name);
    let mut proof = circuit_data.proof();
    proof.grand_product_accumulator_computed = BabyBearExt4::ZERO;
    let nds = proof_to_nds(name, &proof);
    assert!(
        !common::verify_nds(name, nds),
        "{}: should reject corrupted grand_product_accumulator",
        name
    );
}

macro_rules! generate_corruption_tests {
    ($($name:ident: $schedule:ident: $layout_suffix:expr),* $(,)?) => {
        $(
            paste::paste! {
                #[test]
                fn [<rejects_garbage_proof_ $name>]() {
                    test_rejects_garbage_proof(stringify!($name));
                }

                #[test]
                fn [<rejects_corruption_ $name>]() {
                    test_rejects_corruption_at_fractions(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_gkr_region_ $name>]() {
                    test_rejects_corrupted_gkr_region(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_whir_region_ $name>]() {
                    test_rejects_corrupted_whir_region(stringify!($name));
                }

                #[test]
                fn [<rejects_zeroed_regions_ $name>]() {
                    test_rejects_zeroed_regions(stringify!($name));
                }

                #[test]
                fn [<rejects_shifted_nds_ $name>]() {
                    test_rejects_shifted_nds(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_oracle_caps_ $name>]() {
                    test_rejects_corrupted_oracle_caps(stringify!($name));
                }

                #[test]
                fn [<rejects_truncated_nds_ $name>]() {
                    test_rejects_truncated_nds(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_final_monomials_ $name>]() {
                    test_rejects_corrupted_final_monomials(stringify!($name));
                }

                #[test]
                fn [<rejects_cross_circuit_nds_ $name>]() {
                    test_rejects_cross_circuit_nds(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_init_teardown_bits_ $name>]() {
                    test_rejects_corrupted_init_teardown_bits(stringify!($name));
                }

                #[test]
                fn [<rejects_non_canonical_field_element_ $name>]() {
                    test_rejects_non_canonical_field_element(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_ood_sample_ $name>]() {
                    test_rejects_corrupted_ood_sample(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_pow_nonce_ $name>]() {
                    test_rejects_corrupted_pow_nonce(stringify!($name));
                }

                #[cfg(not(feature = "no_caches"))]
                #[test]
                fn [<rejects_corrupted_cache_relations_ $name>]() {
                    test_rejects_corrupted_cache_relations(stringify!($name));
                }

                #[test]
                fn [<rejects_corrupted_grand_product_ $name>]() {
                    test_rejects_corrupted_grand_product(stringify!($name));
                }

            }
        )*
    };
}
verifier_common::gkr_circuits!(generate_corruption_tests);
