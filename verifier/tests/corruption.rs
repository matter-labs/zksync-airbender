#![cfg(feature = "gkr_verify")]

#[macro_use]
mod common;

use verifier_common::errors::DebugErrorCreator;
use verifier_common::prover::nd_source_std::{set_iterator, ThreadLocalBasedSource};

fn run_corrupted(name: &str, corrupt: impl FnOnce(&mut Vec<u32>)) -> Result<(), String> {
    let mut nds = common::load_nds(name);
    corrupt(&mut nds);

    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(format!("corruption_{}", name))
            .stack_size(1 << 27)
            .spawn_scoped(s, move || {
                set_iterator(nds.into_iter());
                with_circuit!(name, |m| {
                    m::verify::<ThreadLocalBasedSource, DebugErrorCreator>()
                        .map_err(|e| format!("{:?}", e))
                })
            })
            .expect("failed to spawn thread");

        handle.join().unwrap()
    })
}

fn assert_rejects_xor(name: &str, idx: usize, mask: u32, label: &str) {
    let result = run_corrupted(name, |nds| {
        nds[idx] ^= mask;
    });
    assert!(
        result.is_err(),
        "{}: should reject corruption at {}",
        name,
        label
    );
}

fn assert_rejects_overwritten(name: &str, start: usize, count: usize, label: &str) {
    let result = run_corrupted(name, |nds| {
        let end = (start + count).min(nds.len());
        for i in start..end {
            nds[i] ^= 0xDEAD_BEEF;
        }
    });
    assert!(
        result.is_err(),
        "{}: should reject overwritten region at {}",
        name,
        label
    );
}

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::Field;
use prover::gkr::prover::GKRProof;
use prover::merkle_trees::DefaultTreeConstructor;
use verifier_common::gkr::flatten::flatten_gkr_proof_for_nds;

fn run_with_proof(
    name: &str,
    proof: &GKRProof<BabyBearField, BabyBearExt4, DefaultTreeConstructor>,
) -> Result<(), String> {
    let circuit_data = common::circuit_by_name(name);
    let compiled = circuit_data.compiled_circuit();
    let nds = flatten_gkr_proof_for_nds::<BabyBearField, BabyBearExt4, DefaultTreeConstructor>(
        proof,
        &compiled,
        circuit_data.whir_schedule(),
        &[],
    );

    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(format!("corruption_proof_{}", name))
            .stack_size(1 << 27)
            .spawn_scoped(s, move || {
                set_iterator(nds.into_iter());
                with_circuit!(name, |m| {
                    m::verify::<ThreadLocalBasedSource, DebugErrorCreator>()
                        .map_err(|e| format!("{:?}", e))
                })
            })
            .expect("failed to spawn thread");

        handle.join().unwrap()
    })
}

fn test_rejects_garbage_proof(name: &str) {
    let nds_len = common::load_nds(name).len();
    let result = run_corrupted(name, |nds| {
        for i in 0..nds_len {
            nds[i] = (i as u32).wrapping_mul(2654435761);
        }
    });
    assert!(result.is_err(), "{}: should reject garbage proof", name);
}

fn test_rejects_corruption_at_fractions(name: &str) {
    let nds_len = common::load_nds(name).len();
    for fraction in [0.25, 0.50, 0.75] {
        let idx = (nds_len as f64 * fraction) as usize;
        let label = format!("fraction {:.2}", fraction);
        assert_rejects_xor(name, idx, 1, &label);
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
            assert_rejects_xor(name, idx, mask, label);
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
        assert_rejects_xor(name, idx, 1, label);
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
            assert_rejects_overwritten(name, start, count, label);
        }
    });
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

    let result = run_with_proof(name, &proof);
    assert!(
        result.is_err(),
        "{}: should reject corrupted cache relation",
        name
    );
    let err = result.unwrap_err();
    assert!(
        err.contains("CacheRelationFailed"),
        "{}: expected CacheRelationFailed, got: {}",
        name,
        err
    );
}

fn test_rejects_shifted_nds(name: &str) {
    let result = run_corrupted(name, |nds| {
        nds.insert(0, 0);
    });
    assert!(
        result.is_err(),
        "{}: should reject NDS shifted by one word",
        name
    );
}

fn test_rejects_corrupted_oracle_caps(name: &str) {
    with_circuit!(name, |m| {
        let caps_offset = m::constants::CAPS_OFFSET_IN_TRANSCRIPT;
        let cap_offsets = m::constants::ORACLE_CAP_TRANSCRIPT_OFFSETS;

        for (i, &off) in cap_offsets.iter().enumerate() {
            let label = format!("oracle_cap_{}", i);
            assert_rejects_xor(name, caps_offset + off, 1, &label);
        }
    });
}

/// Run a corrupted NDS through the verifier, treating both Err returns and panics
/// (e.g. iterator exhaustion) as rejection. Captures panic messages for debugging.
fn run_corrupted_panic_safe(name: &str, corrupt: impl FnOnce(&mut Vec<u32>)) -> bool {
    let mut nds = common::load_nds(name);
    corrupt(&mut nds);

    let prev_hook = std::panic::take_hook();
    let panic_msg = std::sync::Arc::new(std::sync::Mutex::new(None::<String>));
    let panic_msg_clone = panic_msg.clone();
    std::panic::set_hook(Box::new(move |info| {
        *panic_msg_clone.lock().unwrap() = Some(format!("{}", info));
    }));

    let accepted = std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(format!("corruption_{}", name))
            .stack_size(1 << 27)
            .spawn_scoped(s, move || {
                set_iterator(nds.into_iter());
                with_circuit!(name, |m| {
                    m::verify::<ThreadLocalBasedSource, DebugErrorCreator>()
                        .map_err(|e| format!("{:?}", e))
                })
            })
            .expect("failed to spawn thread");

        matches!(handle.join(), Ok(Ok(())))
    });

    std::panic::set_hook(prev_hook);

    if !accepted {
        if let Some(msg) = panic_msg.lock().unwrap().take() {
            eprintln!("  [corruption test] {} rejected via panic: {}", name, msg);
        }
    }

    accepted
}

fn test_rejects_truncated_nds(name: &str) {
    let accepted = run_corrupted_panic_safe(name, |nds| {
        let new_len = nds.len() * 9 / 10;
        nds.truncate(new_len);
    });
    assert!(!accepted, "{}: should reject truncated NDS", name);
}

fn test_rejects_corrupted_final_monomials(name: &str) {
    with_circuit!(name, |m| {
        let monomial_words = m::constants::FINAL_MONOMIALS_LEN * 4; // ext4 = 4 u32 per element
        let nds_len = common::load_nds(name).len();
        assert_rejects_overwritten(
            name,
            nds_len - monomial_words,
            monomial_words,
            "final_monomials",
        );
    });
}

fn test_rejects_cross_circuit_nds(name: &str) {
    let other = common::CIRCUITS
        .iter()
        .find(|c| c.name != name)
        .expect("need at least two circuits");

    let accepted = run_corrupted_panic_safe(name, |nds| {
        let other_nds = other.load_nds();
        nds.clear();
        nds.extend_from_slice(&other_nds);
    });
    assert!(!accepted, "{}: should reject NDS from {}", name, other.name);
}

fn test_rejects_corrupted_init_teardown_bits(name: &str) {
    let circuit_data = common::circuit_by_name(name);
    let compiled = circuit_data.compiled_circuit();
    let num_teardown_sets = compiled.memory_layout.teardown_sets.len();
    if num_teardown_sets == 0 {
        return;
    }
    for i in 0..num_teardown_sets {
        let label = format!("teardown_top_bit_{}", i);
        assert_rejects_xor(name, i, 0xFFFF_FFFF, &label);
    }
}

fn test_rejects_non_canonical_field_element(name: &str) {
    with_circuit!(name, |m| {
        let gkr_off = m::constants::GKR_TRANSCRIPT_U32;
        assert_rejects_xor(
            name,
            gkr_off + 4,
            0x7800_0001,
            "non_canonical_field_element",
        );
    });
}

macro_rules! generate_corruption_tests {
    ($($name:ident: $schedule:ident),* $(,)?) => {
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

                #[cfg(not(feature = "no_caches"))]
                #[test]
                fn [<rejects_corrupted_cache_relations_ $name>]() {
                    test_rejects_corrupted_cache_relations(stringify!($name));
                }
            }
        )*
    };
}
verifier_common::gkr_circuits!(generate_corruption_tests);
