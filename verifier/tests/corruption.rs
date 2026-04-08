#![cfg(feature = "gkr_verify")]

#[macro_use]
mod common;

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
                    m::verify::<ThreadLocalBasedSource>().map_err(|e| format!("{:?}", e))
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

fn assert_rejects_zeroed(name: &str, start: usize, count: usize, label: &str) {
    let result = run_corrupted(name, |nds| {
        for i in start..start + count {
            if i < nds.len() {
                nds[i] = 0;
            }
        }
    });
    assert!(
        result.is_err(),
        "{}: should reject zeroed region at {}",
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

const CIRCUIT: &str = "add_sub_lui_auipc_mop";

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
                    m::verify::<ThreadLocalBasedSource>().map_err(|e| format!("{:?}", e))
                })
            })
            .expect("failed to spawn thread");

        handle.join().unwrap()
    })
}

#[cfg(not(feature = "no_caches"))]
#[test]
fn rejects_corrupted_cache_relations() {
    let circuit_data = common::circuit_by_name(CIRCUIT);
    let mut proof = circuit_data.proof();

    // The base layer (layer 0) has cached relations: certain claims must equal
    // a linear combination of other claims. The extra_evaluations_from_caching_relations
    // field carries these values. Corrupting one should trigger CacheRelationFailed.
    let base_layer = proof
        .sumcheck_intermediate_values
        .get_mut(&0)
        .expect("proof must have layer 0");
    assert!(
        !base_layer
            .extra_evaluations_from_caching_relations
            .is_empty(),
        "base layer must have cached relations"
    );

    // Corrupt the first cached relation evaluation by adding ONE
    let (_addr, eval) = base_layer
        .extra_evaluations_from_caching_relations
        .iter_mut()
        .next()
        .unwrap();
    eval.add_assign(&BabyBearExt4::ONE);

    let result = run_with_proof(CIRCUIT, &proof);
    assert!(result.is_err(), "should reject corrupted cache relation");
    let err = result.unwrap_err();
    assert!(
        err.contains("CacheRelationFailed"),
        "expected CacheRelationFailed, got: {}",
        err
    );
}

#[test]
fn rejects_corrupted_gkr_region() {
    let gkr_off = verifier::add_sub_lui_auipc_mop::constants::GKR_TRANSCRIPT_U32;
    let gkr_evals = verifier::add_sub_lui_auipc_mop::constants::GKR_EVALS;

    let cases: &[(usize, u32, &str)] = &[
        (10, 1, "transcript_start"),
        (gkr_off - 1, 0xFF, "transcript_end"),
        (gkr_off, 1, "first_eval"),
        (gkr_off + 50, 1, "mid_eval"),
        (gkr_off + gkr_evals * 4 + 10, 1, "sumcheck_coeffs"),
    ];

    for &(idx, mask, label) in cases {
        assert_rejects_xor(CIRCUIT, idx, mask, label);
    }
}

#[test]
fn rejects_corrupted_whir_region() {
    let nds_len = common::load_nds(CIRCUIT).len();

    let cases: &[(usize, &str)] = &[
        (nds_len / 2, "whir_early"),
        (nds_len - 100, "whir_late"),
        (nds_len - 1, "last_word"),
    ];

    for &(idx, label) in cases {
        assert_rejects_xor(CIRCUIT, idx, 1, label);
    }
}

#[test]
fn rejects_zeroed_regions() {
    let gkr_off = verifier::add_sub_lui_auipc_mop::constants::GKR_TRANSCRIPT_U32;
    let nds_len = common::load_nds(CIRCUIT).len();

    let cases: &[(usize, usize, &str)] = &[
        (gkr_off + 200, 32, "sumcheck_chunk"),
        (nds_len * 3 / 4, 64, "whir_chunk"),
    ];

    for &(start, count, label) in cases {
        assert_rejects_zeroed(CIRCUIT, start, count, label);
    }
}

const DELEGATION_CIRCUIT: &str = "keccak_special5";

#[cfg(not(feature = "no_caches"))]
#[test]
fn delegation_rejects_corrupted_cache_relations() {
    let circuit_data = common::circuit_by_name(DELEGATION_CIRCUIT);
    let mut proof = circuit_data.proof();

    let base_layer = proof
        .sumcheck_intermediate_values
        .get_mut(&0)
        .expect("proof must have layer 0");
    assert!(
        !base_layer
            .extra_evaluations_from_caching_relations
            .is_empty(),
        "base layer must have cached relations"
    );

    let (_addr, eval) = base_layer
        .extra_evaluations_from_caching_relations
        .iter_mut()
        .next()
        .unwrap();
    eval.add_assign(&BabyBearExt4::ONE);

    let result = run_with_proof(DELEGATION_CIRCUIT, &proof);
    assert!(result.is_err(), "should reject corrupted cache relation");
    let err = result.unwrap_err();
    assert!(
        err.contains("CacheRelationFailed"),
        "expected CacheRelationFailed, got: {}",
        err
    );
}

#[test]
fn delegation_rejects_corrupted_gkr_region() {
    let gkr_off = verifier::keccak_special5::constants::GKR_TRANSCRIPT_U32;
    let gkr_evals = verifier::keccak_special5::constants::GKR_EVALS;

    let cases: &[(usize, u32, &str)] = &[
        (10, 1, "transcript_start"),
        (gkr_off - 1, 0xFF, "transcript_end"),
        (gkr_off, 1, "first_eval"),
        (gkr_off + 50, 1, "mid_eval"),
        (gkr_off + gkr_evals * 4 + 10, 1, "sumcheck_coeffs"),
    ];

    for &(idx, mask, label) in cases {
        assert_rejects_xor(DELEGATION_CIRCUIT, idx, mask, label);
    }
}

#[test]
fn delegation_rejects_corrupted_whir_region() {
    let nds_len = common::load_nds(DELEGATION_CIRCUIT).len();

    let cases: &[(usize, &str)] = &[
        (nds_len / 2, "whir_early"),
        (nds_len - 100, "whir_late"),
        (nds_len - 1, "last_word"),
    ];

    for &(idx, label) in cases {
        assert_rejects_xor(DELEGATION_CIRCUIT, idx, 1, label);
    }
}

#[test]
fn rejects_garbage_proof() {
    // A completely random NDS should be rejected by every circuit.
    for circuit in common::CIRCUITS.iter() {
        let nds_len = circuit.load_nds().len();
        let result = run_corrupted(circuit.name, |nds| {
            // Deterministic "random" fill: use index as seed
            for i in 0..nds_len {
                nds[i] = (i as u32).wrapping_mul(2654435761); // Knuth multiplicative hash
            }
        });
        assert!(
            result.is_err(),
            "{}: should reject garbage proof",
            circuit.name
        );
    }
}

#[test]
fn all_circuits_reject_corruption() {
    for circuit in common::CIRCUITS.iter() {
        let nds_len = circuit.load_nds().len();
        for fraction in [0.25, 0.50, 0.75] {
            let idx = (nds_len as f64 * fraction) as usize;
            let label = format!("fraction {:.2}", fraction);
            assert_rejects_xor(circuit.name, idx, 1, &label);
        }
    }
}
