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
                    m::verify_all::<ThreadLocalBasedSource>().map_err(|e| format!("{:?}", e))
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

use verifier_common::gkr::GKRVerificationError;

const CIRCUIT: &str = "add_sub_lui_auipc_mop";

fn run_corrupted_typed(
    name: &str,
    corrupt: impl FnOnce(&mut Vec<u32>),
) -> Result<(), verifier::add_sub_lui_auipc_mop::VerificationError> {
    let mut nds = common::load_nds(name);
    corrupt(&mut nds);

    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name(format!("corruption_typed_{}", name))
            .stack_size(1 << 27)
            .spawn_scoped(s, move || {
                set_iterator(nds.into_iter());
                verifier::add_sub_lui_auipc_mop::verify_all::<ThreadLocalBasedSource>()
            })
            .expect("failed to spawn thread");

        handle.join().unwrap()
    })
}

fn is_cache_relation_error(err: &verifier::add_sub_lui_auipc_mop::VerificationError) -> bool {
    matches!(
        err,
        verifier::add_sub_lui_auipc_mop::VerificationError::Gkr(
            GKRVerificationError::CacheRelationFailed { .. }
        )
    )
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
