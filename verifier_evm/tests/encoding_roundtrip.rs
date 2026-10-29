//! F1 round factorization and the committed proof's transcript replay.
mod common;
use field::{Field, Proth120};
use verifier_evm::encoding::*;
fn fe(v: u128) -> Proth120 {
    Proth120::new(v)
}

#[test]
fn e1_factorization_including_degenerate_points() {
    let p = Proth120::ORDER;
    let u = [fe(5), fe(p - 7), fe(11)];
    let half = fe(2).inverse().unwrap();
    let mut halves = u;
    for v in &mut halves {
        v.mul_assign(&half);
    }
    for (z, coefficients) in [
        (half, [halves[0], halves[1], halves[2], Proth120::ZERO]),
        (Proth120::ONE, [fe(0), fe(5), fe(p - 7), fe(11)]),
        (Proth120::ZERO, [fe(5), fe(p - 12), fe(18), fe(p - 11)]),
        (fe(3), [fe(p - 10), fe(39), fe(p - 57), fe(55)]),
    ] {
        assert_eq!(split_round(&coefficients, z), u);
    }
    for (z, bad) in [
        (half, [fe(0), fe(1), fe(2), fe(3)]),
        (Proth120::ONE, [fe(1), fe(1), fe(2), fe(3)]),
    ] {
        assert!(std::panic::catch_unwind(|| split_round(&bad, z)).is_err());
    }
}

#[test]
fn replay_reaches_the_whir_batching_claim() {
    let (circuit, proof, aux) = common::load();
    let replay = replay_gkr_points(&circuit, &proof, &aux, &common::prover_config());
    // dimension-reducing layers bind e..t−1 variables, the circuit layers t each
    let config = common::prover_config();
    let (e, t) = (
        config.sumcheck_explicit_output_size_log_2,
        config.trace_len_log2,
    );
    let rounds: usize = replay.layers.iter().map(|l| l.r.len()).sum();
    assert_eq!(rounds, (e..t).sum::<usize>() + circuit.layers.len() * t);
}

#[test]
fn encoder_rejects_a_config_the_proof_does_not_fit() {
    let (circuit, proof, aux) = common::load();
    let config = common::prover_config();
    let params = common::f1_params();
    let encode = |config: prover::gkr::prover_config::ProverConfig| {
        encode_single_tx(&circuit, &proof, &aux, &config, &params)
    };
    let mut invalid = config.clone();
    invalid.whir_schedule.base_round.physical_packing_log2 = 0;
    common::assert_panics_with("expected packed merged prover config", || encode(invalid));
    let mut invalid = config.clone();
    invalid.whir_schedule.base_round.fold_log2 += 1;
    invalid.whir_schedule.internal_rounds[0].folding_log2 -= 1;
    common::assert_panics_with("profile folds differ from the proof", || encode(invalid));
    let mut invalid = config.clone();
    invalid.whir_schedule.base_round.num_queries -= 1;
    common::assert_panics_with("profile queries differ from the proof", || encode(invalid));
    let mut invalid = config.clone();
    invalid.sumcheck_explicit_output_size_log_2 -= 1;
    common::assert_panics_with("profile explicit output log differs from the proof", || {
        encode(invalid)
    });
    let mut invalid = config.clone();
    invalid.trace_len_log2 += 1;
    common::assert_panics_with("profile trace log differs from the circuit", || {
        encode(invalid)
    });
    let mut invalid = config;
    invalid.whir_schedule.cap_size *= 2;
    common::assert_panics_with("profile cap differs from the proof", || encode(invalid));
}
