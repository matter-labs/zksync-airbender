//! The sumcheck round wire messages of both
//! [`SumcheckCoefficientsStrategy`]s: the message builders of
//! `crate::gkr::sumcheck`, and the serialized layout of the proof fields
//! that carry them.

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::Field;

use super::utils::*;
use crate::definitions::SumcheckCoefficientsStrategy;
use crate::gkr::prover::{GKRProof, GKRSumcheckRoundMessage, SumcheckRoundCoefficients};
use crate::gkr::prover_config::ProverConfig;
use crate::gkr::sumcheck::{
    evaluate_eq_poly, evaluate_small_univariate_poly, next_normalized_sumcheck_claim,
    output_sumcheck_round_message_max_quadratic, whir_sumcheck_round_message,
};
use crate::gkr::whir::WhirSumcheckRoundMessage;
use crate::merkle_trees::DefaultTreeConstructor;

type F = BabyBearField;
type E = BabyBearExt4;

/// Both strategies describe the same round: from `h(X) = e + d * X + c * X^2`
/// and its claim, `Plain` sends the cubic `eq(tau, X) * h(X)`, `Minimal`
/// sends `[d, c]`, and both open to `h(r)`.
#[test]
fn gkr_round_message_strategies_agree_on_the_next_claim() {
    for _ in 0..16 {
        let [e, d, c, tau, r]: [E; 5] = random_poly_in_ext::<F, E>(5).try_into().unwrap();

        // H = (1 - tau) * h(0) + tau * h(1)
        let h = [e, d, c];
        let h0 = evaluate_small_univariate_poly::<F, E, 3>(&h, &E::ZERO);
        let h1 = evaluate_small_univariate_poly::<F, E, 3>(&h, &E::ONE);
        let mut claim = h1;
        claim.sub_assign(&h0);
        claim.mul_assign(&tau);
        claim.add_assign(&h0);
        let h_at_r = evaluate_small_univariate_poly::<F, E, 3>(&h, &r);

        let plain = output_sumcheck_round_message_max_quadratic::<F, E>(
            SumcheckCoefficientsStrategy::Plain,
            tau,
            claim,
            e,
            c,
        );
        assert_eq!(plain.len(), 4);
        // the cubic is eq(tau, X) * h(X)
        let cubic: &[E; 4] = plain.as_slice().try_into().unwrap();
        let mut expected = h_at_r;
        expected.mul_assign(&evaluate_eq_poly::<F, E>(&r, &tau));
        assert_eq!(
            evaluate_small_univariate_poly::<F, E, 4>(cubic, &r),
            expected
        );

        let minimal = output_sumcheck_round_message_max_quadratic::<F, E>(
            SumcheckCoefficientsStrategy::Minimal,
            tau,
            claim,
            e,
            c,
        );
        assert_eq!(minimal.as_slice(), &[d, c]);

        for (strategy, message) in [
            (SumcheckCoefficientsStrategy::Plain, &plain),
            (SumcheckCoefficientsStrategy::Minimal, &minimal),
        ] {
            assert_eq!(
                next_normalized_sumcheck_claim::<F, E>(strategy, message, tau, claim, &r),
                h_at_r,
                "{strategy:?}"
            );
        }
    }
}

/// `Minimal` drops exactly the coefficient the claim determines.
#[test]
fn whir_round_message_drops_only_the_linear_coefficient() {
    let coeffs: [E; 3] = random_poly_in_ext::<F, E>(3).try_into().unwrap();
    let mut claim = evaluate_small_univariate_poly::<F, E, 3>(&coeffs, &E::ZERO);
    claim.add_assign(&evaluate_small_univariate_poly::<F, E, 3>(&coeffs, &E::ONE));

    let plain = whir_sumcheck_round_message(SumcheckCoefficientsStrategy::Plain, &coeffs);
    assert_eq!(plain.as_slice(), &coeffs);

    let minimal = whir_sumcheck_round_message(SumcheckCoefficientsStrategy::Minimal, &coeffs);
    assert_eq!(minimal.as_slice(), &[coeffs[0], coeffs[2]]);
    // c1 = claim - 2 * c0 - c2
    let mut c1 = claim;
    c1.sub_assign(&minimal[0]);
    c1.sub_assign(&minimal[0]);
    c1.sub_assign(&minimal[1]);
    assert_eq!(c1, coeffs[1]);
}

/// The `ArrayVec` messages serialize exactly like the fixed arrays they
/// replaced, and a JSON written from those arrays deserializes into them.
#[test]
fn round_messages_keep_the_fixed_array_json_layout() {
    let gkr: [E; 4] = random_poly_in_ext::<F, E>(4).try_into().unwrap();
    let as_array = serde_json::to_string(&gkr).unwrap();
    let message: GKRSumcheckRoundMessage<E> = gkr.into();
    assert_eq!(serde_json::to_string(&message).unwrap(), as_array);
    let parsed: GKRSumcheckRoundMessage<E> = serde_json::from_str(&as_array).unwrap();
    assert_eq!(parsed, message);

    // the enum the proof stores, in the layout the fixed-array variant had
    let legacy = format!("{{\"Multilinear\":{as_array}}}");
    let round: SumcheckRoundCoefficients<E> = serde_json::from_str(&legacy).unwrap();
    assert_eq!(round.as_multilinear(), &gkr);
    assert_eq!(serde_json::to_string(&round).unwrap(), legacy);

    let whir: [E; 3] = random_poly_in_ext::<F, E>(3).try_into().unwrap();
    let as_array = serde_json::to_string(&whir).unwrap();
    let message: WhirSumcheckRoundMessage<E> = whir.into();
    assert_eq!(serde_json::to_string(&message).unwrap(), as_array);
    let parsed: WhirSumcheckRoundMessage<E> = serde_json::from_str(&as_array).unwrap();
    assert_eq!(parsed, message);

    // a shorter (minimal) message round-trips, a longer one is rejected
    let minimal: GKRSumcheckRoundMessage<E> = gkr[..2].iter().copied().collect();
    let json = serde_json::to_string(&minimal).unwrap();
    assert_eq!(
        serde_json::from_str::<GKRSumcheckRoundMessage<E>>(&json).unwrap(),
        minimal
    );
    let too_long = serde_json::to_string(&[gkr[0]; 4]).unwrap();
    assert!(serde_json::from_str::<WhirSumcheckRoundMessage<E>>(&too_long).is_err());
}

/// Proofs and prover configs tracked in the repository — written before the
/// coefficients strategy existed — deserialize as `Plain`, and a proof
/// re-serializes to its original JSON plus the one new field.
#[test]
fn tracked_proofs_and_configs_deserialize_unchanged() {
    for name in [
        "add_sub_lui_auipc_mop_sec_100_gkr_proof.json",
        "add_sub_lui_auipc_mop_sec_100_ethproofs_soundcalc_gkr_proof.json",
    ] {
        let path = format!("test_proofs/{name}");
        let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
        let mut original: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        let proof: GKRProof<F, E, DefaultTreeConstructor> = serde_json::from_slice(&bytes).unwrap();

        assert_eq!(
            proof.sumcheck_coefficients_strategy,
            SumcheckCoefficientsStrategy::Plain
        );
        for values in proof.sumcheck_intermediate_values.values() {
            for round in values.internal_round_coefficients.iter() {
                assert_eq!(round.as_multilinear().len(), 4);
            }
        }
        assert!(proof.whir_proof.all_sumcheck_polys().count() > 0);
        for poly in proof.whir_proof.all_sumcheck_polys() {
            assert_eq!(poly.len(), 3);
        }

        let object = original.as_object_mut().unwrap();
        assert!(!object.contains_key("sumcheck_coefficients_strategy"));
        object.insert(
            "sumcheck_coefficients_strategy".to_string(),
            serde_json::Value::String("Plain".to_string()),
        );
        assert_eq!(serde_json::to_value(&proof).unwrap(), original, "{name}");
    }

    for name in [
        "prover_config_sec_100_pessimistic_conjecture.json",
        "prover_config_sec_100_ethproofs_soundcalc.json",
    ] {
        let path =
            format!("../circuit_defs/unrolled_circuits/add_sub_lui_auipc_mop/generated/{name}");
        let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
        let config: ProverConfig = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(
            config.sumcheck_coefficients_strategy,
            SumcheckCoefficientsStrategy::Plain
        );
    }
}

fn add(a: E, b: E) -> E {
    let mut t = a;
    t.add_assign(&b);
    t
}

fn sub(a: E, b: E) -> E {
    let mut t = a;
    t.sub_assign(&b);
    t
}

fn mul(a: E, b: E) -> E {
    let mut t = a;
    t.mul_assign(&b);
    t
}

/// Values where a format that divides (by the claim-point coordinate, by a
/// claim, by a coefficient) would break down, plus random ones.
fn degenerate_and_random_values() -> Vec<E> {
    let minus_one = sub(E::ZERO, E::ONE);
    let mut values = vec![E::ZERO, E::ONE, minus_one];
    values.extend(random_poly_in_ext::<F, E>(2));
    values
}

/// The `Minimal` verifier never divides and never branches, so its implicit
/// round polynomial satisfies the round constraint for EVERY combination of
/// claim-point coordinate, running claim and prover coefficients — zeros
/// included: the message `[d, c]` always opens a quadratic `h` with
/// `(1 - tau) * h(0) + tau * h(1) == claim`. The map from messages to such
/// quadratics is a bijection, so a prover gains no freedom over `Plain`.
#[test]
fn minimal_gkr_round_constraint_holds_for_degenerate_values() {
    let values = degenerate_and_random_values();
    let open = |message: &[E; 2], tau: E, claim: E, r: E| {
        next_normalized_sumcheck_claim::<F, E>(
            SumcheckCoefficientsStrategy::Minimal,
            message,
            tau,
            claim,
            &r,
        )
    };
    for &tau in &values {
        for &claim in &values {
            for &d in &values {
                for &c in &values {
                    let message = [d, c];
                    let h0 = open(&message, tau, claim, E::ZERO);
                    let h1 = open(&message, tau, claim, E::ONE);
                    // (1 - tau) * h(0) + tau * h(1)
                    let sum = add(h0, mul(tau, sub(h1, h0)));
                    assert_eq!(sum, claim, "tau {tau:?} claim {claim:?} d {d:?} c {c:?}");
                    // and the opened polynomial is the quadratic with the
                    // sent linear and quadratic coefficients
                    assert_eq!(sub(sub(h1, h0), c), d);
                    let r = values[values.len() - 1];
                    let expected = add(h0, mul(r, add(d, mul(r, c))));
                    assert_eq!(open(&message, tau, claim, r), expected);
                }
            }
        }
    }
}

/// Same for the WHIR step: `[c0, c2]` with `c1 = claim - 2 * c0 - c2` always
/// opens a quadratic whose sum over `{0, 1}` is the claim.
#[test]
fn minimal_whir_round_constraint_holds_for_degenerate_values() {
    let values = degenerate_and_random_values();
    for &claim in &values {
        for &c0 in &values {
            for &c2 in &values {
                // the generated `verify_whir_sumcheck_step_minimal`
                let c1 = sub(sub(sub(claim, c0), c0), c2);
                let s0 = c0;
                let s1 = add(add(c0, c1), c2);
                assert_eq!(add(s0, s1), claim);
                // the honest builder sends exactly these two coefficients
                let message = whir_sumcheck_round_message(
                    SumcheckCoefficientsStrategy::Minimal,
                    &[c0, c1, c2],
                );
                assert_eq!(message.as_slice(), &[c0, c2]);
            }
        }
    }
}

/// `eq(tau, x)` over the hypercube index `x`, LSB-first (bit `k` of `x` pairs
/// with `tau[k]`).
fn eq_weight_lsb_first(tau: &[E], x: usize) -> E {
    tau.iter().enumerate().fold(E::ONE, |acc, (k, t)| {
        let factor = if (x >> k) & 1 == 1 {
            *t
        } else {
            sub(E::ONE, *t)
        };
        mul(acc, factor)
    })
}

fn product_claim(a: &[E], b: &[E], tau: &[E]) -> E {
    (0..a.len()).fold(E::ZERO, |acc, x| {
        add(acc, mul(eq_weight_lsb_first(tau, x), mul(a[x], b[x])))
    })
}

struct SumcheckRun {
    accepted: bool,
    /// whether any sent message differed from the honest one
    tampered: bool,
}

/// A whole `Minimal` sumcheck of `sum_x eq(tau, x) * a(x) * b(x)` (LSB-first
/// binding) between a division-free reference prover and the `Minimal`
/// verifier update, closed by the final check against the gate on the folded
/// values. `tamper(round, honest message)` is what the prover actually
/// sends.
fn run_minimal_product_sumcheck(
    a: &[E],
    b: &[E],
    tau: &[E],
    challenges: &[E],
    claimed: E,
    tamper: impl Fn(usize, [E; 2]) -> [E; 2],
) -> SumcheckRun {
    let rounds = tau.len();
    assert_eq!(a.len(), 1 << rounds);
    let (mut a, mut b) = (a.to_vec(), b.to_vec());
    let mut claim = claimed;
    let mut tampered = false;
    for round in 0..rounds {
        let pairs = a.len() / 2;
        // eq over the not yet bound coordinates above this round's
        let suffix = &tau[round + 1..];
        let (mut h0, mut h1, mut quadratic) = (E::ZERO, E::ZERO, E::ZERO);
        for j in 0..pairs {
            let w = eq_weight_lsb_first(suffix, j);
            h0 = add(h0, mul(w, mul(a[2 * j], b[2 * j])));
            h1 = add(h1, mul(w, mul(a[2 * j + 1], b[2 * j + 1])));
            let da = sub(a[2 * j + 1], a[2 * j]);
            let db = sub(b[2 * j + 1], b[2 * j]);
            quadratic = add(quadratic, mul(w, mul(da, db)));
        }
        let honest = [sub(sub(h1, h0), quadratic), quadratic];
        // the production builder sends the same message wherever it is
        // defined (it derives `d` from the true claim through `1 / tau`)
        if tau[round] != E::ZERO {
            let true_claim = add(h0, mul(tau[round], sub(h1, h0)));
            let built = output_sumcheck_round_message_max_quadratic::<F, E>(
                SumcheckCoefficientsStrategy::Minimal,
                tau[round],
                true_claim,
                h0,
                quadratic,
            );
            assert_eq!(built.as_slice(), &honest);
        }
        let message = tamper(round, honest);
        tampered |= message != honest;

        let r = challenges[round];
        claim = next_normalized_sumcheck_claim::<F, E>(
            SumcheckCoefficientsStrategy::Minimal,
            &message,
            tau[round],
            claim,
            &r,
        );
        for j in 0..pairs {
            a[j] = add(a[2 * j], mul(r, sub(a[2 * j + 1], a[2 * j])));
            b[j] = add(b[2 * j], mul(r, sub(b[2 * j + 1], b[2 * j])));
        }
        a.truncate(pairs);
        b.truncate(pairs);
    }
    SumcheckRun {
        // `verify_final_step_check_minimal`
        accepted: mul(a[0], b[0]) == claim,
        tampered,
    }
}

/// Forgery attempts against the `Minimal` round format around the values
/// where a careless format degenerates: a true or a claimed ZERO claim, ZERO
/// prover coefficients, and claim points with coordinates 0 and 1 (where a
/// format deriving a coefficient by dividing by `tau` or `1 - tau` would
/// accept anything). Honest runs accept in every setting; every false claim
/// is rejected whatever is sent, and a true claim is accepted exactly when
/// no message was changed.
#[test]
fn minimal_sumcheck_rejects_forgeries_in_degenerate_settings() {
    const ROUNDS: usize = 5;
    let size = 1usize << ROUNDS;
    let honest = |_: usize, message: [E; 2]| message;
    let zeros = |_: usize, _: [E; 2]| [E::ZERO; 2];

    let random_tau = random_poly_in_ext::<F, E>(ROUNDS);
    let mut tau_with_zero = random_tau.clone();
    tau_with_zero[0] = E::ZERO;
    tau_with_zero[3] = E::ZERO;
    let mut tau_with_one = random_tau.clone();
    tau_with_one[1] = E::ONE;
    tau_with_one[ROUNDS - 1] = E::ONE;
    let boolean_tau: Vec<E> = (0..ROUNDS)
        .map(|i| if i % 2 == 0 { E::ZERO } else { E::ONE })
        .collect();
    let taus = [random_tau, tau_with_zero, tau_with_one, boolean_tau];

    let a = random_poly_in_ext::<F, E>(size);
    let b = random_poly_in_ext::<F, E>(size);
    let zero_poly = vec![E::ZERO; size];
    let challenges = random_poly_in_ext::<F, E>(ROUNDS);
    let offset = random_poly_in_ext::<F, E>(1)[0];

    for tau in &taus {
        // ---- a non-zero true claim
        let claim = product_claim(&a, &b, tau);
        assert_ne!(claim, E::ZERO);
        let run = run_minimal_product_sumcheck(&a, &b, tau, &challenges, claim, honest);
        assert!(run.accepted && !run.tampered);

        // claimed zero, shifted, scaled: rejected with honest messages and
        // with all-zero messages alike
        for false_claim in [E::ZERO, add(claim, offset), mul(claim, offset)] {
            assert_ne!(false_claim, claim);
            for all_zero in [false, true] {
                let tamper = |round: usize, message: [E; 2]| {
                    if all_zero {
                        zeros(round, message)
                    } else {
                        message
                    }
                };
                let run =
                    run_minimal_product_sumcheck(&a, &b, tau, &challenges, false_claim, tamper);
                assert!(!run.accepted, "false claim {false_claim:?}");
            }
        }

        // the true claim with one coefficient zeroed or shifted in one
        // round, or every coefficient zeroed
        let run = run_minimal_product_sumcheck(&a, &b, tau, &challenges, claim, zeros);
        assert!(run.tampered && !run.accepted);
        for round in 0..ROUNDS {
            for coefficient in 0..2 {
                for shift in [None, Some(offset)] {
                    let tamper = |r: usize, mut message: [E; 2]| {
                        if r == round {
                            message[coefficient] = match shift {
                                None => E::ZERO,
                                Some(delta) => add(message[coefficient], delta),
                            };
                        }
                        message
                    };
                    let run = run_minimal_product_sumcheck(&a, &b, tau, &challenges, claim, tamper);
                    assert_eq!(
                        run.accepted, !run.tampered,
                        "round {round} coefficient {coefficient}"
                    );
                }
            }
        }

        // ---- a ZERO true claim (the zero polynomial): every honest
        // coefficient is zero as well, so the all-zero message IS honest
        assert_eq!(product_claim(&zero_poly, &b, tau), E::ZERO);
        for tamper in [honest, zeros] {
            let run =
                run_minimal_product_sumcheck(&zero_poly, &b, tau, &challenges, E::ZERO, tamper);
            assert!(run.accepted && !run.tampered);
        }
        for false_claim in [E::ONE, offset] {
            let run =
                run_minimal_product_sumcheck(&zero_poly, &b, tau, &challenges, false_claim, zeros);
            assert!(!run.accepted);
        }
        // non-zero coefficients against the true zero claim
        let run =
            run_minimal_product_sumcheck(&zero_poly, &b, tau, &challenges, E::ZERO, |_, _| {
                [offset, offset]
            });
        assert!(run.tampered && !run.accepted);
    }
}
