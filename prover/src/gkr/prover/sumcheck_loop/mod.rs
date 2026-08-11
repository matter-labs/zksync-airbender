use crate::gkr::prover::SumcheckIntermediateProofValues;
use std::collections::BTreeMap;

use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::sumcheck::evaluation_kernels::*;
use crate::gkr::{
    prover::dimension_reduction::forward::DimensionReducingInputOutput,
    sumcheck::{
        access_and_fold::GKRStorage,
        eq_poly::{
            evaluate_constant_and_quadratic_coeffs_with_precomputed_eq,
            evaluate_with_precomputed_eq, evaluate_with_precomputed_eq_ext, make_eq_poly_in_full,
        },
        evaluate_eq_poly, evaluate_small_univariate_poly,
        output_univariate_monomial_form_max_quadratic,
    },
};
use crate::worker::Worker;
use field::{Field, FieldExtension, PrimeField};

use crate::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use cs::gkr_compiler::GKRLayerDescription;
use cs::{definitions::GKRAddress, gkr_compiler::OutputType};
use kernel_collector::KernelCollector;
use transcript::Transcript;

pub(crate) mod batch_evaluation;
mod distribution_analysis;
mod kernel_collector;
pub(crate) mod windowed_mode;

/// # Panics
/// Panics if claims or challenge points for the output layer are missing from storage.
pub fn evaluate_dimension_reducing_sumcheck_for_layer<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
>(
    layer_idx: usize,
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    claim_points: &mut BTreeMap<usize, Vec<E>>,
    claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    gkr_storage: &mut GKRStorage<F, E>,
    batching_challenge: &mut E,
    seed: &mut TR::Seed,
    trace_len_after_reduction: usize,
    worker: &Worker,
) -> SumcheckIntermediateProofValues<F, E>
where
    [(); E::DEGREE]: Sized,
{
    println!("Evaluating layer {layer_idx} (dimension reducing) in sumcheck direction");
    let layer_timer = std::time::Instant::now();
    println!("Trace length of reduced poly is {trace_len_after_reduction}");
    let output_layer_idx = layer_idx + 1;

    let output_claims = claims_storage
        .get(&output_layer_idx)
        .expect("claims for output layer must exist");
    let prev_challenges = claim_points
        .get(&output_layer_idx)
        .expect("claim points for output layer must exist");

    assert!(trace_len_after_reduction.is_power_of_two());
    let folding_steps = trace_len_after_reduction.trailing_zeros() as usize;
    assert!(folding_steps >= 2, "need at least 2 folding steps");

    // Precompute eq polynomial evaluations over the boolean hypercube
    let eq_polys = make_eq_poly_in_full::<E>(prev_challenges, &worker);

    let batch_challenge_base = *batching_challenge;

    let collector =
        KernelCollector::from_dimension_reducing_relations(layer, layer_idx, batch_challenge_base);
    debug_assert!(!collector.is_empty());

    let claim = collector.compute_combined_claim(output_claims);

    // Debug break-point path (GKR_LSB_DEBUG=1, gkr_self_checks builds): run
    // the LSB-binding dimension-reducing engine on the SAME layer data with
    // deterministic challenges and validate it end-to-end -- eq orientation
    // against the production claim, per-round chaining (internal asserts),
    // and the final claim against direct at-point multilinear evaluation of
    // every input poly. The naive path still runs afterwards so the layer
    // chain stays intact; `prover/mod.rs` panics after ALL dimension-reducing
    // layers under the same gate.
    #[cfg(feature = "gkr_self_checks")]
    if std::env::var("GKR_LSB_DEBUG").is_ok() {
        use crate::gkr::prover::dimension_reduction::lsb_backward::{
            lsb_dim_reducing_sumcheck_prove, LsbDimReducingRelation,
        };
        // mirror KernelCollector::from_dimension_reducing_relations exactly:
        // same relation order, same successive batch-challenge powers
        // (the collector starts at ONE, then multiplies by the base)
        let mut cbc = E::ONE;
        let mut poly_addrs: Vec<GKRAddress> = vec![];
        let mut relations: Vec<LsbDimReducingRelation<E>> = vec![];
        fn idx_of(addrs: &mut Vec<GKRAddress>, a: GKRAddress) -> usize {
            if let Some(i) = addrs.iter().position(|x| *x == a) {
                i
            } else {
                addrs.push(a);
                addrs.len() - 1
            }
        }
        for (k, v) in layer {
            match *k {
                OutputType::PermutationProduct | OutputType::InitsAndTeardownsProduct => {
                    for inp in v.inputs.iter() {
                        let alpha = cbc;
                        cbc.mul_assign(&batch_challenge_base);
                        let input = idx_of(&mut poly_addrs, *inp);
                        relations.push(LsbDimReducingRelation::PairwiseProduct { input, alpha });
                    }
                }
                OutputType::Lookup16Bits
                | OutputType::LookupTimestamps
                | OutputType::GenericLookup => {
                    let alpha_num = cbc;
                    cbc.mul_assign(&batch_challenge_base);
                    let alpha_den = cbc;
                    cbc.mul_assign(&batch_challenge_base);
                    let num = idx_of(&mut poly_addrs, v.inputs[0]);
                    let den = idx_of(&mut poly_addrs, v.inputs[1]);
                    relations.push(LsbDimReducingRelation::LogupPair {
                        num,
                        den,
                        alpha_num,
                        alpha_den,
                    });
                }
                _ => panic!("unexpected output type in dimension-reducing layer"),
            }
        }
        let dbg_inputs = GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: poly_addrs.clone(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        };
        let sources = unsafe { gkr_storage.get_for_sumcheck_round_0(&dbg_inputs) };
        let polys: Vec<&[E]> = sources
            .extension_field_inputs
            .iter()
            .map(|src| src.current_values())
            .collect();
        let rounds = folding_steps;
        let m = 1usize << rounds;
        let gate = |at: &dyn Fn(usize, usize) -> E| -> E {
            let mut acc = E::ZERO;
            for rel in relations.iter() {
                match rel {
                    LsbDimReducingRelation::PairwiseProduct { input, alpha } => {
                        let mut t = at(*input, 0);
                        t.mul_assign(&at(*input, 1));
                        t.mul_assign(alpha);
                        acc.add_assign(&t);
                    }
                    LsbDimReducingRelation::LogupPair {
                        num,
                        den,
                        alpha_num,
                        alpha_den,
                    } => {
                        let (n0, n1) = (at(*num, 0), at(*num, 1));
                        let (d0, d1) = (at(*den, 0), at(*den, 1));
                        let mut nn = n0;
                        nn.mul_assign(&d1);
                        let mut t = n1;
                        t.mul_assign(&d0);
                        nn.add_assign(&t);
                        nn.mul_assign(alpha_num);
                        acc.add_assign(&nn);
                        let mut dd = d0;
                        dd.mul_assign(&d1);
                        dd.mul_assign(alpha_den);
                        acc.add_assign(&dd);
                    }
                }
            }
            acc
        };
        let eq_table_for = |chals: &[E]| -> Vec<E> {
            let mut eq = vec![E::ONE; 1 << chals.len()];
            for (b, c) in chals.iter().enumerate() {
                let half = 1usize << b;
                let mut om = E::ONE;
                om.sub_assign(c);
                for i in 0..half {
                    let mut hi = eq[i];
                    hi.mul_assign(c);
                    eq[i + half] = hi;
                    eq[i].mul_assign(&om);
                }
            }
            eq
        };
        // resolve the eq orientation of `prev_challenges` against the
        // production claim: LSB engine wants tau[s] = coordinate of the
        // variable bound at round s (low first)
        let direct_sum = |tau: &[E]| -> E {
            let eq = eq_table_for(tau);
            let mut acc = E::ZERO;
            for y in 0..m {
                let v = gate(&|p, b| polys[p][2 * y + b]);
                let mut t = v;
                t.mul_assign(&eq[y]);
                acc.add_assign(&t);
            }
            acc
        };
        let tau_fwd: Vec<E> = prev_challenges.to_vec();
        let tau_rev: Vec<E> = prev_challenges.iter().rev().copied().collect();
        let tau = if direct_sum(&tau_fwd) == claim {
            println!("[LSB-DEBUG] layer {layer_idx}: eq orientation = forward (low-var-first)");
            tau_fwd
        } else {
            let s_rev = direct_sum(&tau_rev);
            assert_eq!(
                s_rev, claim,
                "layer {layer_idx}: neither eq orientation reproduces the claim"
            );
            println!("[LSB-DEBUG] layer {layer_idx}: eq orientation = reversed (high-var-first storage)");
            tau_rev
        };
        // deterministic debug challenges
        let mut ch_seed = claim;
        let challenges: Vec<E> = (0..rounds)
            .map(|_| {
                ch_seed.square();
                let mut t = ch_seed;
                t.add_assign(&batch_challenge_base);
                ch_seed = t;
                t
            })
            .collect();
        let out = lsb_dim_reducing_sumcheck_prove::<F, E>(&polys, &relations, &tau, claim, &challenges);
        // final claim validated by direct at-point multilinear evaluation
        let eq_r = eq_table_for(&challenges);
        for (p, poly) in polys.iter().enumerate() {
            for b in 0..2 {
                let mut ev = E::ZERO;
                for y in 0..m {
                    let mut t = eq_r[y];
                    t.mul_assign(&poly[2 * y + b]);
                    ev.add_assign(&t);
                }
                assert_eq!(
                    ev, out.final_values[p][b],
                    "layer {layer_idx}: at-point evaluation mismatch, poly {p} b {b}"
                );
            }
        }
        let mut g = gate(&|p, b| out.final_values[p][b]);
        g.mul_assign(&out.eq_factor);
        assert_eq!(g, out.final_claim, "layer {layer_idx}: final claim identity");
        println!(
            "[LSB-DEBUG] layer {layer_idx}: LSB sumcheck validated ({} rounds, {} polys, {} relations)",
            rounds,
            polys.len(),
            relations.len()
        );
    }

    let (mut folding_challenges, internal_round_coefficients, last_evaluations, final_claim) =
        run_sumcheck_loop::<F, E, TR, 4, false>(
            &collector,
            claim,
            prev_challenges,
            &eq_polys,
            gkr_storage,
            &BatchedGKRTermDescriptionConstants::<F, E>::default(),
            folding_steps,
            worker,
            seed,
        );

    assert_eq!(folding_challenges.len(), folding_steps);
    assert_eq!(internal_round_coefficients.len(), folding_steps);

    // The last folding challenge drawn inside the loop is the challenge for the last *output*
    // coordinate (`r_before_last`). It fixes that coordinate of the `[E;4]` bilinear
    // `last_evaluations` (over (last output coord) x (pairwise/LSB coord)), reducing it to a
    // `[E;2]` line in the remaining LSB coordinate. That line is what we send in the proof and
    // commit to the transcript; we then draw the LSB challenge `r_last` to fix it and obtain
    // the next-layer at-point claims.
    assert_eq!(
        trace_len_after_reduction.trailing_zeros() as usize,
        folding_challenges.len()
    );
    let r_before_last = *folding_challenges
        .last()
        .expect("at least one folding round");

    // `[E;4]` layout: [v0, v1, v2, v3] split as (x_last=0: v0,v1 | x_last=1: v2,v3), so the
    // LSB=0 component is (v0 @ x_last=0, v2 @ x_last=1) and LSB=1 is (v1, v3). Interpolating
    // over x_last at `r_before_last` yields the `[E;2]` LSB line [lsb0, lsb1].
    let lsb_lines: BTreeMap<GKRAddress, [E; 2]> = last_evaluations
        .iter()
        .map(|(addr, evals)| {
            let lsb0 = interpolate_linear::<E>(evals[0], evals[2], &r_before_last);
            let lsb1 = interpolate_linear::<E>(evals[1], evals[3], &r_before_last);
            (*addr, [lsb0, lsb1])
        })
        .collect();

    #[cfg(feature = "gkr_self_checks")]
    {
        // We use old evaluation function, but format the data to match the expectations
        let augmented_claims: BTreeMap<_, [E; 4]> = lsb_lines
            .iter()
            .map(|(addr, v)| (*addr, [v[0], v[1], E::ZERO, E::ZERO]))
            .collect();
        let recomputed = collector.compute_last_step_accumulator_from_evals(
            &BatchedGKRTermDescriptionConstants::<F, E>::default(),
            &augmented_claims,
        );
        assert_eq!(
            recomputed[0], final_claim,
            "final_claim inconsistent with recomputed gate kernels"
        );
    }

    // Send the LSB lines in the proof and commit them before drawing the LSB challenge.
    let final_step_evaluations: BTreeMap<GKRAddress, Vec<E>> =
        lsb_lines.iter().map(|(k, v)| (*k, v.to_vec())).collect();

    let transcript_inputs: Vec<E> = lsb_lines.values().flatten().copied().collect();
    commit_field_els::<F, E, TR>(seed, &transcript_inputs);

    let challenges = draw_random_field_els::<F, E, TR>(seed, 2);
    let [r_last, next_batching_challenge] = challenges.try_into().unwrap();
    folding_challenges.push(r_last);

    assert_eq!(
        trace_len_after_reduction.trailing_zeros() as usize,
        folding_challenges.len() - 1
    );

    // After sumcheck completes, extract claims for the input layer by fixing the LSB
    // coordinate at `r_last`.
    let new_claims: BTreeMap<_, _> = lsb_lines
        .iter()
        .map(|(addr, [lsb0, lsb1])| (*addr, interpolate_linear::<E>(*lsb0, *lsb1, &r_last)))
        .collect();

    #[cfg(feature = "gkr_self_checks")]
    {
        println!("Self-checking explicit at-point evaluations");
        let eq_polys = make_eq_poly_in_full::<E>(&folding_challenges, worker);
        for (k, v) in new_claims.iter() {
            if let Some(poly) = gkr_storage.try_get_base_poly(*k) {
                let eval = evaluate_with_precomputed_eq(poly, &eq_polys.last().unwrap()[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else if let Some(poly) = gkr_storage.try_get_ext_poly(*k) {
                let eval = evaluate_with_precomputed_eq_ext(poly, &eq_polys.last().unwrap()[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else {
                unreachable!()
            }
        }
    }

    claims_storage.insert(layer_idx, new_claims);
    claim_points.insert(layer_idx, folding_challenges);

    // and we can purge the storage
    gkr_storage.purge_up_to_layer(layer_idx);

    *batching_challenge = next_batching_challenge;

    println!(
        "Dimension-reducing layer {layer_idx} sumcheck took {:?}",
        layer_timer.elapsed()
    );

    SumcheckIntermediateProofValues {
        sumcheck_num_rounds: folding_steps,
        internal_round_coefficients: internal_round_coefficients
            .into_iter()
            .map(crate::gkr::prover::SumcheckRoundCoefficients::Multilinear)
            .collect(),
        final_step_evaluations,
        extra_evaluations_from_caching_relations: BTreeMap::new(), // none are possible here
        _marker: core::marker::PhantomData,
    }
}

/// LSB-binding variant of [`evaluate_dimension_reducing_sumcheck_for_layer`]:
/// the sumcheck binds the OUTPUT space's variables LSB-first through the raw
/// slice engine (`dimension_reduction::lsb_backward`), reading contiguous
/// 4-blocks per round and folding with dense ping-pong writes. The stored
/// claim point is emitted in the legacy (high-variable-first) order --
/// `reverse(lsb challenges) + [r_last]` -- so downstream layers, claims and
/// verifiers keep their existing conventions.
pub fn evaluate_dimension_reducing_sumcheck_for_layer_lsb<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
    CK: Fn(
            &[usize],
            &[usize],
            &[[usize; 2]],
            &[crate::gkr::prover::dimension_reduction::lsb_backward::LsbDimReducingRelation<E>],
            Option<E>,
            usize,
            usize,
            usize,
        ) -> [E; 2]
        + Send
        + Sync
        + Copy,
>(
    chunk_kernel: CK,
    layer_idx: usize,
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    claim_points: &mut BTreeMap<usize, Vec<E>>,
    claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    gkr_storage: &mut GKRStorage<F, E>,
    batching_challenge: &mut E,
    seed: &mut TR::Seed,
    trace_len_after_reduction: usize,
    worker: &Worker,
) -> SumcheckIntermediateProofValues<F, E>
where
    [(); E::DEGREE]: Sized,
{
    use crate::gkr::prover::dimension_reduction::lsb_backward::{
        lsb_dim_reducing_sumcheck_prove_fused, LsbDimReducingRelation,
    };

    println!("Evaluating layer {layer_idx} (dimension reducing, LSB) in sumcheck direction");
    let layer_timer = std::time::Instant::now();
    let output_layer_idx = layer_idx + 1;

    let output_claims = claims_storage
        .get(&output_layer_idx)
        .expect("claims for output layer must exist");
    let prev_challenges = claim_points
        .get(&output_layer_idx)
        .expect("claim points for output layer must exist");

    assert!(trace_len_after_reduction.is_power_of_two());
    let folding_steps = trace_len_after_reduction.trailing_zeros() as usize;
    assert!(folding_steps >= 2, "need at least 2 folding steps");

    let batch_challenge_base = *batching_challenge;

    // relation list + combined claim, mirroring
    // KernelCollector::from_dimension_reducing_relations (challenge powers
    // start at ONE and multiply by the base per challenge)
    let mut cbc = E::ONE;
    let mut poly_addrs: Vec<GKRAddress> = vec![];
    let mut relations: Vec<LsbDimReducingRelation<E>> = vec![];
    let mut relation_outputs: Vec<[GKRAddress; 2]> = vec![];
    let mut claim = E::ZERO;
    fn addr_idx(addrs: &mut Vec<GKRAddress>, a: GKRAddress) -> usize {
        if let Some(i) = addrs.iter().position(|x| *x == a) {
            i
        } else {
            addrs.push(a);
            addrs.len() - 1
        }
    }
    for (k, v) in layer {
        match *k {
            OutputType::PermutationProduct | OutputType::InitsAndTeardownsProduct => {
                for (inp, out) in v.inputs.iter().zip(v.output.iter()) {
                    let alpha = cbc;
                    cbc.mul_assign(&batch_challenge_base);
                    let input = addr_idx(&mut poly_addrs, *inp);
                    relations.push(LsbDimReducingRelation::PairwiseProduct { input, alpha });
                    relation_outputs.push([*out, *out]);
                    let mut t = alpha;
                    t.mul_assign(&output_claims[out]);
                    claim.add_assign(&t);
                }
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let alpha_num = cbc;
                cbc.mul_assign(&batch_challenge_base);
                let alpha_den = cbc;
                cbc.mul_assign(&batch_challenge_base);
                let num = addr_idx(&mut poly_addrs, v.inputs[0]);
                let den = addr_idx(&mut poly_addrs, v.inputs[1]);
                relations.push(LsbDimReducingRelation::LogupPair {
                    num,
                    den,
                    alpha_num,
                    alpha_den,
                });
                relation_outputs.push([v.output[0], v.output[1]]);
                let mut t = alpha_num;
                t.mul_assign(&output_claims[&v.output[0]]);
                claim.add_assign(&t);
                let mut t = alpha_den;
                t.mul_assign(&output_claims[&v.output[1]]);
                claim.add_assign(&t);
            }
            _ => panic!("unexpected output type in dimension-reducing layer"),
        }
    }

    // materialize raw pointers up front (no storage borrows held during the
    // sumcheck -- the round-0 purge callback needs `&mut gkr_storage`)
    let (poly_raw, output_ptr_table): (Vec<(usize, usize)>, Vec<[usize; 2]>) = {
        let out_addrs: Vec<GKRAddress> = relation_outputs
            .iter()
            .flat_map(|p| p.iter().copied())
            .collect();
        let lsb_inputs = GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: poly_addrs.clone(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        };
        let sources = unsafe { gkr_storage.get_for_sumcheck_round_0(&lsb_inputs) };
        let poly_raw: Vec<(usize, usize)> = sources
            .extension_field_inputs
            .iter()
            .map(|src| {
                let v = src.current_values();
                (v.as_ptr() as usize, v.len())
            })
            .collect();
        drop(sources);
        let out_inputs = GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: out_addrs.clone(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        };
        let out_sources = unsafe { gkr_storage.get_for_sumcheck_round_0(&out_inputs) };
        let flat: Vec<usize> = out_sources
            .extension_field_inputs
            .iter()
            .map(|src| src.current_values().as_ptr() as usize)
            .collect();
        let table: Vec<[usize; 2]> = flat.chunks(2).map(|c| [c[0], c[1]]).collect();
        (poly_raw, table)
    };
    let polys: Vec<&[E]> = poly_raw
        .iter()
        .map(|&(p, l)| unsafe { core::slice::from_raw_parts(p as *const E, l) })
        .collect();

    // incoming claim points are stored high-variable-first; the LSB rounds
    // consume them low-variable-first
    let tau: Vec<E> = prev_challenges.iter().rev().copied().collect();

    let gkr_storage_cell = core::cell::RefCell::new(&mut *gkr_storage);
    let (out, lsb_challenges) = lsb_dim_reducing_sumcheck_prove_fused::<F, E, CK>(
        &polys,
        &relations,
        &output_ptr_table,
        &tau,
        claim,
        worker,
        chunk_kernel,
        |coeffs| {
            commit_field_els::<F, E, TR>(seed, coeffs);
            draw_random_field_els::<F, E, TR>(seed, 1)[0]
        },
        || {
            // output layer fully consumed by round 0; free it now so the
            // fold scratch reuses the pages fault-free
            gkr_storage_cell.borrow_mut().purge_up_to_layer(layer_idx);
        },
    );
    drop(polys);
    let gkr_storage: &mut GKRStorage<F, E> = gkr_storage_cell.into_inner();

    // the engine's final values ARE the [E;2] LSB lines per input address
    let lsb_lines: BTreeMap<GKRAddress, [E; 2]> = poly_addrs
        .iter()
        .zip(out.final_values.iter())
        .map(|(addr, v)| (*addr, *v))
        .collect();

    let final_step_evaluations: BTreeMap<GKRAddress, Vec<E>> =
        lsb_lines.iter().map(|(k, v)| (*k, v.to_vec())).collect();

    let transcript_inputs: Vec<E> = lsb_lines.values().flatten().copied().collect();
    commit_field_els::<F, E, TR>(seed, &transcript_inputs);

    let challenges = draw_random_field_els::<F, E, TR>(seed, 2);
    let [r_last, next_batching_challenge] = challenges.try_into().unwrap();

    // legacy point order: high-variable-first for the output rounds, gate
    // (lowest input) coordinate appended last
    let mut folding_challenges: Vec<E> = lsb_challenges.iter().rev().copied().collect();
    folding_challenges.push(r_last);

    let new_claims: BTreeMap<_, _> = lsb_lines
        .iter()
        .map(|(addr, [lsb0, lsb1])| (*addr, interpolate_linear::<E>(*lsb0, *lsb1, &r_last)))
        .collect();

    #[cfg(feature = "gkr_self_checks")]
    {
        println!("Self-checking explicit at-point evaluations (LSB path)");
        let eq_polys = make_eq_poly_in_full::<E>(&folding_challenges, worker);
        for (k, v) in new_claims.iter() {
            if let Some(poly) = gkr_storage.try_get_base_poly(*k) {
                let eval = evaluate_with_precomputed_eq(poly, &eq_polys.last().unwrap()[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else if let Some(poly) = gkr_storage.try_get_ext_poly(*k) {
                let eval = evaluate_with_precomputed_eq_ext(poly, &eq_polys.last().unwrap()[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else {
                unreachable!()
            }
        }
    }

    claims_storage.insert(layer_idx, new_claims);
    claim_points.insert(layer_idx, folding_challenges);

    gkr_storage.purge_up_to_layer(layer_idx);

    *batching_challenge = next_batching_challenge;

    println!(
        "Dimension-reducing layer {layer_idx} sumcheck took {:?}",
        layer_timer.elapsed()
    );

    SumcheckIntermediateProofValues {
        sumcheck_num_rounds: folding_steps,
        internal_round_coefficients: out
            .round_coefficients
            .into_iter()
            .map(crate::gkr::prover::SumcheckRoundCoefficients::Multilinear)
            .collect(),
        final_step_evaluations,
        extra_evaluations_from_caching_relations: BTreeMap::new(), // none are possible here
        _marker: core::marker::PhantomData,
    }
}

/// # Panics
/// Panics if claims or challenge points for the output layer are missing from storage.
pub fn evaluate_sumcheck_for_layer<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
>(
    layer_idx: usize,
    layer: &GKRLayerDescription<F>,
    claim_points: &mut BTreeMap<usize, Vec<E>>,
    claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    gkr_storage: &mut GKRStorage<F, E>,
    batching_challenge: &mut E,
    _compiled_circuit: &cs::gkr_compiler::GKRCircuitArtifact<F>,
    trace_len: usize,
    lookup_challenges_multiplicative_part: E,
    lookup_challenges_additive_part: E,
    inits_and_teardowns_top_bits: &[u32],
    address_high_bits_shift: u32,
    external_challenges: &GKRExternalChallenges<F, E>,
    seed: &mut TR::Seed,
    worker: &Worker,
) -> SumcheckIntermediateProofValues<F, E>
where
    [(); E::DEGREE]: Sized,
{
    println!("Evaluating layer {layer_idx} in sumcheck direction");

    let output_layer_idx = layer_idx + 1;

    let output_claims = claims_storage
        .get(&output_layer_idx)
        .expect("claims for output layer must exist");
    let prev_challenges = claim_points
        .get(&output_layer_idx)
        .expect("claim points for output layer must exist");

    assert!(trace_len.is_power_of_two());
    let folding_steps = trace_len.trailing_zeros() as usize;
    assert!(folding_steps >= 4, "need at least 4 folding steps");

    let eq_polys = make_eq_poly_in_full::<E>(prev_challenges, worker);

    let batch_challenge_base = *batching_challenge;

    let collector = KernelCollector::from_layer(
        layer,
        layer_idx,
        batch_challenge_base,
        lookup_challenges_multiplicative_part,
        lookup_challenges_additive_part,
        inits_and_teardowns_top_bits,
        address_high_bits_shift,
    );

    debug_assert!(!collector.is_empty());

    let claim = collector.compute_combined_claim(output_claims);

    let challenge_constants = BatchedGKRTermDescriptionConstants::<F, E> {
        external_challenges: *external_challenges,
        lookup_challenges_multiplicative_part: lookup_challenges_multiplicative_part,
        lookup_challenges_additive_part: lookup_challenges_additive_part,
        _marker: core::marker::PhantomData,
    };

    let (folding_challenges, internal_round_coefficients, last_evaluations, final_claim) =
        run_sumcheck_loop::<F, E, TR, 2, true>(
            &collector,
            claim,
            prev_challenges,
            &eq_polys,
            gkr_storage,
            &challenge_constants,
            folding_steps,
            worker,
            seed,
        );

    assert_eq!(folding_challenges.len(), folding_steps);
    assert_eq!(internal_round_coefficients.len(), folding_steps);

    // After sumcheck completes, the last folding challenge (drawn inside the loop together
    // with the final univariate monomial) fixes the final coordinate. We reduce each input
    // poly's line `[f0, f1]` to a single at-point evaluation, which is both the next-layer
    // claim and the value sent in the proof. These at-point evaluations are committed to the
    // transcript before the next batching challenge is drawn.
    assert_eq!(
        folding_challenges.len(),
        trace_len.trailing_zeros() as usize
    );
    let last_r = *folding_challenges
        .last()
        .expect("at least one folding round");

    let mut new_claims: BTreeMap<_, _> = last_evaluations
        .iter()
        .map(|(addr, &[f0, f1])| (*addr, interpolate_linear::<E>(f0, f1, &last_r)))
        .collect();

    #[cfg(feature = "gkr_self_checks")]
    {
        // We use old function to perform evaluate of gates at-point, but we will just ignore the second evaluation point.
        // Final claim represents something like eq(prev_round_challenges, folding_challenges) * a(folding_challenges) * b(folding_challenges)
        // for same sized kernels, and eq(prev_round_challenges, folding_challenges, 0) * a(folding_challenges, 1) for dimension reducing kernels
        let augmented_claims: BTreeMap<_, [E; 2]> = new_claims
            .iter()
            .map(|(addr, v)| (*addr, [*v, E::ZERO]))
            .collect();
        let recomputed = collector
            .compute_last_step_accumulator_from_evals(&challenge_constants, &augmented_claims);
        assert_eq!(
            recomputed[0], final_claim,
            "last_evaluations inconsistent with final accumulator constant term G(0)"
        );
    }

    // Snapshot the at-point evaluations to send in the proof before the cached-relation
    // handling extends `new_claims` with extra explicitly-computed dependencies.
    let final_step_evaluations: BTreeMap<GKRAddress, Vec<E>> =
        new_claims.iter().map(|(k, v)| (*k, vec![*v])).collect();

    let mut transcript_inputs: Vec<E> = new_claims.values().copied().collect();

    // self-check
    #[cfg(feature = "gkr_self_checks")]
    {
        println!("Self-checking explicit at-point evaluations");
        let eq_polys = make_eq_poly_in_full::<E>(&folding_challenges, worker);
        for (k, v) in new_claims.iter() {
            if let Some(poly) = gkr_storage.try_get_base_poly(*k) {
                let eval = evaluate_with_precomputed_eq(poly, &eq_polys.last().unwrap()[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else if let Some(poly) = gkr_storage.try_get_ext_poly(*k) {
                let eval = evaluate_with_precomputed_eq_ext(poly, &eq_polys.last().unwrap()[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else {
                unreachable!()
            }
        }
    }

    let mut extra_evaluations_from_caching_relations = BTreeMap::new();
    if layer.cached_relations.is_empty() == false {
        use crate::gkr::sumcheck::eq_poly::*;
        let mut eq_poly = None;

        for (cached_addr, relation) in layer.cached_relations.iter() {
            assert!(
                new_claims.contains_key(cached_addr),
                "Missing claim for cached address {:?}",
                cached_addr
            );

            #[cfg(feature = "gkr_self_checks")]
            {
                println!("Self-checking explicit at-point evaluations for cache relations");
                let claim = new_claims[cached_addr];
                if eq_poly.is_none() {
                    let mut eq_precomputed = make_eq_poly_in_full(&folding_challenges, worker);
                    let eq_at_z = eq_precomputed.pop().unwrap();
                    eq_poly = Some(eq_at_z);
                }
                if let Some(poly) = gkr_storage.try_get_base_poly(*cached_addr) {
                    let eval = evaluate_with_precomputed_eq(poly, &eq_poly.as_ref().unwrap()[..]);
                    // if claim != eval {
                    //     println!(
                    //         "claim diverged for poly {cached_addr:?} from relation {:?}",
                    //         relation
                    //     );
                    // }
                    assert_eq!(
                        eval, claim,
                        "claim diverged for poly {cached_addr:?} from relation {:?}",
                        relation
                    );
                } else if let Some(poly) = gkr_storage.try_get_ext_poly(*cached_addr) {
                    let eval =
                        evaluate_with_precomputed_eq_ext(poly, &eq_poly.as_ref().unwrap()[..]);
                    // if claim != eval {
                    //     println!(
                    //         "claim diverged for poly {cached_addr:?} from relation {:?}",
                    //         relation
                    //     );
                    // }
                    assert_eq!(
                        eval, claim,
                        "claim diverged for poly {cached_addr:?} from relation {:?}",
                        relation
                    );
                } else {
                    unreachable!()
                }
            }

            for dep in relation.dependencies() {
                if new_claims.contains_key(&dep) {
                    continue;
                }
                match dep {
                    GKRAddress::BaseLayerWitness(_)
                    | GKRAddress::BaseLayerMemory(_)
                    | GKRAddress::Setup(_)
                    | GKRAddress::InnerLayer { .. } => {
                        println!("Explicitly computing value for {:?}", dep);
                        if eq_poly.is_none() {
                            let mut eq_precomputed =
                                make_eq_poly_in_full(&folding_challenges, worker);
                            let eq_at_z = eq_precomputed.pop().unwrap();
                            eq_poly = Some(eq_at_z);
                        }
                        let evaluation = if let Some(values) = gkr_storage.try_get_base_poly(dep) {
                            evaluate_with_precomputed_eq::<F, E>(
                                values,
                                &eq_poly.as_ref().unwrap()[..],
                            )
                        } else if let Some(values) = gkr_storage.try_get_ext_poly(dep) {
                            evaluate_with_precomputed_eq_ext::<E>(
                                values,
                                &eq_poly.as_ref().unwrap()[..],
                            )
                        } else {
                            panic!("Unknown poly at address {:?}", dep);
                        };

                        new_claims.insert(dep, evaluation);
                        extra_evaluations_from_caching_relations.insert(dep, evaluation);
                    }
                    _ => {
                        panic!(
                            "Unexpected dependency address {:?} for cached relation {:?}",
                            dep, cached_addr
                        );
                    }
                }
            }
        }

        if !extra_evaluations_from_caching_relations.is_empty() {
            // extend them to transcript seed
            transcript_inputs.extend(extra_evaluations_from_caching_relations.values().copied());
        }

        #[cfg(feature = "gkr_self_checks")]
        assert!(crate::gkr::prover::debug_utils::verify_cache_relations(
            layer,
            &new_claims,
            external_challenges,
            lookup_challenges_multiplicative_part,
        ));
    }

    // after all claims for the next layer are ready - draw the next batching challenge
    commit_field_els::<F, E, TR>(seed, &transcript_inputs);
    let next_batching_challenge = draw_random_field_els::<F, E, TR>(seed, 1)[0];

    claims_storage.insert(layer_idx, new_claims);
    claim_points.insert(layer_idx, folding_challenges);

    // and we can purge the storage
    gkr_storage.purge_up_to_layer(layer_idx);

    *batching_challenge = next_batching_challenge;

    SumcheckIntermediateProofValues {
        sumcheck_num_rounds: folding_steps,
        internal_round_coefficients: internal_round_coefficients
            .into_iter()
            .map(crate::gkr::prover::SumcheckRoundCoefficients::Multilinear)
            .collect(),
        final_step_evaluations,
        extra_evaluations_from_caching_relations,
        _marker: core::marker::PhantomData,
    }
}

fn run_sumcheck_loop<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
    const N: usize,
    const USE_BATCHING: bool,
>(
    collector: &KernelCollector<F, E>,
    initial_claim: E,
    prev_challenges: &[E],
    eq_poly: &[Box<[E]>],
    gkr_storage: &mut GKRStorage<F, E>,
    challenge_constants: &BatchedGKRTermDescriptionConstants<F, E>,
    folding_steps: usize,
    worker: &Worker,
    seed: &mut TR::Seed,
) -> (Vec<E>, Vec<[E; 4]>, BTreeMap<GKRAddress, [E; N]>, E)
where
    [(); E::DEGREE]: Sized,
{
    if USE_BATCHING {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::sumcheck_loop::windowed_sumcheck_loop;
        if let Some(result) = windowed_sumcheck_loop::<F, E, TR, N>(
            collector,
            initial_claim,
            prev_challenges,
            eq_poly,
            gkr_storage,
            challenge_constants,
            folding_steps,
            worker,
            seed,
        ) {
            return result;
        }
        println!("Running sumcheck loop in per-round batched mode");
    } else {
        println!("Running sumcheck loop in individual kernel mode");
    };

    let mut claim = initial_claim;
    let mut folding_challenges = Vec::with_capacity(folding_steps);
    let mut last_evaluations: BTreeMap<GKRAddress, [E; N]> = BTreeMap::new();

    let mut eq_prefactor = E::ONE;

    let max_acc_size = 1 << (folding_steps - 1);
    let mut accumulator_buffer = vec![[E::ZERO; 2]; max_acc_size];
    let mut intermediate_coeffs = Vec::with_capacity(folding_steps);

    let batched_description = if USE_BATCHING {
        collector.make_batched_description(challenge_constants, collector.layer)
    } else {
        Default::default()
    };

    // Every round - including the last one - now emits a univariate monomial and draws a
    // folding challenge. The last round's kernel evaluation produces the monomial form
    // `[G(0), G2]` (see `EXPLICIT_FORM == false` handling in the evaluators) while still
    // folding all input polys down to their line and recording `last_evaluations`, which the
    // callers use to fix the last coordinate at the freshly drawn challenge.
    for step in 0..folding_steps {
        let acc_size = 1 << (folding_steps - step - 1);
        let accumulator = &mut accumulator_buffer[..acc_size];
        if step > 0 {
            accumulator.fill([E::ZERO; 2]);
        }

        if USE_BATCHING {
            use crate::gkr::prover::sumcheck_loop::batch_evaluation::evaluate_batched_gkr_description;
            evaluate_batched_gkr_description(
                &batched_description,
                gkr_storage,
                step,
                &folding_challenges,
                accumulator,
                folding_steps,
                &mut last_evaluations,
                worker,
            );
        } else {
            collector.evaluate_kernels_over_storage(
                gkr_storage,
                step,
                &folding_challenges,
                accumulator,
                folding_steps,
                &mut last_evaluations,
                worker,
            );
        }

        let eq = &eq_poly[folding_steps - step - 1];

        assert_eq!(eq.len(), acc_size);

        let [c0, c2] = evaluate_constant_and_quadratic_coeffs_with_precomputed_eq::<F, E>(
            &accumulator,
            eq,
            worker,
        );

        let mut normalized_claim = claim;
        normalized_claim.mul_assign(&eq_prefactor.inverse().expect("eq prefactor non-zero"));

        let coeffs = output_univariate_monomial_form_max_quadratic::<F, E>(
            prev_challenges[step],
            normalized_claim,
            c0,
            c2,
        );

        #[cfg(feature = "gkr_self_checks")]
        {
            let s0 = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &E::ZERO);
            let s1 = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &E::ONE);
            let mut sum = s0;
            sum.add_assign(&s1);
            sum.mul_assign(&eq_prefactor);
            assert_eq!(
                sum, claim,
                "s(0) + s(1) != claim / eq_prefactor at folding step {}",
                step
            );
        }

        commit_field_els::<F, E, TR>(seed, &coeffs);
        intermediate_coeffs.push(coeffs);
        let folding_challenge = draw_random_field_els::<F, E, TR>(seed, 1)[0];

        let new_claim = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &folding_challenge);

        claim = new_claim;
        eq_prefactor = evaluate_eq_poly::<F, E>(&folding_challenge, &prev_challenges[step]);

        folding_challenges.push(folding_challenge);
    }

    // normalize the claim to avoid prefactors sneaking in for our self-check outside
    let mut normalized_claim = claim;
    normalized_claim.mul_assign(&eq_prefactor.inverse().expect("eq prefactor non-zero"));

    (
        folding_challenges,
        intermediate_coeffs,
        last_evaluations,
        normalized_claim,
    )
}

#[inline(always)]
pub(crate) fn interpolate_linear<E: Field>(f0: E, f1: E, r: &E) -> E {
    let mut result = f1;
    result.sub_assign(&f0);
    result.mul_assign(r);
    result.add_assign(&f0);
    result
}
