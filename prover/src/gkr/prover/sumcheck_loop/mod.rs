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
            evaluate_with_precomputed_eq, evaluate_with_precomputed_eq_ext,
            make_eq_poly_in_full_lsb,
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

/// LSB-binding dimension-reducing backward pass for one layer:
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
        &[crate::gkr::prover::SendConstPtr<E>],
        &[crate::gkr::prover::SendPtr<E>],
        &[[crate::gkr::prover::SendConstPtr<E>; 2]],
        &[crate::gkr::prover::dimension_reduction::lsb_backward::LsbDimReducingRelation<E>],
        Option<E>,
        crate::gkr::prover::SendConstPtr<E>,
        usize,
        usize,
        crate::gkr::prover::SendPtr<[u128; 2]>,
    ) -> [E; 2]
        + Send
        + Sync
        + Copy,
>(
    chunk_kernel: CK,
    schedule: &[crate::gkr::prover_config::SumcheckStep],
    layer_idx: usize,
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    claim_points: &mut BTreeMap<usize, Vec<E>>,
    claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, E>>,
    gkr_storage: &mut GKRStorage<F, E>,
    batching_challenge: &mut E,
    seed: &mut TR::Seed,
    trace_len_after_reduction: usize,
    worker: &Worker,
    scratch: &mut crate::gkr::prover::gkr_backend::DimReducingSumcheckScratch<E>,
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
    let (poly_raw, output_ptr_table): (
        Vec<(*const E, usize)>,
        Vec<[crate::gkr::prover::SendConstPtr<E>; 2]>,
    ) = {
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
        let poly_raw: Vec<(*const E, usize)> = sources
            .extension_field_inputs
            .iter()
            .map(|src| {
                let v = src.current_values();
                (v.as_ptr(), v.len())
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
        let flat: Vec<crate::gkr::prover::SendConstPtr<E>> =
            out_sources
                .extension_field_inputs
                .iter()
                .map(|src| {
                    crate::gkr::prover::SendConstPtr(
                        src.current_values().as_ptr(),
                    )
                })
                .collect();
        let table: Vec<[crate::gkr::prover::SendConstPtr<E>; 2]> =
            flat.chunks(2).map(|c| [c[0], c[1]]).collect();
        (poly_raw, table)
    };
    let polys: Vec<&[E]> = poly_raw
        .iter()
        .map(|&(p, l)| unsafe { core::slice::from_raw_parts(p, l) })
        .collect();

    // incoming claim points are stored in the dimension-reducing emission
    // layout [bits 1.., bit 0]; the engine consumes that layout NATIVELY
    // (per-round accessor + contiguous suffix slice), so the point passes
    // through untouched
    let tau: &[E] = &prev_challenges[..];

    // fold + tri scratch shared across ALL dimension-reducing layers,
    // max-sized and owned by the backward-pass driver loop
    assert!(scratch.fold.len() >= polys.len());
    let num_polys = polys.len();
    let (fold_scratch, tri_scratch) =
        (&mut scratch.fold[..num_polys], &mut scratch.tri[..]);
    let gkr_storage_cell = core::cell::RefCell::new(&mut *gkr_storage);
    let (out, lsb_challenges) = lsb_dim_reducing_sumcheck_prove_fused::<F, E, CK>(
        &polys,
        &relations,
        &output_ptr_table,
        &tau,
        claim,
        worker,
        schedule,
        fold_scratch,
        tri_scratch,
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

    // plain push in protocol order. The dimension-reducing kernel fixes the
    // LOWEST input bit (the gate coordinate) to 0/1 structurally, so the
    // sumcheck rounds bind input bits 1.. (LSB-first) and the gate bit is
    // bound by `r_last` at the very end: element i < n-1 is the coordinate
    // of input bit i+1, the LAST element is input bit 0.
    let mut folding_challenges: Vec<E> = lsb_challenges.clone();
    folding_challenges.push(r_last);

    let new_claims: BTreeMap<_, _> = lsb_lines
        .iter()
        .map(|(addr, [lsb0, lsb1])| (*addr, interpolate_linear::<E>(*lsb0, *lsb1, &r_last)))
        .collect();

    #[cfg(feature = "gkr_self_checks")]
    {
        println!("Self-checking explicit at-point evaluations (LSB path)");
        // the layout-aware builder consumes the emission order directly
        let eq = crate::gkr::sumcheck::eq_poly::make_eq_table_dim_reducing_point::<E>(
            &folding_challenges,
            worker,
        );
        for (k, v) in new_claims.iter() {
            if let Some(poly) = gkr_storage.try_get_base_poly(*k) {
                let eval = evaluate_with_precomputed_eq(poly, &eq[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else if let Some(poly) = gkr_storage.try_get_ext_poly(*k) {
                let eval = evaluate_with_precomputed_eq_ext(poly, &eq[..]);
                assert_eq!(eval, *v, "claim diverged for poly {k:?}");
            } else {
                unreachable!()
            }
        }
    }

    claims_storage.insert(layer_idx, new_claims);
    // the claim/evaluation coordinate must ALWAYS have one entry per bound
    // variable of the INPUT layer: the output rounds plus the kernel-fixed
    // gate bit bound by `r_last` (holds for any schedule, incl. uniskips)
    assert_eq!(folding_challenges.len(), folding_steps + 1);
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
    F: PrimeField + field::TwoAdicField,
    E: FieldExtension<F> + Field,
    TR: Transcript<F, E>,
>(
    layer_idx: usize,
    layer: &GKRLayerDescription<F>,
    claim_points: &mut BTreeMap<usize, Vec<E>>,
    claim_point_entries: &mut BTreeMap<usize, Vec<crate::gkr::prover::EvaluationPointEntry<E>>>,
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
    prev_point_in_dim_reducing_layout: bool,
    same_size_schedules: crate::gkr::prover_config::SameSizeSchedules<'_>,
) -> SumcheckIntermediateProofValues<F, E>
where
    [(); E::DEGREE]: Sized,
{
    println!("Evaluating layer {layer_idx} in sumcheck direction");

    let output_layer_idx = layer_idx + 1;

    let output_claims = claims_storage
        .get(&output_layer_idx)
        .expect("claims for output layer must exist");
    // the previous layer's point: scalar coordinates and/or mixed entries
    // (a uniskip-scheduled producer emits ONLY entries)
    let prev_flat_opt = claim_points.get(&output_layer_idx);
    let prev_entries_opt: Option<Vec<crate::gkr::prover::EvaluationPointEntry<E>>> =
        claim_point_entries.get(&output_layer_idx).cloned();
    assert!(
        prev_flat_opt.is_some() || prev_entries_opt.is_some(),
        "claim point for output layer must exist"
    );
    // the same-size engines consume points in VARIABLE order (LSB round
    // order). A dimension-reducing producer emits [bits 1.., bit 0] (plain
    // push; the gate bit is bound last), so rotate INTERNALLY here.
    let adapted_prev: Vec<E>;
    let prev_flat_opt: Option<&Vec<E>> = match prev_flat_opt {
        Some(pf) if prev_point_in_dim_reducing_layout => {
            let n = pf.len();
            adapted_prev = core::iter::once(&pf[n - 1])
                .chain(pf[..n - 1].iter())
                .copied()
                .collect();
            Some(&adapted_prev)
        }
        other => other,
    };

    assert!(trace_len.is_power_of_two());
    let folding_steps = trace_len.trailing_zeros() as usize;
    assert!(folding_steps >= 4, "need at least 4 folding steps");

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

    // ---- LSB uniskip chain path (schedule-driven; env override for benches) ----
    // The engine computes; THIS caller drives the transcript, emits
    // `SumcheckRoundCoefficients::Uniskip` proof rounds and the mixed claim
    // point as `EvaluationPointEntry::Uniskip` entries, and runs every
    // self-check against the block-tensor eq tables.
    let chain_description = collector.make_batched_description(&challenge_constants, collector.layer);
    let (_chain_compact, chain_base_addrs, chain_ext_addrs) =
        windowed_mode::full_size_scratch::produce_descriptions_from_batched_description(
            &chain_description,
        );
    let (layer_schedule, _width_class) =
        same_size_schedules.for_width(chain_base_addrs.len() + chain_ext_addrs.len());
    // the chain engine needs at least one full uniskip pass plus a sane
    // suffix; tiny layers fall back to the per-round scalar path.
    // GKR_SS_SCHEDULE=naive forces the scalar naive loop (A/B knob),
    // GKR_SS_SCHEDULE=uniskip forces the full uniskip chain.
    let ss_env = std::env::var("GKR_SS_SCHEDULE").ok();
    let use_chain = (matches!(
        layer_schedule.first(),
        Some(crate::gkr::prover_config::SumcheckStep::UniskipInitial { .. })
            | Some(crate::gkr::prover_config::SumcheckStep::WindowedOp(
                crate::gkr::prover_config::WindowedOp::Initial { window: 3 }
            ))
    ) || matches!(ss_env.as_deref(), Some("uniskip") | Some("windowed")))
        && folding_steps >= 6
        && ss_env.as_deref() != Some("naive");
    if use_chain {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::uniskip::*;
        use crate::gkr::prover::EvaluationPointEntry;
        use crate::gkr::sumcheck::eq_poly::make_eq_table_from_weight_blocks;
        let n = folding_steps;
        // pass plan: the schedule's leading pass-steps (head-descriptor
        // semantics: remaining rounds run as naive scalar tail rounds).
        // Env overrides: "uniskip" = all-uniskip chain, "windowed" =
        // all-window chain. A WindowedOp head is a head descriptor for the
        // whole window chain.
        use windowed_mode::lsb_chain::ChainPassKind;
        let pass_kinds: Vec<ChainPassKind> = match ss_env.as_deref() {
            Some("uniskip") => vec![ChainPassKind::Uniskip3; n / 3],
            Some("windowed") => vec![ChainPassKind::Window3; n / 3],
            _ => match layer_schedule.first() {
                Some(crate::gkr::prover_config::SumcheckStep::WindowedOp(
                    crate::gkr::prover_config::WindowedOp::Initial { window: 3 },
                )) => vec![ChainPassKind::Window3; n / 3],
                _ => {
                    let scheduled: Vec<ChainPassKind> = layer_schedule
                        .iter()
                        .map_while(|st| match st {
                            crate::gkr::prover_config::SumcheckStep::UniskipInitial { .. }
                            | crate::gkr::prover_config::SumcheckStep::Uniskip { .. } => {
                                Some(ChainPassKind::Uniskip3)
                            }
                            _ => None,
                        })
                        .collect();
                    if scheduled.is_empty() {
                        vec![ChainPassKind::Uniskip3; n / 3]
                    } else {
                        scheduled.into_iter().take(n / 3).collect()
                    }
                }
            },
        };
        let num_passes = pass_kinds.len();
        let tail_rounds = n - 3 * num_passes;
        let omega16_f: F = ::fft::domain_generator_for_size::<F>(16);

        // previous point as per-entry weight blocks in VARIABLE order
        let prev_blocks: Vec<Vec<E>> = if let Some(entries) = &prev_entries_opt {
            assert_eq!(
                entries.iter().map(|e| e.bound_vars()).sum::<usize>(),
                n,
                "prev point must cover every variable"
            );
            entries
                .iter()
                .map(|e| e.eq_weight_block::<F>(omega16_f))
                .collect()
        } else {
            // scalar storage in variable order: var b <-> prev[b]
            let pf = prev_flat_opt.expect("checked above");
            (0..n)
                .map(|b| {
                    let c = pf[b];
                    let mut om = E::ONE;
                    om.sub_assign(&c);
                    vec![om, c]
                })
                .collect()
        };
        // block variable spans (blocks are in variable order)
        let mut spans: Vec<(usize, usize)> = Vec::with_capacity(prev_blocks.len());
        let mut off = 0usize;
        for b in prev_blocks.iter() {
            let w = b.len().trailing_zeros() as usize;
            spans.push((off, w));
            off += w;
        }
        assert_eq!(off, n);
        let blocks_in = |lo: usize, hi: usize| -> Vec<&[E]> {
            let mut out = Vec::new();
            for ((s0, w), b) in spans.iter().zip(prev_blocks.iter()) {
                if *s0 >= lo && s0 + w <= hi {
                    out.push(&b[..]);
                } else {
                    assert!(
                        s0 + w <= lo || *s0 >= hi,
                        "entry straddles the pass window [{lo}, {hi})"
                    );
                }
            }
            assert_eq!(out.iter().map(|b| b.len().trailing_zeros() as usize).sum::<usize>(), hi - lo);
            out
        };
        // per-pass suffix tables over the HIGH variables
        let eq_suffixes: Vec<Box<[E]>> = (0..num_passes)
            .map(|g| {
                let lo = 3 * (g + 1);
                if lo == n {
                    vec![E::ONE].into_boxed_slice()
                } else {
                    make_eq_table_from_weight_blocks::<E>(&blocks_in(lo, n), worker)
                        .into_boxed_slice()
                }
            })
            .collect();

        // fold arena via the batch-allocation API (LSB ping-pong sizing)
        let alloc_schedule: Vec<crate::gkr::prover_config::SumcheckStep> = (0..num_passes)
            .map(|g| {
                if g == 0 {
                    crate::gkr::prover_config::SumcheckStep::UniskipInitial { window: 3 }
                } else {
                    crate::gkr::prover_config::SumcheckStep::Uniskip { window: 3 }
                }
            })
            .collect();
        let mut chain_fold_map = crate::gkr::prover::gkr_backend::allocate_same_size_fold_buffers::<
            F,
            E,
        >(
            &alloc_schedule,
            1usize << n,
            &chain_base_addrs,
            &chain_ext_addrs,
        );
        let mut chain_fold_arena: Vec<Box<[core::mem::MaybeUninit<E>]>> = chain_base_addrs
            .iter()
            .chain(chain_ext_addrs.iter())
            .map(|a| chain_fold_map.remove(a).expect("allocated"))
            .collect();

        // tail suffix table over the variables above the first tail round
        let mut tail_t_table: Vec<E> = if tail_rounds > 1 {
            make_eq_table_from_weight_blocks::<E>(&blocks_in(3 * num_passes + 1, n), worker)
        } else {
            vec![E::ONE]
        };
        // per-variable scalar coordinates of the prev point, for every
        // variable a SCALAR round binds (window-pass rounds and tail
        // rounds). Each must be a width-1 block: a straddling uniskip block
        // in the producer would make scalar rounds unschedulable there.
        let scalar_coord = |var: usize| -> E {
            let (bi, _) = spans
                .iter()
                .enumerate()
                .find(|(_, (s0, w))| *s0 == var && *w == 1)
                .map(|(i, sp)| (i, *sp))
                .expect("scalar rounds need width-1 prev blocks at their variables");
            prev_blocks[bi][1]
        };
        let var_coords: Vec<Option<E>> = (0..n)
            .map(|var| {
                let in_uniskip_pass = pass_kinds
                    .get(var / 3)
                    .is_some_and(|k| *k == ChainPassKind::Uniskip3);
                if in_uniskip_pass {
                    None
                } else {
                    Some(scalar_coord(var))
                }
            })
            .collect();
        let window_taus: Vec<Option<[E; 2]>> = pass_kinds
            .iter()
            .enumerate()
            .map(|(g, k)| match k {
                ChainPassKind::Uniskip3 => None,
                ChainPassKind::Window3 => Some([
                    var_coords[3 * g + 1].expect("window var"),
                    var_coords[3 * g + 2].expect("window var"),
                ]),
            })
            .collect();

        let mut running_claim = claim;
        let mut chain_rounds: Vec<crate::gkr::prover::SumcheckRoundCoefficients<E>> = Vec::new();
        // the emitted mixed claim point, built in emission (= variable)
        // order by the round callbacks
        let mut point_entries: Vec<EvaluationPointEntry<E>> = Vec::new();
        let mut scalar_eq_prefactor = E::ONE;
        let chain_timer = std::time::Instant::now();
        let finals = {
            let seed_ref = &mut *seed;
            let rc = &mut running_claim;
            let rounds = &mut chain_rounds;
            let entries = &mut point_entries;
            let blocks_in_ref = &blocks_in;
            let var_coords = &var_coords;
            let eq_pref = &mut scalar_eq_prefactor;
            windowed_mode::lsb_chain::run_lsb_uniskip_chain::<F, E, _>(
                &collector,
                &challenge_constants,
                gkr_storage,
                n,
                &pass_kinds,
                &window_taus,
                &eq_suffixes,
                &mut tail_t_table,
                &mut chain_fold_arena,
                worker,
                |round| match round {
                    windowed_mode::lsb_chain::ChainRound::Pass { pass: g, q16 } => {
                        let q16 = &q16;
                        let coeffs = uniskip16_to_monomial::<F, E>(q16, omega16_f);
                        #[cfg(feature = "gkr_self_checks")]
                        {
                            // pass g binds vars 3g..3g+3: its claim identity
                            // uses the prev point's blocks over those vars
                            let eq8: [E; 8] = make_eq_table_from_weight_blocks::<E>(
                                &blocks_in_ref(3 * g, 3 * g + 3),
                                worker,
                            )
                            .try_into()
                            .unwrap();
                            assert_eq!(
                                uniskip16_claim_from_monomial::<F, E>(&coeffs, &eq8, omega16_f),
                                *rc,
                                "LSB uniskip chain: claim identity over H at pass {g}"
                            );
                        }
                        commit_field_els::<F, E, TR>(seed_ref, &coeffs);
                        rounds.push(crate::gkr::prover::SumcheckRoundCoefficients::Uniskip(
                            coeffs.to_vec(),
                        ));
                        let r = draw_random_field_els::<F, E, TR>(seed_ref, 1)[0];
                        *rc = uniskip16_horner(&coeffs, &r);
                        entries.push(EvaluationPointEntry::Uniskip { point: r, width: 3 });
                        r
                    }
                    windowed_mode::lsb_chain::ChainRound::Tail { round: var, h0, hinf } => {
                        // a scalar round binding variable `var`, in the SAME
                        // single-eq-factor form as the naive per-round loop
                        // (byte-identical message for identical inputs)
                        let tau = var_coords[var].expect("scalar round needs a scalar prev coord");
                        let mut normalized_claim = *rc;
                        normalized_claim
                            .mul_assign(&eq_pref.inverse().expect("eq prefactor non-zero"));
                        let coeffs = output_univariate_monomial_form_max_quadratic::<F, E>(
                            tau,
                            normalized_claim,
                            h0,
                            hinf,
                        );
                        if std::env::var("GKR_DBG_ROUNDS").is_ok() {
                            println!("[dbg-round] var {var} coeffs {coeffs:?}");
                        }
                        commit_field_els::<F, E, TR>(seed_ref, &coeffs);
                        rounds.push(crate::gkr::prover::SumcheckRoundCoefficients::Multilinear(
                            coeffs,
                        ));
                        let r = draw_random_field_els::<F, E, TR>(seed_ref, 1)[0];
                        *rc = evaluate_small_univariate_poly::<F, E, _>(&coeffs, &r);
                        *eq_pref = evaluate_eq_poly::<F, E>(&r, &tau);
                        entries.push(EvaluationPointEntry::Coordinate { point: r });
                        r
                    }
                },
            )
        };
        let finals = finals.expect("LSB chain fast path must apply on this platform");
        println!(
            "LSB chain for same-size layer {layer_idx}: {} passes, took {:?}",
            num_passes,
            chain_timer.elapsed()
        );

        assert_eq!(
            point_entries.iter().map(|e| e.bound_vars()).sum::<usize>(),
            folding_steps,
            "the claim point must cover every bound variable"
        );

        let mut new_claims: BTreeMap<GKRAddress, E> = finals;
        // full block-tensor eq table over OWN point: needed by the cached
        // relations (production) and the at-point self-check
        let need_full_eq =
            !layer.cached_relations.is_empty() || cfg!(feature = "gkr_self_checks");
        let full_eq: Option<Vec<E>> = need_full_eq.then(|| {
            let own_blocks: Vec<Vec<E>> = point_entries
                .iter()
                .map(|e| e.eq_weight_block::<F>(omega16_f))
                .collect();
            let refs: Vec<&[E]> = own_blocks.iter().map(|b| &b[..]).collect();
            make_eq_table_from_weight_blocks::<E>(&refs, worker)
        });

        #[cfg(feature = "gkr_self_checks")]
        {
            let eq = full_eq.as_ref().unwrap();
            for (k, v) in new_claims.iter() {
                if let Some(poly) = gkr_storage.try_get_base_poly(*k) {
                    let eval = evaluate_with_precomputed_eq(poly, &eq[..]);
                    assert_eq!(eval, *v, "chain claim diverged for poly {k:?}");
                } else if let Some(poly) = gkr_storage.try_get_ext_poly(*k) {
                    let eval = evaluate_with_precomputed_eq_ext(poly, &eq[..]);
                    assert_eq!(eval, *v, "chain claim diverged for poly {k:?}");
                } else {
                    unreachable!()
                }
            }
            println!("LSB uniskip chain: at-point self-checks passed");
        }

        let final_step_evaluations: BTreeMap<GKRAddress, Vec<E>> =
            new_claims.iter().map(|(k, v)| (*k, vec![*v])).collect();
        let mut transcript_inputs: Vec<E> = new_claims.values().copied().collect();

        // cached relations: extra dependency claims evaluated at the block
        // point, mirroring the scalar path
        let mut extra_evaluations_from_caching_relations = BTreeMap::new();
        for (cached_addr, relation) in layer.cached_relations.iter() {
            assert!(
                new_claims.contains_key(cached_addr),
                "Missing claim for cached address {:?}",
                cached_addr
            );
            for dep in relation.dependencies() {
                if new_claims.contains_key(&dep) {
                    continue;
                }
                match dep {
                    GKRAddress::BaseLayerWitness(_)
                    | GKRAddress::BaseLayerMemory(_)
                    | GKRAddress::Setup(_)
                    | GKRAddress::InnerLayer { .. } => {
                        let eq = full_eq.as_ref().expect("built above");
                        let evaluation = if let Some(values) = gkr_storage.try_get_base_poly(dep) {
                            evaluate_with_precomputed_eq::<F, E>(values, &eq[..])
                        } else if let Some(values) = gkr_storage.try_get_ext_poly(dep) {
                            evaluate_with_precomputed_eq_ext::<E>(values, &eq[..])
                        } else {
                            panic!("Unknown poly at address {:?}", dep);
                        };
                        new_claims.insert(dep, evaluation);
                        extra_evaluations_from_caching_relations.insert(dep, evaluation);
                    }
                    _ => panic!(
                        "Unexpected dependency address {:?} for cached relation {:?}",
                        dep, cached_addr
                    ),
                }
            }
        }
        if !extra_evaluations_from_caching_relations.is_empty() {
            transcript_inputs.extend(extra_evaluations_from_caching_relations.values().copied());
        }
        #[cfg(feature = "gkr_self_checks")]
        assert!(crate::gkr::prover::debug_utils::verify_cache_relations(
            layer,
            &new_claims,
            external_challenges,
            lookup_challenges_multiplicative_part,
        ));

        commit_field_els::<F, E, TR>(seed, &transcript_inputs);
        let next_batching_challenge = draw_random_field_els::<F, E, TR>(seed, 1)[0];

        claims_storage.insert(layer_idx, new_claims);
        // an all-scalar point (no uniskip blocks, e.g. the window chain) is
        // stored as a PLAIN scalar point, indistinguishable from the naive
        // loop's output for every consumer (incl. the WHIR proof fields)
        let all_scalar = point_entries
            .iter()
            .all(|e| matches!(e, EvaluationPointEntry::Coordinate { .. }));
        if all_scalar {
            let flat: Vec<E> = point_entries
                .iter()
                .map(|e| match e {
                    EvaluationPointEntry::Coordinate { point } => *point,
                    _ => unreachable!(),
                })
                .collect();
            claim_points.insert(layer_idx, flat);
        } else {
            claim_point_entries.insert(layer_idx, point_entries);
        }
        gkr_storage.purge_up_to_layer(layer_idx);
        *batching_challenge = next_batching_challenge;

        return SumcheckIntermediateProofValues {
            sumcheck_num_rounds: folding_steps,
            internal_round_coefficients: chain_rounds,
            final_step_evaluations,
            extra_evaluations_from_caching_relations,
            _marker: core::marker::PhantomData,
        };
    }

    // ---- scalar (naive) path: LSB binding, point in variable order ----
    let prev_challenges: &Vec<E> =
        prev_flat_opt.expect("a scalar-consuming schedule requires a scalar-point producer");
    let eq_polys = make_eq_poly_in_full_lsb::<E>(prev_challenges, worker);

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
            same_size_schedules,
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

    #[cfg(feature = "gkr_self_checks")]
    {
        println!("Self-checking explicit at-point evaluations");
        let eq_polys = make_eq_poly_in_full_lsb::<E>(&folding_challenges, worker);
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
                    let mut eq_precomputed = make_eq_poly_in_full_lsb(&folding_challenges, worker);
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
                                make_eq_poly_in_full_lsb(&folding_challenges, worker);
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
        {
            assert!(crate::gkr::prover::debug_utils::verify_cache_relations(
                layer,
                &new_claims,
                external_challenges,
                lookup_challenges_multiplicative_part,
            ));
        }
    }

    // after all claims for the next layer are ready - draw the next batching challenge
    commit_field_els::<F, E, TR>(seed, &transcript_inputs);
    let next_batching_challenge = draw_random_field_els::<F, E, TR>(seed, 1)[0];

    claims_storage.insert(layer_idx, new_claims);
    // one scalar coordinate per bound variable, in variable (round) order
    assert_eq!(folding_challenges.len(), folding_steps);
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
    same_size_schedules: crate::gkr::prover_config::SameSizeSchedules<'_>,
) -> (Vec<E>, Vec<[E; 4]>, BTreeMap<GKRAddress, [E; N]>, E)
where
    [(); E::DEGREE]: Sized,
{
    if USE_BATCHING {
        println!("Running sumcheck loop in batched naive (LSB) mode");
    } else {
        println!("Running sumcheck loop in individual kernel mode");
    }

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

        if std::env::var("GKR_DBG_ROUNDS").is_ok() {
            println!("[dbg-round] var {step} coeffs {coeffs:?}");
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
