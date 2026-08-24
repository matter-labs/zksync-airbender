use std::collections::BTreeMap;

use crate::definitions::SecurityLevel;
use crate::gkr::{prover::WhirSchedule, whir::proximity_testing_modes::ProximityTestingMode};

pub mod example_configs;
pub mod pow_bits;

/// One step of a sumcheck schedule: how many variables the step binds and
/// with which evaluation strategy. The prover binds variables LSB-first
/// (consistent with monomial ordering and WHIR's RS-codeword folding), so a
/// step always consumes the CURRENTLY LOWEST variables of the remaining
/// hypercube.
///
/// The grammar is STRICT (see [`validate_sumcheck_schedule`]): a valid
/// schedule is either all-naive (the empty schedule, or one `NaiveSumcheck`
/// per variable), or a window chain
/// (`WindowInitial, FoldInitial, (WindowContinuing, FoldContinuing)*, Tail`).
/// Pass steps are labeled by what they READ (`*Initial` reads the original
/// layer inputs, `*Continuing` the folded tables); the non-merged fold that
/// materializes each pass's binding is an EXPLICIT step with the same
/// labeling, and the scalar rounds that finish the layer are the explicit
/// `Tail` step.
///
/// Uniskip chains
/// (`UniskipInitial, FoldInitial, (UniskipContinuing, FoldContinuing)*, Tail`)
/// are grammatically reserved but currently UNIMPLEMENTED:
/// [`validate_sumcheck_schedule`] panics on any uniskip step. The redesign
/// makes a uniskip pass emit a Lagrange WEIGHT-BLOCK claim (8 node-Lagrange
/// weights over the window corners instead of 3 bound point coordinates),
/// and neither the same-size engines nor the WHIR handoff carry that claim
/// shape yet.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SumcheckStep {
    /// The classic mode: fold exactly one variable with the per-round batched
    /// evaluator (one `[E; 4]` message per round; the fold is lazy, merged
    /// into the next round's evaluation).
    NaiveSumcheck,
    /// Univariate-skip pass over the ORIGINAL layer inputs: `window`
    /// variables packed into ONE univariate round (message = monomial
    /// coefficients of the packed q, degree `< 2^{window + 1}`). Leaves its
    /// challenge's Lagrange fold to the following [`SumcheckStep::FoldInitial`].
    UniskipInitial { window: usize },
    /// Univariate-skip pass over the PREVIOUSLY FOLDED tables; its fold is
    /// the following [`SumcheckStep::FoldContinuing`].
    UniskipContinuing { window: usize },
    /// Windowed-accumulator pass over the ORIGINAL layer inputs: the
    /// `{0,1,inf}^window` accumulator is computed in one pass and `window`
    /// ordinary scalar rounds are emitted from the bind chain. The batched
    /// eq-tensor fold is the following [`SumcheckStep::FoldInitial`].
    WindowInitial { window: usize },
    /// Windowed-accumulator pass over the PREVIOUSLY FOLDED tables; its fold
    /// is the following [`SumcheckStep::FoldContinuing`].
    WindowContinuing { window: usize },
    /// The explicit (non-merged) fold materializing the PRECEDING pass's
    /// binding, reading the ORIGINAL layer inputs (i.e. after an `*Initial`
    /// pass) and writing the first dense folded tables. `width` is the
    /// folding width and must equal the preceding pass's window (validated).
    FoldInitial { width: usize },
    /// The explicit fold after a `*Continuing` pass: reads the previous
    /// dense folded tables, writes the next ones. `width` must equal the
    /// preceding pass's window (validated).
    FoldContinuing { width: usize },
    /// Scalar naive rounds over the dense folded tables, binding ALL
    /// remaining variables (possibly zero) and finishing the layer. Required
    /// after uniskip/window chains.
    Tail,
}

impl SumcheckStep {
    /// Number of hypercube variables this step binds. Folds bind none (they
    /// materialize the preceding pass's binding); [`SumcheckStep::Tail`]
    /// binds "all remaining", which only [`validate_sumcheck_schedule`] can
    /// account for.
    pub fn variables_bound(&self) -> usize {
        match self {
            SumcheckStep::NaiveSumcheck => 1,
            SumcheckStep::UniskipInitial { window }
            | SumcheckStep::UniskipContinuing { window }
            | SumcheckStep::WindowInitial { window }
            | SumcheckStep::WindowContinuing { window } => *window,
            SumcheckStep::FoldInitial { .. }
            | SumcheckStep::FoldContinuing { .. }
            | SumcheckStep::Tail => 0,
        }
    }
}

/// The three valid schedule shapes (see [`validate_sumcheck_schedule`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SumcheckScheduleClass {
    Naive,
    Uniskip,
    Windowed,
}

/// Checks the STRICT schedule grammar for `folding_steps` variables and
/// returns the schedule's class. Valid schedules:
///
/// * all-naive: the EMPTY schedule (naive for every round), or exactly
///   `folding_steps` `NaiveSumcheck` steps;
/// * window chain: `WindowInitial{3}, FoldInitial,
///   (WindowContinuing{3}, FoldContinuing)*, Tail`.
///
/// Chains additionally require `3 * passes <= folding_steps` (the `Tail`
/// binds the remainder, possibly zero) and at least 6 folding steps (the
/// engines' shape guard). Fold labels must match their pass (`FoldInitial`
/// only right after the `*Initial` pass).
///
/// Uniskip steps PANIC as unimplemented (see the [`SumcheckStep`] docs); the
/// uniskip arms of the grammar below are kept as the spec for re-enabling.
pub fn validate_sumcheck_schedule(
    schedule: &[SumcheckStep],
    folding_steps: usize,
) -> Result<SumcheckScheduleClass, String> {
    if schedule.iter().any(|s| {
        matches!(
            s,
            SumcheckStep::UniskipInitial { .. } | SumcheckStep::UniskipContinuing { .. }
        )
    }) {
        unimplemented!(
            "uniskip sumcheck steps: the Lagrange weight-block claim shape is not \
             wired through the same-size engines and the WHIR handoff"
        );
    }
    if schedule.is_empty() {
        return Ok(SumcheckScheduleClass::Naive);
    }
    if schedule
        .iter()
        .all(|s| matches!(s, SumcheckStep::NaiveSumcheck))
    {
        if schedule.len() != folding_steps {
            return Err(format!(
                "all-naive schedule has {} steps, layer has {} variables",
                schedule.len(),
                folding_steps
            ));
        }
        return Ok(SumcheckScheduleClass::Naive);
    }

    // chain grammar
    let class = match schedule.first() {
        Some(SumcheckStep::UniskipInitial { window: 3 }) => SumcheckScheduleClass::Uniskip,
        Some(SumcheckStep::WindowInitial { window: 3 }) => SumcheckScheduleClass::Windowed,
        other => {
            return Err(format!(
            "a chain schedule must open with UniskipInitial{{3}} or WindowInitial{{3}}, got {:?}",
            other
        ))
        }
    };
    if folding_steps < 6 {
        return Err(format!(
            "chain schedules need at least 6 folding steps, layer has {folding_steps}"
        ));
    }
    let first_window = schedule[0].variables_bound();
    match schedule.get(1) {
        Some(SumcheckStep::FoldInitial { width }) if *width == first_window => {}
        Some(SumcheckStep::FoldInitial { width }) => {
            return Err(format!(
                "FoldInitial width {width} does not match the initial pass window {first_window}"
            ))
        }
        other => {
            return Err(format!(
                "the initial pass must be followed by a width-matched FoldInitial, got {other:?}"
            ))
        }
    }
    let mut passes = 1usize;
    let mut i = 2usize;
    loop {
        match (schedule.get(i), class) {
            (Some(SumcheckStep::UniskipContinuing { window: 3 }), SumcheckScheduleClass::Uniskip)
            | (Some(SumcheckStep::WindowContinuing { window: 3 }), SumcheckScheduleClass::Windowed) =>
            {
                let pass_window = schedule[i].variables_bound();
                match schedule.get(i + 1) {
                    Some(SumcheckStep::FoldContinuing { width }) if *width == pass_window => {}
                    Some(SumcheckStep::FoldContinuing { width }) => {
                        return Err(format!(
                            "FoldContinuing width {width} at position {} does not match the \
                             pass window {pass_window}",
                            i + 1
                        ))
                    }
                    other => {
                        return Err(format!(
                            "the continuing pass at position {i} must be followed by a \
                             width-matched FoldContinuing, got {other:?}"
                        ))
                    }
                }
                passes += 1;
                i += 2;
            }
            (Some(SumcheckStep::Tail), _) => {
                if i + 1 != schedule.len() {
                    return Err("Tail must be the last step".to_string());
                }
                break;
            }
            (other, _) => {
                return Err(format!(
                    "unexpected step {:?} at position {i} (expected a matching continuing pass or Tail)",
                    other
                ))
            }
        }
    }
    if 3 * passes > folding_steps {
        return Err(format!(
            "{passes} passes bind {} variables, layer has {folding_steps}",
            3 * passes
        ));
    }
    Ok(class)
}

#[derive(Clone, Debug)]
pub struct ProverConfig {
    /// log2 of the circuit trace length this config was computed for. The
    /// prove entries assert the caller-supplied `trace_len` matches, so a
    /// config can never silently be applied to a different-size circuit
    /// (schedules, query counts and PoW splits are all size-specific).
    pub trace_len_log2: usize,
    pub lde_factor: usize,
    pub cap_size: usize,
    pub base_oracles_values_per_leaf: usize,
    // we do not expect any challenges for sumcheck, as it's soundness
    // error is very small
    pub sumcheck_explicit_output_size_log_2: usize,
    // Both proof-of-work bit counts (lookup challenges, WHIR batching) are derived
    // per-circuit from `security_level` via `pow_bits`, so neither is stored here.
    pub security_level: SecurityLevel,
    pub whir_schedule: WhirSchedule,
    /// Step schedule for the same-size (per-circuit batched relation) layer
    /// sumchecks, applied to every same-size layer regardless of its input
    /// poly count. Must satisfy the STRICT grammar of
    /// [`validate_sumcheck_schedule`] for the trace length's variable count.
    pub same_size_sumcheck_schedule: Vec<SumcheckStep>,
    /// Step schedules for the DIMENSION-REDUCING layer sumchecks (pairwise
    /// products + logup reduction gates only), keyed by the layer's number
    /// of sumcheck rounds: a layer with `n` rounds uses
    /// `dimension_reducing_sumcheck_schedule[&n]` if present, and
    /// NaiveSumcheck for every round otherwise. Each entry must satisfy
    /// [`validate_sumcheck_schedule`] for its key.
    pub dimension_reducing_sumcheck_schedule: BTreeMap<usize, Vec<SumcheckStep>>,
}

impl ProverConfig {
    /// Structural validation of the WHIR schedule for a starting polynomial of
    /// `message_size_log2` variables — equal to [`Self::trace_len_log2`] for
    /// the separate/merged commitment modes and `trace_len_log2 + pack_log2`
    /// for the packed mode. Called by the prove entries after they assert the
    /// caller's `trace_len` against `trace_len_log2`.
    ///
    /// Beyond shape consistency, enforces the plain-text floor: every
    /// COMMITTED intermediate oracle must be an LDE of a polynomial of at
    /// least `1 << DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2` monomials. Folding
    /// below that size must instead TERMINATE the schedule — the tail
    /// polynomial ships as explicit monomial coefficients, which is strictly
    /// cheaper than another LDE + Merkle commitment + query round for both
    /// prover and verifier.
    pub fn validate_for_whir_message_size(&self, message_size_log2: usize) {
        use crate::definitions::DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2;

        let schedule = &self.whir_schedule;
        let num_rounds = schedule.whir_steps_schedule.len();
        assert!(num_rounds >= 1, "empty WHIR schedule");
        assert_eq!(schedule.whir_queries_schedule.len(), num_rounds);
        assert_eq!(schedule.whir_pow_schedule.len(), num_rounds);
        assert_eq!(schedule.whir_steps_lde_factors.len(), num_rounds - 1);
        assert_eq!(schedule.base_lde_factor, self.lde_factor);
        assert_eq!(schedule.cap_size, self.cap_size);
        assert_eq!(
            self.base_oracles_values_per_leaf,
            1usize << schedule.whir_steps_schedule[0],
            "base-oracle leaves hold exactly one round-0 fold worth of values"
        );

        let mut poly_size_log2 = message_size_log2;
        for (round, fold_log2) in schedule.whir_steps_schedule.iter().enumerate() {
            assert!(*fold_log2 >= 1);
            assert!(
                poly_size_log2 >= *fold_log2,
                "WHIR round {round} folds by 2^{fold_log2} but only a 2^{poly_size_log2} \
                 polynomial remains"
            );
            poly_size_log2 -= *fold_log2;
            let commits_an_oracle = round + 1 != num_rounds;
            if commits_an_oracle {
                assert!(
                    poly_size_log2 >= DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
                    "WHIR round {round} would commit an LDE of a 2^{poly_size_log2} polynomial \
                     (below the 2^{DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2} plain-text floor): \
                     terminate the schedule here and ship the tail in plain text instead"
                );
            }
        }
        assert!(
            poly_size_log2 >= 1,
            "the WHIR schedule folds the polynomial away completely"
        );
        assert!(
            poly_size_log2 <= DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            "the schedule's explicit tail (2^{poly_size_log2}) exceeds the plain-text \
             envelope 2^{DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2}"
        );
    }
}

/// The DEFAULT same-size schedule: the full window chain for
/// `folding_steps` variables -- window passes while three variables remain,
/// then the scalar `Tail`.
pub fn windowed_same_size_schedule(folding_steps: usize) -> Vec<SumcheckStep> {
    assert!(folding_steps >= 6);
    let passes = folding_steps / 3;
    let mut schedule = Vec::with_capacity(2 * passes + 1);
    schedule.push(SumcheckStep::WindowInitial { window: 3 });
    schedule.push(SumcheckStep::FoldInitial { width: 3 });
    for _ in 1..passes {
        schedule.push(SumcheckStep::WindowContinuing { window: 3 });
        schedule.push(SumcheckStep::FoldContinuing { width: 3 });
    }
    schedule.push(SumcheckStep::Tail);
    schedule
}

/// The all-naive same-size schedule for ProverConfig literals: the EMPTY
/// schedule, which means NaiveSumcheck for every round (see
/// [`validate_sumcheck_schedule`]). No windows, no uniskip.
pub fn naive_same_size_schedule() -> Vec<SumcheckStep> {
    Vec::new()
}

impl WhirSchedule {
    pub fn current_cost(&self, trace_len_log_2: usize, cost_model: &impl CostModel) -> usize {
        let mut total_cost = 0;
        let cap_depth_cut = self.cap_size.trailing_zeros() as usize;
        let mut whir_sumcheck_terms = 0;

        {
            // base oracle queries
            let depth =
                trace_len_log_2 + (self.base_lde_factor.trailing_zeros() as usize) - cap_depth_cut;
            let num_queries = self.whir_queries_schedule[0];
            whir_sumcheck_terms += num_queries;
            let cost = cost_model.single_merkle_tree_depth_cost() * depth * num_queries;
            total_cost += cost;
        }

        let mut poly_size = trace_len_log_2 - self.whir_steps_schedule[0];

        if self.whir_steps_lde_factors.len() > 0 {
            for i in 0..self.whir_steps_lde_factors.len() {
                let num_queries = self.whir_queries_schedule[i + 1];
                whir_sumcheck_terms += num_queries;
                let rate = self.whir_steps_lde_factors[i].trailing_zeros();
                if poly_size + (rate as usize) < cap_depth_cut {
                    return usize::MAX;
                }
                let depth = poly_size + (rate as usize) - cap_depth_cut;
                let cost = cost_model.single_merkle_tree_depth_cost() * depth * num_queries;
                total_cost = total_cost.saturating_add(cost);
                // and folding
                let fold_by = self.whir_steps_schedule[i + 1];
                let cost = num_queries
                    .saturating_mul(cost_model.whir_leaf_hashing_and_folding_cost(fold_by as u32));
                total_cost = total_cost.saturating_add(cost);
                poly_size -= fold_by as usize;
            }
        }
        // final sumcheck
        let cost = cost_model.whir_sumcheck_terms_cost(poly_size) * whir_sumcheck_terms;
        total_cost = total_cost.saturating_add(cost);

        total_cost
    }
}

// NOTE: consider adding PoW cost
pub trait CostModel: 'static + Send + Sync {
    fn single_merkle_tree_depth_cost(&self) -> usize;
    fn whir_leaf_hashing_and_folding_cost(&self, folding_rate: u32) -> usize;
    fn whir_sumcheck_terms_cost(&self, final_degree_log_2: usize) -> usize;
}

pub struct BlakeHashBabyBearExt4CostModel;

impl CostModel for BlakeHashBabyBearExt4CostModel {
    fn single_merkle_tree_depth_cost(&self) -> usize {
        128
    }
    fn whir_leaf_hashing_and_folding_cost(&self, folding_rate: u32) -> usize {
        match folding_rate {
            0 => {
                unreachable!()
            }
            rate @ 1..=4 => 128 + (1 << rate) * 32,
            rate @ 5 => 128 * 2 + (1 << rate) * 32,
            _ => usize::MAX,
        }
    }
    fn whir_sumcheck_terms_cost(&self, final_degree_log_2: usize) -> usize {
        128 * (1 << final_degree_log_2)
    }
}

pub fn compute_best_prover_config_guess(
    trace_len_log_2: usize,
    lde_factor: usize,
    cap_size: usize,
    base_oracles_values_per_leaf: usize,
    sumcheck_explicit_output_size_log_2: usize,
    security_bits: u32,
    first_round_pow_bits: u32,
    other_rounds_pow_bits: u32,
    min_pow_bits: u32,
    max_lde_factor: usize,
    max_lde_size_log_2: usize,
    whir_target_security_bits: u32,
    max_whir_explicit_output_size_log_2: usize,
    proximity_testing_mode: &impl ProximityTestingMode,
    cost_model: &impl CostModel,
) -> ProverConfig {
    assert!(lde_factor.is_power_of_two());
    assert!(cap_size.is_power_of_two());
    assert!(base_oracles_values_per_leaf.is_power_of_two());
    assert_eq!(
        base_oracles_values_per_leaf, 2,
        "placing 2 values per poly into base oracle leafs is considered optimal for now"
    );

    // NOTE: we do not implement any complex WHIR parameters search strategy, but try to keep all WHIR commits to be
    // roughly the same complexity.

    let mut whir_schedule = WhirSchedule {
        base_lde_factor: lde_factor,
        cap_size,
        whir_steps_schedule: vec![1], // in all our circuits base oracles are relatively large, and packing multiple leafs
        // in them is not obviously beneficial. So one can quickly fold by 2 and move from individual proximity checks
        // to batched one, and then try to using `1 << whir_average_folding_rate_log_2` elements per leaf
        whir_pow_schedule: vec![first_round_pow_bits],
        whir_steps_lde_factors: vec![],
        whir_queries_schedule: vec![],
    };

    let base_rate = lde_factor.trailing_zeros();
    {
        let proximity_testing_bits = whir_target_security_bits - first_round_pow_bits;
        let num_queries = proximity_testing_mode
            .num_queries_for_rate_and_bits_of_security(proximity_testing_bits, base_rate);
        whir_schedule
            .whir_queries_schedule
            .push(num_queries as usize);
    }

    let mut candidates = BTreeMap::new();

    assert!(max_lde_size_log_2 >= trace_len_log_2 + base_rate as usize);
    whir_folding_step(
        &mut candidates,
        trace_len_log_2,
        max_lde_size_log_2,
        other_rounds_pow_bits,
        min_pow_bits,
        max_lde_factor.trailing_zeros() as usize,
        whir_target_security_bits,
        max_whir_explicit_output_size_log_2,
        proximity_testing_mode,
        cost_model,
        &whir_schedule,
    );

    dbg!(&candidates);

    todo!();

    // ProverConfig {
    //     lde_factor,
    //     cap_size,
    //     base_oracles_values_per_leaf,
    //     sumcheck_explicit_output_size_log_2,
    //     security_level,
    //     whir_schedule,
    // }
}

fn whir_folding_step(
    candidates: &mut BTreeMap<usize, WhirSchedule>,
    trace_len_log_2: usize,
    max_lde_size_log_2: usize,
    max_pow_bits: u32,
    min_pow_bits: u32,
    min_rate_log_2: usize,
    whir_target_security_bits: u32,
    max_whir_explicit_output_size_log_2: usize,
    proximity_testing_mode: &impl ProximityTestingMode,
    cost_model: &impl CostModel,
    path: &WhirSchedule,
) {
    // trim candidates

    // TODO: make it better logic, not just lowest 10, but a cost range
    if let Some((&min_cost, _)) = candidates.iter().next() {
        let max_cost = (min_cost * 110) / 100;
        candidates.retain(|cost, _v| *cost <= max_cost);
    }

    assert!(path.total_poly_size_reduction() <= trace_len_log_2);

    let whir_poly_size_log_2 = trace_len_log_2 - path.total_poly_size_reduction();

    if whir_poly_size_log_2 == 0 {
        return;
    }

    // assert!(whir_poly_size_log_2 > 0);
    if whir_poly_size_log_2 <= max_whir_explicit_output_size_log_2 {
        let total_cost = path.current_cost(trace_len_log_2, cost_model);
        let min_cost = candidates
            .iter()
            .next()
            .map(|(k, _v)| *k)
            .unwrap_or(usize::MAX);
        if total_cost < min_cost {
            println!("Inserting {:?} with the cost {}", path, total_cost);
            candidates.insert(total_cost, path.clone());
        }
    }

    if whir_poly_size_log_2 > 1 {
        // we can try to fold more, but we pay for it by queries and LDE
        for fold_by in (1..whir_poly_size_log_2).rev() {
            if fold_by > 5 {
                continue;
            }
            if fold_by >= whir_poly_size_log_2 {
                continue;
            }
            let bound = max_lde_size_log_2 - whir_poly_size_log_2;
            for rate in (1..=bound).rev() {
                let mut pow_bits = max_pow_bits;
                let proximity_testing_bits = whir_target_security_bits - pow_bits;
                let min_queries = proximity_testing_mode
                    .num_queries_for_rate_and_bits_of_security(proximity_testing_bits, rate as u32);

                let mut pow_is_free = true;
                for bits in (min_pow_bits..pow_bits).rev() {
                    let proximity_testing_bits = whir_target_security_bits - pow_bits;
                    let queries = proximity_testing_mode.num_queries_for_rate_and_bits_of_security(
                        proximity_testing_bits,
                        rate as u32,
                    );
                    if queries == min_queries {
                        pow_bits = bits;
                    } else {
                        pow_is_free = false;
                        break;
                    }
                }
                let mut rate_to_use = rate;
                if pow_is_free {
                    // we can try to reduce the rate for this round
                    for better_rate in 1..rate {
                        let proximity_testing_bits = whir_target_security_bits - min_pow_bits;
                        let queries = proximity_testing_mode
                            .num_queries_for_rate_and_bits_of_security(
                                proximity_testing_bits,
                                better_rate as u32,
                            );
                        if queries == min_queries {
                            rate_to_use = better_rate;
                        } else {
                            break;
                        }
                    }
                }
                let current_rate = path
                    .whir_steps_lde_factors
                    .last()
                    .copied()
                    .unwrap_or(path.base_lde_factor.trailing_zeros() as usize);
                if current_rate + whir_poly_size_log_2 < path.cap_size.trailing_zeros() as usize {
                    continue;
                }

                let mut new_path = path.clone();
                new_path.whir_pow_schedule.push(pow_bits);
                new_path.whir_queries_schedule.push(min_queries as usize);
                new_path.whir_steps_schedule.push(fold_by);
                new_path.whir_steps_lde_factors.push(1usize << rate_to_use);

                whir_folding_step(
                    candidates,
                    trace_len_log_2,
                    max_lde_size_log_2,
                    max_pow_bits,
                    min_pow_bits,
                    min_rate_log_2,
                    whir_target_security_bits,
                    max_whir_explicit_output_size_log_2,
                    proximity_testing_mode,
                    cost_model,
                    &new_path,
                );
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{definitions::*, gkr::whir::proximity_testing_modes::PessimisticConjectureMode};

    use super::*;

    #[test]
    fn example_configs_pass_validation() {
        for log in [20usize, 22, 23, 24] {
            let config = example_configs::config_for_100_bits_under_pessimistic_conjecture(log);
            assert_eq!(config.trace_len_log2, log);
            config.validate_for_whir_message_size(log);
        }
        let feeder = example_configs::l1_feeder_config_for_2_23();
        assert_eq!(feeder.trace_len_log2, 23);
        feeder.validate_for_whir_message_size(feeder.trace_len_log2);
    }

    #[test]
    #[should_panic(expected = "plain-text floor")]
    fn sub_plain_text_oracle_is_rejected() {
        // Re-append the retired sixth round of the 2^23 schedule: its oracle
        // would be an LDE of a 2^3 polynomial, below the plain-text floor.
        let mut config = example_configs::config_for_100_bits_under_pessimistic_conjecture(23);
        config.whir_schedule.whir_steps_schedule.push(2);
        config.whir_schedule.whir_queries_schedule.push(5);
        config.whir_schedule.whir_pow_schedule.push(21);
        config.whir_schedule.whir_steps_lde_factors.push(524288);
        config.validate_for_whir_message_size(23);
    }

    #[test]
    fn test_try_compute_some_config() {
        let prover_config = compute_best_prover_config_guess(
            20,
            DEFAULT_LDE_FACTOR,
            DEFAULT_CAP_SIZE,
            2,
            DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            0,
            28,
            24,
            // 20,
            0,
            1 << 22,
            27,
            // 100,
            80,
            DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            &PessimisticConjectureMode,
            &BlakeHashBabyBearExt4CostModel,
        );
        dbg!(prover_config);
    }
}
