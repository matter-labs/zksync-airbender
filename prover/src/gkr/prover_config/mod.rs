use std::collections::BTreeMap;

use crate::definitions::SecurityLevel;
use crate::gkr::whir::proximity_testing_modes::ProximityTestingMode;

pub mod example_configs;
pub mod pow_bits;
pub mod whir_schedule;

pub use example_configs::{BaseColumns, BasePacking, SoundnessMode, WhirInput};
pub use whir_schedule::{WhirBaseRoundSchedule, WhirInternalRound, WhirSchedule};

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

/// How the memory and witness base columns are committed: as two base oracles
/// (two caps in the transcript, two round-0 Merkle paths per query) or as ONE
/// merged oracle holding the memory columns followed by the witness columns
/// (one cap, one path). A property of the proving geometry — part of the
/// [`ProverConfig`] the circuit is proved and verified with — not of how the
/// proof is used (see `prover::gkr::prover::OperationMode` for that).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum CommitmentMode {
    SeparateMemoryAndWitness,
    MergedMemoryAndWitness,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(from = "legacy_compat::ProverConfigRepr")]
pub struct ProverConfig {
    /// log2 of the circuit trace length this config was computed for. The
    /// prove entries assert the caller-supplied `trace_len` matches, so a
    /// config can never silently be applied to a different-size circuit
    /// (schedules, query counts and PoW splits are all size-specific).
    pub trace_len_log2: usize,
    /// Merkle cap size of every committed oracle; equal to
    /// `whir_schedule.cap_size` (asserted by the validation).
    pub cap_size: usize,
    // we do not expect any challenges for sumcheck, as it's soundness
    // error is very small
    pub sumcheck_explicit_output_size_log_2: usize,
    // The lookup-challenge proof-of-work bit count is derived per-circuit from
    // `security_level` via `pow_bits`; the WHIR-side PoW knobs live in the
    // schedule.
    pub security_level: SecurityLevel,
    /// The whole WHIR geometry: the base round ([`WhirBaseRoundSchedule`]:
    /// the base oracles' LDE factor, physical packing, round-0 fold — `0` is
    /// virtual packing with one value per column per leaf — and base query
    /// draw), and one [`WhirInternalRound`] per intermediate oracle.
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
    /// Whether memory and witness are committed as two base oracles or as one
    /// merged oracle (see [`CommitmentMode`]). Decides the transcript layout,
    /// the committed (packed) column grouping and thus the generated verifier.
    pub commitment_mode: CommitmentMode,
}

impl ProverConfig {
    /// A bare config for WHIR-only drivers and tests: a
    /// `SeparateMemoryAndWitness` commitment of `2^trace_len_log2` columns
    /// under `whir_schedule` (the base LDE factor, cap, packing and round-0
    /// leaf size are the schedule's); the GKR-side schedules are the all-naive
    /// defaults.
    pub fn whir_only(
        trace_len_log2: usize,
        whir_schedule: WhirSchedule,
        security_level: SecurityLevel,
    ) -> Self {
        Self {
            trace_len_log2,
            cap_size: whir_schedule.cap_size,
            sumcheck_explicit_output_size_log_2:
                crate::definitions::DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2,
            security_level,
            whir_schedule,
            same_size_sumcheck_schedule: naive_same_size_schedule(),
            dimension_reducing_sumcheck_schedule: Default::default(),
            commitment_mode: CommitmentMode::SeparateMemoryAndWitness,
        }
    }

    /// Whether memory and witness were committed as ONE merged base oracle.
    pub fn merged_memory_and_witness(&self) -> bool {
        matches!(self.commitment_mode, CommitmentMode::MergedMemoryAndWitness)
    }

    /// The base round of the WHIR schedule: the base oracles' rate, packing,
    /// round-0 fold and query draw (see [`WhirBaseRoundSchedule`]).
    pub fn base_round(&self) -> &WhirBaseRoundSchedule {
        &self.whir_schedule.base_round
    }

    /// log2 of the BASE-COMMITMENT packing factor. Every committed column set
    /// (memory and witness — separately in `SeparateMemoryAndWitness`, as one
    /// merged set in the merged modes — and the setup) is packed by
    /// `2^pack_log2` consecutive columns into ONE `(trace_len_log2 +
    /// pack_log2)`-variate multilinear (block `y` of the packed poly is
    /// sub-poly `y`; a short tail group is zero-padded), which is LDE'd and
    /// Merkle-committed over the enlarged domain. The WHIR message is then
    /// `2^(trace_len_log2 + pack_log2)` and the base claims are merged with
    /// `pack_log2` extra claim-point coordinates drawn after the GKR phase.
    /// `0` = unpacked (one committed column per base column). Independent of
    /// the round-0 fold (virtual packing). Twiddles passed to the prover must
    /// cover the `2^(trace_len_log2 + pack_log2)` domain.
    pub fn pack_log2(&self) -> usize {
        self.whir_schedule.pack_log2()
    }

    /// The base oracles' LDE factor.
    pub fn lde_factor(&self) -> usize {
        self.whir_schedule.base_lde_factor()
    }

    pub fn base_lde_factor_log2(&self) -> usize {
        self.whir_schedule.base_lde_factor_log2()
    }

    /// Values every base-oracle leaf holds per committed column: one round-0
    /// fold worth (`2^folding_log2` under explicit packing, `1` under virtual
    /// packing).
    pub fn base_oracles_values_per_leaf(&self) -> usize {
        self.whir_schedule.base_values_per_leaf()
    }

    /// Whether the base round is the virtual-packing (one value per column per
    /// leaf, no round-0 sumcheck) one.
    pub fn is_virtual_packing(&self) -> bool {
        self.whir_schedule.is_virtual_packing()
    }

    /// log2 of the WHIR message size — the committed (packed) column length
    /// `trace_len_log2 + pack_log2`; equal to [`Self::trace_len_log2`] when
    /// unpacked.
    pub fn whir_message_size_log2(&self) -> usize {
        self.trace_len_log2 + self.pack_log2()
    }

    /// Structural validation of the WHIR schedule for a starting polynomial of
    /// `message_size_log2` variables — [`Self::whir_message_size_log2`], i.e.
    /// `trace_len_log2 + pack_log2`. Called by the prove entries after they
    /// assert the caller's `trace_len` against `trace_len_log2`.
    ///
    /// Beyond shape consistency, enforces the plain-text floor: every
    /// COMMITTED intermediate oracle must be an LDE of a polynomial of at
    /// least `1 << DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2` monomials. Folding
    /// below that size must instead TERMINATE the schedule — the tail
    /// polynomial ships as explicit monomial coefficients, which is strictly
    /// cheaper than another LDE + Merkle commitment + query round for both
    /// prover and verifier.
    ///
    /// Also checks the Merkle geometry of EVERY committed oracle (the base
    /// oracles and each intermediate one): LDE factors, cap and leaf sizes are
    /// powers of two, a leaf never exceeds its coset, and the cap never exceeds
    /// the tree's leaf count. These are the only geometric constraints — the
    /// storage policy ([`WhirOracleStorage`](crate::gkr::prover::WhirOracleStorage),
    /// in-memory, coset-by-coset recompute or on-disk) imposes none of its own,
    /// in particular no relation between `cap_size` and the LDE factors.
    pub fn validate_for_whir_message_size(&self, message_size_log2: usize) {
        use crate::definitions::DEFAULT_PLAIN_TEXT_POLY_SIZE_LOG2;

        let schedule = &self.whir_schedule;
        assert_eq!(
            message_size_log2,
            self.whir_message_size_log2(),
            "the WHIR message size is trace_len_log2 + pack_log2"
        );
        let num_rounds = schedule.num_rounds();
        assert!(
            num_rounds >= 2,
            "a WHIR schedule needs the base round and at least one internal round"
        );
        assert_eq!(schedule.cap_size, self.cap_size);
        assert!(
            schedule.base_lde_factor_log2() >= 1,
            "base LDE factor {} must be a power of two >= 2",
            schedule.base_lde_factor()
        );
        assert!(
            self.cap_size.is_power_of_two(),
            "cap size {} must be a power of two",
            self.cap_size
        );
        assert!(schedule.base_round.num_queries >= 1);
        for (i, round) in schedule.internal_rounds.iter().enumerate() {
            assert!(
                round.lde_factor_log2 >= 1,
                "WHIR intermediate oracle {i} LDE factor {} must be a power of two >= 2",
                round.lde_factor()
            );
            assert!(
                round.folding_log2 >= 1,
                "WHIR intermediate oracle {i} must be folded by at least one step"
            );
            assert!(
                round.num_ood_samples >= 1,
                "WHIR intermediate oracle {i} needs at least one OOD sample"
            );
            assert!(round.num_queries >= 1);
        }

        // Merkle geometry of the oracle committed with LDE factor `lde_factor`
        // over a 2^poly_size_log2 polynomial, `2^values_per_leaf_log2` values
        // per leaf: valid for any `cap_size` up to the number of leaves.
        let check_tree = |what: &str,
                          poly_size_log2: usize,
                          lde_factor: usize,
                          values_per_leaf_log2: usize| {
            assert!(
                values_per_leaf_log2 <= poly_size_log2,
                "{what}: a leaf of 2^{values_per_leaf_log2} values exceeds the 2^{poly_size_log2} coset"
            );
            let num_leaves_log2 =
                poly_size_log2 + lde_factor.trailing_zeros() as usize - values_per_leaf_log2;
            assert!(
                self.cap_size.trailing_zeros() as usize <= num_leaves_log2,
                "{what}: cap size {} exceeds the tree's 2^{num_leaves_log2} leaves \
                 (2^{poly_size_log2} polynomial, LDE factor {lde_factor}, \
                 2^{values_per_leaf_log2} values per leaf)",
                self.cap_size
            );
        };
        check_tree(
            "base oracles",
            message_size_log2,
            schedule.base_lde_factor(),
            schedule.base_folding_log2(),
        );

        let mut poly_size_log2 = message_size_log2;
        let fold_steps = schedule.fold_steps();
        for (round, fold_log2) in fold_steps.iter().enumerate() {
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
                // the oracle committed after this round is intermediate oracle
                // `round`: its leaves hold one fold of ITS round worth of values
                let oracle = &schedule.internal_rounds[round];
                check_tree(
                    &format!("WHIR round {round} intermediate oracle"),
                    poly_size_log2,
                    oracle.lde_factor(),
                    oracle.folding_log2,
                );
            }
        }
        assert!(
            poly_size_log2 >= 1,
            "the WHIR schedule folds the polynomial away completely"
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
            let depth = trace_len_log_2 + self.base_lde_factor_log2() - cap_depth_cut;
            let num_queries = self.base_round.num_queries;
            whir_sumcheck_terms += num_queries;
            let cost = cost_model.single_merkle_tree_depth_cost() * depth * num_queries;
            total_cost += cost;
        }

        let mut poly_size = trace_len_log_2 - self.base_folding_log2();

        for round in self.internal_rounds.iter() {
            let num_queries = round.num_queries;
            whir_sumcheck_terms += num_queries;
            let rate = round.lde_factor_log2;
            if poly_size + rate < cap_depth_cut {
                return usize::MAX;
            }
            let depth = poly_size + rate - cap_depth_cut;
            let cost = cost_model.single_merkle_tree_depth_cost() * depth * num_queries;
            total_cost = total_cost.saturating_add(cost);
            // and folding
            let fold_by = round.folding_log2;
            let cost = num_queries
                .saturating_mul(cost_model.whir_leaf_hashing_and_folding_cost(fold_by as u32));
            total_cost = total_cost.saturating_add(cost);
            poly_size -= fold_by;
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
    _sumcheck_explicit_output_size_log_2: usize,
    _security_bits: u32,
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

    let base_rate = lde_factor.trailing_zeros();
    let num_base_queries = {
        let proximity_testing_bits = whir_target_security_bits - first_round_pow_bits;
        proximity_testing_mode
            .num_queries_for_rate_and_bits_of_security(proximity_testing_bits, base_rate)
    };
    let whir_schedule = WhirSchedule {
        cap_size,
        base_round: WhirBaseRoundSchedule {
            lde_factor_log2: base_rate as usize,
            // in all our circuits base oracles are relatively large, and packing multiple leafs
            // in them is not obviously beneficial. So one can quickly fold by 2 and move from individual proximity checks
            // to batched one, and then try to using `1 << whir_average_folding_rate_log_2` elements per leaf
            physical_packing_log2: 0,
            fold_log2: 1,
            batching_pow_bits: None,
            folding_pow_bits: 0,
            num_queries: num_base_queries as usize,
            queries_pow_bits: first_round_pow_bits,
        },
        internal_rounds: vec![],
        merkle_multiproofs: false,
    };

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
    _min_rate_log_2: usize,
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
                    .internal_rounds
                    .last()
                    .map(|r| r.lde_factor_log2)
                    .unwrap_or(path.base_lde_factor_log2());
                if current_rate + whir_poly_size_log_2 < path.cap_size.trailing_zeros() as usize {
                    continue;
                }

                let mut new_path = path.clone();
                new_path.internal_rounds.push(WhirInternalRound {
                    lde_factor_log2: rate_to_use,
                    folding_log2: fold_by,
                    num_queries: min_queries as usize,
                    queries_pow_bits: pow_bits,
                    folding_pow_bits: 0,
                    num_ood_samples: 1,
                    ood_pow_bits: 0,
                });

                whir_folding_step(
                    candidates,
                    trace_len_log_2,
                    max_lde_size_log_2,
                    max_pow_bits,
                    min_pow_bits,
                    _min_rate_log_2,
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

// LEGACY-COMPAT (delete once every tracked proof / config fixture has been
// regenerated with the refactored layout): the pre-refactor serialized
// `ProverConfig` carried `lde_factor`, `base_oracles_values_per_leaf` and
// `pack_log2` as its own fields (now derived from the schedule). The decoder
// accepts both layouts; a legacy `pack_log2` is re-applied to the (legacy,
// unpacked-decoded) schedule, and the legacy LDE factor / leaf size are
// asserted against it.
mod legacy_compat {
    use super::*;

    #[derive(serde::Deserialize)]
    pub(crate) struct ProverConfigRepr {
        trace_len_log2: usize,
        cap_size: usize,
        sumcheck_explicit_output_size_log_2: usize,
        security_level: SecurityLevel,
        whir_schedule: WhirSchedule,
        #[serde(default)]
        same_size_sumcheck_schedule: Vec<SumcheckStep>,
        #[serde(default)]
        dimension_reducing_sumcheck_schedule: BTreeMap<usize, Vec<SumcheckStep>>,
        commitment_mode: CommitmentMode,
        // legacy fields
        #[serde(default)]
        lde_factor: Option<usize>,
        #[serde(default)]
        base_oracles_values_per_leaf: Option<usize>,
        #[serde(default)]
        pack_log2: Option<usize>,
    }

    impl From<ProverConfigRepr> for ProverConfig {
        fn from(repr: ProverConfigRepr) -> Self {
            let mut whir_schedule = repr.whir_schedule;
            if let Some(pack_log2) = repr.pack_log2 {
                let schedule_pack_log2 = &mut whir_schedule.base_round.physical_packing_log2;
                assert!(
                    *schedule_pack_log2 == 0 || *schedule_pack_log2 == pack_log2,
                    "legacy config pack_log2 {pack_log2} contradicts the schedule's"
                );
                *schedule_pack_log2 = pack_log2;
            }
            if let Some(lde_factor) = repr.lde_factor {
                assert_eq!(
                    lde_factor,
                    whir_schedule.base_lde_factor(),
                    "legacy config lde_factor contradicts the schedule's"
                );
            }
            if let Some(values_per_leaf) = repr.base_oracles_values_per_leaf {
                assert_eq!(
                    values_per_leaf,
                    whir_schedule.base_values_per_leaf(),
                    "legacy config base_oracles_values_per_leaf contradicts the schedule's"
                );
            }
            Self {
                trace_len_log2: repr.trace_len_log2,
                cap_size: repr.cap_size,
                sumcheck_explicit_output_size_log_2: repr.sumcheck_explicit_output_size_log_2,
                security_level: repr.security_level,
                whir_schedule,
                same_size_sumcheck_schedule: repr.same_size_sumcheck_schedule,
                dimension_reducing_sumcheck_schedule: repr.dimension_reducing_sumcheck_schedule,
                commitment_mode: repr.commitment_mode,
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
        for log in [20usize, 21, 22, 23, 24] {
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
        config
            .whir_schedule
            .internal_rounds
            .push(WhirInternalRound {
                lde_factor_log2: 19,
                folding_log2: 2,
                num_queries: 5,
                queries_pow_bits: 21,
                folding_pow_bits: 0,
                num_ood_samples: 1,
                ood_pow_bits: 0,
            });
        config.validate_for_whir_message_size(23);
    }

    #[test]
    fn legacy_config_json_decodes_with_its_packing() {
        // the pre-refactor serialized layout of a PACKED config: the packing
        // lived on the config, the schedule was six flat arrays
        let json = r#"{"trace_len_log2": 20, "lde_factor": 2, "cap_size": 16, "base_oracles_values_per_leaf": 2,
            "sumcheck_explicit_output_size_log_2": 4, "security_level": "Sec100",
            "whir_schedule": {"base_lde_factor": 2, "cap_size": 16, "whir_steps_schedule": [1, 5, 5, 5, 4, 3],
                "whir_queries_schedule": [89, 23, 10, 7, 5, 5], "whir_steps_lde_factors": [16, 512, 16384, 524288, 524288],
                "whir_pow_schedule": [26, 24, 25, 19, 21, 21]},
            "same_size_sumcheck_schedule": [], "dimension_reducing_sumcheck_schedule": {},
            "pack_log2": 4, "commitment_mode": "SeparateMemoryAndWitness"}"#;
        let decoded: ProverConfig = serde_json::from_str(json).unwrap();
        assert_eq!(decoded.pack_log2(), 4);
        assert_eq!(decoded.lde_factor(), 2);
        assert_eq!(decoded.base_oracles_values_per_leaf(), 2);
        assert_eq!(decoded.whir_message_size_log2(), 24);
        decoded.validate_for_whir_message_size(24);
        // the current layout round-trips
        let reencoded = serde_json::to_string(&decoded).unwrap();
        let again: ProverConfig = serde_json::from_str(&reencoded).unwrap();
        assert_eq!(again, decoded);
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

#[cfg(test)]
mod geometry_validation_tests {
    use super::example_configs::{
        config_for_security_level_under_pessimistic_conjecture,
        packed_config_for_security_level_under_pessimistic_conjecture,
    };
    use crate::definitions::SecurityLevel;

    #[test]
    fn example_configs_pass_for_every_storage_policy() {
        // Unpacked and packed family shapes (cap 16 over an LDE factor of 2 — the
        // cap lives inside the cosets); the validation has no cap/LDE relation.
        for trace_len_log2 in [20usize, 22, 23, 24] {
            let config = config_for_security_level_under_pessimistic_conjecture(
                trace_len_log2,
                SecurityLevel::Sec100,
            );
            assert!(config.cap_size > config.lde_factor());
            config.validate_for_whir_message_size(config.whir_message_size_log2());
        }
        let packed = packed_config_for_security_level_under_pessimistic_conjecture(
            20,
            4,
            SecurityLevel::Sec100,
        );
        packed.validate_for_whir_message_size(packed.whir_message_size_log2());
    }

    #[test]
    #[should_panic(expected = "cap size")]
    fn cap_larger_than_base_tree_is_rejected() {
        let mut config =
            config_for_security_level_under_pessimistic_conjecture(20, SecurityLevel::Sec100);
        // 2^20 message x LDE 2 / 2 values per leaf = 2^20 leaves
        config.cap_size = 1 << 21;
        config.whir_schedule.cap_size = 1 << 21;
        config.validate_for_whir_message_size(config.whir_message_size_log2());
    }

    #[test]
    #[should_panic(expected = "intermediate oracle")]
    fn cap_larger_than_an_intermediate_tree_is_rejected() {
        let mut config =
            config_for_security_level_under_pessimistic_conjecture(20, SecurityLevel::Sec100);
        // shrink the first intermediate oracle's LDE so its tree has fewer leaves
        // than the cap: poly 2^(20 - fold0), LDE 2, leaves / 2^fold1
        config.whir_schedule.internal_rounds[0].lde_factor_log2 = 1;
        let fold0 = config.whir_schedule.base_folding_log2();
        let fold1 = config.whir_schedule.internal_rounds[0].folding_log2;
        let leaves_log2 = 20 - fold0 + 1 - fold1;
        config.cap_size = 1 << (leaves_log2 + 1);
        config.whir_schedule.cap_size = config.cap_size;
        config.validate_for_whir_message_size(config.whir_message_size_log2());
    }
}
