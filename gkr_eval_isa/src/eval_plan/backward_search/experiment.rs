use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::time::{Duration, Instant};

use cs::gkr_compiler::dag_ir::{BwdRegime, DagLayer, ExprId};

use crate::bwd::distill::DistilledLayer;
use crate::bwd::plan::{BwdOccurrencePlan, PlanAction, plan_entries_fnv};
use crate::bwd::trace::{BwdEvent, positioned_physical_traffic_events};
use crate::bwd::trace::{BwdFingerprint, BwdServeKind};
use crate::eval_plan::PlanError;
use crate::eval_plan::backward::{BackwardEvaluationError, CompiledBackwardEvaluation};
use crate::eval_plan::search_driver::{
    SearchAdapter, SearchDriverConfig, SearchDriverError, SearchDriverOutcome, StableRng,
    run_search_driver,
};
use crate::fwd::stats::OP_MOV;

use super::genome::{
    BackwardAdapter, BackwardAdapterTelemetry, BackwardAdapterTelemetrySnapshot, BackwardGenome,
    BackwardSearchArm, decode_fragment_order, paging_seed,
};
use super::pager::{
    ExactPagingPlan, PagerOutcome, PagingAction, PagingObjective, PagingTelemetry,
    solve_exact_paging,
};
use super::problem::{
    BackwardSearchProblem, ProblemClassification, StableFragmentKey, build_backward_search_problem,
    build_problem_for_order,
};
use super::replay::{PagingCertificate, reprice_source_read};
use super::{
    BackwardScore, BackwardSearchError, CertifiedBackwardCandidate, MAX_PAGER_STATES, RoundProfile,
    ScoredAcceptedBackwardCandidate, SourceCost, StaticMaterialization, compile_and_certify_paging,
    compile_and_score_occurrence_plan,
};

const SEARCH_POPULATION: usize = 32;
const SEARCH_BATCH: usize = 16;
const SEARCH_SEED: u64 = 0x706c_616e_332d_7437;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExperimentArm {
    Uncached,
    Incumbent,
    ExactConstructive,
    OrderSearch,
    CacheSearch,
    JointSearch,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArmClassification {
    Searched,
    Trivial {
        reason: &'static str,
    },
    Infeasible {
        reason: String,
    },
    SolverCapped {
        cap: usize,
        demand_position: usize,
        peak_states: usize,
    },
    UnavailableIncumbent,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PagerRunTelemetry {
    pub calls: usize,
    pub generated_states: u64,
    pub merged_states: u64,
    pub peak_states: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstanceKey {
    pub fixture: String,
    pub layer_index: usize,
    pub regime: BwdRegime,
    pub budget_cells: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CertificateMetrics {
    pub actions_consumed: u128,
    pub diverged: u128,
    pub refused_retains: u128,
    pub predicted_source_reads: u128,
    pub realized_source_reads: u128,
    pub read_count_mismatches: u128,
    pub read_cost_mismatches: u128,
}

impl CertificateMetrics {
    fn failures(self) -> u128 {
        self.diverged
            + self.refused_retains
            + self.read_count_mismatches
            + self.read_cost_mismatches
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ArmMeasurements {
    pub source_reads: u128,
    pub plain_read_bytes: u128,
    pub lazy_read_bytes: u128,
    pub materialized_read_bytes: u128,
    pub materialization_write_bytes: u128,
    pub bf_add: u128,
    pub bf_mul: u128,
    pub mixed_add: u128,
    pub mixed_mul: u128,
    pub ext_add: u128,
    pub ext_mul: u128,
    pub primitive_equivalents: u128,
    pub arithmetic_ops: u128,
    pub instructions: u128,
    pub encoded_lanes: u128,
    pub moves: u128,
    pub relocations: u128,
    pub peak_lanes: u128,
    pub peak_cells: u128,
    pub certificate: Option<CertificateMetrics>,
}

impl ArmMeasurements {
    pub fn dram_bytes(self) -> u128 {
        self.plain_read_bytes
            + self.lazy_read_bytes
            + self.materialized_read_bytes
            + self.materialization_write_bytes
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SignedDelta {
    pub negative: bool,
    pub magnitude: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Percentage {
    pub numerator: SignedDelta,
    pub denominator: u128,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DeltaPercentage {
    pub delta: SignedDelta,
    pub percentage: Option<Percentage>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MetricDeltas {
    pub dram_bytes: DeltaPercentage,
    pub primitive_equivalents: DeltaPercentage,
    pub arithmetic_ops: DeltaPercentage,
    pub instructions: DeltaPercentage,
    pub encoded_lanes: DeltaPercentage,
    pub moves: DeltaPercentage,
    pub relocations: DeltaPercentage,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ArmComparisons {
    pub uncached: Option<MetricDeltas>,
    pub incumbent: Option<MetricDeltas>,
    pub arm1: Option<MetricDeltas>,
    pub arm2: Option<MetricDeltas>,
}

#[derive(Clone, Debug)]
pub struct ArmResult {
    pub arm: ExperimentArm,
    pub classification: ArmClassification,
    pub score: Option<BackwardScore>,
    pub order: Option<Vec<usize>>,
    pub plan: Option<BwdOccurrencePlan>,
    pub first_winning_ordinal: Option<usize>,
    pub improvement_ordinals: Vec<usize>,
    pub evaluations: usize,
    pub pager: PagerRunTelemetry,
    pub compile_time: Duration,
    pub wall_time: Duration,
    pub winning_tier: Option<usize>,
    pub measurements: Option<ArmMeasurements>,
    pub comparisons: ArmComparisons,
}

#[derive(Clone, Debug)]
pub struct InstanceMetrics {
    pub key: InstanceKey,
    pub trace_len: usize,
    pub round_profiles: Vec<RoundProfile>,
    pub classification: ArmClassification,
    pub reason: Option<String>,
    pub fragment_count: Option<u128>,
    pub reusable_leaf_count: Option<u128>,
    pub demand_count: Option<u128>,
    pub materialization_bindings: Option<u128>,
    pub materialization: Option<StaticMaterialization>,
    pub all_ext_boundary: Option<u8>,
    pub stream_reductions: Option<bool>,
    pub fixture: String,
    pub layer_index: usize,
    pub budget_cells: usize,
    pub uncached: ArmResult,
    pub incumbent: ArmResult,
    pub arm1: ArmResult,
    pub arm2: ArmResult,
    pub arm3: ArmResult,
    pub arm4: ArmResult,
}

pub type InstanceResult = InstanceMetrics;

#[derive(Clone, Debug)]
pub struct AcceptedIncumbent {
    pub order: Vec<usize>,
    pub plan: BwdOccurrencePlan,
}

impl InstanceResult {
    /// Stable report digest. Timings are intentionally omitted because they are
    /// observational telemetry, not deterministic search output.
    pub fn deterministic_digest(&self) -> u64 {
        let mut digest = 0xcbf2_9ce4_8422_2325;
        digest_usize(&mut digest, self.fixture.len());
        digest_bytes(&mut digest, self.fixture.as_bytes());
        digest_usize(&mut digest, self.layer_index);
        digest_usize(&mut digest, self.budget_cells);
        digest_usize(&mut digest, self.trace_len);
        for arm in [
            &self.uncached,
            &self.incumbent,
            &self.arm1,
            &self.arm2,
            &self.arm3,
            &self.arm4,
        ] {
            digest_arm(&mut digest, arm);
        }
        digest
    }

    pub fn certificate_failures(&self) -> u128 {
        [
            &self.uncached,
            &self.incumbent,
            &self.arm1,
            &self.arm2,
            &self.arm3,
            &self.arm4,
        ]
        .into_iter()
        .filter_map(|arm| arm.measurements?.certificate)
        .map(CertificateMetrics::failures)
        .sum()
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BudgetCounts {
    pub total: u128,
    pub feasible: u128,
    pub trivial: u128,
    pub infeasible: u128,
    pub solver_capped: u128,
    pub matching_incumbent: u128,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ArmRollup {
    pub computed_instances: u128,
    pub covered_rows: u128,
    pub dram_bytes: u128,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReportRollup {
    pub corpus_instances: u128,
    pub corpus_rows: u128,
    pub uncached: ArmRollup,
    pub incumbent: ArmRollup,
    pub arm1: ArmRollup,
    pub arm2: ArmRollup,
    pub arm3: ArmRollup,
    pub arm4: ArmRollup,
}

#[derive(Clone, Debug)]
pub struct ExperimentReport {
    pub commit: String,
    pub instances: Vec<InstanceMetrics>,
    pub counts_by_budget: BTreeMap<usize, BudgetCounts>,
    pub equal_instance: ReportRollup,
    pub whole_pass: ReportRollup,
    pub incumbent_comparable: u128,
    pub paged_computed: u128,
}

impl Default for ExperimentReport {
    fn default() -> Self {
        Self {
            commit: exact_git_commit(),
            instances: Vec::new(),
            counts_by_budget: [2usize, 3, 4]
                .into_iter()
                .map(|budget| (budget, BudgetCounts::default()))
                .collect(),
            equal_instance: ReportRollup::default(),
            whole_pass: ReportRollup::default(),
            incumbent_comparable: 0,
            paged_computed: 0,
        }
    }
}

impl ExperimentReport {
    pub fn from_instances(instances: Vec<InstanceMetrics>) -> Self {
        let mut report = Self::default();
        report.instances = instances;
        report.recompute();
        report
    }

    pub fn push(&mut self, instance: InstanceMetrics) {
        self.instances.push(instance);
        self.recompute();
    }

    fn recompute(&mut self) {
        self.instances
            .sort_by(|lhs, rhs| instance_sort_key(lhs).cmp(&instance_sort_key(rhs)));
        self.counts_by_budget = [2usize, 3, 4]
            .into_iter()
            .map(|budget| (budget, BudgetCounts::default()))
            .collect();
        for instance in &self.instances {
            let counts = self
                .counts_by_budget
                .entry(instance.key.budget_cells)
                .or_default();
            counts.total += 1;
            match instance.classification {
                ArmClassification::Searched => counts.feasible += 1,
                ArmClassification::Trivial { .. } => counts.trivial += 1,
                ArmClassification::Infeasible { .. } => counts.infeasible += 1,
                ArmClassification::SolverCapped { .. } => counts.solver_capped += 1,
                ArmClassification::UnavailableIncumbent => {
                    unreachable!("instance classification is never incumbent availability")
                }
            }
            if instance.key.budget_cells == 4 && instance.incumbent.measurements.is_some() {
                counts.matching_incumbent += 1;
            }
        }
        self.incumbent_comparable = self
            .instances
            .iter()
            .filter(|instance| {
                instance.key.budget_cells == 4
                    && instance.incumbent.measurements.is_some()
                    && instance.arm1.measurements.is_some()
            })
            .count() as u128;
        self.paged_computed = self
            .instances
            .iter()
            .filter(|instance| instance.arm1.measurements.is_some())
            .count() as u128;
        self.equal_instance = equal_instance_rollup(&self.instances);
        self.whole_pass = whole_pass_rollup(&self.instances);
    }
}

fn exact_git_commit() -> String {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("gkr_eval_isa has a workspace parent");
    std::process::Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(repo)
        .output()
        .ok()
        .filter(|output| output.status.success())
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .map(|commit| commit.trim().to_owned())
        .filter(|commit| !commit.is_empty())
        .unwrap_or_else(|| "unavailable (git rev-parse HEAD failed)".to_owned())
}

fn instance_sort_key(instance: &InstanceMetrics) -> (&str, usize, u8, usize) {
    (
        &instance.key.fixture,
        instance.key.layer_index,
        match instance.key.regime {
            BwdRegime::R0 => 0,
            BwdRegime::Ext => 1,
        },
        instance.key.budget_cells,
    )
}

fn arm_dram(arm: &ArmResult) -> Option<u128> {
    arm.measurements.map(ArmMeasurements::dram_bytes)
}

fn instance_rows(instance: &InstanceMetrics) -> u128 {
    instance
        .round_profiles
        .iter()
        .map(|profile| profile.rows as u128)
        .try_fold(0u128, u128::checked_add)
        .expect("instance row total fits u128")
}

fn arm_rollup(
    instances: &[InstanceMetrics],
    arm: ExperimentArm,
    equal_instance: bool,
) -> ArmRollup {
    let mut rollup = ArmRollup::default();
    for instance in instances {
        let Some(dram_bytes) = arm_dram(arm_by_kind(instance, arm)) else {
            continue;
        };
        rollup.computed_instances = rollup
            .computed_instances
            .checked_add(1)
            .expect("computed instance count fits u128");
        rollup.covered_rows = rollup
            .covered_rows
            .checked_add(instance_rows(instance))
            .expect("covered row count fits u128");
        rollup.dram_bytes = rollup
            .dram_bytes
            .checked_add(dram_bytes)
            .expect("whole-pass metric total fits u128");
    }
    if equal_instance && rollup.computed_instances != 0 {
        rollup.dram_bytes /= rollup.computed_instances;
    }
    rollup
}

fn report_rollup(instances: &[InstanceMetrics], equal_instance: bool) -> ReportRollup {
    ReportRollup {
        corpus_instances: instances.len() as u128,
        corpus_rows: instances
            .iter()
            .map(instance_rows)
            .try_fold(0u128, u128::checked_add)
            .expect("corpus row total fits u128"),
        uncached: arm_rollup(instances, ExperimentArm::Uncached, equal_instance),
        incumbent: arm_rollup(instances, ExperimentArm::Incumbent, equal_instance),
        arm1: arm_rollup(instances, ExperimentArm::ExactConstructive, equal_instance),
        arm2: arm_rollup(instances, ExperimentArm::OrderSearch, equal_instance),
        arm3: arm_rollup(instances, ExperimentArm::CacheSearch, equal_instance),
        arm4: arm_rollup(instances, ExperimentArm::JointSearch, equal_instance),
    }
}

fn equal_instance_rollup(instances: &[InstanceMetrics]) -> ReportRollup {
    report_rollup(instances, true)
}

fn whole_pass_rollup(instances: &[InstanceMetrics]) -> ReportRollup {
    // Source costs and writes are already scaled by each instance's round
    // profiles. Preserve coverage without multiplying whole-pass totals again.
    report_rollup(instances, false)
}

pub fn render_markdown(report: &ExperimentReport) -> String {
    use std::fmt::Write;

    let mut out = String::new();
    writeln!(out, "# Plan 3 backward paging search experiment\n").unwrap();
    writeln!(out, "## Run metadata\n").unwrap();
    writeln!(out, "- Commit: `{}`", report.commit).unwrap();
    writeln!(out, "- Instances: {}", report.instances.len()).unwrap();
    writeln!(out, "- Budgets: 2, 3, and 4 cells").unwrap();
    writeln!(out, "- Regimes: R0 and Ext\n").unwrap();

    writeln!(out, "## Per-budget denominators\n").unwrap();
    writeln!(
        out,
        "| cells | total | feasible | trivial | infeasible | solver-capped | matching incumbent |"
    )
    .unwrap();
    writeln!(out, "|---:|---:|---:|---:|---:|---:|---:|").unwrap();
    for (&budget, counts) in &report.counts_by_budget {
        writeln!(
            out,
            "| {budget} | {} | {} | {} | {} | {} | {} |",
            counts.total,
            counts.feasible,
            counts.trivial,
            counts.infeasible,
            counts.solver_capped,
            counts.matching_incumbent
        )
        .unwrap();
    }
    writeln!(out).unwrap();

    writeln!(out, "## Materialization and reduction-mode census\n").unwrap();
    let mut census = BTreeMap::<(Option<u128>, Option<u8>, Option<bool>), u128>::new();
    for instance in &report.instances {
        *census
            .entry((
                instance.materialization_bindings,
                instance.all_ext_boundary,
                instance.stream_reductions,
            ))
            .or_default() += 1;
    }
    writeln!(
        out,
        "| bindings | all-Ext boundary | stream reductions | instances |"
    )
    .unwrap();
    writeln!(out, "|---:|---:|:---:|---:|").unwrap();
    for ((bindings, boundary, reductions), count) in census {
        writeln!(
            out,
            "| {} | {} | {} | {count} |",
            optional(bindings),
            optional(boundary),
            reductions.map_or("unavailable", |value| if value { "yes" } else { "no" })
        )
        .unwrap();
    }
    writeln!(out).unwrap();
    writeln!(out, "Materialization writes are a CPU model overlay; read traffic is certified against the emitted program.\n").unwrap();

    writeln!(out, "## Savings\n").unwrap();
    writeln!(out, "### Equal-instance results\n").unwrap();
    render_rollup(
        &mut out,
        report.equal_instance,
        "integer mean whole-pass DRAM bytes",
    );

    writeln!(out, "## Whole-pass row/round-weighted results\n").unwrap();
    writeln!(
        out,
        "Actual logical row evaluations: {}.\n",
        report.whole_pass.corpus_rows
    )
    .unwrap();
    render_rollup(&mut out, report.whole_pass, "whole-pass DRAM bytes");

    writeln!(out, "## Arm2−Arm1 order value\n").unwrap();
    render_pair_summary(
        &mut out,
        report,
        ExperimentArm::OrderSearch,
        ExperimentArm::ExactConstructive,
    );

    writeln!(out, "## Arm3−Arm1 cache-genome secondary value\n").unwrap();
    writeln!(out, "Primary DRAM delta: **definitionally zero**. Secondary metrics retain only computed Arm3/Arm1 pairs.\n").unwrap();
    render_pair_summary(
        &mut out,
        report,
        ExperimentArm::CacheSearch,
        ExperimentArm::ExactConstructive,
    );

    writeln!(out, "## Arm4−Arm2 joint value\n").unwrap();
    render_pair_summary(
        &mut out,
        report,
        ExperimentArm::JointSearch,
        ExperimentArm::OrderSearch,
    );

    writeln!(out, "## U/I comparisons with explicit denominators\n").unwrap();
    writeln!(
        out,
        "- Uncached-versus-paged computed denominator: {}.",
        report.paged_computed
    )
    .unwrap();
    writeln!(
        out,
        "- Incumbent-versus-paged comparable denominator: {}.",
        report.incumbent_comparable
    )
    .unwrap();
    writeln!(out, "- Unavailable incumbents, infeasible/trivial instances, solver-capped arms, and uncomputed metrics are excluded from their percentage denominators. Zero-valued references do not produce a percentage.\n").unwrap();

    writeln!(out, "### Arm1−U uncached comparison\n").unwrap();
    render_pair_summary(
        &mut out,
        report,
        ExperimentArm::ExactConstructive,
        ExperimentArm::Uncached,
    );

    writeln!(out, "### Arm1−I incumbent comparison\n").unwrap();
    render_pair_summary(
        &mut out,
        report,
        ExperimentArm::ExactConstructive,
        ExperimentArm::Incumbent,
    );

    writeln!(
        out,
        "## Solver, placement, certificate, timing, and state telemetry\n"
    )
    .unwrap();
    writeln!(out, "| instance | arm | class/reason | fragments | reusable leaves | demands | source reads | plain/lazy/materialized/write bytes | BF add/mul | mixed add/mul | Ext add/mul | primitive eq | arithmetic | instructions/lanes | pager states (generated/merged/peak) | moves/relocations | peak lanes/cells | certificate failures | tier/evaluations | first winner | improvements | compile ns | wall ns |").unwrap();
    writeln!(out, "|:---|:---|:---|---:|---:|---:|---:|:---|:---|:---|:---|---:|---:|:---|:---|:---|:---|---:|:---|---:|:---|---:|---:|").unwrap();
    for instance in &report.instances {
        for arm in instance_arms(instance) {
            let metrics = arm.measurements.unwrap_or_default();
            let certificate_failures = metrics.certificate.map_or_else(
                || "unavailable".to_owned(),
                |certificate| certificate.failures().to_string(),
            );
            writeln!(
                out,
                "| {} L{} {:?} c{} | {:?} | {} | {} | {} | {} | {} | {}/{}/{}/{} | {}/{} | {}/{} | {}/{} | {} | {} | {}/{} | {}/{}/{} | {}/{} | {}/{} | {} | {}/{} | {} | {:?} | {} | {} |",
                instance.key.fixture,
                instance.key.layer_index,
                instance.key.regime,
                instance.key.budget_cells,
                arm.arm,
                classification_with_reason(&arm.classification),
                optional(instance.fragment_count),
                optional(instance.reusable_leaf_count),
                optional(instance.demand_count),
                metrics.source_reads,
                metrics.plain_read_bytes,
                metrics.lazy_read_bytes,
                metrics.materialized_read_bytes,
                metrics.materialization_write_bytes,
                metrics.bf_add,
                metrics.bf_mul,
                metrics.mixed_add,
                metrics.mixed_mul,
                metrics.ext_add,
                metrics.ext_mul,
                metrics.primitive_equivalents,
                metrics.arithmetic_ops,
                metrics.instructions,
                metrics.encoded_lanes,
                arm.pager.generated_states,
                arm.pager.merged_states,
                arm.pager.peak_states,
                metrics.moves,
                metrics.relocations,
                metrics.peak_lanes,
                metrics.peak_cells,
                certificate_failures,
                arm.winning_tier.map_or(0, |value| value),
                arm.evaluations,
                arm.first_winning_ordinal.map_or(0, |value| value),
                arm.improvement_ordinals,
                arm.compile_time.as_nanos(),
                arm.wall_time.as_nanos(),
            )
            .unwrap();
        }
    }
    writeln!(out).unwrap();

    writeln!(out, "### Pager and certificate counters\n").unwrap();
    writeln!(out, "| instance | arm | pager calls | certificate actions | certificate reads (predicted/realized) | certificate counters (diverged/refused/read-count/read-cost) | certificate failures |").unwrap();
    writeln!(out, "|:---|:---|---:|---:|:---|:---|---:|").unwrap();
    for instance in &report.instances {
        for arm in instance_arms(instance) {
            let certificate = arm.measurements.and_then(|metrics| metrics.certificate);
            let (actions, reads, counters, failures) = certificate.map_or_else(
                || {
                    (
                        "unavailable".to_owned(),
                        "unavailable".to_owned(),
                        "unavailable".to_owned(),
                        "unavailable".to_owned(),
                    )
                },
                |certificate| {
                    (
                        certificate.actions_consumed.to_string(),
                        format!(
                            "{}/{}",
                            certificate.predicted_source_reads, certificate.realized_source_reads
                        ),
                        format!(
                            "{}/{}/{}/{}",
                            certificate.diverged,
                            certificate.refused_retains,
                            certificate.read_count_mismatches,
                            certificate.read_cost_mismatches
                        ),
                        certificate.failures().to_string(),
                    )
                },
            );
            writeln!(
                out,
                "| {} L{} {:?} c{} | {:?} | {} | {actions} | {reads} | {counters} | {failures} |",
                instance.key.fixture,
                instance.key.layer_index,
                instance.key.regime,
                instance.key.budget_cells,
                arm.arm,
                arm.pager.calls,
            )
            .unwrap();
        }
    }
    writeln!(out).unwrap();

    writeln!(out, "## Observations for RR\n").unwrap();
    writeln!(out, "This audit presents measured values and explicit denominators. It intentionally applies no automatic keep/remove recommendation threshold.").unwrap();
    out
}

fn optional<T: core::fmt::Display>(value: Option<T>) -> String {
    value.map_or_else(|| "unavailable".to_owned(), |value| value.to_string())
}

fn classification_with_reason(classification: &ArmClassification) -> String {
    match classification {
        ArmClassification::Searched => "feasible".to_owned(),
        ArmClassification::Trivial { reason } => format!("trivial: {reason}"),
        ArmClassification::Infeasible { reason } => format!("infeasible: {reason}"),
        ArmClassification::SolverCapped {
            cap,
            demand_position,
            peak_states,
        } => format!("solver-capped: cap {cap}, demand {demand_position}, peak {peak_states}"),
        ArmClassification::UnavailableIncumbent => "unavailable incumbent".to_owned(),
    }
}

fn render_rollup(out: &mut String, rollup: ReportRollup, value_label: &str) {
    use std::fmt::Write;
    writeln!(
        out,
        "Corpus coverage: {} instances and {} logical rows.\n",
        rollup.corpus_instances, rollup.corpus_rows
    )
    .unwrap();
    writeln!(
        out,
        "| arm | computed instances | covered logical rows | {value_label} |"
    )
    .unwrap();
    writeln!(out, "|:---|---:|---:|---:|").unwrap();
    for (label, arm) in [
        ("U", rollup.uncached),
        ("I", rollup.incumbent),
        ("Arm1", rollup.arm1),
        ("Arm2", rollup.arm2),
        ("Arm3", rollup.arm3),
        ("Arm4", rollup.arm4),
    ] {
        writeln!(
            out,
            "| {label} | {} | {} | {} |",
            arm.computed_instances, arm.covered_rows, arm.dram_bytes
        )
        .unwrap();
    }
    writeln!(out).unwrap();
}

fn render_pair_summary(
    out: &mut String,
    report: &ExperimentReport,
    value_arm: ExperimentArm,
    reference_arm: ExperimentArm,
) {
    use std::fmt::Write;
    let pairs = report
        .instances
        .iter()
        .filter_map(|instance| {
            let value = arm_by_kind(instance, value_arm).measurements?;
            let reference = arm_by_kind(instance, reference_arm).measurements?;
            Some((value.dram_bytes(), reference.dram_bytes()))
        })
        .collect::<Vec<_>>();
    writeln!(out, "Comparable instances: {}.", pairs.len()).unwrap();
    let comparable_rows = report
        .instances
        .iter()
        .filter(|instance| {
            arm_by_kind(instance, value_arm).measurements.is_some()
                && arm_by_kind(instance, reference_arm).measurements.is_some()
        })
        .map(instance_rows)
        .try_fold(0u128, u128::checked_add)
        .expect("comparable row total fits u128");
    writeln!(out, "Comparable logical rows: {comparable_rows}.").unwrap();
    writeln!(
        out,
        "| metric | arm total | reference total | raw delta | percentage |"
    )
    .unwrap();
    writeln!(out, "|:---|---:|---:|---:|:---|").unwrap();
    let measurements = report
        .instances
        .iter()
        .filter_map(|instance| {
            Some((
                arm_by_kind(instance, value_arm).measurements?,
                arm_by_kind(instance, reference_arm).measurements?,
            ))
        })
        .collect::<Vec<_>>();
    let metric = |measurement: ArmMeasurements| {
        [
            measurement.dram_bytes(),
            measurement.primitive_equivalents,
            measurement.arithmetic_ops,
            measurement.instructions,
            measurement.encoded_lanes,
            measurement.moves,
            measurement.relocations,
        ]
    };
    for (index, label) in [
        "DRAM bytes",
        "primitive equivalents",
        "arithmetic ops",
        "instructions",
        "encoded lanes",
        "moves",
        "relocations",
    ]
    .into_iter()
    .enumerate()
    {
        let value = measurements
            .iter()
            .map(|(value, _)| metric(*value)[index])
            .try_fold(0u128, u128::checked_add)
            .expect("report metric total fits u128");
        let reference = measurements
            .iter()
            .map(|(_, reference)| metric(*reference)[index])
            .try_fold(0u128, u128::checked_add)
            .expect("report metric total fits u128");
        let comparison = delta_percentage(value, reference);
        writeln!(
            out,
            "| {label} | {value} | {reference} | {} | {} |",
            format_delta(comparison.delta),
            format_percentage(comparison.percentage)
        )
        .unwrap();
    }
    writeln!(out).unwrap();
}

fn format_delta(delta: SignedDelta) -> String {
    if delta.negative && delta.magnitude != 0 {
        format!("-{}", delta.magnitude)
    } else {
        delta.magnitude.to_string()
    }
}

fn format_percentage(percentage: Option<Percentage>) -> String {
    let Some(percentage) = percentage else {
        return "percentage unavailable: zero or excluded denominator".to_owned();
    };
    let Some(basis_points) = percentage
        .numerator
        .magnitude
        .checked_mul(10_000)
        .map(|scaled| scaled / percentage.denominator)
    else {
        return format!(
            "exact ratio {}/{} (decimal overflow)",
            format_delta(percentage.numerator),
            percentage.denominator
        );
    };
    let sign = if percentage.numerator.negative && basis_points != 0 {
        "-"
    } else {
        ""
    };
    format!("{sign}{}.{:02}%", basis_points / 100, basis_points % 100)
}

fn instance_arms(instance: &InstanceMetrics) -> [&ArmResult; 6] {
    [
        &instance.uncached,
        &instance.incumbent,
        &instance.arm1,
        &instance.arm2,
        &instance.arm3,
        &instance.arm4,
    ]
}

fn arm_by_kind(instance: &InstanceMetrics, arm: ExperimentArm) -> &ArmResult {
    match arm {
        ExperimentArm::Uncached => &instance.uncached,
        ExperimentArm::Incumbent => &instance.incumbent,
        ExperimentArm::ExactConstructive => &instance.arm1,
        ExperimentArm::OrderSearch => &instance.arm2,
        ExperimentArm::CacheSearch => &instance.arm3,
        ExperimentArm::JointSearch => &instance.arm4,
    }
}

pub fn escalation_tiers(
    improved_seed_at_128: bool,
    late_winner_at_128: bool,
    improved_512_over_128: bool,
) -> Vec<usize> {
    let mut tiers = vec![128];
    if improved_seed_at_128 || late_winner_at_128 {
        tiers.push(512);
        if improved_512_over_128 {
            tiers.push(2048);
        }
    }
    tiers
}

enum EscalationStep<T, K> {
    Completed {
        value: T,
        score: K,
        first_winning_ordinal: usize,
    },
    Terminal(T),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct EscalationTelemetry {
    adapter: BackwardAdapterTelemetrySnapshot,
    wall_time: Duration,
}

impl EscalationTelemetry {
    fn merge(
        &mut self,
        next: BackwardAdapterTelemetrySnapshot,
        wall_time: Duration,
    ) -> Result<(), BackwardSearchError> {
        self.adapter.evaluation_attempts = self
            .adapter
            .evaluation_attempts
            .checked_add(next.evaluation_attempts)
            .ok_or(BackwardSearchError::CostOverflow)?;
        self.adapter.pager_calls = self
            .adapter
            .pager_calls
            .checked_add(next.pager_calls)
            .ok_or(BackwardSearchError::CostOverflow)?;
        self.adapter.pager_generated_states = self
            .adapter
            .pager_generated_states
            .checked_add(next.pager_generated_states)
            .ok_or(BackwardSearchError::CostOverflow)?;
        self.adapter.pager_merged_states = self
            .adapter
            .pager_merged_states
            .checked_add(next.pager_merged_states)
            .ok_or(BackwardSearchError::CostOverflow)?;
        self.adapter.pager_peak_states = self.adapter.pager_peak_states.max(next.pager_peak_states);
        self.adapter.compile_time = self
            .adapter
            .compile_time
            .checked_add(next.compile_time)
            .ok_or(BackwardSearchError::CostOverflow)?;
        self.wall_time = self
            .wall_time
            .checked_add(wall_time)
            .ok_or(BackwardSearchError::CostOverflow)?;
        Ok(())
    }
}

fn run_escalation_schedule<T, E, K: Copy + Ord>(
    seed_floor: K,
    mut run_tier: impl FnMut(usize) -> Result<EscalationStep<T, K>, E>,
) -> Result<T, E> {
    let (tier128, score128, first_winning_ordinal) = match run_tier(128)? {
        EscalationStep::Completed {
            value,
            score,
            first_winning_ordinal,
        } => (value, score, first_winning_ordinal),
        EscalationStep::Terminal(value) => return Ok(value),
    };
    let improved_seed = score128 < seed_floor;
    let late_winner = first_winning_ordinal >= 96;
    if !escalation_tiers(improved_seed, late_winner, false).contains(&512) {
        return Ok(tier128);
    }

    let (tier512, score512) = match run_tier(512)? {
        EscalationStep::Completed { value, score, .. } => (value, score),
        EscalationStep::Terminal(value) => return Ok(value),
    };
    let improved_512 = score512 < score128;
    if !escalation_tiers(improved_seed, late_winner, improved_512).contains(&2048) {
        return Ok(tier512);
    }

    Ok(match run_tier(2048)? {
        EscalationStep::Completed { value, .. } | EscalationStep::Terminal(value) => value,
    })
}

fn tier_search_config(evaluations: usize) -> SearchDriverConfig {
    SearchDriverConfig {
        population: SEARCH_POPULATION,
        evaluations,
        guided_evaluations: 0,
        score_batch: SEARCH_BATCH,
        seed: SEARCH_SEED,
    }
}

pub fn run_instance(
    fixture: &str,
    layer_index: usize,
    canonical: &DagLayer,
    d: &DistilledLayer,
    trace_len: usize,
    budget_cells: usize,
    incumbent: Option<&AcceptedIncumbent>,
) -> Result<InstanceResult, BackwardSearchError> {
    run_instance_with_pager_cap(
        fixture,
        layer_index,
        canonical,
        d,
        trace_len,
        budget_cells,
        incumbent,
        MAX_PAGER_STATES,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_instance_with_pager_cap(
    fixture: &str,
    layer_index: usize,
    canonical: &DagLayer,
    d: &DistilledLayer,
    trace_len: usize,
    budget_cells: usize,
    incumbent: Option<&AcceptedIncumbent>,
    pager_cap: usize,
) -> Result<InstanceResult, BackwardSearchError> {
    let (classification, problem) =
        build_backward_search_problem(canonical, d, trace_len, budget_cells)?;
    let Some(problem) = problem else {
        let ProblemClassification::Infeasible {
            false_floor,
            true_floor,
        } = classification
        else {
            unreachable!("only infeasible problems omit the built problem")
        };
        let reason = format!(
            "budget {budget_cells} is below both mode floors ({false_floor}, {true_floor})"
        );
        return Ok(classified_instance(
            fixture,
            layer_index,
            d.regime,
            trace_len,
            budget_cells,
            ArmClassification::Infeasible { reason },
        ));
    };

    let uncached = run_uncached_reference(d, &problem)?;
    let incumbent_result =
        run_incumbent_reference(canonical, d, trace_len, budget_cells, incumbent)?;
    if let ProblemClassification::Trivial { reason } = classification {
        let classification = ArmClassification::Trivial { reason };
        return Ok(finish_instance(InstanceResult {
            key: InstanceKey {
                fixture: fixture.to_owned(),
                layer_index,
                regime: d.regime,
                budget_cells,
            },
            trace_len,
            round_profiles: round_profiles(trace_len, d.regime),
            classification: classification.clone(),
            reason: classification_reason(&classification),
            fragment_count: Some(problem.fragment_domain.len() as u128),
            reusable_leaf_count: Some(problem.leaf_domain.len() as u128),
            demand_count: Some(problem.demands.len() as u128),
            materialization_bindings: Some(problem.materialization.bindings.len() as u128),
            materialization: Some(problem.materialization.clone()),
            all_ext_boundary: problem.materialization.all_ext_from,
            stream_reductions: Some(problem.stream_reductions),
            fixture: fixture.to_owned(),
            layer_index,
            budget_cells,
            uncached,
            incumbent: incumbent_result,
            arm1: classified_arm(ExperimentArm::ExactConstructive, classification.clone()),
            arm2: classified_arm(ExperimentArm::OrderSearch, classification.clone()),
            arm3: classified_arm(ExperimentArm::CacheSearch, classification.clone()),
            arm4: classified_arm(ExperimentArm::JointSearch, classification),
        }));
    }

    let arm1 = run_exact_constructive(d, &problem, pager_cap)?;
    let Some(arm1_score) = arm1.score else {
        let capped = arm1.classification.clone();
        return Ok(finish_instance(InstanceResult {
            key: InstanceKey {
                fixture: fixture.to_owned(),
                layer_index,
                regime: d.regime,
                budget_cells,
            },
            trace_len,
            round_profiles: round_profiles(trace_len, d.regime),
            classification: capped.clone(),
            reason: classification_reason(&capped),
            fragment_count: Some(problem.fragment_domain.len() as u128),
            reusable_leaf_count: Some(problem.leaf_domain.len() as u128),
            demand_count: Some(problem.demands.len() as u128),
            materialization_bindings: Some(problem.materialization.bindings.len() as u128),
            materialization: Some(problem.materialization.clone()),
            all_ext_boundary: problem.materialization.all_ext_from,
            stream_reductions: Some(problem.stream_reductions),
            fixture: fixture.to_owned(),
            layer_index,
            budget_cells,
            uncached,
            incumbent: incumbent_result,
            arm1,
            arm2: classified_arm(ExperimentArm::OrderSearch, capped.clone()),
            arm3: classified_arm(ExperimentArm::CacheSearch, capped.clone()),
            arm4: classified_arm(ExperimentArm::JointSearch, capped),
        }));
    };
    let arm1_plan = arm1
        .plan
        .as_ref()
        .expect("scored exact arm carries its certified plan");
    let exact = exact_from_plan(&problem, arm1_plan)?;

    let arm2_tier = run_staged_search(
        canonical,
        d,
        &problem,
        &exact,
        trace_len,
        BackwardSearchArm::OrderOnly,
        vec![BackwardGenome::constructive(&problem)],
        arm1_score,
        pager_cap,
    )?;
    let arm2 = match arm2_tier {
        StagedOutcome::Completed(tier) => tier.into_arm_result(ExperimentArm::OrderSearch),
        StagedOutcome::Capped(classification, telemetry, wall_time) => capped_arm(
            ExperimentArm::OrderSearch,
            classification,
            telemetry,
            wall_time,
        ),
    };

    let arm3 = run_staged_search(
        canonical,
        d,
        &problem,
        &exact,
        trace_len,
        BackwardSearchArm::CacheOnly,
        vec![paging_seed(&problem, &exact)?],
        arm1_score,
        pager_cap,
    )?
    .into_arm_result_or_capped(ExperimentArm::CacheSearch);

    let arm4 = if arm2.score.is_some() {
        let arm2_seed = joint_seed_from_arm2(canonical, d, &problem, trace_len, &arm2)?;
        run_staged_search(
            canonical,
            d,
            &problem,
            &exact,
            trace_len,
            BackwardSearchArm::Joint,
            vec![paging_seed(&problem, &exact)?, arm2_seed],
            min_score(arm1_score, arm2.score.expect("checked above")),
            pager_cap,
        )?
        .into_arm_result_or_capped(ExperimentArm::JointSearch)
    } else {
        classified_arm(ExperimentArm::JointSearch, arm2.classification.clone())
    };

    Ok(finish_instance(InstanceResult {
        key: InstanceKey {
            fixture: fixture.to_owned(),
            layer_index,
            regime: d.regime,
            budget_cells,
        },
        trace_len,
        round_profiles: round_profiles(trace_len, d.regime),
        classification: ArmClassification::Searched,
        reason: None,
        fragment_count: Some(problem.fragment_domain.len() as u128),
        reusable_leaf_count: Some(problem.leaf_domain.len() as u128),
        demand_count: Some(problem.demands.len() as u128),
        materialization_bindings: Some(problem.materialization.bindings.len() as u128),
        materialization: Some(problem.materialization.clone()),
        all_ext_boundary: problem.materialization.all_ext_from,
        stream_reductions: Some(problem.stream_reductions),
        fixture: fixture.to_owned(),
        layer_index,
        budget_cells,
        uncached,
        incumbent: incumbent_result,
        arm1,
        arm2,
        arm3,
        arm4,
    }))
}

fn run_uncached_reference(
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
) -> Result<ArmResult, BackwardSearchError> {
    let started = Instant::now();
    let paging = paging_from_actions(problem, vec![PagingAction::Bypass; problem.demands.len()])?;
    let telemetry = BackwardAdapterTelemetry::default();
    let compile_started = Instant::now();
    let candidate = compile_and_certify_paging(d, problem, &paging, 0);
    telemetry.record_compile_time(compile_started.elapsed());
    candidate_to_reference_result(
        ExperimentArm::Uncached,
        candidate?,
        problem.selected_order_indices.clone(),
        telemetry.snapshot(),
        started.elapsed(),
    )
}

fn run_incumbent_reference(
    canonical: &DagLayer,
    d: &DistilledLayer,
    trace_len: usize,
    budget_cells: usize,
    incumbent: Option<&AcceptedIncumbent>,
) -> Result<ArmResult, BackwardSearchError> {
    let Some(incumbent) = incumbent.filter(|_| budget_cells == 4) else {
        return Ok(classified_arm(
            ExperimentArm::Incumbent,
            ArmClassification::UnavailableIncumbent,
        ));
    };
    let started = Instant::now();
    validate_full_order(&incumbent.order, d.fragments.fragments.len())?;
    let problem = build_problem_for_order(
        canonical,
        d,
        &incumbent.order,
        trace_len,
        budget_cells,
        incumbent.plan.stream_reductions,
    )?;
    let candidate = match compile_and_score_occurrence_plan(
        d,
        &problem,
        &incumbent.plan,
        &incumbent.order,
        0,
    ) {
        Ok(candidate) => candidate,
        Err(error) if incumbent_backend_incompatibility(&error) => {
            let mut unavailable = classified_arm(
                ExperimentArm::Incumbent,
                ArmClassification::UnavailableIncumbent,
            );
            unavailable.wall_time = started.elapsed();
            return Ok(unavailable);
        }
        Err(error) => return Err(error),
    };
    accepted_candidate_to_reference_result(
        d,
        &problem,
        candidate,
        incumbent.order.clone(),
        started.elapsed(),
    )
}

fn incumbent_backend_incompatibility(error: &BackwardSearchError) -> bool {
    matches!(
        error,
        BackwardSearchError::PagingReplayRefused { .. }
            | BackwardSearchError::PlacementIntegrationFailure
            | BackwardSearchError::BackwardEvaluation(BackwardEvaluationError::Plan(
                PlanError::ReplayInfeasible
            ))
    )
}

fn run_exact_constructive(
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
    pager_cap: usize,
) -> Result<ArmResult, BackwardSearchError> {
    let telemetry = BackwardAdapterTelemetry::default();
    let started = Instant::now();
    telemetry.record_evaluation_attempts(1);
    telemetry.record_pager_call();
    let outcome = solve_exact_paging(&problem.demands, pager_cap)?;
    telemetry.record_pager_outcome(&outcome);
    let paging = match outcome {
        PagerOutcome::Solved(paging) => paging,
        PagerOutcome::SolverCapped {
            cap,
            demand_position,
            peak_states,
            ..
        } => {
            return Ok(capped_arm(
                ExperimentArm::ExactConstructive,
                ArmClassification::SolverCapped {
                    cap,
                    demand_position,
                    peak_states,
                },
                telemetry.snapshot(),
                started.elapsed(),
            ));
        }
    };
    let compile_started = Instant::now();
    let candidate = compile_and_certify_paging(d, problem, &paging, 0);
    telemetry.record_compile_time(compile_started.elapsed());
    candidate_to_reference_result(
        ExperimentArm::ExactConstructive,
        candidate?,
        problem.selected_order_indices.clone(),
        telemetry.snapshot(),
        started.elapsed(),
    )
}

struct SeededAdapter<'a> {
    inner: BackwardAdapter<'a>,
    seeds: Vec<BackwardGenome>,
}

impl SearchAdapter for SeededAdapter<'_> {
    type Genome = BackwardGenome;
    type Score = BackwardScore;
    type Evaluation = Option<CertifiedBackwardCandidate>;
    type Error = BackwardSearchError;
    type GuidedTrial = ();

    fn seeds(&self) -> Result<Vec<Self::Genome>, Self::Error> {
        Ok(self.seeds.clone())
    }

    fn seed_is_pinned(&self, seed_index: usize) -> bool {
        seed_index < self.seeds.len()
    }

    fn parent_eligible(&self, score: &Self::Score) -> bool {
        self.inner.parent_eligible(score)
    }

    fn population_fill_seed(
        &self,
        seeds: &[Self::Genome],
        seed_scores: &[Self::Score],
        population_len: usize,
    ) -> Self::Genome {
        self.inner
            .population_fill_seed(seeds, seed_scores, population_len)
    }

    fn mutate(&self, genome: &mut Self::Genome, rng: &mut StableRng) {
        self.inner.mutate(genome, rng);
    }

    fn score_batch(
        &self,
        candidates: &[(usize, Self::Genome)],
    ) -> Vec<Result<(Self::Score, Self::Evaluation), Self::Error>> {
        self.inner.score_batch(candidates)
    }

    fn guided_trials(
        &self,
        pre_guided_best: &Self::Genome,
        pre_guided_evaluation: &Self::Evaluation,
    ) -> Vec<Self::GuidedTrial> {
        self.inner
            .guided_trials(pre_guided_best, pre_guided_evaluation)
    }

    fn apply_guided_trial(
        &self,
        trial: &Self::GuidedTrial,
        live_best: &Self::Genome,
        live_evaluation: &Self::Evaluation,
    ) -> Self::Genome {
        self.inner
            .apply_guided_trial(trial, live_best, live_evaluation)
    }
}

struct TierOutcome {
    outcome: SearchDriverOutcome<BackwardGenome, BackwardScore, Option<CertifiedBackwardCandidate>>,
    order: Vec<usize>,
    telemetry: BackwardAdapterTelemetrySnapshot,
    wall_time: Duration,
    tier: usize,
}

enum StagedOutcome {
    Completed(TierOutcome),
    Capped(
        ArmClassification,
        BackwardAdapterTelemetrySnapshot,
        Duration,
    ),
}

impl StagedOutcome {
    fn observed_work(&self) -> (BackwardAdapterTelemetrySnapshot, Duration) {
        match self {
            Self::Completed(tier) => (tier.telemetry, tier.wall_time),
            Self::Capped(_, telemetry, wall_time) => (*telemetry, *wall_time),
        }
    }

    fn with_cumulative_telemetry(self, total: EscalationTelemetry) -> Self {
        match self {
            Self::Completed(mut tier) => {
                tier.telemetry = total.adapter;
                tier.wall_time = total.wall_time;
                Self::Completed(tier)
            }
            Self::Capped(classification, _, _) => {
                Self::Capped(classification, total.adapter, total.wall_time)
            }
        }
    }

    fn into_arm_result_or_capped(self, arm: ExperimentArm) -> ArmResult {
        match self {
            Self::Completed(tier) => tier.into_arm_result(arm),
            Self::Capped(classification, telemetry, wall_time) => {
                capped_arm(arm, classification, telemetry, wall_time)
            }
        }
    }
}

impl TierOutcome {
    fn into_arm_result(self, arm: ExperimentArm) -> ArmResult {
        let candidate = self
            .outcome
            .best_evaluation
            .expect("parent-eligible backward winner is certified");
        let measurements = certified_measurements(&candidate);
        ArmResult {
            arm,
            classification: ArmClassification::Searched,
            score: Some(self.outcome.best_score),
            order: Some(self.order),
            plan: Some(candidate.occurrence_plan),
            first_winning_ordinal: Some(self.outcome.best_ordinal),
            improvement_ordinals: self.outcome.improvement_ordinals,
            evaluations: self.telemetry.evaluation_attempts,
            pager: pager_telemetry(self.telemetry),
            compile_time: self.telemetry.compile_time,
            wall_time: self.wall_time,
            winning_tier: Some(self.tier),
            measurements: Some(measurements),
            comparisons: ArmComparisons::default(),
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn run_staged_search(
    canonical: &DagLayer,
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
    exact_seed: &ExactPagingPlan,
    trace_len: usize,
    arm: BackwardSearchArm,
    seeds: Vec<BackwardGenome>,
    seed_floor: BackwardScore,
    pager_cap: usize,
) -> Result<StagedOutcome, BackwardSearchError> {
    let mut cumulative = EscalationTelemetry::default();
    let selected = run_escalation_schedule(score_key(seed_floor), |evaluations| {
        let staged = run_tier(
            canonical,
            d,
            problem,
            exact_seed,
            trace_len,
            arm,
            &seeds,
            evaluations,
            pager_cap,
        )?;
        let (telemetry, wall_time) = staged.observed_work();
        cumulative.merge(telemetry, wall_time)?;
        Ok(match staged {
            StagedOutcome::Completed(tier) => {
                let score = score_key(tier.outcome.best_score);
                let first_winning_ordinal = tier.outcome.best_ordinal;
                EscalationStep::Completed {
                    value: StagedOutcome::Completed(tier),
                    score,
                    first_winning_ordinal,
                }
            }
            capped => EscalationStep::Terminal(capped),
        })
    })?;
    Ok(selected.with_cumulative_telemetry(cumulative))
}

#[allow(clippy::too_many_arguments)]
fn run_tier(
    canonical: &DagLayer,
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
    exact_seed: &ExactPagingPlan,
    trace_len: usize,
    arm: BackwardSearchArm,
    seeds: &[BackwardGenome],
    evaluations: usize,
    pager_cap: usize,
) -> Result<StagedOutcome, BackwardSearchError> {
    let telemetry = BackwardAdapterTelemetry::default();
    let adapter = SeededAdapter {
        inner: BackwardAdapter::new(canonical, d, problem, exact_seed, trace_len, arm)
            .with_pager_cap(pager_cap)
            .with_telemetry(&telemetry),
        seeds: seeds.to_vec(),
    };
    let started = Instant::now();
    let outcome = run_search_driver(&adapter, tier_search_config(evaluations));
    let wall_time = started.elapsed();
    let snapshot = telemetry.snapshot();
    match outcome {
        Ok(outcome) => {
            let order = order_from_genome(problem, &outcome.best_genome)?;
            Ok(StagedOutcome::Completed(TierOutcome {
                outcome,
                order,
                telemetry: snapshot,
                wall_time,
                tier: evaluations,
            }))
        }
        Err(SearchDriverError::Adapter(BackwardSearchError::ExactPagerSolverCapped {
            cap,
            demand_position,
            peak_states,
            ..
        })) => Ok(StagedOutcome::Capped(
            ArmClassification::SolverCapped {
                cap,
                demand_position,
                peak_states,
            },
            snapshot,
            wall_time,
        )),
        Err(SearchDriverError::Adapter(error)) => Err(error),
        Err(SearchDriverError::EmptySeeds) => Err(BackwardSearchError::SearchDriverFailure {
            reason: "empty backward search seeds",
        }),
        Err(SearchDriverError::InvalidConfig(reason)) => {
            Err(BackwardSearchError::SearchDriverFailure { reason })
        }
        Err(SearchDriverError::ScoreBatchLength { .. }) => {
            Err(BackwardSearchError::SearchDriverFailure {
                reason: "backward score batch length mismatch",
            })
        }
    }
}

fn joint_seed_from_arm2(
    canonical: &DagLayer,
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
    trace_len: usize,
    arm2: &ArmResult,
) -> Result<BackwardGenome, BackwardSearchError> {
    let order = arm2
        .order
        .as_ref()
        .expect("scored order arm carries an order");
    let plan = arm2.plan.as_ref().expect("scored order arm carries a plan");
    let ordered_problem = build_problem_for_order(
        canonical,
        d,
        order,
        trace_len,
        problem.budget_cells,
        problem.stream_reductions,
    )?;
    let paging = exact_from_plan(&ordered_problem, plan)?;
    paging_seed(&ordered_problem, &paging)
}

fn order_from_genome(
    problem: &BackwardSearchProblem,
    genome: &BackwardGenome,
) -> Result<Vec<usize>, BackwardSearchError> {
    let original_indices = problem
        .selected_order
        .iter()
        .cloned()
        .zip(problem.selected_order_indices.iter().copied())
        .collect::<BTreeMap<StableFragmentKey, usize>>();
    decode_fragment_order(problem, genome)?
        .into_iter()
        .map(|key| {
            original_indices
                .get(&key)
                .copied()
                .ok_or(BackwardSearchError::InvalidGenomeDomain {
                    gene: "winning fragment order",
                })
        })
        .collect()
}

fn candidate_to_reference_result(
    arm: ExperimentArm,
    candidate: CertifiedBackwardCandidate,
    order: Vec<usize>,
    telemetry: BackwardAdapterTelemetrySnapshot,
    wall_time: Duration,
) -> Result<ArmResult, BackwardSearchError> {
    let measurements = certified_measurements(&candidate);
    Ok(ArmResult {
        arm,
        classification: ArmClassification::Searched,
        score: Some(candidate.score),
        order: Some(order),
        plan: Some(candidate.occurrence_plan),
        first_winning_ordinal: Some(0),
        improvement_ordinals: Vec::new(),
        evaluations: 1,
        pager: pager_telemetry(telemetry),
        compile_time: telemetry.compile_time,
        wall_time,
        winning_tier: None,
        measurements: Some(measurements),
        comparisons: ArmComparisons::default(),
    })
}

fn accepted_candidate_to_reference_result(
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
    candidate: ScoredAcceptedBackwardCandidate,
    order: Vec<usize>,
    wall_time: Duration,
) -> Result<ArmResult, BackwardSearchError> {
    let measurements = accepted_measurements(d, problem, &candidate)?;
    Ok(ArmResult {
        arm: ExperimentArm::Incumbent,
        classification: ArmClassification::Searched,
        score: Some(candidate.score),
        order: Some(order),
        plan: Some(candidate.occurrence_plan),
        first_winning_ordinal: Some(0),
        improvement_ordinals: Vec::new(),
        evaluations: 1,
        pager: PagerRunTelemetry::default(),
        compile_time: candidate.compile_time,
        wall_time,
        winning_tier: None,
        measurements: Some(measurements),
        comparisons: ArmComparisons::default(),
    })
}

fn certified_measurements(candidate: &CertifiedBackwardCandidate) -> ArmMeasurements {
    measurements_from_compiled(
        &candidate.compiled,
        candidate.certificate.realized_read_cost,
        candidate.certificate.fixed_write_cost,
        candidate.certificate.realized_source_reads as u128,
        Some(&candidate.certificate),
    )
}

fn accepted_measurements(
    d: &DistilledLayer,
    problem: &BackwardSearchProblem,
    candidate: &ScoredAcceptedBackwardCandidate,
) -> Result<ArmMeasurements, BackwardSearchError> {
    let physical = positioned_physical_traffic_events(
        &d.layer,
        &candidate.compiled.compiled.program,
        &candidate.compiled.compiled.specials,
        &d.leaf_descs,
        &candidate.compiled.compiled.backings,
        &candidate.compiled.compiled.source_windows,
    )
    .ok_or(BackwardSearchError::PagingCertificateMismatch {
        observable: "incumbent physical traffic source mapping",
    })?;
    let read_cost = physical
        .iter()
        .try_fold(SourceCost::default(), |cost, positioned| {
            let BwdEvent::TrafficRead { value, cells } = positioned.event else {
                unreachable!("physical traffic scan emits only reads")
            };
            cost.checked_add(reprice_source_read(
                problem,
                d.leaf_descs.get(&value).copied(),
                cells
                    .try_into()
                    .map_err(|_| BackwardSearchError::CostOverflow)?,
            )?)
        })?;
    Ok(measurements_from_compiled(
        &candidate.compiled,
        read_cost,
        problem.materialization.fixed_writes,
        physical.len() as u128,
        None,
    ))
}

fn measurements_from_compiled(
    compiled: &CompiledBackwardEvaluation,
    read_cost: SourceCost,
    fixed_write_cost: SourceCost,
    source_reads: u128,
    certificate: Option<&PagingCertificate>,
) -> ArmMeasurements {
    let cost = read_cost
        .checked_add(fixed_write_cost)
        .expect("certified source costs already passed checked scoring");
    let certificate = certificate.map(|certificate| CertificateMetrics {
        actions_consumed: certificate.actions_consumed as u128,
        diverged: u128::from(certificate.diverged.is_some()),
        refused_retains: certificate.refused_retains as u128,
        predicted_source_reads: certificate.predicted_source_reads as u128,
        realized_source_reads: certificate.realized_source_reads as u128,
        read_count_mismatches: u128::from(
            certificate.predicted_source_reads != certificate.realized_source_reads,
        ),
        read_cost_mismatches: u128::from(
            certificate.predicted_read_cost != certificate.realized_read_cost,
        ),
    });
    let peak_lanes = compiled.binding_stats.max_live_lanes as u128;
    ArmMeasurements {
        source_reads,
        plain_read_bytes: cost.plain_read_bytes,
        lazy_read_bytes: cost.lazy_read_bytes,
        materialized_read_bytes: cost.materialized_read_bytes,
        materialization_write_bytes: cost.materialization_write_bytes,
        bf_add: cost.ops.bf_add,
        bf_mul: cost.ops.bf_mul,
        mixed_add: cost.ops.mixed_add,
        mixed_mul: cost.ops.mixed_mul,
        ext_add: cost.ops.ext_add,
        ext_mul: cost.ops.ext_mul,
        primitive_equivalents: cost
            .ops
            .primitive_equivalents()
            .expect("certified source-op cost already passed checked scoring"),
        arithmetic_ops: [1usize, 2, 3]
            .into_iter()
            .map(|opcode| compiled.compiled.stats.op_counts[opcode] as u128)
            .sum(),
        instructions: compiled.compiled.program.instrs.len() as u128,
        encoded_lanes: compiled.encoded.len() as u128,
        moves: compiled.compiled.stats.op_counts[OP_MOV] as u128,
        relocations: compiled.binding_stats.relocation_moves as u128,
        peak_lanes,
        peak_cells: peak_lanes.div_ceil(4),
        certificate,
    }
}

pub fn round_profiles(trace_len: usize, regime: BwdRegime) -> Vec<RoundProfile> {
    assert!(trace_len.is_power_of_two() && trace_len >= 2);
    let rounds = trace_len.trailing_zeros() as u8;
    (0..rounds)
        .filter(|&round| match regime {
            BwdRegime::R0 => round == 0,
            BwdRegime::Ext => round != 0,
        })
        .map(|round| RoundProfile {
            round,
            rows: (trace_len >> (round as usize + 1)) as u64,
        })
        .collect()
}

fn classification_reason(classification: &ArmClassification) -> Option<String> {
    match classification {
        ArmClassification::Searched | ArmClassification::UnavailableIncumbent => None,
        ArmClassification::Trivial { reason } => Some((*reason).to_owned()),
        ArmClassification::Infeasible { reason } => Some(reason.clone()),
        ArmClassification::SolverCapped {
            cap,
            demand_position,
            peak_states,
        } => Some(format!(
            "solver cap {cap} at demand {demand_position} (peak states {peak_states})"
        )),
    }
}

fn signed_delta(value: u128, reference: u128) -> SignedDelta {
    SignedDelta {
        negative: value < reference,
        magnitude: value.abs_diff(reference),
    }
}

fn delta_percentage(value: u128, reference: u128) -> DeltaPercentage {
    let delta = signed_delta(value, reference);
    DeltaPercentage {
        delta,
        percentage: (reference != 0).then_some(Percentage {
            numerator: delta,
            denominator: reference,
        }),
    }
}

fn metric_deltas(value: ArmMeasurements, reference: ArmMeasurements) -> MetricDeltas {
    MetricDeltas {
        dram_bytes: delta_percentage(value.dram_bytes(), reference.dram_bytes()),
        primitive_equivalents: delta_percentage(
            value.primitive_equivalents,
            reference.primitive_equivalents,
        ),
        arithmetic_ops: delta_percentage(value.arithmetic_ops, reference.arithmetic_ops),
        instructions: delta_percentage(value.instructions, reference.instructions),
        encoded_lanes: delta_percentage(value.encoded_lanes, reference.encoded_lanes),
        moves: delta_percentage(value.moves, reference.moves),
        relocations: delta_percentage(value.relocations, reference.relocations),
    }
}

fn finish_instance(mut result: InstanceMetrics) -> InstanceMetrics {
    let references = [
        result.uncached.measurements,
        result.incumbent.measurements,
        result.arm1.measurements,
        result.arm2.measurements,
    ];
    for arm in [
        &mut result.uncached,
        &mut result.incumbent,
        &mut result.arm1,
        &mut result.arm2,
        &mut result.arm3,
        &mut result.arm4,
    ] {
        let Some(value) = arm.measurements else {
            continue;
        };
        arm.comparisons = ArmComparisons {
            uncached: references[0].map(|reference| metric_deltas(value, reference)),
            incumbent: references[1].map(|reference| metric_deltas(value, reference)),
            arm1: references[2].map(|reference| metric_deltas(value, reference)),
            arm2: references[3].map(|reference| metric_deltas(value, reference)),
        };
    }
    result
}

#[cfg(test)]
impl InstanceMetrics {
    fn report_fixture(
        key: InstanceKey,
        trace_len: usize,
        arm1_dram_bytes: u128,
        incumbent_dram_bytes: Option<u128>,
    ) -> Self {
        let measured_arm = |arm, bytes| {
            let mut result = classified_arm(arm, ArmClassification::Searched);
            result.score = Some(BackwardScore {
                infeasible: false,
                whole_pass_dram_bytes: bytes,
                primitive_source_ops: 0,
                instructions: 0,
                encoded_lanes: 0,
                arithmetic_ops: 0,
                ordinal: 0,
            });
            result.measurements = Some(ArmMeasurements {
                plain_read_bytes: bytes,
                ..ArmMeasurements::default()
            });
            result
        };
        let uncached = measured_arm(ExperimentArm::Uncached, arm1_dram_bytes);
        let incumbent = incumbent_dram_bytes.map_or_else(
            || {
                classified_arm(
                    ExperimentArm::Incumbent,
                    ArmClassification::UnavailableIncumbent,
                )
            },
            |bytes| measured_arm(ExperimentArm::Incumbent, bytes),
        );
        let arm1 = measured_arm(ExperimentArm::ExactConstructive, arm1_dram_bytes);
        let arm2 = measured_arm(ExperimentArm::OrderSearch, arm1_dram_bytes);
        let arm3 = measured_arm(ExperimentArm::CacheSearch, arm1_dram_bytes);
        let arm4 = measured_arm(ExperimentArm::JointSearch, arm1_dram_bytes);
        finish_instance(Self {
            fixture: key.fixture.clone(),
            layer_index: key.layer_index,
            budget_cells: key.budget_cells,
            round_profiles: round_profiles(trace_len, key.regime),
            key,
            trace_len,
            classification: ArmClassification::Searched,
            reason: None,
            fragment_count: Some(1),
            reusable_leaf_count: Some(1),
            demand_count: Some(1),
            materialization_bindings: Some(0),
            materialization: None,
            all_ext_boundary: None,
            stream_reductions: Some(false),
            uncached,
            incumbent,
            arm1,
            arm2,
            arm3,
            arm4,
        })
    }
}

fn classified_instance(
    fixture: &str,
    layer_index: usize,
    regime: BwdRegime,
    trace_len: usize,
    budget_cells: usize,
    classification: ArmClassification,
) -> InstanceResult {
    finish_instance(InstanceResult {
        key: InstanceKey {
            fixture: fixture.to_owned(),
            layer_index,
            regime,
            budget_cells,
        },
        trace_len,
        round_profiles: round_profiles(trace_len, regime),
        classification: classification.clone(),
        reason: classification_reason(&classification),
        fragment_count: None,
        reusable_leaf_count: None,
        demand_count: None,
        materialization_bindings: None,
        materialization: None,
        all_ext_boundary: None,
        stream_reductions: None,
        fixture: fixture.to_owned(),
        layer_index,
        budget_cells,
        uncached: classified_arm(ExperimentArm::Uncached, classification.clone()),
        incumbent: classified_arm(
            ExperimentArm::Incumbent,
            ArmClassification::UnavailableIncumbent,
        ),
        arm1: classified_arm(ExperimentArm::ExactConstructive, classification.clone()),
        arm2: classified_arm(ExperimentArm::OrderSearch, classification.clone()),
        arm3: classified_arm(ExperimentArm::CacheSearch, classification.clone()),
        arm4: classified_arm(ExperimentArm::JointSearch, classification),
    })
}

fn classified_arm(arm: ExperimentArm, classification: ArmClassification) -> ArmResult {
    ArmResult {
        arm,
        classification,
        score: None,
        order: None,
        plan: None,
        first_winning_ordinal: None,
        improvement_ordinals: Vec::new(),
        evaluations: 0,
        pager: PagerRunTelemetry::default(),
        compile_time: Duration::ZERO,
        wall_time: Duration::ZERO,
        winning_tier: None,
        measurements: None,
        comparisons: ArmComparisons::default(),
    }
}

fn capped_arm(
    arm: ExperimentArm,
    classification: ArmClassification,
    telemetry: BackwardAdapterTelemetrySnapshot,
    wall_time: Duration,
) -> ArmResult {
    let mut result = classified_arm(arm, classification);
    result.evaluations = telemetry.evaluation_attempts;
    result.pager = pager_telemetry(telemetry);
    result.compile_time = telemetry.compile_time;
    result.wall_time = wall_time;
    result
}

fn pager_telemetry(snapshot: BackwardAdapterTelemetrySnapshot) -> PagerRunTelemetry {
    PagerRunTelemetry {
        calls: snapshot.pager_calls,
        generated_states: snapshot.pager_generated_states,
        merged_states: snapshot.pager_merged_states,
        peak_states: snapshot.pager_peak_states,
    }
}

fn validate_full_order(order: &[usize], fragments: usize) -> Result<(), BackwardSearchError> {
    if order.len() != fragments
        || order.iter().copied().collect::<BTreeSet<_>>().len() != fragments
        || order.iter().any(|&index| index >= fragments)
    {
        return Err(BackwardSearchError::InvalidGenomeDomain {
            gene: "accepted incumbent full-decomposition order",
        });
    }
    Ok(())
}

fn exact_from_plan(
    problem: &BackwardSearchProblem,
    plan: &BwdOccurrencePlan,
) -> Result<ExactPagingPlan, BackwardSearchError> {
    if plan.epoch != problem.epoch
        || plan.stream_reductions != problem.stream_reductions
        || plan.entries_fnv != plan_entries_fnv(&plan.entries)
        || plan.entries.len() != problem.all_domain_serves.len()
        || plan
            .entries
            .iter()
            .zip(&problem.all_domain_serves)
            .any(|(entry, fp)| entry.fp != *fp)
    {
        return Err(BackwardSearchError::PagingCertificateMismatch {
            observable: "accepted incumbent plan identity",
        });
    }
    let mut demands = BTreeMap::<FingerprintKey, VecDeque<usize>>::new();
    for (index, demand) in problem.demands.iter().enumerate() {
        demands
            .entry(demand.fp.into())
            .or_default()
            .push_back(index);
    }
    let mut actions = vec![PagingAction::Bypass; problem.demands.len()];
    for entry in &plan.entries {
        if let Some(index) = demands
            .get_mut(&entry.fp.into())
            .and_then(VecDeque::pop_front)
        {
            actions[index] = match entry.action {
                PlanAction::Bypass => PagingAction::Bypass,
                PlanAction::Retain => PagingAction::Retain,
            };
        } else if entry.action == PlanAction::Retain {
            return Err(BackwardSearchError::PagingCertificateMismatch {
                observable: "accepted incumbent non-leaf retain",
            });
        }
    }
    if demands.values().any(|queue| !queue.is_empty()) {
        return Err(BackwardSearchError::PagingCertificateMismatch {
            observable: "accepted incumbent leaf coverage",
        });
    }
    paging_from_actions(problem, actions)
}

fn paging_from_actions(
    problem: &BackwardSearchProblem,
    actions: Vec<PagingAction>,
) -> Result<ExactPagingPlan, BackwardSearchError> {
    if actions.len() != problem.demands.len() {
        return Err(BackwardSearchError::PagingActionCount {
            expected: problem.demands.len(),
            actual: actions.len(),
        });
    }
    let mut residents = BTreeMap::<ExprId, u8>::new();
    let mut live_lanes_after = Vec::with_capacity(actions.len());
    let mut objective = PagingObjective::default();
    let mut misses = 0u32;
    let mut peak_live_lanes = 0u8;
    for (position, (demand, action)) in problem.demands.iter().zip(&actions).enumerate() {
        if residents.remove(&demand.expr).is_some() {
            objective.evictions = objective
                .evictions
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
        } else {
            misses = misses
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
            objective.dram_bytes = objective
                .dram_bytes
                .checked_add(demand.miss_cost.dram_bytes()?)
                .ok_or(BackwardSearchError::CostOverflow)?;
            objective.primitive_source_ops = objective
                .primitive_source_ops
                .checked_add(demand.miss_cost.ops.primitive_equivalents()?)
                .ok_or(BackwardSearchError::CostOverflow)?;
        }
        if *action == PagingAction::Retain {
            if !demand.has_next {
                return Err(BackwardSearchError::CacheGenomeInfeasible {
                    demand_position: position,
                });
            }
            residents.insert(demand.expr, demand.width_lanes);
            objective.admissions = objective
                .admissions
                .checked_add(1)
                .ok_or(BackwardSearchError::CostOverflow)?;
        }
        let live = residents.values().try_fold(0u8, |total, width| {
            total
                .checked_add(*width)
                .ok_or(BackwardSearchError::CostOverflow)
        })?;
        if live > demand.gap_capacity_lanes {
            return Err(BackwardSearchError::CacheGenomeInfeasible {
                demand_position: position,
            });
        }
        peak_live_lanes = peak_live_lanes.max(live);
        live_lanes_after.push(live);
    }
    Ok(ExactPagingPlan {
        actions,
        live_lanes_after,
        objective,
        predicted_misses: misses,
        refused_retains: 0,
        telemetry: PagingTelemetry {
            peak_live_lanes,
            ..PagingTelemetry::default()
        },
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FingerprintKey {
    term: u32,
    kind: u8,
    value: u32,
    consumer: Option<u32>,
}

impl From<BwdFingerprint> for FingerprintKey {
    fn from(fp: BwdFingerprint) -> Self {
        Self {
            term: fp.term,
            kind: match fp.kind {
                BwdServeKind::RootOutput => 0,
                BwdServeKind::Operand => 1,
            },
            value: fp.value.0,
            consumer: fp.consumer.map(|consumer| consumer.0),
        }
    }
}

fn min_score(left: BackwardScore, right: BackwardScore) -> BackwardScore {
    if score_key(left) <= score_key(right) {
        left
    } else {
        right
    }
}

fn score_key(score: BackwardScore) -> (bool, u128, u128, usize, usize, usize) {
    (
        score.infeasible,
        score.whole_pass_dram_bytes,
        score.primitive_source_ops,
        score.instructions,
        score.encoded_lanes,
        score.arithmetic_ops,
    )
}

fn digest_arm(digest: &mut u64, result: &ArmResult) {
    digest_usize(digest, result.arm as usize);
    digest_classification(digest, &result.classification);
    if let Some(score) = result.score {
        digest_usize(digest, 1);
        digest_usize(digest, usize::from(score.infeasible));
        digest_bytes(digest, &score.whole_pass_dram_bytes.to_le_bytes());
        digest_bytes(digest, &score.primitive_source_ops.to_le_bytes());
        for value in [
            score.instructions,
            score.encoded_lanes,
            score.arithmetic_ops,
            score.ordinal,
        ] {
            digest_usize(digest, value);
        }
    } else {
        digest_usize(digest, 0);
    }
    if let Some(order) = &result.order {
        digest_usize(digest, 1);
        digest_usize(digest, order.len());
        for value in order {
            digest_usize(digest, *value);
        }
    } else {
        digest_usize(digest, 0);
    }
    if let Some(plan) = &result.plan {
        digest_usize(digest, 1);
        digest_bytes(digest, &plan.epoch.to_le_bytes());
        digest_bytes(digest, &plan.entries_fnv.to_le_bytes());
        digest_usize(digest, usize::from(plan.stream_reductions));
        digest_usize(digest, plan.entries.len());
    } else {
        digest_usize(digest, 0);
    }
    digest_usize(digest, result.first_winning_ordinal.unwrap_or(usize::MAX));
    digest_usize(digest, result.improvement_ordinals.len());
    for &ordinal in &result.improvement_ordinals {
        digest_usize(digest, ordinal);
    }
    for value in [
        result.evaluations,
        result.pager.calls,
        result.pager.peak_states,
        result.winning_tier.unwrap_or(0),
    ] {
        digest_usize(digest, value);
    }
    digest_bytes(digest, &result.pager.generated_states.to_le_bytes());
    digest_bytes(digest, &result.pager.merged_states.to_le_bytes());
}

fn digest_classification(digest: &mut u64, classification: &ArmClassification) {
    match classification {
        ArmClassification::Searched => digest_usize(digest, 0),
        ArmClassification::Trivial { reason } => {
            digest_usize(digest, 1);
            digest_usize(digest, reason.len());
            digest_bytes(digest, reason.as_bytes());
        }
        ArmClassification::Infeasible { reason } => {
            digest_usize(digest, 2);
            digest_usize(digest, reason.len());
            digest_bytes(digest, reason.as_bytes());
        }
        ArmClassification::SolverCapped {
            cap,
            demand_position,
            peak_states,
        } => {
            digest_usize(digest, 3);
            digest_usize(digest, *cap);
            digest_usize(digest, *demand_position);
            digest_usize(digest, *peak_states);
        }
        ArmClassification::UnavailableIncumbent => digest_usize(digest, 4),
    }
}

fn digest_usize(digest: &mut u64, value: usize) {
    digest_bytes(digest, &value.to_le_bytes());
}

fn digest_bytes(digest: &mut u64, bytes: &[u8]) {
    for byte in bytes {
        *digest = (*digest ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet, HashMap};
    use std::time::Duration;

    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, BwdRegime, ClaimInfo, DagLayer, Expr, ExprId, ReadPlace, Root, RootGroup,
        RootId, RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind,
    };

    use crate::bwd::compile::FragmentBackend;
    use crate::bwd::construct::construct_fragment_order;
    use crate::bwd::distill::stable_distilled_site_domain;
    use crate::bwd::distill::{DistilledLayer, distill};
    use crate::bwd::fif::coordinate_correct_frozen_with_backend;
    use crate::bwd::plan::PlanAction;
    use crate::bwd::price::compound_batch_plan;
    use crate::bwd::trace::{BwdEvent, positioned_physical_traffic_events};
    use crate::eval_plan::search_driver::{SearchAdapter, StableRng};
    use crate::eval_plan::{BackwardEvaluationError, PlanError};

    use super::super::replay::reprice_source_read;
    use super::super::{BackwardSearchError, SourceCost};
    use super::{
        AcceptedIncumbent, ArmClassification, BackwardAdapter, BackwardAdapterTelemetrySnapshot,
        BackwardGenome, BackwardSearchArm, EscalationStep, EscalationTelemetry, ExperimentReport,
        InstanceKey, InstanceMetrics, InstanceResult, RoundProfile, SeededAdapter,
        build_backward_search_problem, build_problem_for_order, escalation_tiers, exact_from_plan,
        incumbent_backend_incompatibility, joint_seed_from_arm2, paging_seed, render_markdown,
        round_profiles, run_escalation_schedule, run_instance, run_instance_with_pager_cap,
        run_tier, tier_search_config,
    };

    #[test]
    fn per_budget_denominators_precede_savings_and_sum_to_total() {
        let report = synthetic_report();
        for budget in [2, 3, 4] {
            let counts = report.counts_by_budget[&budget];
            assert_eq!(
                counts.total,
                counts.feasible + counts.trivial + counts.infeasible + counts.solver_capped
            );
        }
        let markdown = render_markdown(&report);
        assert!(
            markdown.find("## Per-budget denominators").unwrap()
                < markdown.find("## Savings").unwrap()
        );
    }

    #[test]
    fn whole_pass_rollup_sums_preweighted_totals_without_double_weighting() {
        let report = ExperimentReport::from_instances(vec![
            report_fixture("first", BwdRegime::R0, 4, 100, Some(100), 8),
            report_fixture("second", BwdRegime::R0, 4, 200, Some(200), 8),
        ]);
        assert_eq!(report.equal_instance.arm1.dram_bytes, 150);
        assert_eq!(report.whole_pass.corpus_rows, 8);
        assert_eq!(report.whole_pass.arm1.dram_bytes, 300);
    }

    #[test]
    fn rollups_expose_independent_per_arm_instance_and_row_coverage() {
        let report = ExperimentReport::from_instances(vec![
            report_fixture("with-incumbent", BwdRegime::R0, 4, 100, Some(80), 8),
            report_fixture("without-incumbent", BwdRegime::R0, 4, 200, None, 8),
        ]);

        assert_eq!(report.equal_instance.arm1.computed_instances, 2);
        assert_eq!(report.equal_instance.arm1.covered_rows, 8);
        assert_eq!(report.equal_instance.arm1.dram_bytes, 150);
        assert_eq!(report.equal_instance.incumbent.computed_instances, 1);
        assert_eq!(report.equal_instance.incumbent.covered_rows, 4);
        assert_eq!(report.equal_instance.incumbent.dram_bytes, 80);

        assert_eq!(report.whole_pass.arm1.computed_instances, 2);
        assert_eq!(report.whole_pass.arm1.covered_rows, 8);
        assert_eq!(report.whole_pass.arm1.dram_bytes, 300);
        assert_eq!(report.whole_pass.incumbent.computed_instances, 1);
        assert_eq!(report.whole_pass.incumbent.covered_rows, 4);
        assert_eq!(report.whole_pass.incumbent.dram_bytes, 80);

        let markdown = render_markdown(&report);
        assert!(markdown.contains("| I | 1 | 4 | 80 |"));
        assert!(markdown.contains("| Arm1 | 2 | 8 | 150 |"));
        assert!(markdown.contains("| Arm1 | 2 | 8 | 300 |"));
        assert!(markdown.contains("Comparable logical rows: 4."));
    }

    #[test]
    fn unavailable_incumbent_and_solver_capped_never_enter_percentage_denominators() {
        let mut capped = report_fixture("capped", BwdRegime::Ext, 4, 0, Some(40), 8);
        capped.arm1 = super::classified_arm(
            super::ExperimentArm::ExactConstructive,
            ArmClassification::SolverCapped {
                cap: 1,
                demand_position: 0,
                peak_states: 1,
            },
        );
        let mut unavailable = report_fixture("unavailable", BwdRegime::Ext, 4, 20, None, 8);
        unavailable.classification = ArmClassification::Trivial {
            reason: "uncomputed fixture",
        };
        unavailable.arm1 = super::classified_arm(
            super::ExperimentArm::ExactConstructive,
            unavailable.classification.clone(),
        );
        let report = ExperimentReport::from_instances(vec![
            report_fixture("comparable", BwdRegime::Ext, 4, 30, Some(40), 8),
            unavailable,
            capped,
        ]);
        assert_eq!(report.incumbent_comparable, 1);
        assert_eq!(report.paged_computed, 1);
    }

    #[test]
    fn matching_incumbent_counts_matching_budget_provenance_not_score_equality() {
        let report = ExperimentReport::from_instances(vec![
            report_fixture("different-score-c4", BwdRegime::R0, 4, 30, Some(40), 8),
            report_fixture("non-production-c2", BwdRegime::R0, 2, 30, Some(40), 8),
        ]);
        assert_eq!(report.counts_by_budget[&4].matching_incumbent, 1);
        assert_eq!(report.counts_by_budget[&2].matching_incumbent, 0);
        assert_eq!(report.incumbent_comparable, 1);
    }

    #[test]
    fn uncached_and_incumbent_sections_render_their_comparisons() {
        let report = ExperimentReport::from_instances(vec![report_fixture(
            "comparable",
            BwdRegime::R0,
            4,
            30,
            Some(40),
            8,
        )]);
        let markdown = render_markdown(&report);
        assert!(markdown.contains("### Arm1−U uncached comparison"));
        assert!(markdown.contains("### Arm1−I incumbent comparison"));
    }

    #[test]
    fn telemetry_renders_pager_calls_and_detailed_certificate_counters() {
        let mut instance = report_fixture("telemetry", BwdRegime::R0, 4, 30, Some(40), 8);
        instance.arm1.pager.calls = 7;
        instance.arm1.measurements.as_mut().unwrap().certificate =
            Some(super::CertificateMetrics {
                actions_consumed: 9,
                diverged: 1,
                refused_retains: 2,
                predicted_source_reads: 3,
                realized_source_reads: 4,
                read_count_mismatches: 5,
                read_cost_mismatches: 6,
            });
        let markdown = render_markdown(&ExperimentReport::from_instances(vec![instance]));
        assert!(markdown.contains("pager calls"));
        assert!(markdown.contains("certificate actions"));
        assert!(markdown.contains("certificate reads (predicted/realized)"));
        assert!(markdown.contains("certificate counters (diverged/refused/read-count/read-cost)"));
        assert!(markdown.contains("| 7 | 9 | 3/4 | 1/2/5/6 | 14 |"));
    }

    #[test]
    fn primary_telemetry_renders_missing_certificate_as_unavailable() {
        let report = ExperimentReport::from_instances(vec![report_fixture(
            "uncertified-incumbent",
            BwdRegime::R0,
            4,
            30,
            Some(40),
            8,
        )]);
        let markdown = render_markdown(&report);
        let primary = markdown
            .split("### Pager and certificate counters")
            .next()
            .unwrap();
        let incumbent_row = primary
            .lines()
            .find(|line| line.contains("| Incumbent |"))
            .unwrap();
        let cells = incumbent_row.split('|').map(str::trim).collect::<Vec<_>>();
        assert_eq!(cells[18], "unavailable");
    }

    #[test]
    fn report_round_profiles_match_r0_and_ext_logical_row_evaluations() {
        assert_eq!(
            round_profiles(8, BwdRegime::R0),
            vec![RoundProfile { round: 0, rows: 4 }]
        );
        assert_eq!(
            round_profiles(8, BwdRegime::Ext),
            vec![
                RoundProfile { round: 1, rows: 2 },
                RoundProfile { round: 2, rows: 1 },
            ]
        );
    }

    fn synthetic_report() -> ExperimentReport {
        ExperimentReport::from_instances(vec![
            report_fixture("feasible-c2", BwdRegime::R0, 2, 10, None, 8),
            report_fixture("feasible-c3", BwdRegime::R0, 3, 10, None, 8),
            report_fixture("feasible-c4", BwdRegime::R0, 4, 10, Some(10), 8),
        ])
    }

    fn report_fixture(
        fixture: &str,
        regime: BwdRegime,
        budget_cells: usize,
        arm1_dram_bytes: u128,
        incumbent_dram_bytes: Option<u128>,
        trace_len: usize,
    ) -> InstanceMetrics {
        InstanceMetrics::report_fixture(
            InstanceKey {
                fixture: fixture.to_owned(),
                layer_index: 0,
                regime,
                budget_cells,
            },
            trace_len,
            arm1_dram_bytes,
            incumbent_dram_bytes,
        )
    }

    #[test]
    fn every_searched_arm_keeps_its_required_exact_incumbent() {
        let result = run_synthetic_instance().unwrap();
        assert!(result.arm2.score <= result.arm1.score);
        assert!(result.arm3.score <= result.arm1.score);
        assert!(result.arm4.score <= result.arm2.score);
    }

    #[test]
    fn arm4_pins_both_required_seeds_as_eligible_parents() {
        let result = run_synthetic_instance().unwrap();
        let (layer, distilled) = synthetic_fixture();
        let (_, problem) = build_backward_search_problem(&layer, &distilled, 8, 4).unwrap();
        let problem = problem.expect("synthetic search problem");
        let exact = exact_from_plan(&problem, result.arm1.plan.as_ref().unwrap()).unwrap();
        let arm1_seed = paging_seed(&problem, &exact).unwrap();
        let arm2_seed =
            joint_seed_from_arm2(&layer, &distilled, &problem, 8, &result.arm2).unwrap();
        let adapter = SeededAdapter {
            inner: BackwardAdapter::new(
                &layer,
                &distilled,
                &problem,
                &exact,
                8,
                BackwardSearchArm::Joint,
            ),
            seeds: vec![arm1_seed, arm2_seed],
        };
        assert!(adapter.seed_is_pinned(0));
        assert!(adapter.seed_is_pinned(1));
        let seeds = adapter.seeds().unwrap();
        for result in adapter.score_batch(&[(0, seeds[0].clone()), (1, seeds[1].clone())]) {
            let (score, candidate) = result.unwrap();
            assert!(adapter.parent_eligible(&score));
            assert!(candidate.is_some());
        }
    }

    #[test]
    fn tier_escalation_matches_the_approved_rules() {
        assert_eq!(escalation_tiers(false, false, false), vec![128]);
        assert_eq!(escalation_tiers(true, false, false), vec![128, 512]);
        assert_eq!(escalation_tiers(false, true, false), vec![128, 512]);
        assert_eq!(escalation_tiers(true, false, true), vec![128, 512, 2048]);
    }

    #[test]
    fn staged_escalation_restarts_each_tier_and_reaches_2048() {
        #[derive(Debug)]
        struct FakeTier {
            evaluations: usize,
        }

        let mut traces = Vec::new();
        let winner = run_escalation_schedule(30_u8, |evaluations| {
            let config = tier_search_config(evaluations);
            let mut rng = StableRng::new(config.seed);
            let trace = (0..config.evaluations)
                .map(|_| rng.next_u64())
                .collect::<Vec<_>>();
            traces.push(trace);
            let (score, first_winning_ordinal) = match evaluations {
                128 => (20, 100),
                512 => (10, 400),
                2048 => (5, 1500),
                _ => unreachable!(),
            };
            Ok::<_, ()>(EscalationStep::Completed {
                value: FakeTier { evaluations },
                score,
                first_winning_ordinal,
            })
        })
        .unwrap();

        assert_eq!(winner.evaluations, 2048);
        assert_eq!(
            traces.iter().map(Vec::len).collect::<Vec<_>>(),
            [128, 512, 2048]
        );
        assert_eq!(traces[0], traces[1][..128]);
        assert_eq!(traces[1], traces[2][..512]);
    }

    #[test]
    fn staged_escalation_stops_at_512_without_a_second_improvement() {
        let mut tiers = Vec::new();
        let winner = run_escalation_schedule(30_u8, |evaluations| {
            tiers.push(evaluations);
            Ok::<_, ()>(EscalationStep::Completed {
                value: evaluations,
                score: 20,
                first_winning_ordinal: 100,
            })
        })
        .unwrap();
        assert_eq!(winner, 512);
        assert_eq!(tiers, [128, 512]);
    }

    #[test]
    fn escalation_telemetry_sums_work_and_maxes_peak_state() {
        let mut total = EscalationTelemetry::default();
        total
            .merge(
                BackwardAdapterTelemetrySnapshot {
                    evaluation_attempts: 128,
                    pager_calls: 9,
                    pager_generated_states: 100,
                    pager_merged_states: 7,
                    pager_peak_states: 13,
                    compile_time: Duration::from_millis(40),
                },
                Duration::from_millis(50),
            )
            .unwrap();
        total
            .merge(
                BackwardAdapterTelemetrySnapshot {
                    evaluation_attempts: 512,
                    pager_calls: 11,
                    pager_generated_states: 200,
                    pager_merged_states: 5,
                    pager_peak_states: 8,
                    compile_time: Duration::from_millis(60),
                },
                Duration::from_millis(70),
            )
            .unwrap();

        assert_eq!(total.adapter.evaluation_attempts, 640);
        assert_eq!(total.adapter.pager_calls, 20);
        assert_eq!(total.adapter.pager_generated_states, 300);
        assert_eq!(total.adapter.pager_merged_states, 12);
        assert_eq!(total.adapter.pager_peak_states, 13);
        assert_eq!(total.adapter.compile_time, Duration::from_millis(100));
        assert_eq!(total.wall_time, Duration::from_millis(120));
    }

    #[test]
    fn escalation_telemetry_rejects_counter_overflow() {
        let mut total = EscalationTelemetry::default();
        total
            .merge(
                BackwardAdapterTelemetrySnapshot {
                    evaluation_attempts: usize::MAX,
                    ..Default::default()
                },
                Duration::default(),
            )
            .unwrap();

        let error = total
            .merge(
                BackwardAdapterTelemetrySnapshot {
                    evaluation_attempts: 1,
                    ..Default::default()
                },
                Duration::default(),
            )
            .unwrap_err();

        assert!(matches!(error, BackwardSearchError::CostOverflow));
    }

    #[test]
    fn capped_required_seed_caps_dependent_arm_without_substitution() {
        let result = run_with_pager_cap(1).unwrap();
        assert!(matches!(
            result.arm1.classification,
            ArmClassification::SolverCapped { .. }
        ));
        assert!(matches!(
            result.arm2.classification,
            ArmClassification::SolverCapped { .. }
        ));
        assert!(result.arm1.score.is_none());
        assert!(result.arm2.score.is_none());
        assert_eq!(result.arm1.evaluations, 1);
        assert_eq!(result.arm1.pager.calls, 1);
        assert!(result.arm1.pager.generated_states > 0);
        assert_eq!(result.arm2.evaluations, 0);
        assert_eq!(result.arm2.pager.calls, 0);
    }

    #[test]
    fn in_tier_order_cap_reports_attempted_evaluations_and_pager_state() {
        let result = run_synthetic_instance().unwrap();
        let (layer, distilled) = synthetic_fixture();
        let (_, problem) = build_backward_search_problem(&layer, &distilled, 8, 4).unwrap();
        let problem = problem.expect("synthetic search problem");
        let exact = exact_from_plan(&problem, result.arm1.plan.as_ref().unwrap()).unwrap();
        let staged = run_tier(
            &layer,
            &distilled,
            &problem,
            &exact,
            8,
            BackwardSearchArm::OrderOnly,
            &[BackwardGenome::constructive(&problem)],
            128,
            1,
        )
        .unwrap();
        let arm = staged.into_arm_result_or_capped(super::ExperimentArm::OrderSearch);
        assert!(matches!(
            arm.classification,
            ArmClassification::SolverCapped { .. }
        ));
        assert!(arm.score.is_none());
        assert_eq!(arm.evaluations, 1);
        assert_eq!(arm.pager.calls, 1);
        assert!(arm.pager.generated_states > 0);
        assert!(arm.pager.merged_states <= arm.pager.generated_states);
    }

    #[test]
    fn arm3_primary_delta_is_definitionally_zero() {
        let result = run_synthetic_instance().unwrap();
        assert_eq!(
            result.arm3.score.unwrap().whole_pass_dram_bytes,
            result.arm1.score.unwrap().whole_pass_dram_bytes
        );
    }

    #[test]
    fn successful_two_tier_arm_reports_cumulative_attempts() {
        let result = run_synthetic_instance().unwrap();
        let arm = &result.arm2;

        assert_eq!(result.arm2.winning_tier, Some(512));
        assert_eq!(result.arm2.evaluations, 128 + 512);
        assert!(arm.first_winning_ordinal.unwrap() < arm.winning_tier.unwrap());
        assert!(
            arm.improvement_ordinals
                .iter()
                .all(|&ordinal| ordinal < arm.winning_tier.unwrap())
        );
        assert_eq!(arm.pager.calls, arm.evaluations);
    }

    #[test]
    fn successful_three_tier_arm_reports_cumulative_attempts() {
        let tier = synthetic_completed_tier(2048);
        let first_winning_ordinal = tier.outcome.best_ordinal;
        let improvement_ordinals = tier.outcome.improvement_ordinals.clone();
        let arm = super::StagedOutcome::Completed(tier)
            .with_cumulative_telemetry(cumulative_attempts(&[128, 512, 2048]))
            .into_arm_result_or_capped(super::ExperimentArm::OrderSearch);

        assert_eq!(arm.evaluations, 128 + 512 + 2048);
        assert_eq!(arm.winning_tier, Some(2048));
        assert_eq!(arm.first_winning_ordinal, Some(first_winning_ordinal));
        assert_eq!(arm.improvement_ordinals, improvement_ordinals);
        assert!(arm.first_winning_ordinal.unwrap() < arm.winning_tier.unwrap());
        assert!(
            arm.improvement_ordinals
                .iter()
                .all(|&ordinal| ordinal < arm.winning_tier.unwrap())
        );
    }

    #[test]
    fn capped_escalation_reports_all_attempted_evaluations() {
        let arm = super::StagedOutcome::Capped(
            ArmClassification::SolverCapped {
                cap: 1,
                demand_position: 0,
                peak_states: 2,
            },
            BackwardAdapterTelemetrySnapshot {
                evaluation_attempts: 9,
                ..Default::default()
            },
            Duration::ZERO,
        )
        .with_cumulative_telemetry(cumulative_attempts(&[128, 9]))
        .into_arm_result_or_capped(super::ExperimentArm::OrderSearch);

        assert_eq!(arm.evaluations, 128 + 9);
        assert_eq!(arm.winning_tier, None);
    }

    #[test]
    fn accepted_c4_incumbent_replays_but_other_budgets_do_not_compile_it() {
        let first = run_synthetic_instance().unwrap();
        assert!(matches!(
            first.incumbent.classification,
            ArmClassification::UnavailableIncumbent
        ));
        let incumbent = AcceptedIncumbent {
            order: first.arm1.order.clone().unwrap(),
            plan: first.arm1.plan.clone().unwrap(),
        };
        let (layer, distilled) = synthetic_fixture();
        let c4 = run_instance("synthetic", 0, &layer, &distilled, 8, 4, Some(&incumbent)).unwrap();
        assert_eq!(c4.incumbent.score, first.arm1.score);

        let c3 = run_instance("synthetic", 0, &layer, &distilled, 8, 3, Some(&incumbent)).unwrap();
        assert!(matches!(
            c3.incumbent.classification,
            ArmClassification::UnavailableIncumbent
        ));
        let c2 = run_instance("synthetic", 0, &layer, &distilled, 8, 2, Some(&incumbent)).unwrap();
        assert!(matches!(
            c2.incumbent.classification,
            ArmClassification::UnavailableIncumbent
        ));
        assert_eq!(c2.incumbent.evaluations, 0);
        assert_eq!(c3.incumbent.evaluations, 0);
    }

    #[test]
    fn incumbent_unavailability_accepts_only_backend_schedule_incompatibility() {
        for error in [
            BackwardSearchError::PagingReplayRefused { count: 1 },
            BackwardSearchError::PlacementIntegrationFailure,
            BackwardSearchError::BackwardEvaluation(BackwardEvaluationError::Plan(
                PlanError::ReplayInfeasible,
            )),
        ] {
            assert!(incumbent_backend_incompatibility(&error));
        }
        for error in [
            BackwardSearchError::PagingReplayDiverged { at_entry: 3 },
            BackwardSearchError::PagingCertificateMismatch { observable: "test" },
            BackwardSearchError::BackwardEvaluation(BackwardEvaluationError::StaleReplayEpoch {
                expected: 1,
                actual: 2,
            }),
        ] {
            assert!(!incumbent_backend_incompatibility(&error));
        }
    }

    #[test]
    fn stale_incumbent_plan_remains_an_error() {
        let first = run_synthetic_instance().unwrap();
        let mut plan = first.arm1.plan.clone().unwrap();
        plan.epoch ^= 1;
        let incumbent = AcceptedIncumbent {
            order: first.arm1.order.clone().unwrap(),
            plan,
        };
        let (layer, distilled) = synthetic_fixture();
        assert!(run_instance("synthetic", 0, &layer, &distilled, 8, 4, Some(&incumbent),).is_err());
    }

    #[test]
    fn compound_retaining_incumbent_is_replayed_without_leaf_projection() {
        let (layer, distilled) = synthetic_shared_compound_fixture();
        let order = construct_fragment_order(
            &layer,
            &distilled,
            &stable_distilled_site_domain(&distilled),
        );
        let frozen = coordinate_correct_frozen_with_backend(
            &distilled,
            16,
            &FragmentBackend {
                order: order.clone(),
            },
        )
        .unwrap();
        let mut counts = BTreeMap::new();
        for (fp, _) in &frozen.domain_serves {
            *counts.entry(fp.value).or_insert(0usize) += 1;
        }
        let compound = counts
            .into_iter()
            .find_map(|(value, count)| {
                (count >= 2 && !matches!(distilled.layer.exprs[value.0 as usize], Expr::Source(_)))
                    .then_some(value)
            })
            .expect("fixture has a repeated compound serve");
        let plan = compound_batch_plan(&frozen, &BTreeSet::from([compound]));
        assert!(
            plan.entries
                .iter()
                .any(|entry| { entry.fp.value == compound && entry.action == PlanAction::Retain })
        );
        let problem =
            build_problem_for_order(&layer, &distilled, &order, 8, 4, plan.stream_reductions)
                .unwrap();
        let scored =
            super::compile_and_score_occurrence_plan(&distilled, &problem, &plan, &order, 0)
                .unwrap();
        let physical = positioned_physical_traffic_events(
            &distilled.layer,
            &scored.compiled.compiled.program,
            &scored.compiled.compiled.specials,
            &distilled.leaf_descs,
            &scored.compiled.compiled.backings,
            &scored.compiled.compiled.source_windows,
        )
        .unwrap();
        let expected_reads = physical
            .iter()
            .try_fold(SourceCost::default(), |cost, positioned| {
                let BwdEvent::TrafficRead { value, cells } = positioned.event else {
                    unreachable!("physical scan emits only traffic reads")
                };
                let read = reprice_source_read(
                    &problem,
                    distilled.leaf_descs.get(&value).copied(),
                    cells.try_into().unwrap(),
                )?;
                cost.checked_add(read)
            })
            .unwrap();
        let expected = expected_reads
            .checked_add(problem.materialization.fixed_writes)
            .unwrap();
        assert_eq!(
            scored.score.whole_pass_dram_bytes,
            expected.dram_bytes().unwrap()
        );
        assert_eq!(
            scored.score.primitive_source_ops,
            expected.ops.primitive_equivalents().unwrap()
        );

        let incumbent = AcceptedIncumbent { order, plan };
        let result =
            run_instance("compound", 0, &layer, &distilled, 8, 4, Some(&incumbent)).unwrap();
        assert!(result.incumbent.score.is_some());
        assert!(matches!(
            result.incumbent.classification,
            ArmClassification::Searched
        ));
    }

    #[test]
    fn deterministic_digest_excludes_all_timing_fields() {
        let result = run_synthetic_instance().unwrap();
        let mut retimed = result.clone();
        for arm in [
            &mut retimed.uncached,
            &mut retimed.incumbent,
            &mut retimed.arm1,
            &mut retimed.arm2,
            &mut retimed.arm3,
            &mut retimed.arm4,
        ] {
            arm.compile_time += std::time::Duration::from_secs(3);
            arm.wall_time += std::time::Duration::from_secs(7);
        }
        assert_eq!(
            result.deterministic_digest(),
            retimed.deterministic_digest()
        );
    }

    #[test]
    fn deterministic_digest_includes_cumulative_search_work() {
        let result = run_synthetic_instance().unwrap();
        let mut changed_evaluations = result.clone();
        changed_evaluations.arm2.evaluations += 1;
        assert_ne!(
            result.deterministic_digest(),
            changed_evaluations.deterministic_digest()
        );

        let mut changed_pager = result.clone();
        changed_pager.arm2.pager.calls += 1;
        assert_ne!(
            result.deterministic_digest(),
            changed_pager.deterministic_digest()
        );
    }

    #[test]
    fn search_is_thread_deterministic() {
        let result = run_synthetic_instance().unwrap();
        let digest = result.deterministic_digest();
        assert_eq!(digest, 0x2817_d47e_35f4_c806);
        println!("PLAN3-SEARCH-DIGEST {digest:016x}");
    }

    fn run_synthetic_instance() -> Result<InstanceResult, super::BackwardSearchError> {
        let (layer, distilled) = synthetic_fixture();
        run_instance("synthetic", 0, &layer, &distilled, 8, 4, None)
    }

    fn synthetic_completed_tier(evaluations: usize) -> super::TierOutcome {
        let result = run_synthetic_instance().unwrap();
        let (layer, distilled) = synthetic_fixture();
        let (_, problem) = build_backward_search_problem(&layer, &distilled, 8, 4).unwrap();
        let problem = problem.expect("synthetic search problem");
        let exact = exact_from_plan(&problem, result.arm1.plan.as_ref().unwrap()).unwrap();
        match run_tier(
            &layer,
            &distilled,
            &problem,
            &exact,
            8,
            BackwardSearchArm::OrderOnly,
            &[BackwardGenome::constructive(&problem)],
            evaluations,
            usize::MAX,
        )
        .unwrap()
        {
            super::StagedOutcome::Completed(tier) => tier,
            super::StagedOutcome::Capped(..) => panic!("synthetic tier must complete"),
        }
    }

    fn cumulative_attempts(tiers: &[usize]) -> EscalationTelemetry {
        let mut total = EscalationTelemetry::default();
        for &evaluation_attempts in tiers {
            total
                .merge(
                    BackwardAdapterTelemetrySnapshot {
                        evaluation_attempts,
                        ..Default::default()
                    },
                    Duration::ZERO,
                )
                .unwrap();
        }
        total
    }

    fn run_with_pager_cap(cap: usize) -> Result<InstanceResult, super::BackwardSearchError> {
        let (layer, distilled) = synthetic_fixture();
        run_instance_with_pager_cap("synthetic", 0, &layer, &distilled, 8, 4, None, cap)
    }

    fn synthetic_fixture() -> (DagLayer, DistilledLayer) {
        let layer = synthetic_two_shared_sources_layer();
        let distilled = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
        (layer, distilled)
    }

    fn synthetic_shared_compound_fixture() -> (DagLayer, DistilledLayer) {
        let mut sources = Vec::new();
        let mut exprs = Vec::new();
        let mut read = || {
            let source = SourceId(sources.len() as u32);
            sources.push(read_source(sources.len()));
            let expr = ExprId(exprs.len() as u32);
            exprs.push(Expr::Source(source));
            expr
        };
        let ru0 = read();
        let ru1 = read();
        let rw = read();
        let rv = read();
        let ra = read();
        let rb = read();
        let rc = read();
        let rd = read();
        let mut add = |expr: Expr| {
            let id = ExprId(exprs.len() as u32);
            exprs.push(expr);
            id
        };
        let u = add(Expr::Add(vec![ru0, ru1]));
        let w = add(Expr::Mul(vec![u, rw]));
        let v = add(Expr::Mul(vec![w, rv]));
        let m_va = add(Expr::Mul(vec![v, ra]));
        let m_vb = add(Expr::Mul(vec![v, rb]));
        let m_wc = add(Expr::Mul(vec![w, rc]));
        let m_ud = add(Expr::Mul(vec![u, rd]));
        let root = add(Expr::Add(vec![m_va, m_vb, m_wc, m_ud]));
        let layer = DagLayer {
            sources,
            exprs,
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            roots: vec![claim_root(root, 0)],
            resolutions: BTreeMap::new(),
        };
        let distilled = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
        (layer, distilled)
    }

    fn synthetic_two_shared_sources_layer() -> DagLayer {
        let sources = (0..6).map(read_source).collect::<Vec<_>>();
        let mut exprs = (0..6)
            .map(|source| Expr::Source(SourceId(source)))
            .collect::<Vec<_>>();
        for children in [[0, 2], [0, 3], [1, 4], [1, 5]] {
            exprs.push(Expr::Mul(children.map(ExprId).into_iter().collect()));
        }
        DagLayer {
            sources,
            exprs,
            batching: BatchingOrder {
                roots: (0..4).map(RootId).collect(),
            },
            roots: (0..4)
                .map(|index| claim_root(ExprId(6 + index), index as usize))
                .collect(),
            resolutions: BTreeMap::new(),
        }
    }

    fn read_source(column: usize) -> SourceInfo {
        SourceInfo {
            kind: SourceKind::Read {
                place: ReadPlace::BaseLayerWitness { column },
            },
        }
    }

    fn claim_root(expr: ExprId, relation_index: usize) -> Root {
        Root {
            expr,
            materialize: None,
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index,
                    slot: RootSlot::Constraint(0),
                },
            }),
        }
    }
}
