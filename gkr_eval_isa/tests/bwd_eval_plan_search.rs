mod common;

use std::{
    collections::{BTreeMap, HashMap},
    io::Write,
    sync::{
        Arc, Barrier, Mutex,
        atomic::{AtomicUsize, Ordering},
    },
    time::{Duration, Instant},
};

use common::assert_bwd_value_parity;
use cs::gkr_compiler::dag_ir::{
    BatchingOrder, BwdRegime, ClaimInfo, DagLayer, Expr, ExprId, ReadPlace, Root, RootGroup,
    RootId, RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind,
};
use gkr_eval_isa::bwd::distill::{DistilledLayer, distill};
use gkr_eval_isa::eval_plan::backward_search::experiment::{
    AcceptedIncumbent, ArmClassification, ExperimentReport, InstanceResult, render_markdown,
    run_instance,
};
use gkr_eval_isa::eval_plan::backward_search::problem::{
    ProblemClassification, build_backward_search_problem,
};
use gkr_eval_isa::eval_plan::backward_search::{
    BackwardSearchError, CertifiedBackwardCandidate, MAX_PAGER_STATES, PagerOutcome,
    compile_and_certify_paging, solve_exact_paging,
};
use gkr_eval_isa::fwd::encode::{decode, encode};
use rayon::prelude::*;

#[test]
fn three_way_progress_eta_uses_completed_mean() {
    assert_eq!(
        estimated_remaining(Duration::from_secs(30), 6, 342),
        Some(Duration::from_secs(560))
    );
    assert_eq!(estimated_remaining(Duration::ZERO, 0, 342), None);
    assert_eq!(
        estimated_remaining(Duration::from_secs(30), 342, 342),
        Some(Duration::ZERO)
    );
}

#[test]
fn parallel_map_ordered_overlaps_jobs_and_preserves_input_order() {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .expect("build incumbent-prepass test pool");
    let barrier = Arc::new(Barrier::new(4));
    let active = Arc::new(AtomicUsize::new(0));
    let peak = Arc::new(AtomicUsize::new(0));
    let inputs = [0usize, 1, 2, 3];

    let outputs = pool.install(|| {
        parallel_map_ordered(&inputs, |&input| {
            let now = active.fetch_add(1, Ordering::SeqCst) + 1;
            peak.fetch_max(now, Ordering::SeqCst);
            barrier.wait();
            active.fetch_sub(1, Ordering::SeqCst);
            10 + input
        })
    });

    assert_eq!(outputs, vec![10, 11, 12, 13]);
    assert_eq!(peak.load(Ordering::SeqCst), 4);
}

#[test]
fn incumbent_eta_uses_current_rayon_width() {
    assert_eq!(
        estimated_remaining_with_width(Duration::from_secs(48), 6, 114, 12),
        Some(Duration::from_secs(72))
    );
    assert_eq!(
        estimated_remaining_with_width(Duration::ZERO, 0, 114, 12),
        None
    );
}

#[test]
fn progress_completion_snapshots_keep_elapsed_and_count_coherent() {
    let progress = Arc::new(ProgressReporter::new());
    let start = Arc::new(Barrier::new(4));
    let jobs = [11u64, 23, 47].map(|nanos| {
        let progress = Arc::clone(&progress);
        let start = Arc::clone(&start);
        std::thread::spawn(move || {
            start.wait();
            progress.record_completion(Duration::from_nanos(nanos))
        })
    });
    start.wait();
    let snapshots = jobs.map(|job| job.join().expect("progress job must not panic"));

    for snapshot in snapshots {
        let valid_elapsed = match snapshot.completed {
            1 => [11, 23, 47].contains(&snapshot.completed_job_nanos),
            2 => [34, 58, 70].contains(&snapshot.completed_job_nanos),
            3 => snapshot.completed_job_nanos == 81,
            _ => false,
        };
        assert!(
            valid_elapsed,
            "completion count {} cannot have {} elapsed nanoseconds",
            snapshot.completed, snapshot.completed_job_nanos,
        );
    }
}

#[test]
fn plan3_audit_write_creates_missing_parent() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock must follow Unix epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "gkr-plan3-audit-write-{}-{unique}",
        std::process::id()
    ));
    let output = root.join("missing/nested/report.md");
    assert!(!root.exists());

    write_plan3_audit(&output, "audit body\n");

    assert_eq!(
        std::fs::read_to_string(&output).expect("read written Plan 3 audit"),
        "audit body\n"
    );
    std::fs::remove_dir_all(root).expect("remove Plan 3 audit test directory");
}

#[test]
fn plan3_audit_write_roots_relative_path_at_repository() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock must follow Unix epoch")
        .as_nanos();
    let relative = std::path::PathBuf::from(format!(
        ".agents/audits/gkr-plan3-relative-write-{}-{unique}/report.md",
        std::process::id()
    ));
    let crate_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let repository_root = crate_root
        .parent()
        .expect("gkr_eval_isa must be inside the repository root");
    let canonical_current_dir = std::fs::canonicalize(
        std::env::current_dir().expect("read Plan 3 audit test current directory"),
    )
    .expect("canonicalize Plan 3 audit test current directory");
    let canonical_crate_root =
        std::fs::canonicalize(crate_root).expect("canonicalize gkr_eval_isa crate root");
    let canonical_repository_root =
        std::fs::canonicalize(repository_root).expect("canonicalize Plan 3 repository root");
    assert_eq!(canonical_current_dir, canonical_crate_root);
    assert_ne!(canonical_current_dir, canonical_repository_root);
    let expected = repository_root.join(&relative);
    let wrong = crate_root.join(&relative);
    let expected_parent = expected.parent().expect("relative report has a parent");
    let wrong_parent = wrong.parent().expect("wrong report has a parent");
    assert!(!expected_parent.exists());
    assert!(!wrong_parent.exists());

    write_plan3_audit(&relative, "audit body\n");

    let expected_body = std::fs::read_to_string(&expected);
    let wrong_exists = wrong.exists();
    if expected_parent.exists() {
        std::fs::remove_dir_all(expected_parent)
            .expect("remove repository-root Plan 3 audit test directory");
    }
    if wrong_parent.exists() {
        std::fs::remove_dir_all(wrong_parent)
            .expect("remove crate-root Plan 3 audit test directory");
    }
    assert_eq!(
        expected_body.expect("read repository-root Plan 3 audit"),
        "audit body\n"
    );
    assert!(
        !wrong_exists,
        "relative audit must not resolve at crate root"
    );
}

#[test]
#[ignore = "Plan 3 parallel budget-group release equivalence"]
fn plan3_parallel_budget_group_matches_sequential() {
    let fixture = "add_sub_lui_auipc_mop_layout_gkr.json";
    let artifact = common::load_fixture(fixture);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact)
        .unwrap_or_else(|error| panic!("[{fixture}] lower DAG: {error}"));
    let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
        .next()
        .expect("add_sub has a backward layer");
    let regime = BwdRegime::Ext;
    let distilled = distill(&layer, regime, &cross, None);
    let current = gkr_eval_isa::bwd::engine::cs_schedule_bwd_layer(&layer, regime, &cross, 16);
    let incumbent = current
        .fragment_order
        .zip(current.plan)
        .map(|(order, plan)| AcceptedIncumbent { order, plan })
        .expect("add_sub Ext c4 ships a fragment-plan incumbent");
    let sequential = [2usize, 3, 4]
        .into_iter()
        .map(|budget_cells| {
            (
                budget_cells,
                run_instance(
                    fixture,
                    layer_index,
                    &layer,
                    &distilled,
                    dag.globals.trace_len,
                    budget_cells,
                    (budget_cells == 4).then_some(&incumbent),
                ),
            )
        })
        .collect::<Vec<_>>();
    let progress = ProgressReporter::new();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(48)
        .build()
        .expect("build Plan 3 parallel test pool");
    let parallel = pool.install(|| {
        run_budget_group(1, &progress, fixture, layer_index, regime, |budget_cells| {
            run_instance(
                fixture,
                layer_index,
                &layer,
                &distilled,
                dag.globals.trace_len,
                budget_cells,
                (budget_cells == 4).then_some(&incumbent),
            )
        })
    });

    assert_eq!(parallel.len(), sequential.len());
    for ((parallel_budget, parallel), (sequential_budget, sequential)) in
        parallel.into_iter().zip(sequential)
    {
        assert_eq!(parallel_budget, sequential_budget);
        let parallel = parallel.unwrap();
        let sequential = sequential.unwrap();
        assert_eq!(parallel.key, sequential.key);
        assert_eq!(parallel.classification, sequential.classification);
        assert_eq!(
            parallel.deterministic_digest(),
            sequential.deterministic_digest()
        );
    }
}

#[test]
#[ignore = "Plan 3 parallel incumbent-prepass release equivalence"]
fn plan3_parallel_incumbent_prepass_matches_sequential() {
    let fixture = "add_sub_lui_auipc_mop_layout_gkr.json";
    let artifact = common::load_fixture(fixture);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact)
        .unwrap_or_else(|error| panic!("[{fixture}] lower DAG: {error}"));
    let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
        .next()
        .expect("add_sub has a backward layer");
    let input = CorpusLayer {
        fixture,
        layer_index,
        trace_len: dag.globals.trace_len,
        layer,
        cross,
    };
    let regimes = [BwdRegime::R0, BwdRegime::Ext];
    let sequential = regimes.map(|regime| build_incumbent(&input, regime));
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(2)
        .build()
        .expect("build incumbent-prepass equivalence pool");
    let parallel =
        pool.install(|| parallel_map_ordered(&regimes, |&regime| build_incumbent(&input, regime)));

    for (parallel, sequential) in parallel.iter().zip(sequential.iter()) {
        match (parallel, sequential) {
            (Some(parallel), Some(sequential)) => {
                assert_eq!(parallel.order, sequential.order);
                assert_eq!(parallel.plan.epoch, sequential.plan.epoch);
                assert_eq!(parallel.plan.entries_fnv, sequential.plan.entries_fnv);
                assert_eq!(
                    parallel.plan.stream_reductions,
                    sequential.plan.stream_reductions
                );
                assert_eq!(parallel.plan.entries, sequential.plan.entries);
            }
            (None, None) => {}
            _ => panic!("parallel and sequential incumbent availability differ"),
        }
    }
}

const PLAN3_INSTANCES: usize = 342;
const PLAN3_INCUMBENT_JOBS: usize = 114;
const BUDGET_CONCURRENCY: u128 = 3;

fn estimated_remaining_with_width(
    completed_job_time: Duration,
    completed: usize,
    total: usize,
    concurrency: usize,
) -> Option<Duration> {
    if completed == 0 || concurrency == 0 {
        return None;
    }
    let remaining = total.saturating_sub(completed) as u128;
    let nanos = completed_job_time
        .as_nanos()
        .checked_div(completed as u128)?
        .checked_mul(remaining)?
        .checked_div(concurrency as u128)?;
    Some(Duration::from_nanos(
        u64::try_from(nanos).unwrap_or(u64::MAX),
    ))
}

fn estimated_remaining(
    completed_job_time: Duration,
    completed: usize,
    total: usize,
) -> Option<Duration> {
    estimated_remaining_with_width(
        completed_job_time,
        completed,
        total,
        usize::try_from(BUDGET_CONCURRENCY).expect("budget concurrency fits usize"),
    )
}

struct CorpusLayer {
    fixture: &'static str,
    layer_index: usize,
    trace_len: usize,
    layer: DagLayer,
    cross: common::CrossFields,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct IncumbentJob {
    corpus_layer: usize,
    regime: BwdRegime,
}

struct PreparedIncumbent {
    job: IncumbentJob,
    incumbent: Option<AcceptedIncumbent>,
}

fn build_corpus_layers() -> Vec<CorpusLayer> {
    let mut layers = Vec::new();
    for &fixture in common::FIXTURES {
        let artifact = common::load_fixture(fixture);
        let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact)
            .unwrap_or_else(|error| panic!("[{fixture}] lower DAG: {error}"));
        let trace_len = dag.globals.trace_len;
        layers.extend(
            common::layers_with_bwd_roots(fixture).map(|(layer_index, layer, cross)| CorpusLayer {
                fixture,
                layer_index,
                trace_len,
                layer,
                cross,
            }),
        );
    }
    assert_eq!(layers.len(), PLAN3_INCUMBENT_JOBS / 2);
    layers
}

fn incumbent_jobs(layers: &[CorpusLayer]) -> Vec<IncumbentJob> {
    let jobs = (0..layers.len())
        .flat_map(|corpus_layer| {
            [BwdRegime::R0, BwdRegime::Ext].map(move |regime| IncumbentJob {
                corpus_layer,
                regime,
            })
        })
        .collect::<Vec<_>>();
    assert_eq!(jobs.len(), PLAN3_INCUMBENT_JOBS);
    jobs
}

fn build_incumbent(input: &CorpusLayer, regime: BwdRegime) -> Option<AcceptedIncumbent> {
    let distilled = distill(&input.layer, regime, &input.cross, None);
    gkr_eval_isa::bwd::compile::compile_distilled(&distilled, 16, None)
        .ok()
        .and_then(|_| {
            let current = gkr_eval_isa::bwd::engine::cs_schedule_bwd_layer(
                &input.layer,
                regime,
                &input.cross,
                16,
            );
            current.fragment_order.zip(current.plan)
        })
        .map(|(order, plan)| AcceptedIncumbent { order, plan })
}

fn parallel_map_ordered<T: Sync, R: Send>(
    items: &[T],
    run: impl Fn(&T) -> R + Sync + Send,
) -> Vec<R> {
    items.par_iter().map(run).collect()
}

fn incumbent_job_id(job: IncumbentJob) -> usize {
    job.corpus_layer * 2
        + match job.regime {
            BwdRegime::R0 => 1,
            BwdRegime::Ext => 2,
        }
}

#[derive(Clone, Copy)]
struct ProgressSnapshot {
    completed: usize,
    completed_job_nanos: u64,
}

#[derive(Default)]
struct ProgressState {
    completed: usize,
    completed_job_nanos: u64,
}

struct ProgressReporter {
    started: Instant,
    state: Mutex<ProgressState>,
}

fn classification_tag(classification: &ArmClassification) -> &'static str {
    match classification {
        ArmClassification::Searched => "Searched",
        ArmClassification::Trivial { .. } => "Trivial",
        ArmClassification::Infeasible { .. } => "Infeasible",
        ArmClassification::SolverCapped { .. } => "SolverCapped",
        ArmClassification::UnavailableIncumbent => "UnavailableIncumbent",
    }
}

impl ProgressReporter {
    fn new() -> Self {
        Self {
            started: Instant::now(),
            state: Mutex::new(ProgressState::default()),
        }
    }

    fn record_completion(&self, instance_elapsed: Duration) -> ProgressSnapshot {
        let nanos = u64::try_from(instance_elapsed.as_nanos()).unwrap_or(u64::MAX);
        let mut state = self.state.lock().expect("lock Plan 3 progress state");
        state.completed_job_nanos = state.completed_job_nanos.saturating_add(nanos);
        state.completed += 1;
        ProgressSnapshot {
            completed: state.completed,
            completed_job_nanos: state.completed_job_nanos,
        }
    }

    fn start(
        &self,
        job: usize,
        fixture: &str,
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
    ) {
        let mut stderr = std::io::stderr().lock();
        writeln!(
            stderr,
            "START job={job}/{PLAN3_INSTANCES} fixture={fixture} layer={layer} regime={regime:?} budget=c{budget_cells} total_elapsed={:?}",
            self.started.elapsed(),
        )
        .expect("write Plan 3 START");
        stderr.flush().expect("flush Plan 3 progress");
    }

    fn done(
        &self,
        job: usize,
        fixture: &str,
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
        instance_elapsed: Duration,
        classification: &ArmClassification,
    ) {
        let snapshot = self.record_completion(instance_elapsed);
        let eta = estimated_remaining(
            Duration::from_nanos(snapshot.completed_job_nanos),
            snapshot.completed,
            PLAN3_INSTANCES,
        )
        .map_or_else(
            || "unavailable".to_owned(),
            |eta| format!("{eta:?}-estimate"),
        );
        let mut stderr = std::io::stderr().lock();
        writeln!(
            stderr,
            "DONE completed={}/{PLAN3_INSTANCES} job={job}/{PLAN3_INSTANCES} fixture={fixture} layer={layer} regime={regime:?} budget=c{budget_cells} class={} instance_elapsed={instance_elapsed:?} total_elapsed={:?} eta={eta}",
            snapshot.completed,
            classification_tag(classification),
            self.started.elapsed(),
        )
        .expect("write Plan 3 DONE");
        stderr.flush().expect("flush Plan 3 progress");
    }

    fn error(
        &self,
        job: usize,
        fixture: &str,
        layer: usize,
        regime: BwdRegime,
        budget_cells: usize,
        instance_elapsed: Duration,
        error: &BackwardSearchError,
    ) {
        let mut stderr = std::io::stderr().lock();
        writeln!(
            stderr,
            "ERROR job={job}/{PLAN3_INSTANCES} fixture={fixture} layer={layer} regime={regime:?} budget=c{budget_cells} instance_elapsed={instance_elapsed:?} total_elapsed={:?} error={error:?}",
            self.started.elapsed(),
        )
        .expect("write Plan 3 ERROR");
        stderr.flush().expect("flush Plan 3 progress");
    }
}

struct IncumbentProgressReporter {
    started: Instant,
    state: Mutex<ProgressState>,
}

impl IncumbentProgressReporter {
    fn new() -> Self {
        Self {
            started: Instant::now(),
            state: Mutex::new(ProgressState::default()),
        }
    }

    fn record_completion(&self, instance_elapsed: Duration) -> ProgressSnapshot {
        let nanos = u64::try_from(instance_elapsed.as_nanos()).unwrap_or(u64::MAX);
        let mut state = self
            .state
            .lock()
            .expect("lock Plan 3 incumbent progress state");
        state.completed_job_nanos = state.completed_job_nanos.saturating_add(nanos);
        state.completed += 1;
        ProgressSnapshot {
            completed: state.completed,
            completed_job_nanos: state.completed_job_nanos,
        }
    }

    fn start(&self, job: IncumbentJob, input: &CorpusLayer) {
        let mut stderr = std::io::stderr().lock();
        writeln!(
            stderr,
            "PREP START job={}/{PLAN3_INCUMBENT_JOBS} fixture={} layer={} regime={:?} total_elapsed={:?}",
            incumbent_job_id(job),
            input.fixture,
            input.layer_index,
            job.regime,
            self.started.elapsed(),
        )
        .expect("write Plan 3 PREP START");
        stderr.flush().expect("flush Plan 3 incumbent progress");
    }

    fn done(
        &self,
        job: IncumbentJob,
        input: &CorpusLayer,
        instance_elapsed: Duration,
        available: bool,
    ) {
        let snapshot = self.record_completion(instance_elapsed);
        let eta = estimated_remaining_with_width(
            Duration::from_nanos(snapshot.completed_job_nanos),
            snapshot.completed,
            PLAN3_INCUMBENT_JOBS,
            rayon::current_num_threads(),
        )
        .map_or_else(
            || "unavailable".to_owned(),
            |eta| format!("{eta:?}-estimate"),
        );
        let mut stderr = std::io::stderr().lock();
        writeln!(
            stderr,
            "PREP DONE completed={}/{PLAN3_INCUMBENT_JOBS} job={}/{PLAN3_INCUMBENT_JOBS} fixture={} layer={} regime={:?} available={available} instance_elapsed={instance_elapsed:?} total_elapsed={:?} eta={eta}",
            snapshot.completed,
            incumbent_job_id(job),
            input.fixture,
            input.layer_index,
            job.regime,
            self.started.elapsed(),
        )
        .expect("write Plan 3 PREP DONE");
        stderr.flush().expect("flush Plan 3 incumbent progress");
    }
}

fn prepare_incumbents(layers: &[CorpusLayer]) -> Vec<PreparedIncumbent> {
    let jobs = incumbent_jobs(layers);
    let progress = IncumbentProgressReporter::new();
    let prepared = parallel_map_ordered(&jobs, |&job| {
        let input = &layers[job.corpus_layer];
        let started = Instant::now();
        progress.start(job, input);
        let incumbent = build_incumbent(input, job.regime);
        progress.done(job, input, started.elapsed(), incumbent.is_some());
        PreparedIncumbent { job, incumbent }
    });
    assert_eq!(prepared.len(), PLAN3_INCUMBENT_JOBS);
    prepared
}

fn run_budget_group(
    job_base: usize,
    progress: &ProgressReporter,
    fixture: &str,
    layer: usize,
    regime: BwdRegime,
    run: impl Fn(usize) -> Result<InstanceResult, BackwardSearchError> + Sync,
) -> Vec<(usize, Result<InstanceResult, BackwardSearchError>)> {
    let mut results = [2usize, 3, 4]
        .into_par_iter()
        .enumerate()
        .map(|(offset, budget_cells)| {
            let job = job_base + offset;
            let started = Instant::now();
            progress.start(job, fixture, layer, regime, budget_cells);
            let result = run(budget_cells);
            match &result {
                Ok(instance) => progress.done(
                    job,
                    fixture,
                    layer,
                    regime,
                    budget_cells,
                    started.elapsed(),
                    &instance.classification,
                ),
                Err(error) => progress.error(
                    job,
                    fixture,
                    layer,
                    regime,
                    budget_cells,
                    started.elapsed(),
                    error,
                ),
            }
            (budget_cells, result)
        })
        .collect::<Vec<_>>();
    results.sort_by_key(|(budget, _)| *budget);
    results
}

fn resolve_plan3_audit_path(output: &std::path::Path) -> std::path::PathBuf {
    if output.is_absolute() {
        return output.to_owned();
    }
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("gkr_eval_isa must be inside the repository root")
        .join(output)
}

fn write_plan3_audit(output: &std::path::Path, markdown: &str) {
    let output = resolve_plan3_audit_path(output);
    if let Some(parent) = output.parent()
        && !parent.as_os_str().is_empty()
    {
        std::fs::create_dir_all(parent).expect("create Plan 3 audit directory");
    }
    std::fs::write(&output, markdown).expect("write Plan 3 audit");
}

#[test]
#[ignore = "Plan 3 full 342-instance release experiment"]
fn full_plan3_backward_paging_search_experiment() {
    let corpus_layers = build_corpus_layers();
    let prepared_incumbents = prepare_incumbents(&corpus_layers);
    let mut prepared = prepared_incumbents.into_iter();
    let mut report = ExperimentReport::default();
    let progress = ProgressReporter::new();
    let mut next_job = 1usize;
    for (corpus_layer, input) in corpus_layers.iter().enumerate() {
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            let prepared_incumbent = prepared
                .next()
                .expect("Plan 3 incumbent prepass must cover every group");
            assert_eq!(
                prepared_incumbent.job,
                IncumbentJob {
                    corpus_layer,
                    regime,
                }
            );
            let distilled = distill(&input.layer, regime, &input.cross, None);
            let budget_results = run_budget_group(
                next_job,
                &progress,
                input.fixture,
                input.layer_index,
                regime,
                |budget_cells| {
                    run_instance(
                        input.fixture,
                        input.layer_index,
                        &input.layer,
                        &distilled,
                        input.trace_len,
                        budget_cells,
                        (budget_cells == 4)
                            .then_some(prepared_incumbent.incumbent.as_ref())
                            .flatten(),
                    )
                },
            );
            next_job += 3;
            for (budget_cells, result) in budget_results {
                report.push(result.unwrap_or_else(|error| {
                    panic!(
                        "Plan 3 instance must classify or succeed: {} L{} {regime:?} c{budget_cells}: {error:?}",
                        input.fixture, input.layer_index,
                    )
                }));
            }
        }
    }
    assert!(prepared.next().is_none());
    assert_eq!(next_job, 343);
    assert_eq!(report.instances.len(), PLAN3_INSTANCES);
    assert!(
        report
            .instances
            .iter()
            .all(|instance| instance.certificate_failures() == 0)
    );
    let markdown = render_markdown(&report);
    let output = std::env::var("GKR_PLAN3_REPORT")
        .expect("GKR_PLAN3_REPORT must name the ignored audit output");
    write_plan3_audit(std::path::Path::new(&output), &markdown);
}

#[test]
#[ignore = "Plan 3 add_sub exact-paging release smoke"]
fn plan3_add_sub_release_smoke() {
    let fixture = "add_sub_lui_auipc_mop_layout_gkr.json";
    let artifact = common::load_fixture(fixture);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact)
        .unwrap_or_else(|error| panic!("[{fixture}] lower DAG: {error}"));
    let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
        .next()
        .expect("add_sub has a backward layer");
    let distilled = distill(&layer, BwdRegime::Ext, &cross, None);
    let current =
        gkr_eval_isa::bwd::engine::cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, 16);
    let incumbent = current
        .fragment_order
        .zip(current.plan)
        .map(|(order, plan)| AcceptedIncumbent { order, plan })
        .expect("add_sub Ext c4 ships a fragment-plan incumbent");
    let result = run_instance(
        fixture,
        layer_index,
        &layer,
        &distilled,
        dag.globals.trace_len,
        4,
        Some(&incumbent),
    )
    .expect("add_sub Ext c4 must classify or succeed");
    assert_eq!(result.key.budget_cells, 4);
    assert_eq!(result.key.regime, BwdRegime::Ext);
    assert!(matches!(
        result.incumbent.classification,
        ArmClassification::Searched
    ));
    assert!(result.incumbent.score.is_some());
    assert_eq!(result.certificate_failures(), 0);
}

#[test]
#[ignore = "Plan 3 inits-and-teardowns c2 classification regression"]
fn plan3_inits_and_teardowns_r0_c2_classifies() {
    let fixture = "inits_and_teardowns_preprocessed_layout_gkr.json";
    let artifact = common::load_fixture(fixture);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact)
        .unwrap_or_else(|error| panic!("[{fixture}] lower DAG: {error}"));
    let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
        .find(|(layer_index, _, _)| *layer_index == 0)
        .expect("inits-and-teardowns has backward layer zero");
    let distilled = distill(&layer, BwdRegime::R0, &cross, None);
    let (classification, problem) =
        build_backward_search_problem(&layer, &distilled, dag.globals.trace_len, 2)
            .expect("inits-and-teardowns c2 problem must classify");
    assert!(matches!(
        classification,
        ProblemClassification::Trivial { .. }
    ));
    let problem = problem.expect("trivial c2 problem retains its replay surface");
    assert!(problem.stream_reductions);
    assert!(
        problem
            .demands
            .iter()
            .all(|demand| matches!(layer.exprs[demand.expr.0 as usize], Expr::Source(_)))
    );
    let exact = match solve_exact_paging(&problem.demands, MAX_PAGER_STATES)
        .expect("trivial c2 paging solve")
    {
        PagerOutcome::Solved(exact) => exact,
        PagerOutcome::SolverCapped { .. } => panic!("trivial c2 paging must not cap"),
    };
    let candidate = compile_and_certify_paging(&distilled, &problem, &exact, 0)
        .expect("trivial c2 all-bypass replay must consume its logical stream");
    let decoded = decode(&candidate.compiled.encoded).expect("decode c2 replay lanes");
    assert_eq!(decoded, candidate.compiled.compiled.program);
    assert_eq!(
        encode(&decoded).expect("re-encode c2 replay lanes"),
        candidate.compiled.encoded
    );
    assert_eq!(
        candidate.certificate.predicted_read_cost,
        candidate.certificate.realized_read_cost
    );
    assert_bwd_value_parity(&candidate.compiled.compiled, &distilled, &layer);
    let result = run_instance(
        fixture,
        layer_index,
        &layer,
        &distilled,
        dag.globals.trace_len,
        2,
        None,
    )
    .expect("inits-and-teardowns L0 R0 c2 must classify or succeed");
    assert_eq!(result.key.budget_cells, 2);
    assert_eq!(result.key.regime, BwdRegime::R0);
}

#[test]
#[ignore = "Plan 3 unsigned-mul-div Ext c4 replay regression"]
fn plan3_unsigned_mul_div_l1_ext_c4_classifies() {
    let fixture = "unsigned_mul_div_layout_gkr.json";
    let artifact = common::load_fixture(fixture);
    let dag = cs::gkr_compiler::dag_ir::lower_dag(&artifact)
        .unwrap_or_else(|error| panic!("[{fixture}] lower DAG: {error}"));
    let (layer_index, layer, cross) = common::layers_with_bwd_roots(fixture)
        .find(|(layer_index, _, _)| *layer_index == 1)
        .expect("unsigned-mul-div has backward layer one");
    let distilled = distill(&layer, BwdRegime::Ext, &cross, None);
    let current =
        gkr_eval_isa::bwd::engine::cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, 16);
    let incumbent = current
        .fragment_order
        .zip(current.plan)
        .map(|(order, plan)| AcceptedIncumbent { order, plan });
    assert!(
        incumbent.is_some(),
        "fixture must expose its production incumbent"
    );
    let result = run_instance(
        fixture,
        layer_index,
        &layer,
        &distilled,
        dag.globals.trace_len,
        4,
        incumbent.as_ref(),
    )
    .expect("unsigned-mul-div L1 Ext c4 must classify or succeed");
    assert_eq!(result.key.budget_cells, 4);
    assert_eq!(result.key.regime, BwdRegime::Ext);
    assert!(matches!(
        result.incumbent.classification,
        ArmClassification::UnavailableIncumbent
    ));
    for arm in [&result.arm1, &result.arm2, &result.arm3, &result.arm4] {
        assert!(matches!(arm.classification, ArmClassification::Searched));
        assert!(arm.score.is_some());
    }
    assert_eq!(result.certificate_failures(), 0);
    let report = ExperimentReport::from_instances(vec![result]);
    assert_eq!(report.incumbent_comparable, 0);
    assert_eq!(report.counts_by_budget[&4].matching_incumbent, 0);
    assert_eq!(report.paged_computed, 1);
}

#[test]
fn backward_uncached_and_replay_share_leaf_only_fused_stream() {
    let mut layer = common::synthetic_fma_compound_products_layer(1, 2).layer;
    let products = layer
        .exprs
        .iter()
        .enumerate()
        .filter_map(|(index, expr)| matches!(expr, Expr::Mul(_)).then_some(ExprId(index as u32)))
        .collect::<Vec<_>>();
    let direct = products
        .iter()
        .copied()
        .find(|product| match &layer.exprs[product.0 as usize] {
            Expr::Mul(children) => children
                .iter()
                .all(|child| matches!(layer.exprs[child.0 as usize], Expr::Source(_))),
            _ => false,
        })
        .expect("synthetic FMA layer has a direct product");
    let compound = products
        .iter()
        .copied()
        .find(|product| match &layer.exprs[product.0 as usize] {
            Expr::Mul(children) => children
                .iter()
                .any(|child| matches!(layer.exprs[child.0 as usize], Expr::Add(_))),
            _ => false,
        })
        .expect("synthetic FMA layer has a compound product");
    let repeated_add = layer
        .exprs
        .iter_mut()
        .find_map(|expr| match expr {
            Expr::Add(children) if children.contains(&direct) && children.contains(&compound) => {
                Some(children)
            }
            _ => None,
        })
        .expect("synthetic FMA layer has an Add containing both product kinds");
    repeated_add.extend([direct, compound]);
    let distilled = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
    let replay_domain = gkr_eval_isa::bwd::distill::distilled_site_domain(&distilled)
        .into_iter()
        .map(|site| site.value)
        .collect::<std::collections::BTreeSet<_>>();
    assert!(replay_domain.contains(&direct));
    assert!(replay_domain.contains(&compound));
    let uncached =
        gkr_eval_isa::eval_plan::compile_backward_fragments_uncached(&distilled, None, 4, true)
            .expect("streaming mixed FMA reference compile");
    let entries = uncached
        .trace
        .events
        .iter()
        .filter_map(|event| match event {
            gkr_eval_isa::bwd::trace::BwdEvent::Serve { fp, .. }
                if replay_domain.contains(&fp.value) =>
            {
                Some(gkr_eval_isa::bwd::plan::PlanEntry {
                    fp: *fp,
                    action: gkr_eval_isa::bwd::plan::PlanAction::Bypass,
                })
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        entries
            .iter()
            .all(|entry| entry.fp.value != direct && entry.fp.value != compound)
    );
    let replay_plan = gkr_eval_isa::bwd::plan::BwdOccurrencePlan {
        epoch: uncached.trace.epoch,
        entries_fnv: gkr_eval_isa::bwd::plan::plan_entries_fnv(&entries),
        stream_reductions: true,
        entries,
    };
    let replayed = gkr_eval_isa::eval_plan::compile_backward_fragments_replayed(
        &distilled,
        &replay_plan,
        None,
        4,
    )
    .expect("streaming mixed FMA reference must replay exactly");
    assert_eq!(replayed.encoded, uncached.encoded);
    assert_eq!(replayed.compiled.stats_ext, uncached.compiled.stats_ext);
    let (_, problem) = build_backward_search_problem(&layer, &distilled, 8, 4)
        .expect("mixed direct/compound FMA problem must build");
    let problem = problem.expect("mixed direct/compound FMA problem retains its replay surface");
    assert!(
        problem
            .demands
            .iter()
            .all(|demand| matches!(layer.exprs[demand.expr.0 as usize], Expr::Source(_)))
    );
    assert!(
        problem
            .all_domain_serves
            .iter()
            .all(|serve| serve.value != direct && serve.value != compound)
    );
    let exact = match solve_exact_paging(&problem.demands, MAX_PAGER_STATES)
        .expect("mixed direct/compound FMA paging solve")
    {
        PagerOutcome::Solved(exact) => exact,
        PagerOutcome::SolverCapped { .. } => panic!("small mixed FMA paging must not cap"),
    };
    let candidate = compile_and_certify_paging(&distilled, &problem, &exact, 0)
        .expect("mixed direct/compound FMA replay must consume its logical stream");
    let decoded = decode(&candidate.compiled.encoded).expect("decode mixed FMA replay lanes");
    assert_eq!(decoded, candidate.compiled.compiled.program);
    assert_eq!(
        encode(&decoded).expect("re-encode mixed FMA replay lanes"),
        candidate.compiled.encoded
    );
    assert_eq!(
        candidate.certificate.predicted_read_cost,
        candidate.certificate.realized_read_cost
    );
    assert_bwd_value_parity(&candidate.compiled.compiled, &distilled, &layer);
}

#[test]
fn paging_replay_has_r0_and_ext_cpu_value_parity_at_c4() {
    for (layer, distilled, candidate) in certified_r0_and_ext_candidates() {
        assert_bwd_value_parity(&candidate.compiled.compiled, &distilled, &layer);
    }
}

#[test]
fn paging_replay_encoded_lanes_decode_and_round_trip_exactly() {
    for (_, _, candidate) in certified_r0_and_ext_candidates() {
        let decoded = decode(&candidate.compiled.encoded).expect("decode certified lanes");
        assert_eq!(decoded, candidate.compiled.compiled.program);
        assert_eq!(
            encode(&decoded).expect("re-encode certified program"),
            candidate.compiled.encoded
        );
    }
}

fn certified_r0_and_ext_candidates() -> Vec<(DagLayer, DistilledLayer, CertifiedBackwardCandidate)>
{
    [BwdRegime::R0, BwdRegime::Ext]
        .into_iter()
        .map(|regime| {
            let layer = synthetic_shared_read_layer();
            let distilled = distill(&layer, regime, &HashMap::new(), None);
            let (_, problem) = build_backward_search_problem(&layer, &distilled, 8, 4).unwrap();
            let problem = problem.expect("synthetic shared-read problem");
            let exact = match solve_exact_paging(&problem.demands, MAX_PAGER_STATES).unwrap() {
                PagerOutcome::Solved(exact) => exact,
                outcome => panic!("expected solved paging problem, got {outcome:?}"),
            };
            let candidate = compile_and_certify_paging(&distilled, &problem, &exact, 0).unwrap();
            (layer, distilled, candidate)
        })
        .collect()
}

fn synthetic_shared_read_layer() -> DagLayer {
    DagLayer {
        sources: (0..3).map(read_source).collect(),
        exprs: vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Source(SourceId(2)),
            Expr::Mul(vec![ExprId(0), ExprId(1)]),
            Expr::Mul(vec![ExprId(0), ExprId(2)]),
        ],
        batching: BatchingOrder {
            roots: vec![RootId(0), RootId(1)],
        },
        roots: vec![claim_root(ExprId(3), 0), claim_root(ExprId(4), 1)],
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
