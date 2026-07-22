//! Pure symbolic evaluation planning between `dag_ir` and the concrete VM ISA.
//!
//! The planner owns continuation-driven traversal, stable structural sites,
//! cache-oracle decisions, accumulator stashes, instruction packing, and
//! concrete placement before action-aware forward-VM binding.

mod artifact;
mod backward;
mod backward_artifact;
pub mod backward_search;
mod concrete;
mod fitness;
mod genome;
mod identity;
mod interp;
mod packed;
mod packed_interp;
mod search;
mod search_driver;

#[cfg(test)]
mod search_driver_visibility_tests {
    use super::search_driver::StableRng;

    #[test]
    fn stable_rng_constructor_is_visible_to_sibling_modules() {
        let mut first = StableRng::new(17);
        let mut second = StableRng::new(17);
        assert_eq!(first.next_u64(), second.next_u64());
    }
}

pub use artifact::{
    CompiledEvaluationCircuit, CompiledEvaluationLayer, DomainCertificate, EvaluationArtifactError,
    EvaluationCompileError, EvaluationGenomeArtifact, EvaluationGenomeCircuitArtifact,
    EvaluationLayoutVariant, EvaluationPass, ForwardActionProvenance, ForwardActionRecord,
    SearchProvenance, compile_circuit_with_evaluation_genomes,
    compile_layer_with_evaluation_genome, load_evaluation_genome_artifact,
    produce_searched_evaluation_genome_artifact,
};
pub use backward::{
    BackwardEvaluationError, BackwardSymbolicEvaluation, CompiledBackwardEvaluation,
    compile_backward_fragments_replayed, compile_backward_fragments_uncached,
    elaborate_backward_fragments_uncached,
};
pub use backward_artifact::{
    BackwardArtifactCoordinate, BackwardArtifactError, BackwardEvaluationCircuitArtifact,
    BackwardLayerArtifact, BackwardPagingCertificateArtifact, BackwardPlanArtifact,
    BackwardProblemCertificate, BackwardRegimeArtifact, BackwardRegimeChainProgress,
    BackwardScoreArtifact, CanonicalU128, SourceCostArtifact, backward_problem_certificate,
    capture_backward_plan_artifact, compile_backward_plan_artifact,
    load_backward_evaluation_artifact, produce_backward_regime_chain,
    produce_backward_regime_chain_with_progress, publish_backward_evaluation_artifact,
    select_backward_plan,
};
pub use concrete::{
    ConcreteBindError, ConcreteBindingStats, ConcreteEvalProgram, ConcreteTerminal,
    PlacementTelemetry, bind_packed_plan, bind_packed_plan_with_actions,
    disassemble_concrete_eval_program, validate_concrete_eval_program,
};
pub use fitness::{
    EvaluationGenome, EvaluationUnit, EvaluationUnitKey, FitnessError, PlacementStatus,
    PlanFitness, PlanSearchContext, ScoredEvaluation, adapt_forward_relations, fitness_key,
};
pub use genome::{
    GenomeOracle, GenomeOracleError, StagingPair, StructuralSiteIndex, ValueCostProfile,
};
pub use identity::{
    IdentityError, ValueFingerprint, structural_fingerprints, validate_structural_identity,
};
pub use interp::{PlanExecution, PlanInterpError, RootObservation, interpret_plan};
pub use packed::{PackConfig, PackError, PackedEvalOp, PackedEvalPlan, PackedStats, pack_plan};
pub use packed_interp::interpret_packed_plan;
pub use search::{
    MutationSearchConfig, MutationSearchError, MutationSearchOutcome, SearchTelemetry,
    StagingRefinementOutcome, mutation_search, staging_refinement,
};

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::bwd::plan::{PlanAction, PlanRun};
use crate::bwd::trace::{BwdEvent, BwdFingerprint, BwdServeKind, BwdServedFrom};
use crate::fwd::isa::{MAX_CELL, Sign};
use cs::gkr_compiler::dag_ir::{
    DagLayer, Expr, ExprId, FieldKind, Root, RootId, RootOrigin, SinkInfo, SourceKind, join,
};

const BABYBEAR_NEG_ONE: u32 = 0x7800_0001 - 1;

pub(crate) const LANES_PER_STORAGE_CELL: usize = 4;

pub(crate) fn budget_lanes_from_cells(budget_cells: usize) -> Option<usize> {
    if budget_cells == 0 {
        return None;
    }
    budget_cells
        .checked_mul(LANES_PER_STORAGE_CELL)
        .filter(|&budget_lanes| budget_lanes <= MAX_CELL as usize)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ReductionOp {
    Add,
    Mul,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct RootKey {
    pub expr: ValueFingerprint,
    pub materialize: Option<SinkInfo>,
    pub claim_origin: Option<RootOrigin>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct PathStep {
    pub parent: ValueFingerprint,
    pub operation: ReductionOp,
    pub child: ValueFingerprint,
    /// Canonical ordinal among children with the same structural fingerprint.
    pub duplicate_ordinal: u32,
}

/// Stable identity of an actual structural demand. `path` is canonical and is
/// independent of the order in which commutative children are executed.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct SiteId {
    pub root: RootKey,
    pub path: Vec<PathStep>,
    pub value: ValueFingerprint,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ValueRef {
    /// Arena-local handle used to bind the plan back to this `DagLayer`.
    pub expr: ExprId,
    /// Stable identity used by planning/search provenance.
    pub fingerprint: ValueFingerprint,
    pub field: FieldKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TempId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TempRef {
    pub id: TempId,
    pub field: FieldKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Operand {
    /// Direct source/leaf use. A `Read` source contributes DRAM traffic.
    Source(ValueRef),
    /// Future cache-aware elaboration serves hits through this variant.
    Resident(ValueRef),
    /// Single-consumer accumulator/operand stash.
    Temp(TempRef),
    /// Synthetic normalized field unit; it is never a DAG read or cache value.
    Unit { negative: bool },
    /// Backward-only scalar-pure descriptor. It is always extension-field and
    /// is bound only by the closed backward source path.
    BackwardSpecial { desc: u16 },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CacheStoreFrom {
    /// Store the just-computed accumulator value (`Mov DstFromAcc`).
    Acc,
    /// Load a direct source into residency before consuming it (`Mov DstFromSrc`).
    Source,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MaterializeFrom {
    /// The expression has just been computed into the accumulator.
    Acc,
    /// A direct source is available without disturbing the accumulator.
    Source(ValueRef),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalOp {
    AccInit(Operand),
    AccAdd {
        sign: Sign,
        operand: Operand,
    },
    AccMul(Operand),
    AccFma {
        sign: Sign,
        lhs: Operand,
        rhs: Operand,
    },
    AccNeg,
    SaveAcc(TempRef),
    /// Reserved vocabulary for the cache-aware elaborator.
    CacheStore {
        value: ValueRef,
        from: CacheStoreFrom,
    },
    /// Reserved vocabulary for the cache-aware elaborator.
    CacheDrop(ValueRef),
    Commit {
        root_id: RootId,
        root: RootKey,
        sink: SinkInfo,
        from: MaterializeFrom,
    },
    ReturnAcc {
        root: RootKey,
    },
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PlanStats {
    /// Width-weighted real-DRAM source reads (Base=1, Ext=4).
    pub dram_read_lanes: usize,
    /// Accumulator Add/Mul/FMA operations. FMA counts as one plan operation.
    pub arithmetic_ops: usize,
    pub stash_stores: usize,
    pub stash_loads: usize,
    pub cache_stores: usize,
    pub cache_drops: usize,
    pub cache_hits: usize,
    /// Peak combined width of saved temporaries and resident cache values.
    pub peak_live_lanes: usize,
    pub commits: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ExprAttribution {
    /// Actual structural demands reached after cache-hit cone pruning.
    pub demands: usize,
    /// Demands reached as children of an additive reduction.
    pub additive_demands: usize,
    /// Full evaluations started because the value was not resident.
    pub computations: usize,
    pub resident_hits: usize,
    /// Accumulator arithmetic emitted while evaluating this reduction.
    pub arithmetic_ops: usize,
    /// Times this expression initialized a reduction accumulator.
    pub accumulator_seeds: usize,
    /// Product boundaries eliminated into a consuming FMA.
    pub fma_fusions: usize,
    /// Effective binary products added only after evaluating a non-ready operand cone.
    pub unready_product_adds: usize,
    /// Effective binary product results consumed from residency instead of fused.
    pub resident_product_adds: usize,
    /// Ready products kept explicit because their result had to survive/materialize.
    pub preserved_product_adds: usize,
    /// Single-factor product boundaries eliminated into signed Add.
    pub signed_add_fusions: usize,
    pub cache_stores: usize,
    pub materializations: usize,
}

/// Realized cache-policy replay retained for differential diagnostics. Unlike a
/// genome, this records the traversal that survived cache-hit cone pruning.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlanResidencyEventKind {
    Demand { hit: bool },
    Admit,
    Evict,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlanResidencyEvent {
    pub site: Option<SiteId>,
    pub value: ValueRef,
    pub kind: PlanResidencyEventKind,
    pub residents_after: Vec<ValueRef>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalPlan {
    pub ops: Vec<EvalOp>,
    /// Symbolic scratchpad budget used during elaboration. Packing uses it to
    /// reject metadata motion that would extend physical liveness past capacity.
    pub budget_lanes: usize,
    /// Sites in the authoritative traversal order. Cache-aware traversal may
    /// skip descendants on a hit; their structural IDs remain pre-enumerable.
    pub sites: Vec<SiteId>,
    pub stats: PlanStats,
    /// Per-DAG-expression execution attribution for diagnostics and fitness
    /// analysis. It has no effect on packing or concrete emission.
    pub attribution: BTreeMap<ExprId, ExprAttribution>,
    pub residency_events: Vec<PlanResidencyEvent>,
}

/// Future oracle input. Entry residency is factual elaborator state; the oracle
/// supplies only ranked desired survivors.
#[derive(Clone, Copy, Debug)]
pub struct CacheStateView<'a> {
    pub residents: &'a [ValueRef],
    /// Resident values temporarily protected because an emitted instruction has
    /// not consumed their already-selected operand yet.
    pub pinned: &'a [ValueFingerprint],
    pub resident_lanes: usize,
    pub transient_lanes: usize,
    pub budget_lanes: usize,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct RetentionPreference {
    pub value: ValueFingerprint,
    pub priority: f64,
}

#[derive(Clone, Debug, PartialEq)]
pub struct StagingPreference {
    /// Natural structural demand to compute before the current boundary.
    pub site: SiteId,
    /// Residency priority while the staged value waits for that demand.
    pub priority: f64,
}

pub trait CacheOracle {
    fn stage_before(&mut self, _boundary: &SiteId) -> Vec<StagingPreference> {
        Vec::new()
    }

    fn desired_after(
        &mut self,
        site: &SiteId,
        entry: CacheStateView<'_>,
    ) -> Vec<RetentionPreference>;
}

/// Enumerate the complete structural genome domain for `roots` without
/// executing them. Unlike [`EvalPlan::sites`], this set is unaffected by root
/// execution order, cache hits, or child scheduling choices.
///
/// The return type is intentionally unordered: a genome should bind decisions
/// by [`SiteId`], then separately choose a deterministic serialization if it
/// needs a dense vector representation.
pub fn enumerate_structural_sites(
    layer: &DagLayer,
    roots: &[RootId],
) -> Result<HashSet<SiteId>, PlanError> {
    let fingerprints = structural_fingerprints(layer)?;
    let mut sites = HashSet::new();
    for &root_id in roots {
        let root = layer
            .roots
            .get(root_id.0 as usize)
            .ok_or(PlanError::RootOutOfBounds(root_id))?;
        let root_key = root_key(root.expr, root, &fingerprints)?;
        enumerate_site_cone(
            layer,
            &fingerprints,
            root.expr,
            &root_key,
            &mut Vec::new(),
            &mut sites,
        )?;
    }
    Ok(sites)
}

#[derive(Default)]
pub struct NoCacheOracle;

impl CacheOracle for NoCacheOracle {
    fn desired_after(
        &mut self,
        _site: &SiteId,
        _entry: CacheStateView<'_>,
    ) -> Vec<RetentionPreference> {
        Vec::new()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum PlanError {
    Identity(IdentityError),
    FieldCount {
        expected: usize,
        actual: usize,
    },
    RootOutOfBounds(RootId),
    EmptyReduction(ExprId),
    ExpectedSource(ExprId),
    TempConsumedTwice(TempId),
    LiveTempAtEnd(TempId),
    DuplicateSinkRoot(RootId),
    SinkRootWithoutMaterialization(RootId),
    ResidentWithPendingSinks(ExprId),
    UnmaterializedSinks(Vec<RootId>),
    InvalidPriority {
        site: Box<SiteId>,
        priority: f64,
    },
    InvalidStaging {
        boundary: Box<SiteId>,
        staged: Box<SiteId>,
    },
    DuplicateStaging(SiteId),
    UnconsumedStaging(Vec<SiteId>),
    BudgetExceeded {
        budget_lanes: usize,
        required_transient_lanes: usize,
    },
    ReplayDiverged {
        at_entry: usize,
    },
    ReplayNotFullyConsumed {
        at_entry: usize,
    },
    ReplayRefused {
        value: ExprId,
        need: usize,
    },
    ReplayInfeasible,
}

impl From<IdentityError> for PlanError {
    fn from(value: IdentityError) -> Self {
        Self::Identity(value)
    }
}

/// Elaborate selected roots with no ephemeral residency: every demand walks its
/// expression cone again. `expr_fields` is arena-indexed and must already include
/// any cross-layer/fold field overrides known by the caller.
pub fn elaborate_uncached(
    layer: &DagLayer,
    expr_fields: &[FieldKind],
    roots: &[RootId],
) -> Result<EvalPlan, PlanError> {
    let sink_roots = materialized_subset(layer, roots)?;
    elaborate_internal(
        layer,
        expr_fields,
        roots,
        &sink_roots,
        usize::MAX,
        None,
        false,
    )
}

/// Elaborate with oracle-driven ephemeral residency. Preferences are queried at
/// site entry and inherited by descendant evaluations, so a parent can request
/// that a subexpression produced anywhere in its cone survive until parent exit.
pub fn elaborate_with_oracle(
    layer: &DagLayer,
    expr_fields: &[FieldKind],
    roots: &[RootId],
    budget_lanes: usize,
    oracle: &mut dyn CacheOracle,
) -> Result<EvalPlan, PlanError> {
    let sink_roots = materialized_subset(layer, roots)?;
    elaborate_internal(
        layer,
        expr_fields,
        roots,
        &sink_roots,
        budget_lanes,
        Some(oracle),
        false,
    )
}

fn materialized_subset(layer: &DagLayer, roots: &[RootId]) -> Result<Vec<RootId>, PlanError> {
    let mut sinks = Vec::new();
    for &root_id in roots {
        let root = layer
            .roots
            .get(root_id.0 as usize)
            .ok_or(PlanError::RootOutOfBounds(root_id))?;
        if root.materialize.is_some() {
            sinks.push(root_id);
        }
    }
    Ok(sinks)
}

/// Elaborate driver roots while treating `sink_roots` as eager materialization
/// obligations. This is the forward-pass entry point when cache roots can be
/// produced inside another root's expression cone.
pub fn elaborate_with_oracle_and_sinks(
    layer: &DagLayer,
    expr_fields: &[FieldKind],
    roots: &[RootId],
    sink_roots: &[RootId],
    budget_lanes: usize,
    oracle: &mut dyn CacheOracle,
) -> Result<EvalPlan, PlanError> {
    elaborate_internal(
        layer,
        expr_fields,
        roots,
        sink_roots,
        budget_lanes,
        Some(oracle),
        false,
    )
}

/// Diagnostic variant of [`elaborate_with_oracle_and_sinks`] that retains the
/// realized demand/admission/eviction replay. Normal scoring keeps this disabled
/// to avoid cloning resident snapshots for every candidate.
pub fn elaborate_with_oracle_and_sinks_traced(
    layer: &DagLayer,
    expr_fields: &[FieldKind],
    roots: &[RootId],
    sink_roots: &[RootId],
    budget_lanes: usize,
    oracle: &mut dyn CacheOracle,
) -> Result<EvalPlan, PlanError> {
    elaborate_internal(
        layer,
        expr_fields,
        roots,
        sink_roots,
        budget_lanes,
        Some(oracle),
        true,
    )
}

fn elaborate_internal(
    layer: &DagLayer,
    expr_fields: &[FieldKind],
    roots: &[RootId],
    sink_roots: &[RootId],
    budget_lanes: usize,
    oracle: Option<&mut dyn CacheOracle>,
    trace_residency: bool,
) -> Result<EvalPlan, PlanError> {
    if expr_fields.len() != layer.exprs.len() {
        return Err(PlanError::FieldCount {
            expected: layer.exprs.len(),
            actual: expr_fields.len(),
        });
    }
    let fingerprints = structural_fingerprints(layer)?;
    let mut pending_sinks = BTreeMap::<ExprId, Vec<SinkObligation>>::new();
    let mut seen_sink_roots = HashSet::new();
    for &root_id in sink_roots {
        if !seen_sink_roots.insert(root_id) {
            return Err(PlanError::DuplicateSinkRoot(root_id));
        }
        let root = layer
            .roots
            .get(root_id.0 as usize)
            .ok_or(PlanError::RootOutOfBounds(root_id))?;
        let Some(sink) = root.materialize.clone() else {
            return Err(PlanError::SinkRootWithoutMaterialization(root_id));
        };
        pending_sinks
            .entry(root.expr)
            .or_default()
            .push(SinkObligation {
                root_id,
                root: root_key(root.expr, root, &fingerprints)?,
                sink,
            });
    }
    let mut elaborator = Elaborator {
        layer,
        expr_fields,
        fingerprints,
        plan: EvalPlan {
            ops: Vec::new(),
            budget_lanes,
            sites: Vec::new(),
            stats: PlanStats::default(),
            attribution: BTreeMap::new(),
            residency_events: Vec::new(),
        },
        next_temp: 0,
        live_temps: HashMap::new(),
        live_lanes: 0,
        residents: BTreeMap::new(),
        replay_logically_retired: BTreeSet::new(),
        pinned: BTreeSet::new(),
        resident_lanes: 0,
        budget_lanes,
        cache_policy: oracle.map_or(ElaborationCachePolicy::None, ElaborationCachePolicy::Ranked),
        trace_residency,
        pending_sinks,
        staged_demands: Vec::new(),
        backward_demand: None,
        backward_stream_reductions: None,
    };
    for &root_id in roots {
        elaborator.elaborate_root(root_id)?;
    }
    if let Some((&id, _)) = elaborator.live_temps.iter().next() {
        return Err(PlanError::LiveTempAtEnd(id));
    }
    if !elaborator.pending_sinks.is_empty() {
        let mut pending = elaborator
            .pending_sinks
            .values()
            .flatten()
            .map(|obligation| obligation.root_id)
            .collect::<Vec<_>>();
        pending.sort_by_key(|root| root.0);
        return Err(PlanError::UnmaterializedSinks(pending));
    }
    if !elaborator.staged_demands.is_empty() {
        return Err(PlanError::UnconsumedStaging(
            elaborator
                .staged_demands
                .into_iter()
                .map(|(site, _)| site)
                .collect(),
        ));
    }
    Ok(elaborator.plan)
}

/// Backward-only fragment driver. The public adapter validates and schedules
/// fragments, then this keeps every expression cone on the established
/// [`Elaborator::eval_expr`] walker with residency disabled.
pub(super) fn elaborate_backward_fragments_driver(
    layer: &DagLayer,
    root_id: RootId,
    expr_fields: &[FieldKind],
    fragments: &[crate::bwd::fragment::FragmentSpec],
    scheduled_fragments: &[usize],
    coefficient_descs: &[Option<u16>],
    acc_init_desc: Option<u16>,
    budget_lanes: usize,
    stream_reductions: bool,
) -> Result<(EvalPlan, Vec<BwdEvent>), PlanError> {
    elaborate_backward_fragments_with_policy(
        layer,
        root_id,
        expr_fields,
        fragments,
        scheduled_fragments,
        coefficient_descs,
        acc_init_desc,
        budget_lanes,
        stream_reductions,
        None,
    )
}

pub(super) fn elaborate_backward_fragments_replayed_driver(
    layer: &DagLayer,
    root_id: RootId,
    expr_fields: &[FieldKind],
    fragments: &[crate::bwd::fragment::FragmentSpec],
    scheduled_fragments: &[usize],
    coefficient_descs: &[Option<u16>],
    acc_init_desc: Option<u16>,
    budget_lanes: usize,
    stream_reductions: bool,
    replay: &mut BackwardReplay,
) -> Result<(EvalPlan, Vec<BwdEvent>), PlanError> {
    elaborate_backward_fragments_with_policy(
        layer,
        root_id,
        expr_fields,
        fragments,
        scheduled_fragments,
        coefficient_descs,
        acc_init_desc,
        budget_lanes,
        stream_reductions,
        Some(replay),
    )
}

#[allow(clippy::too_many_arguments)]
fn elaborate_backward_fragments_with_policy(
    layer: &DagLayer,
    root_id: RootId,
    expr_fields: &[FieldKind],
    fragments: &[crate::bwd::fragment::FragmentSpec],
    scheduled_fragments: &[usize],
    coefficient_descs: &[Option<u16>],
    acc_init_desc: Option<u16>,
    budget_lanes: usize,
    stream_reductions: bool,
    replay: Option<&mut BackwardReplay>,
) -> Result<(EvalPlan, Vec<BwdEvent>), PlanError> {
    if expr_fields.len() != layer.exprs.len() {
        return Err(PlanError::FieldCount {
            expected: layer.exprs.len(),
            actual: expr_fields.len(),
        });
    }
    let root = layer
        .roots
        .get(root_id.0 as usize)
        .ok_or(PlanError::RootOutOfBounds(root_id))?;
    let fingerprints = structural_fingerprints(layer)?;
    let root_key = root_key(root.expr, root, &fingerprints)?;
    let mut elaborator = Elaborator {
        layer,
        expr_fields,
        fingerprints,
        plan: EvalPlan {
            ops: Vec::new(),
            budget_lanes,
            sites: Vec::new(),
            stats: PlanStats::default(),
            attribution: BTreeMap::new(),
            residency_events: Vec::new(),
        },
        next_temp: 0,
        live_temps: HashMap::new(),
        live_lanes: 0,
        residents: BTreeMap::new(),
        replay_logically_retired: BTreeSet::new(),
        pinned: BTreeSet::new(),
        resident_lanes: 0,
        budget_lanes,
        cache_policy: replay.map_or(
            ElaborationCachePolicy::None,
            ElaborationCachePolicy::BackwardReplay,
        ),
        trace_residency: false,
        pending_sinks: BTreeMap::new(),
        staged_demands: Vec::new(),
        backward_demand: Some(BackwardDemandState {
            schedule_pos: 0,
            consumer_stack: Vec::new(),
            events: Vec::new(),
        }),
        backward_stream_reductions: Some(stream_reductions),
    };

    // Mode selection is deliberately explicit. Both boundaries use the same
    // symbolic cone walker; neither silently substitutes the other.
    elaborator.elaborate_backward_fragments(
        &root_key,
        fragments,
        scheduled_fragments,
        coefficient_descs,
        acc_init_desc,
    )?;
    elaborator.finish_backward_replay()?;
    if let Some((&id, _)) = elaborator.live_temps.iter().next() {
        return Err(PlanError::LiveTempAtEnd(id));
    }
    debug_assert!(elaborator.residents.is_empty());
    let demand_events = elaborator
        .backward_demand
        .take()
        .expect("backward fragment elaboration always has demand bookkeeping")
        .events;
    Ok((elaborator.plan, demand_events))
}

struct ChildOccurrence {
    expr: ExprId,
    step: PathStep,
}

fn root_key(
    expr: ExprId,
    root: &Root,
    fingerprints: &[ValueFingerprint],
) -> Result<RootKey, PlanError> {
    let Some(&expr_fingerprint) = fingerprints.get(expr.0 as usize) else {
        return Err(IdentityError::ExprOutOfBounds(expr).into());
    };
    Ok(RootKey {
        expr: expr_fingerprint,
        materialize: root.materialize.clone(),
        claim_origin: root.claim.as_ref().map(|claim| claim.origin.clone()),
    })
}

fn canonical_child_occurrences(
    fingerprints: &[ValueFingerprint],
    parent: ExprId,
    operation: ReductionOp,
    children: &[ExprId],
) -> Vec<ChildOccurrence> {
    let mut canonical: Vec<(ValueFingerprint, ExprId)> = children
        .iter()
        .map(|&child| (fingerprints[child.0 as usize], child))
        .collect();
    canonical.sort_unstable_by_key(|&(fingerprint, expr)| (fingerprint, expr));
    let mut last = None;
    let mut duplicate_ordinal = 0u32;
    canonical
        .into_iter()
        .map(|(fingerprint, expr)| {
            if last == Some(fingerprint) {
                duplicate_ordinal += 1;
            } else {
                last = Some(fingerprint);
                duplicate_ordinal = 0;
            }
            ChildOccurrence {
                expr,
                step: PathStep {
                    parent: fingerprints[parent.0 as usize],
                    operation,
                    child: fingerprint,
                    duplicate_ordinal,
                },
            }
        })
        .collect()
}

/// Resolve a stable descendant path relative to the exact arena expression at
/// its boundary. Looking up by fingerprint alone is insufficient because two
/// structurally equal expressions may have distinct sink obligations.
fn resolve_descendant_expr(
    layer: &DagLayer,
    fingerprints: &[ValueFingerprint],
    mut expr: ExprId,
    steps: &[PathStep],
) -> Option<ExprId> {
    for step in steps {
        let (operation, children) = match layer.exprs.get(expr.0 as usize)? {
            Expr::Add(children) => (ReductionOp::Add, children),
            Expr::Mul(children) => (ReductionOp::Mul, children),
            Expr::Source(_) => return None,
        };
        if operation != step.operation || fingerprints.get(expr.0 as usize) != Some(&step.parent) {
            return None;
        }
        expr = effective_child_occurrences(
            layer,
            canonical_child_occurrences(fingerprints, expr, operation, children),
            operation,
        )
        .into_iter()
        .find(|occurrence| occurrence.step == *step)?
        .expr;
    }
    Some(expr)
}

fn enumerate_site_cone(
    layer: &DagLayer,
    fingerprints: &[ValueFingerprint],
    expr: ExprId,
    root: &RootKey,
    path: &mut Vec<PathStep>,
    sites: &mut HashSet<SiteId>,
) -> Result<(), PlanError> {
    let Some(&value) = fingerprints.get(expr.0 as usize) else {
        return Err(IdentityError::ExprOutOfBounds(expr).into());
    };
    sites.insert(SiteId {
        root: root.clone(),
        path: path.clone(),
        value,
    });
    if layer.resolutions.contains_key(&expr) {
        return Ok(());
    }
    if unit_sign_expr(layer, expr).is_some() {
        return Ok(());
    }

    let (operation, children) = match &layer.exprs[expr.0 as usize] {
        Expr::Source(_) => return Ok(()),
        Expr::Add(children) => (ReductionOp::Add, children),
        Expr::Mul(children) => (ReductionOp::Mul, children),
    };
    if children.is_empty() {
        return Err(PlanError::EmptyReduction(expr));
    }
    for child in effective_child_occurrences(
        layer,
        canonical_child_occurrences(fingerprints, expr, operation, children),
        operation,
    ) {
        path.push(child.step);
        enumerate_site_cone(layer, fingerprints, child.expr, root, path, sites)?;
        path.pop();
    }
    Ok(())
}

struct PreparedOperand {
    operand: Operand,
    value: ValueRef,
    scope: PreferenceMap,
}

enum FmaOperandPreparation {
    Ready(PreparedOperand),
    NeedsEvaluation {
        expr: ExprId,
        value: ValueRef,
        scope: PreferenceMap,
    },
}

enum BinaryFmaPreparation {
    Ready {
        first: PreparedOperand,
        second: PreparedOperand,
    },
    NeedsEvaluation {
        first: PreparedOperand,
        expr: ExprId,
        value: ValueRef,
        scope: PreferenceMap,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReplayResidentState {
    Absent,
    Visible,
    RetiredPinned,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct BackwardDemandOutcome {
    action: Option<PlanAction>,
    was_visible: bool,
    retire_after_select: bool,
}

impl BackwardDemandOutcome {
    fn needs_fresh_admission(self) -> bool {
        self.action == Some(PlanAction::Retain) && !self.was_visible
    }
}

#[derive(Clone)]
struct ResidentEntry {
    value: ValueRef,
    priority: f64,
    /// Plan intervals are keyed by arena identity while the physical resident
    /// is keyed by structural fingerprint. Every alias that retained this
    /// fingerprint owns the cell until its own interval closes.
    replay_owners: BTreeSet<ExprId>,
}

impl ResidentEntry {
    fn replay_closes_at(&self, run: &PlanRun) -> Option<usize> {
        self.replay_owners
            .iter()
            .filter_map(|&owner| run.retention(owner))
            .max()
    }

    fn replay_dead(&self, run: &PlanRun) -> bool {
        self.replay_owners
            .iter()
            .all(|&owner| run.remaining(owner) == 0)
    }

    fn retain_for(&mut self, owner: ExprId, closes_at: usize) {
        self.replay_owners.insert(owner);
        self.priority = self.priority.max(closes_at as f64);
    }
}

struct SinkObligation {
    root_id: RootId,
    root: RootKey,
    sink: SinkInfo,
}

struct StagedEntry {
    value: ValueRef,
    scope: PreferenceMap,
}

/// Closed backward demand bookkeeping. It deliberately lives on the shared
/// elaborator rather than an observer trait so the backward adapter owns the
/// exact demand context its later concrete binding path will consume.
struct BackwardDemandState {
    schedule_pos: u32,
    consumer_stack: Vec<ExprId>,
    events: Vec<BwdEvent>,
}

pub(super) struct BackwardReplay {
    run: PlanRun,
    /// Independent static eligibility from `distilled_site_domain`, never
    /// derived from supplied plan entries. Every actual eligible serve is
    /// dispatched through `PlanRun`, so deleting a value or the entire entry
    /// stream is detected; structurally eliminated boundaries simply never
    /// become actual serves.
    domain: BTreeSet<ExprId>,
}

impl BackwardReplay {
    pub(super) fn new(run: PlanRun, domain: BTreeSet<ExprId>) -> Self {
        Self { run, domain }
    }
}

enum ElaborationCachePolicy<'a> {
    None,
    Ranked(&'a mut dyn CacheOracle),
    BackwardReplay(&'a mut BackwardReplay),
}

type PreferenceMap = BTreeMap<ValueFingerprint, f64>;

struct Elaborator<'a, 'oracle> {
    layer: &'a DagLayer,
    expr_fields: &'a [FieldKind],
    fingerprints: Vec<ValueFingerprint>,
    plan: EvalPlan,
    next_temp: u32,
    live_temps: HashMap<TempId, usize>,
    live_lanes: usize,
    residents: BTreeMap<ValueFingerprint, ResidentEntry>,
    /// Replay hits selected by a closing Bypass remain physically resident
    /// while a pending instruction pins their cell, but are no longer
    /// available to later logical demands.
    replay_logically_retired: BTreeSet<ValueFingerprint>,
    pinned: BTreeSet<ValueFingerprint>,
    resident_lanes: usize,
    budget_lanes: usize,
    cache_policy: ElaborationCachePolicy<'oracle>,
    trace_residency: bool,
    pending_sinks: BTreeMap<ExprId, Vec<SinkObligation>>,
    staged_demands: Vec<(SiteId, StagedEntry)>,
    backward_demand: Option<BackwardDemandState>,
    backward_stream_reductions: Option<bool>,
}

impl Elaborator<'_, '_> {
    fn uses_backward_eliminated_product_stream(&self) -> bool {
        self.backward_demand.is_some()
            && matches!(
                &self.cache_policy,
                ElaborationCachePolicy::None | ElaborationCachePolicy::BackwardReplay(_)
            )
    }

    fn elaborate_backward_fragments(
        &mut self,
        root: &RootKey,
        fragments: &[crate::bwd::fragment::FragmentSpec],
        scheduled_fragments: &[usize],
        coefficient_descs: &[Option<u16>],
        acc_init_desc: Option<u16>,
    ) -> Result<(), PlanError> {
        if let Some(desc) = acc_init_desc {
            self.emit(EvalOp::AccInit(Operand::BackwardSpecial { desc }))?;
        }
        let mut seeded = acc_init_desc.is_some();
        for (schedule_pos, &fragment_index) in scheduled_fragments.iter().enumerate() {
            if let Some(state) = &mut self.backward_demand {
                state.schedule_pos = schedule_pos as u32;
            }
            let fragment = &fragments[fragment_index];
            debug_assert!(!fragment.atoms.is_empty());
            let saved_total = if seeded {
                Some(self.save_acc(FieldKind::Ext)?)
            } else {
                None
            };
            self.eval_expr(fragment.atoms[0], root, &[], &PreferenceMap::new())?;
            for &atom in &fragment.atoms[1..] {
                let product = self.save_acc(FieldKind::Ext)?;
                self.eval_expr(atom, root, &[], &PreferenceMap::new())?;
                self.emit(EvalOp::AccMul(Operand::Temp(product)))?;
            }
            if let Some(desc) = coefficient_descs[fragment_index] {
                self.emit(EvalOp::AccMul(Operand::BackwardSpecial { desc }))?;
            }
            if let Some(total) = saved_total {
                self.emit(EvalOp::AccAdd {
                    sign: Sign::Plus,
                    operand: Operand::Temp(total),
                })?;
            }
            seeded = true;
        }
        self.emit(EvalOp::ReturnAcc { root: root.clone() })
    }

    fn finish_backward_replay(&mut self) -> Result<(), PlanError> {
        if !matches!(
            &self.cache_policy,
            ElaborationCachePolicy::BackwardReplay(_)
        ) {
            return Ok(());
        }
        self.replay_drop_expired()?;
        let at_entry = {
            let ElaborationCachePolicy::BackwardReplay(replay) = &mut self.cache_policy else {
                unreachable!()
            };
            replay.run.finish();
            replay.run.diverged()
        };
        if let Some(at_entry) = at_entry {
            self.backward_demand
                .as_mut()
                .expect("backward replay always records demand events")
                .events
                .push(BwdEvent::Diverge { at_entry });
            return Err(PlanError::ReplayNotFullyConsumed { at_entry });
        }
        if !self.residents.is_empty() {
            return Err(PlanError::ReplayInfeasible);
        }
        Ok(())
    }

    fn elaborate_root(&mut self, root_id: RootId) -> Result<(), PlanError> {
        let Some(root) = self.layer.roots.get(root_id.0 as usize) else {
            return Err(PlanError::RootOutOfBounds(root_id));
        };
        let root_key = root_key(root.expr, root, &self.fingerprints)?;
        self.eval_expr(root.expr, &root_key, &[], &PreferenceMap::new())?;
        if root.materialize.is_none() {
            self.emit(EvalOp::ReturnAcc { root: root_key })?;
        }
        Ok(())
    }

    fn eval_expr(
        &mut self,
        expr: ExprId,
        root: &RootKey,
        path: &[PathStep],
        inherited: &PreferenceMap,
    ) -> Result<FieldKind, PlanError> {
        self.record_backward_demand(expr)?;
        if let Some(staged) = self.take_staged(expr, root, path) {
            self.plan.stats.cache_hits += 1;
            self.plan.attribution.entry(expr).or_default().resident_hits += 1;
            self.emit(EvalOp::AccInit(Operand::Resident(staged.value)))?;
            self.pinned.remove(&staged.value.fingerprint);
            self.realize_exit(&staged.scope, Some((staged.value, CacheStoreFrom::Acc)))?;
            return Ok(staged.value.field);
        }
        let (_site, scope) = self.enter_and_stage(expr, root, path, inherited)?;
        self.eval_entered_expr(expr, root, path, &scope)
    }

    fn record_backward_demand(&mut self, expr: ExprId) -> Result<BackwardDemandOutcome, PlanError> {
        let Some(state) = &self.backward_demand else {
            return Ok(BackwardDemandOutcome::default());
        };
        let fp = BwdFingerprint {
            term: state.schedule_pos,
            kind: BwdServeKind::Operand,
            value: expr,
            consumer: state.consumer_stack.last().copied(),
        };
        let fingerprint = self.fingerprint(expr);
        let was_visible = self.replay_resident_state(fingerprint) == ReplayResidentState::Visible;
        self.backward_demand
            .as_mut()
            .expect("checked Some above")
            .events
            .push(BwdEvent::Serve {
                fp,
                from: if was_visible {
                    BwdServedFrom::Resident
                } else {
                    BwdServedFrom::Recomputed
                },
            });

        let ElaborationCachePolicy::BackwardReplay(replay) = &mut self.cache_policy else {
            return Ok(BackwardDemandOutcome {
                was_visible,
                ..BackwardDemandOutcome::default()
            });
        };
        if !replay.domain.contains(&expr) {
            return Ok(BackwardDemandOutcome {
                was_visible,
                ..BackwardDemandOutcome::default()
            });
        }
        let action = replay.run.on_serve(&fp);
        if let Some(at_entry) = replay.run.diverged() {
            self.backward_demand
                .as_mut()
                .expect("backward replay always records demand events")
                .events
                .push(BwdEvent::Diverge { at_entry });
            return Err(PlanError::ReplayDiverged { at_entry });
        }
        if action == PlanAction::Retain && was_visible {
            let closes_at = replay
                .run
                .retention(expr)
                .expect("a matched Retain has an open interval");
            if let Some(entry) = self.residents.get_mut(&fingerprint) {
                entry.retain_for(expr, closes_at);
            }
        }
        let retire_after_select = action == PlanAction::Bypass
            && was_visible
            && self
                .residents
                .get(&fingerprint)
                .and_then(|entry| entry.replay_closes_at(&replay.run))
                .is_none();
        Ok(BackwardDemandOutcome {
            action: Some(action),
            was_visible,
            retire_after_select,
        })
    }

    fn source_operand(&mut self, value: ValueRef) -> Operand {
        self.record_source_traffic(value);
        Operand::Source(value)
    }

    fn record_source_traffic(&mut self, value: ValueRef) {
        let traffic_cells = match &self.layer.exprs[value.expr.0 as usize] {
            Expr::Source(source)
                if matches!(
                    self.layer.sources[source.0 as usize].kind,
                    SourceKind::Read { .. }
                ) =>
            {
                Some(field_lanes(value.field) as u32)
            }
            _ => None,
        };
        if let (Some(cells), Some(state)) = (traffic_cells, &mut self.backward_demand) {
            state.events.push(BwdEvent::TrafficRead {
                value: value.expr,
                cells,
            });
        }
    }

    fn push_backward_consumer(&mut self, expr: ExprId) {
        if let Some(state) = &mut self.backward_demand {
            state.consumer_stack.push(expr);
        }
    }

    fn pop_backward_consumer(&mut self, expr: ExprId) {
        if let Some(state) = &mut self.backward_demand {
            let popped = state.consumer_stack.pop();
            debug_assert_eq!(popped, Some(expr));
        }
    }

    fn enter_and_stage(
        &mut self,
        expr: ExprId,
        root: &RootKey,
        path: &[PathStep],
        inherited: &PreferenceMap,
    ) -> Result<(SiteId, PreferenceMap), PlanError> {
        let hit = self.is_logically_resident(self.fingerprint(expr));
        let (site, scope) = self.enter_site(expr, root, path, inherited)?;
        if !hit {
            let staging = match &mut self.cache_policy {
                ElaborationCachePolicy::Ranked(oracle) => oracle.stage_before(&site),
                ElaborationCachePolicy::None | ElaborationCachePolicy::BackwardReplay(_) => {
                    Vec::new()
                }
            };
            self.stage_requested(expr, &site, root, &scope, staging)?;
        }
        Ok((site, scope))
    }

    fn take_staged(
        &mut self,
        expr: ExprId,
        root: &RootKey,
        path: &[PathStep],
    ) -> Option<StagedEntry> {
        let site = SiteId {
            root: root.clone(),
            path: path.to_vec(),
            value: self.fingerprint(expr),
        };
        let position = self
            .staged_demands
            .iter()
            .position(|(candidate, _)| *candidate == site)?;
        Some(self.staged_demands.remove(position).1)
    }

    fn stage_requested(
        &mut self,
        boundary_expr: ExprId,
        boundary: &SiteId,
        root: &RootKey,
        inherited: &PreferenceMap,
        staging: Vec<StagingPreference>,
    ) -> Result<(), PlanError> {
        for preference in staging {
            let staged = preference.site;
            if !preference.priority.is_finite()
                || staged.root != *root
                || staged.path.len() <= boundary.path.len()
                || !staged.path.starts_with(&boundary.path)
            {
                return Err(PlanError::InvalidStaging {
                    boundary: Box::new(boundary.clone()),
                    staged: Box::new(staged),
                });
            }
            if self
                .staged_demands
                .iter()
                .any(|(candidate, _)| *candidate == staged)
            {
                return Err(PlanError::DuplicateStaging(staged));
            }
            if self.staged_demands.iter().any(|(candidate, _)| {
                candidate.root == staged.root
                    && staged.path.len() > candidate.path.len()
                    && staged.path.starts_with(&candidate.path)
            }) {
                // Computing the already-staged ancestor necessarily visited
                // this descendant. Its natural demand will also disappear
                // when that ancestor is consumed, so it cannot be staged a
                // second time as an independent frontier input.
                continue;
            }
            let suffix = &staged.path[boundary.path.len()..];
            if suffix[..suffix.len() - 1]
                .iter()
                .any(|step| self.is_logically_resident(step.child))
            {
                // The natural walk will hit this resident ancestor and prune
                // the requested site's cone, so computing the descendant now
                // would create a staged value with no eventual consumer.
                continue;
            }
            let Some(expr) =
                resolve_descendant_expr(self.layer, &self.fingerprints, boundary_expr, suffix)
            else {
                return Err(PlanError::InvalidStaging {
                    boundary: Box::new(boundary.clone()),
                    staged: Box::new(staged),
                });
            };
            if self.fingerprint(expr) != staged.value {
                return Err(PlanError::InvalidStaging {
                    boundary: Box::new(boundary.clone()),
                    staged: Box::new(staged),
                });
            }
            if self.is_logically_resident(staged.value) {
                continue;
            }
            let (actual, scope) = self.enter_and_stage(expr, root, &staged.path, inherited)?;
            if actual != staged {
                return Err(PlanError::InvalidStaging {
                    boundary: Box::new(boundary.clone()),
                    staged: Box::new(staged),
                });
            }
            let field = self.eval_entered_expr(expr, root, &actual.path, &scope)?;
            let value = self.value_ref(expr);
            debug_assert_eq!(field, value.field);
            if let Some(entry) = self.residents.get_mut(&value.fingerprint) {
                entry.priority = entry.priority.max(preference.priority);
            } else {
                self.ensure_transient_capacity(field_lanes(value.field))?;
                self.emit(EvalOp::CacheStore {
                    value,
                    from: CacheStoreFrom::Acc,
                })?;
                self.plan.attribution.entry(expr).or_default().cache_stores += 1;
                self.resident_lanes += field_lanes(value.field);
                self.residents.insert(
                    value.fingerprint,
                    ResidentEntry {
                        value,
                        priority: preference.priority,
                        replay_owners: BTreeSet::new(),
                    },
                );
                self.update_peak();
            }
            self.pinned.insert(value.fingerprint);
            self.staged_demands
                .push((actual, StagedEntry { value, scope }));
        }
        Ok(())
    }

    /// Evaluate a site whose oracle query and structural-site emission already
    /// happened. Used by oracle-aware FMA after it decides the product must be
    /// materialized, avoiding a second site/gene lookup for the same demand.
    fn eval_entered_expr(
        &mut self,
        expr: ExprId,
        root: &RootKey,
        path: &[PathStep],
        scope: &PreferenceMap,
    ) -> Result<FieldKind, PlanError> {
        let value = self.value_ref(expr);
        if self.is_logically_resident(value.fingerprint) {
            if self.pending_sinks.contains_key(&expr) {
                return Err(PlanError::ResidentWithPendingSinks(expr));
            }
            self.plan.stats.cache_hits += 1;
            self.plan.attribution.entry(expr).or_default().resident_hits += 1;
            self.emit(EvalOp::AccInit(Operand::Resident(value)))?;
            self.realize_exit(scope, Some((value, CacheStoreFrom::Acc)))?;
            return Ok(value.field);
        }

        self.plan.attribution.entry(expr).or_default().computations += 1;

        if let Some(negative) = unit_sign_expr(self.layer, expr) {
            self.emit(EvalOp::AccInit(Operand::Unit { negative }))?;
        } else if self.layer.resolutions.contains_key(&expr) {
            let operand = self.source_operand(value);
            self.emit(EvalOp::AccInit(operand))?;
        } else {
            match self.layer.exprs[expr.0 as usize].clone() {
                Expr::Source(_) => {
                    let operand = self.source_operand(value);
                    self.emit(EvalOp::AccInit(operand))?;
                }
                Expr::Add(children) => {
                    self.eval_reduction(expr, ReductionOp::Add, &children, root, path, scope)?;
                }
                Expr::Mul(children) => {
                    self.eval_reduction(expr, ReductionOp::Mul, &children, root, path, scope)?;
                }
            }
        }
        self.materialize(expr, MaterializeFrom::Acc)?;
        self.realize_exit(scope, Some((value, CacheStoreFrom::Acc)))?;
        Ok(self.field(expr))
    }

    fn eval_reduction(
        &mut self,
        parent: ExprId,
        operation: ReductionOp,
        children: &[ExprId],
        root: &RootKey,
        path: &[PathStep],
        scope: &PreferenceMap,
    ) -> Result<(), PlanError> {
        if let Some(state) = &mut self.backward_demand {
            state.consumer_stack.push(parent);
        }
        let result = if self.backward_stream_reductions == Some(false) {
            self.eval_reduction_prematerialized(parent, operation, children, root, path, scope)
        } else {
            self.eval_reduction_inner(parent, operation, children, root, path, scope)
        };
        if let Some(state) = &mut self.backward_demand {
            let popped = state.consumer_stack.pop();
            debug_assert_eq!(popped, Some(parent));
        }
        result
    }

    /// The legacy boundary: keep one running partial and evaluate the
    /// highest-pressure child first. Direct leaves fold without a stash;
    /// compound children use one partial-accumulator stash. This preserves the
    /// incumbent convention that the accumulator is outside the smem budget.
    /// This is backward-only; forward elaboration keeps its incumbent path.
    fn eval_reduction_prematerialized(
        &mut self,
        parent: ExprId,
        operation: ReductionOp,
        children: &[ExprId],
        root: &RootKey,
        path: &[PathStep],
        scope: &PreferenceMap,
    ) -> Result<(), PlanError> {
        let mut children = effective_child_occurrences(
            self.layer,
            self.child_occurrences(parent, operation, children),
            operation,
        );
        if children.is_empty() {
            return Err(PlanError::EmptyReduction(parent));
        }
        self.plan
            .attribution
            .entry(parent)
            .or_default()
            .arithmetic_ops += children.len().saturating_sub(1)
            + usize::from(operation == ReductionOp::Mul && product_unit_sign(self.layer, parent));

        let mut need_memo = HashMap::new();
        let avoid_fused_product_seed = self.uses_backward_eliminated_product_stream()
            && operation == ReductionOp::Add
            && children
                .iter()
                .any(|child| !self.eliminated_add_product(child.expr));
        let first_index = (0..children.len())
            .filter(|&index| {
                !avoid_fused_product_seed || !self.eliminated_add_product(children[index].expr)
            })
            .min_by_key(|&index| {
                (
                    self.transient_need_with_first(
                        &children,
                        operation,
                        scope,
                        index,
                        &mut need_memo,
                    ),
                    std::cmp::Reverse(index),
                )
            })
            .expect("a non-empty reduction has an accumulator seed");
        let first = children.remove(first_index);
        self.plan
            .attribution
            .entry(first.expr)
            .or_default()
            .accumulator_seeds += 1;
        let first_path = extended(path, first.step);
        let replay_eliminated_product = self.uses_backward_eliminated_product_stream()
            && operation == ReductionOp::Add
            && !self.is_direct(first.expr)
            && self.eliminated_add_product(first.expr);
        let mut acc_field = if replay_eliminated_product {
            self.seed_eliminated_product(first.expr, root, &first_path, scope)?
        } else {
            self.eval_expr(first.expr, root, &first_path, scope)?
        };
        for child in children {
            let child_path = extended(path, child.step);
            // A resident compound is already the value this Add needs. Consume
            // that cell before considering replay-only product folding; the
            // fusion path is only for a genuinely nonresident eliminated node.
            if self.is_direct(child.expr) {
                self.fold_direct(child.expr, operation, root, &child_path, scope)?;
            } else if self.uses_backward_eliminated_product_stream()
                && operation == ReductionOp::Add
                && self.direct_signed_single_product(child.expr).is_some()
            {
                self.fold_or_signed_single_product(
                    child.expr,
                    root,
                    &child_path,
                    scope,
                    acc_field,
                )?;
            } else if self.uses_backward_eliminated_product_stream()
                && operation == ReductionOp::Add
                && self.direct_binary_product(child.expr)
            {
                self.fold_or_fma_product(child.expr, root, &child_path, scope, acc_field)?;
            } else if self.uses_backward_eliminated_product_stream()
                && operation == ReductionOp::Add
                && self.eliminated_add_product(child.expr)
            {
                let saved = self.save_acc(acc_field)?;
                self.seed_eliminated_product(child.expr, root, &child_path, scope)?;
                self.emit(EvalOp::AccAdd {
                    sign: Sign::Plus,
                    operand: Operand::Temp(saved),
                })?;
            } else {
                let saved = self.save_acc(acc_field)?;
                self.eval_expr(child.expr, root, &child_path, scope)?;
                self.emit(match operation {
                    ReductionOp::Add => EvalOp::AccAdd {
                        sign: Sign::Plus,
                        operand: Operand::Temp(saved),
                    },
                    ReductionOp::Mul => EvalOp::AccMul(Operand::Temp(saved)),
                })?;
            }
            acc_field = join(acc_field, self.field(child.expr));
        }
        if operation == ReductionOp::Mul && product_unit_sign(self.layer, parent) {
            self.emit(EvalOp::AccNeg)?;
        }
        debug_assert_eq!(acc_field, self.field(parent));
        Ok(())
    }

    /// Seed an Add accumulator from a product that the incumbent FMA lowering
    /// eliminates. The product itself never becomes a served/cacheable value;
    /// its operands retain the enclosing Add as their consumer. Resident
    /// products never reach this path and are consumed through `eval_expr`.
    fn seed_eliminated_product(
        &mut self,
        product: ExprId,
        root: &RootKey,
        path: &[PathStep],
        inherited: &PreferenceMap,
    ) -> Result<FieldKind, PlanError> {
        let (_site, product_scope) = self.enter_and_stage(product, root, path, inherited)?;
        if product_scope.contains_key(&self.fingerprint(product))
            || self.pending_sinks.contains_key(&product)
        {
            return self.eval_entered_expr(product, root, path, &product_scope);
        }

        if let Some((sign, child)) = self.direct_single_product(product) {
            let child_path = extended(path, child.step);
            let prepared =
                self.prepare_ready_fma_operand(child.expr, root, &child_path, &product_scope)?;
            self.emit(EvalOp::AccInit(prepared.operand))?;
            if sign == Sign::Minus {
                self.emit(EvalOp::AccNeg)?;
            }
            self.plan
                .attribution
                .entry(product)
                .or_default()
                .signed_add_fusions += 1;
            self.pinned.remove(&prepared.value.fingerprint);
            self.realize_exit(&prepared.scope, None)?;
            self.realize_exit(&product_scope, None)?;
            return Ok(self.field(product));
        }

        let Expr::Mul(children) = self.layer.exprs[product.0 as usize].clone() else {
            unreachable!("caller checked the direct product kind")
        };
        let product_children = effective_child_occurrences(
            self.layer,
            self.child_occurrences(product, ReductionOp::Mul, &children),
            ReductionOp::Mul,
        );
        debug_assert!(matches!(product_children.len(), 1 | 2));
        if !product_children
            .iter()
            .all(|child| self.is_direct(child.expr))
        {
            let direct_first = product_children.len() == 2
                && self.is_direct(product_children[0].expr)
                && !self.is_direct(product_children[1].expr);
            let product_field = if direct_first {
                // Preserve the incumbent serve order without seeding ACC from
                // the direct factor and stashing it while the compound cone is
                // evaluated. Preparing a source emits no instruction; the
                // compound can therefore use ACC directly before multiplying
                // by the deferred operand.
                let first = &product_children[0];
                let first_path = extended(path, first.step);
                let prepared =
                    self.prepare_ready_fma_operand(first.expr, root, &first_path, &product_scope)?;
                let second = &product_children[1];
                let second_path = extended(path, second.step);
                let second_field =
                    self.eval_expr(second.expr, root, &second_path, &product_scope)?;
                self.emit(EvalOp::AccMul(prepared.operand))?;
                self.pinned.remove(&prepared.value.fingerprint);
                self.realize_exit(&prepared.scope, None)?;
                join(prepared.value.field, second_field)
            } else {
                let mut children = product_children.into_iter();
                let first = children
                    .next()
                    .expect("an eliminated product has an operand");
                let first_path = extended(path, first.step);
                let mut product_field =
                    self.eval_expr(first.expr, root, &first_path, &product_scope)?;
                for child in children {
                    let child_path = extended(path, child.step);
                    if self.is_direct(child.expr) {
                        self.fold_direct(
                            child.expr,
                            ReductionOp::Mul,
                            root,
                            &child_path,
                            &product_scope,
                        )?;
                    } else {
                        let saved = self.save_acc(product_field)?;
                        self.eval_expr(child.expr, root, &child_path, &product_scope)?;
                        self.emit(EvalOp::AccMul(Operand::Temp(saved)))?;
                    }
                    product_field = join(product_field, self.field(child.expr));
                }
                product_field
            };
            if product_unit_sign(self.layer, product) {
                self.emit(EvalOp::AccNeg)?;
            }
            self.plan
                .attribution
                .entry(product)
                .or_default()
                .fma_fusions += 1;
            self.materialize(product, MaterializeFrom::Acc)?;
            self.realize_exit(
                &product_scope,
                Some((self.value_ref(product), CacheStoreFrom::Acc)),
            )?;
            return Ok(self.field(product));
        }

        debug_assert_eq!(product_children.len(), 2);
        let second_path = extended(path, product_children[1].step);
        match self.prepare_binary_fma_operands(&product_children, root, path, &product_scope)? {
            BinaryFmaPreparation::Ready { first, second } => {
                self.emit(EvalOp::AccInit(first.operand))?;
                self.emit(EvalOp::AccMul(second.operand))?;
                self.release_prepared_operand(first)?;
                self.release_prepared_operand(second)?;
            }
            BinaryFmaPreparation::NeedsEvaluation {
                first,
                expr,
                value,
                scope,
            } => {
                self.release_retired_fma_operand(first)?;
                self.eval_and_square_entered_operand(expr, value, root, &second_path, &scope)?;
            }
        }
        if product_unit_sign(self.layer, product) {
            self.emit(EvalOp::AccNeg)?;
        }
        self.plan
            .attribution
            .entry(product)
            .or_default()
            .fma_fusions += 1;
        self.realize_exit(&product_scope, None)?;
        Ok(self.field(product))
    }

    fn eval_reduction_inner(
        &mut self,
        parent: ExprId,
        operation: ReductionOp,
        children: &[ExprId],
        root: &RootKey,
        path: &[PathStep],
        scope: &PreferenceMap,
    ) -> Result<(), PlanError> {
        let mut children = effective_child_occurrences(
            self.layer,
            self.child_occurrences(parent, operation, children),
            operation,
        );
        if children.is_empty() {
            return Err(PlanError::EmptyReduction(parent));
        }
        self.plan
            .attribution
            .entry(parent)
            .or_default()
            .arithmetic_ops += children.len().saturating_sub(1)
            + usize::from(operation == ReductionOp::Mul && product_unit_sign(self.layer, parent));

        // Entry-resident values the parent does not want at exit go first; values
        // the parent wants produced for exit go last. The structural baseline is
        // the tie-break: compound cones seed the accumulator, direct leaves
        // follow, and uncached ready products come last to expose FMA.
        children.sort_by_key(|child| {
            let fingerprint = child.step.child;
            let resident = self.is_logically_resident(fingerprint);
            let desired = scope.contains_key(&fingerprint);
            let pressure_class = match (resident, desired) {
                (true, false) => 0u8,
                (false, true) => 2u8,
                _ => 1u8,
            };
            let release_order = if pressure_class == 0 {
                usize::MAX - field_lanes(self.field(child.expr))
            } else {
                0
            };
            let structural_class =
                if operation == ReductionOp::Add && self.direct_binary_product(child.expr) {
                    2u8
                } else if operation == ReductionOp::Add
                    && self.direct_single_product(child.expr).is_some()
                {
                    2u8
                } else if self.is_direct(child.expr) {
                    1u8
                } else {
                    0u8
                };
            (
                pressure_class,
                release_order,
                structural_class,
                fingerprint,
                child.step.duplicate_ordinal,
            )
        });

        // Cache-pressure ordering is preferred, but it must not turn an
        // otherwise feasible cone into an over-budget accumulator stack. Try
        // each child as the accumulator seed and repair only when the preferred
        // order's predicted transient requirement exceeds the remaining budget.
        let mut need_memo = HashMap::new();
        let preferred_need =
            self.transient_need_with_first(&children, operation, scope, 0, &mut need_memo);
        let occupied_lanes = self.live_lanes.saturating_add(
            if matches!(
                &self.cache_policy,
                ElaborationCachePolicy::BackwardReplay(_)
            ) {
                self.resident_lanes
            } else {
                0
            },
        );
        if occupied_lanes.saturating_add(preferred_need) > self.budget_lanes {
            let mut best = (preferred_need, 0usize);
            for first_index in 1..children.len() {
                let need = self.transient_need_with_first(
                    &children,
                    operation,
                    scope,
                    first_index,
                    &mut need_memo,
                );
                best = best.min((need, first_index));
            }
            if best.1 != 0 {
                let first = children.remove(best.1);
                children.insert(0, first);
            }
        }

        let first = children.remove(0);
        self.plan
            .attribution
            .entry(first.expr)
            .or_default()
            .accumulator_seeds += 1;
        let first_path = extended(path, first.step);
        let replay_eliminated_product = self.uses_backward_eliminated_product_stream()
            && operation == ReductionOp::Add
            && !self.is_direct(first.expr)
            && self.eliminated_add_product(first.expr);
        let mut acc_field = if replay_eliminated_product {
            self.seed_eliminated_product(first.expr, root, &first_path, scope)?
        } else {
            self.eval_expr(first.expr, root, &first_path, scope)?
        };

        for child in children {
            let child_path = extended(path, child.step);
            let binary_product = operation == ReductionOp::Add
                && self.effective_product_arity(child.expr) == Some(2);
            if self.is_logically_resident(child.step.child) {
                if binary_product {
                    self.plan
                        .attribution
                        .entry(child.expr)
                        .or_default()
                        .resident_product_adds += 1;
                }
                self.fold_direct(child.expr, operation, root, &child_path, scope)?;
            } else if operation == ReductionOp::Add
                && self.direct_single_product(child.expr).is_some()
                && (!self.uses_backward_eliminated_product_stream()
                    || self.eliminated_add_product(child.expr))
            {
                self.fold_or_signed_single_product(
                    child.expr,
                    root,
                    &child_path,
                    scope,
                    acc_field,
                )?;
            } else if operation == ReductionOp::Add && self.direct_binary_product(child.expr) {
                if !self.uses_backward_eliminated_product_stream()
                    && matches!(&self.cache_policy, ElaborationCachePolicy::None)
                    && !self.pending_sinks.contains_key(&child.expr)
                {
                    self.emit_ready_fma(child.expr, root, &child_path)?;
                } else {
                    self.fold_or_fma_product(child.expr, root, &child_path, scope, acc_field)?;
                }
            } else if self.uses_backward_eliminated_product_stream()
                && operation == ReductionOp::Add
                && self.eliminated_add_product(child.expr)
            {
                let saved = self.save_acc(acc_field)?;
                self.seed_eliminated_product(child.expr, root, &child_path, scope)?;
                self.emit(EvalOp::AccAdd {
                    sign: Sign::Plus,
                    operand: Operand::Temp(saved),
                })?;
            } else if self.is_direct(child.expr) {
                self.fold_direct(child.expr, operation, root, &child_path, scope)?;
            } else {
                if binary_product {
                    self.plan
                        .attribution
                        .entry(child.expr)
                        .or_default()
                        .unready_product_adds += 1;
                }
                let saved = self.save_acc(acc_field)?;
                self.eval_expr(child.expr, root, &child_path, scope)?;
                self.emit(match operation {
                    ReductionOp::Add => EvalOp::AccAdd {
                        sign: Sign::Plus,
                        operand: Operand::Temp(saved),
                    },
                    ReductionOp::Mul => EvalOp::AccMul(Operand::Temp(saved)),
                })?;
            }
            acc_field = join(acc_field, self.field(child.expr));
        }
        if operation == ReductionOp::Mul && product_unit_sign(self.layer, parent) {
            self.emit(EvalOp::AccNeg)?;
        }
        debug_assert_eq!(acc_field, self.field(parent));
        Ok(())
    }

    fn transient_need_with_first(
        &self,
        children: &[ChildOccurrence],
        operation: ReductionOp,
        scope: &PreferenceMap,
        first_index: usize,
        memo: &mut HashMap<ExprId, usize>,
    ) -> usize {
        let first = &children[first_index];
        let mut peak = self.transient_need(first.expr, scope, memo);
        let mut acc_field = self.field(first.expr);
        for (index, child) in children.iter().enumerate() {
            if index == first_index {
                continue;
            }
            if self.child_needs_separate_evaluation(operation, child.expr, scope) {
                peak = peak.max(
                    field_lanes(acc_field)
                        .saturating_add(self.transient_need(child.expr, scope, memo)),
                );
            }
            acc_field = join(acc_field, self.field(child.expr));
        }
        peak
    }

    fn transient_need(
        &self,
        expr: ExprId,
        scope: &PreferenceMap,
        memo: &mut HashMap<ExprId, usize>,
    ) -> usize {
        if self.is_direct(expr) {
            return 0;
        }
        if let Some(&need) = memo.get(&expr) {
            return need;
        }
        let (operation, children) = match &self.layer.exprs[expr.0 as usize] {
            Expr::Source(_) => return 0,
            Expr::Add(children) => (ReductionOp::Add, children),
            Expr::Mul(children) => (ReductionOp::Mul, children),
        };
        let occurrences = effective_child_occurrences(
            self.layer,
            self.child_occurrences(expr, operation, children),
            operation,
        );
        let need = (0..occurrences.len())
            .map(|first_index| {
                self.transient_need_with_first(&occurrences, operation, scope, first_index, memo)
            })
            .min()
            .unwrap_or(0);
        memo.insert(expr, need);
        need
    }

    fn child_needs_separate_evaluation(
        &self,
        operation: ReductionOp,
        expr: ExprId,
        scope: &PreferenceMap,
    ) -> bool {
        if self.is_direct(expr) {
            return false;
        }
        let ready_product = if self.uses_backward_eliminated_product_stream() {
            self.direct_binary_product(expr) || self.direct_signed_single_product(expr).is_some()
        } else {
            self.direct_binary_product(expr) || self.direct_single_product(expr).is_some()
        };
        !(operation == ReductionOp::Add
            && ready_product
            && !scope.contains_key(&self.fingerprint(expr))
            && !self.pending_sinks.contains_key(&expr))
    }

    fn fold_direct(
        &mut self,
        expr: ExprId,
        operation: ReductionOp,
        root: &RootKey,
        path: &[PathStep],
        inherited: &PreferenceMap,
    ) -> Result<(), PlanError> {
        self.record_backward_demand(expr)?;
        let staged = self.take_staged(expr, root, path);
        let scope = if let Some(staged) = &staged {
            staged.scope.clone()
        } else {
            self.enter_and_stage(expr, root, path, inherited)?.1
        };
        let value = self.value_ref(expr);
        let was_resident = self.is_logically_resident(value.fingerprint);
        if was_resident && self.pending_sinks.contains_key(&expr) {
            return Err(PlanError::ResidentWithPendingSinks(expr));
        }
        if !was_resident && self.is_source_like(expr) {
            self.materialize(expr, MaterializeFrom::Source(value))?;
        }
        if !was_resident && self.is_source_like(expr) && scope.contains_key(&value.fingerprint) {
            // A direct source must be loaded into residency before the fold. If
            // we folded from Global first and stored afterward, the physical
            // DstFromSrc would be a second DRAM read not represented by the plan.
            self.realize_exit(&scope, Some((value, CacheStoreFrom::Source)))?;
        }
        let operand = if self.is_logically_resident(value.fingerprint) {
            if was_resident {
                self.plan.stats.cache_hits += 1;
            }
            Operand::Resident(value)
        } else if self.is_source_like(expr) {
            self.source_operand(value)
        } else {
            return Err(PlanError::ExpectedSource(expr));
        };
        self.emit(match operation {
            ReductionOp::Add => EvalOp::AccAdd {
                sign: Sign::Plus,
                operand,
            },
            ReductionOp::Mul => EvalOp::AccMul(operand),
        })?;
        if staged.is_some() {
            self.pinned.remove(&value.fingerprint);
        }
        if was_resident || !scope.contains_key(&value.fingerprint) {
            self.realize_exit(&scope, None)?;
        }
        Ok(())
    }

    fn emit_ready_fma(
        &mut self,
        product: ExprId,
        root: &RootKey,
        path: &[PathStep],
    ) -> Result<(), PlanError> {
        let preserve_product_boundary = !self.uses_backward_eliminated_product_stream();
        if preserve_product_boundary {
            self.record_backward_demand(product)?;
        }
        self.plan
            .attribution
            .entry(product)
            .or_default()
            .fma_fusions += 1;
        self.record_site(product, root, path);
        let Expr::Mul(children) = &self.layer.exprs[product.0 as usize] else {
            unreachable!("direct_binary_product checked the expression kind")
        };
        let product_children = effective_child_occurrences(
            self.layer,
            self.child_occurrences(product, ReductionOp::Mul, children),
            ReductionOp::Mul,
        );
        debug_assert_eq!(product_children.len(), 2);
        let mut operands = Vec::with_capacity(2);
        if preserve_product_boundary {
            self.push_backward_consumer(product);
        }
        for child in product_children {
            let child_path = extended(path, child.step);
            self.record_backward_demand(child.expr)?;
            self.record_site(child.expr, root, &child_path);
            let value = self.value_ref(child.expr);
            self.materialize(child.expr, MaterializeFrom::Source(value))?;
            operands.push(self.source_operand(value));
        }
        if preserve_product_boundary {
            self.pop_backward_consumer(product);
        }
        self.emit(EvalOp::AccFma {
            sign: if product_unit_sign(self.layer, product) {
                Sign::Minus
            } else {
                Sign::Plus
            },
            lhs: operands[0],
            rhs: operands[1],
        })
    }

    fn fold_or_signed_single_product(
        &mut self,
        product: ExprId,
        root: &RootKey,
        path: &[PathStep],
        inherited: &PreferenceMap,
        acc_field: FieldKind,
    ) -> Result<(), PlanError> {
        // This path is reached only after the caller proved the product is
        // nonresident. The product is eliminated into the enclosing Add and
        // never exists as an independently cacheable value, matching the
        // incumbent serve stream. A resident product takes `fold_direct`
        // instead and records/consumes its real serve there.
        let (_site, product_scope) = self.enter_and_stage(product, root, path, inherited)?;
        let product_value = self.value_ref(product);
        if product_scope.contains_key(&product_value.fingerprint)
            || self.pending_sinks.contains_key(&product)
        {
            let saved = self.save_acc(acc_field)?;
            self.eval_entered_expr(product, root, path, &product_scope)?;
            self.emit(EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Temp(saved),
            })?;
            return Ok(());
        }

        let (sign, child) = self
            .direct_single_product(product)
            .expect("caller checked direct_single_product");
        self.plan
            .attribution
            .entry(product)
            .or_default()
            .signed_add_fusions += 1;
        let child_path = extended(path, child.step);
        let preserve_product_consumer = !self.uses_backward_eliminated_product_stream();
        if preserve_product_consumer {
            self.push_backward_consumer(product);
        }
        let prepared =
            self.prepare_ready_fma_operand(child.expr, root, &child_path, &product_scope)?;
        if preserve_product_consumer {
            self.pop_backward_consumer(product);
        }
        self.emit(EvalOp::AccAdd {
            sign,
            operand: prepared.operand,
        })?;
        self.pinned.remove(&prepared.value.fingerprint);
        self.realize_exit(&prepared.scope, None)?;
        self.realize_exit(&product_scope, None)
    }

    /// Fold one binary product into the existing Add accumulator. If the
    /// product result is requested as a survivor, preserve the product boundary:
    /// stash the outer partial, evaluate/materialize the product, then refold.
    /// Otherwise prepare and pin both direct operands through one FMA.
    fn fold_or_fma_product(
        &mut self,
        product: ExprId,
        root: &RootKey,
        path: &[PathStep],
        inherited: &PreferenceMap,
        acc_field: FieldKind,
    ) -> Result<(), PlanError> {
        // As above, the nonresident product is an eliminated FMA boundary, not
        // a cacheable occurrence. Resident compounds are consumed by
        // `fold_direct` before this function can be selected.
        let (_site, product_scope) = self.enter_and_stage(product, root, path, inherited)?;
        let product_value = self.value_ref(product);
        if product_scope.contains_key(&product_value.fingerprint)
            || self.pending_sinks.contains_key(&product)
        {
            self.plan
                .attribution
                .entry(product)
                .or_default()
                .preserved_product_adds += 1;
            let saved = self.save_acc(acc_field)?;
            self.eval_entered_expr(product, root, path, &product_scope)?;
            self.emit(EvalOp::AccAdd {
                sign: Sign::Plus,
                operand: Operand::Temp(saved),
            })?;
            return Ok(());
        }

        let Expr::Mul(children) = self.layer.exprs[product.0 as usize].clone() else {
            unreachable!("direct_binary_product checked the expression kind")
        };
        let product_children = effective_child_occurrences(
            self.layer,
            self.child_occurrences(product, ReductionOp::Mul, &children),
            ReductionOp::Mul,
        );
        debug_assert_eq!(product_children.len(), 2);
        let second_path = extended(path, product_children[1].step);
        let preserve_product_consumer = !self.uses_backward_eliminated_product_stream();
        if preserve_product_consumer {
            self.push_backward_consumer(product);
        }
        let prepared =
            self.prepare_binary_fma_operands(&product_children, root, path, &product_scope)?;
        if preserve_product_consumer {
            self.pop_backward_consumer(product);
        }

        let negative = product_unit_sign(self.layer, product);
        match prepared {
            BinaryFmaPreparation::Ready { first, second } => {
                self.emit(EvalOp::AccFma {
                    sign: if negative { Sign::Minus } else { Sign::Plus },
                    lhs: first.operand,
                    rhs: second.operand,
                })?;
                self.release_prepared_operand(first)?;
                self.release_prepared_operand(second)?;
            }
            BinaryFmaPreparation::NeedsEvaluation {
                first,
                expr,
                value,
                scope,
            } => {
                self.release_retired_fma_operand(first)?;
                let saved = self.save_acc(acc_field)?;
                self.eval_and_square_entered_operand(expr, value, root, &second_path, &scope)?;
                if negative {
                    self.emit(EvalOp::AccNeg)?;
                }
                self.emit(EvalOp::AccAdd {
                    sign: Sign::Plus,
                    operand: Operand::Temp(saved),
                })?;
            }
        }
        self.plan
            .attribution
            .entry(product)
            .or_default()
            .fma_fusions += 1;
        // The fused product itself never existed independently. Product-level
        // preferences still govern which operand/outer residents survive.
        self.realize_exit(&product_scope, None)
    }

    fn prepare_fma_operand(
        &mut self,
        expr: ExprId,
        root: &RootKey,
        path: &[PathStep],
        inherited: &PreferenceMap,
    ) -> Result<FmaOperandPreparation, PlanError> {
        let demand = self.record_backward_demand(expr)?;
        let scope = if let Some(staged) = self.take_staged(expr, root, path) {
            staged.scope
        } else {
            self.enter_and_stage(expr, root, path, inherited)?.1
        };
        let value = self.value_ref(expr);
        let was_resident = self.is_logically_resident(value.fingerprint);
        let needs_evaluation = demand.action.is_some()
            && !demand.was_visible
            && (!self.is_source_like(expr)
                || (demand.needs_fresh_admission()
                    && self.replay_resident_state(value.fingerprint)
                        == ReplayResidentState::RetiredPinned));
        if needs_evaluation {
            return Ok(FmaOperandPreparation::NeedsEvaluation { expr, value, scope });
        }
        if was_resident && self.pending_sinks.contains_key(&expr) {
            return Err(PlanError::ResidentWithPendingSinks(expr));
        }
        if !was_resident && self.is_source_like(expr) {
            self.materialize(expr, MaterializeFrom::Source(value))?;
        }
        if !was_resident && self.is_source_like(expr) && scope.contains_key(&value.fingerprint) {
            self.realize_exit(&scope, Some((value, CacheStoreFrom::Source)))?;
        }
        let operand = if self.is_logically_resident(value.fingerprint) {
            if was_resident {
                self.plan.stats.cache_hits += 1;
            }
            self.pinned.insert(value.fingerprint);
            Operand::Resident(value)
        } else if self.is_source_like(expr) {
            self.source_operand(value)
        } else {
            return Err(PlanError::ExpectedSource(expr));
        };
        if demand.retire_after_select {
            debug_assert!(was_resident);
            self.replay_logically_retired.insert(value.fingerprint);
        }
        Ok(FmaOperandPreparation::Ready(PreparedOperand {
            operand,
            value,
            scope,
        }))
    }

    fn prepare_ready_fma_operand(
        &mut self,
        expr: ExprId,
        root: &RootKey,
        path: &[PathStep],
        inherited: &PreferenceMap,
    ) -> Result<PreparedOperand, PlanError> {
        match self.prepare_fma_operand(expr, root, path, inherited)? {
            FmaOperandPreparation::Ready(prepared) => Ok(prepared),
            FmaOperandPreparation::NeedsEvaluation { expr, .. } => {
                Err(PlanError::ExpectedSource(expr))
            }
        }
    }

    fn prepare_binary_fma_operands(
        &mut self,
        children: &[ChildOccurrence],
        root: &RootKey,
        path: &[PathStep],
        scope: &PreferenceMap,
    ) -> Result<BinaryFmaPreparation, PlanError> {
        debug_assert_eq!(children.len(), 2);
        let first_child = &children[0];
        let first_path = extended(path, first_child.step);
        let first = match self.prepare_fma_operand(first_child.expr, root, &first_path, scope)? {
            FmaOperandPreparation::Ready(prepared) => prepared,
            FmaOperandPreparation::NeedsEvaluation { expr, .. } => {
                return Err(PlanError::ExpectedSource(expr));
            }
        };

        let second_child = &children[1];
        let second_path = extended(path, second_child.step);
        match self.prepare_fma_operand(second_child.expr, root, &second_path, scope)? {
            FmaOperandPreparation::Ready(second) => {
                Ok(BinaryFmaPreparation::Ready { first, second })
            }
            FmaOperandPreparation::NeedsEvaluation { expr, value, scope } => {
                debug_assert!(matches!(
                    &self.cache_policy,
                    ElaborationCachePolicy::BackwardReplay(_)
                ));
                debug_assert_eq!(first.value.fingerprint, value.fingerprint);
                debug_assert!(matches!(first.operand, Operand::Resident(_)));
                debug_assert_eq!(
                    self.replay_resident_state(first.value.fingerprint),
                    ReplayResidentState::RetiredPinned
                );
                Ok(BinaryFmaPreparation::NeedsEvaluation {
                    first,
                    expr,
                    value,
                    scope,
                })
            }
        }
    }

    fn release_prepared_operand(&mut self, prepared: PreparedOperand) -> Result<(), PlanError> {
        self.pinned.remove(&prepared.value.fingerprint);
        self.realize_exit(&prepared.scope, None)
    }

    fn release_retired_fma_operand(&mut self, prepared: PreparedOperand) -> Result<(), PlanError> {
        debug_assert_eq!(
            self.replay_resident_state(prepared.value.fingerprint),
            ReplayResidentState::RetiredPinned
        );
        let was_pinned = self.pinned.remove(&prepared.value.fingerprint);
        debug_assert!(was_pinned);
        self.realize_exit(&prepared.scope, None)?;
        debug_assert_eq!(
            self.replay_resident_state(prepared.value.fingerprint),
            ReplayResidentState::Absent
        );
        Ok(())
    }

    fn eval_and_square_entered_operand(
        &mut self,
        expr: ExprId,
        value: ValueRef,
        root: &RootKey,
        path: &[PathStep],
        scope: &PreferenceMap,
    ) -> Result<(), PlanError> {
        let field = self.eval_entered_expr(expr, root, path, scope)?;
        debug_assert_eq!(field, value.field);
        let operand = match self.replay_resident_state(value.fingerprint) {
            ReplayResidentState::Visible => Operand::Resident(value),
            ReplayResidentState::Absent => Operand::Temp(self.save_acc(value.field)?),
            ReplayResidentState::RetiredPinned => return Err(PlanError::ReplayInfeasible),
        };
        self.emit(EvalOp::AccMul(operand))?;
        self.realize_exit(scope, None)
    }

    fn materialize(&mut self, expr: ExprId, from: MaterializeFrom) -> Result<(), PlanError> {
        let Some(mut obligations) = self.pending_sinks.remove(&expr) else {
            return Ok(());
        };
        self.plan
            .attribution
            .entry(expr)
            .or_default()
            .materializations += obligations.len();
        obligations.sort_by_key(|obligation| obligation.root_id.0);
        for obligation in obligations {
            self.emit(EvalOp::Commit {
                root_id: obligation.root_id,
                root: obligation.root,
                sink: obligation.sink,
                from,
            })?;
        }
        Ok(())
    }

    fn direct_binary_product(&self, expr: ExprId) -> bool {
        let Expr::Mul(children) = &self.layer.exprs[expr.0 as usize] else {
            return false;
        };
        let children = effective_child_occurrences(
            self.layer,
            self.child_occurrences(expr, ReductionOp::Mul, children),
            ReductionOp::Mul,
        );
        children.len() == 2 && children.iter().all(|child| self.is_direct(child.expr))
    }

    fn effective_product_arity(&self, expr: ExprId) -> Option<usize> {
        let Expr::Mul(children) = &self.layer.exprs[expr.0 as usize] else {
            return None;
        };
        Some(
            children
                .iter()
                .filter(|&&child| unit_sign_expr(self.layer, child).is_none())
                .count(),
        )
    }

    fn eliminated_add_product(&self, expr: ExprId) -> bool {
        match self.effective_product_arity(expr) {
            Some(2) => true,
            Some(1) => product_unit_sign(self.layer, expr),
            _ => false,
        }
    }

    fn direct_single_product(&self, expr: ExprId) -> Option<(Sign, ChildOccurrence)> {
        let Expr::Mul(children) = &self.layer.exprs[expr.0 as usize] else {
            return None;
        };
        let mut children = effective_child_occurrences(
            self.layer,
            self.child_occurrences(expr, ReductionOp::Mul, children),
            ReductionOp::Mul,
        );
        if children.len() != 1 || !self.is_direct(children[0].expr) {
            return None;
        }
        Some((
            if product_unit_sign(self.layer, expr) {
                Sign::Minus
            } else {
                Sign::Plus
            },
            children.remove(0),
        ))
    }

    fn direct_signed_single_product(&self, expr: ExprId) -> Option<(Sign, ChildOccurrence)> {
        self.direct_single_product(expr)
            .filter(|(sign, _)| *sign == Sign::Minus)
    }

    fn is_direct(&self, expr: ExprId) -> bool {
        self.is_logically_resident(self.fingerprint(expr)) || self.is_source_like(expr)
    }

    fn replay_resident_state(&self, fingerprint: ValueFingerprint) -> ReplayResidentState {
        let physically_resident = self.residents.contains_key(&fingerprint);
        let logically_retired = self.replay_logically_retired.contains(&fingerprint);
        debug_assert!(
            !logically_retired || physically_resident,
            "a logically retired replay value must remain physically resident"
        );
        debug_assert!(
            !logically_retired || self.pinned.contains(&fingerprint),
            "a logically retired replay value must remain pinned"
        );
        match (physically_resident, logically_retired) {
            (false, false) => ReplayResidentState::Absent,
            (true, false) => ReplayResidentState::Visible,
            (true, true) => ReplayResidentState::RetiredPinned,
            (false, true) => unreachable!("checked by the replay retirement invariant"),
        }
    }

    fn is_logically_resident(&self, fingerprint: ValueFingerprint) -> bool {
        self.replay_resident_state(fingerprint) == ReplayResidentState::Visible
    }

    fn is_source_like(&self, expr: ExprId) -> bool {
        self.layer.resolutions.contains_key(&expr)
            || matches!(self.layer.exprs[expr.0 as usize], Expr::Source(_))
    }

    fn child_occurrences(
        &self,
        parent: ExprId,
        operation: ReductionOp,
        children: &[ExprId],
    ) -> Vec<ChildOccurrence> {
        canonical_child_occurrences(&self.fingerprints, parent, operation, children)
    }

    fn record_site(&mut self, expr: ExprId, root: &RootKey, path: &[PathStep]) -> SiteId {
        let attribution = self.plan.attribution.entry(expr).or_default();
        attribution.demands += 1;
        attribution.additive_demands += usize::from(
            path.last()
                .is_some_and(|step| step.operation == ReductionOp::Add),
        );
        let site = SiteId {
            root: root.clone(),
            path: path.to_vec(),
            value: self.fingerprint(expr),
        };
        self.plan.sites.push(site.clone());
        site
    }

    fn enter_site(
        &mut self,
        expr: ExprId,
        root: &RootKey,
        path: &[PathStep],
        inherited: &PreferenceMap,
    ) -> Result<(SiteId, PreferenceMap), PlanError> {
        let site = self.record_site(expr, root, path);
        let hit = self.is_logically_resident(site.value);
        let mut scope = if matches!(
            &self.cache_policy,
            ElaborationCachePolicy::BackwardReplay(_)
        ) {
            PreferenceMap::new()
        } else {
            inherited.clone()
        };
        match &mut self.cache_policy {
            ElaborationCachePolicy::Ranked(oracle) => {
                let resident_values: Vec<ValueRef> =
                    self.residents.values().map(|entry| entry.value).collect();
                let pinned_values: Vec<ValueFingerprint> = self.pinned.iter().copied().collect();
                let response = oracle.desired_after(
                    &site,
                    CacheStateView {
                        residents: &resident_values,
                        pinned: &pinned_values,
                        resident_lanes: self.resident_lanes,
                        transient_lanes: self.live_lanes,
                        budget_lanes: self.budget_lanes,
                    },
                );
                for preference in response {
                    if !preference.priority.is_finite() {
                        return Err(PlanError::InvalidPriority {
                            site: Box::new(site),
                            priority: preference.priority,
                        });
                    }
                    merge_priority(&mut scope, preference.value, preference.priority);
                }
            }
            ElaborationCachePolicy::BackwardReplay(replay) => {
                for entry in self.residents.values() {
                    if let Some(closes_at) = entry.replay_closes_at(&replay.run) {
                        scope.insert(entry.value.fingerprint, closes_at as f64);
                    }
                }
                if let Some(closes_at) = replay.run.retention(expr) {
                    scope.insert(site.value, closes_at as f64);
                }
            }
            ElaborationCachePolicy::None => {}
        }
        if self.trace_residency {
            self.plan.residency_events.push(PlanResidencyEvent {
                site: Some(site.clone()),
                value: self.value_ref(expr),
                kind: PlanResidencyEventKind::Demand { hit },
                residents_after: self.residents.values().map(|entry| entry.value).collect(),
            });
        }
        Ok((site, scope))
    }

    /// Realize as much of `preferences` as fits from values that physically
    /// exist now: current residents plus `current`, whose value is either in the
    /// accumulator or is a directly-copyable source. Unavailable requested
    /// values are not fabricated retroactively.
    fn realize_exit(
        &mut self,
        preferences: &PreferenceMap,
        current: Option<(ValueRef, CacheStoreFrom)>,
    ) -> Result<(), PlanError> {
        if matches!(
            &self.cache_policy,
            ElaborationCachePolicy::BackwardReplay(_)
        ) {
            return self.realize_replay_exit(current);
        }
        self.realize_ranked_exit(preferences, current)
    }

    fn realize_ranked_exit(
        &mut self,
        preferences: &PreferenceMap,
        current: Option<(ValueRef, CacheStoreFrom)>,
    ) -> Result<(), PlanError> {
        let mut available: BTreeMap<ValueFingerprint, ValueRef> = self
            .residents
            .iter()
            .map(|(&fingerprint, entry)| (fingerprint, entry.value))
            .collect();
        if let Some((current, _)) = current {
            available.insert(current.fingerprint, current);
        }

        let mut candidates: Vec<(f64, bool, ValueFingerprint, ValueRef)> = preferences
            .iter()
            .filter_map(|(&fingerprint, &priority)| {
                available.get(&fingerprint).copied().map(|value| {
                    (
                        priority,
                        self.residents.contains_key(&fingerprint),
                        fingerprint,
                        value,
                    )
                })
            })
            .collect();
        // Preserve an incumbent on an exact priority tie. Besides avoiding a
        // pointless drop/store pair, this matches admission semantics: a new
        // value must be strictly more valuable to displace a live resident.
        candidates.sort_by(|a, b| {
            b.0.total_cmp(&a.0)
                .then_with(|| b.1.cmp(&a.1))
                .then_with(|| a.2.cmp(&b.2))
        });

        let capacity = self.budget_lanes.saturating_sub(self.live_lanes);
        let mut selected: BTreeSet<ValueFingerprint> = self
            .pinned
            .iter()
            .copied()
            .filter(|fingerprint| self.residents.contains_key(fingerprint))
            .collect();
        let mut selected_lanes: usize = selected
            .iter()
            .map(|fingerprint| field_lanes(self.residents[fingerprint].value.field))
            .sum();
        for (_, _, fingerprint, value) in &candidates {
            if selected.contains(fingerprint) {
                continue;
            }
            let width = field_lanes(value.field);
            if selected_lanes.saturating_add(width) <= capacity {
                selected.insert(*fingerprint);
                selected_lanes += width;
            }
        }

        let to_drop: Vec<ValueFingerprint> = self
            .residents
            .keys()
            .copied()
            .filter(|fingerprint| !selected.contains(fingerprint))
            .collect();
        for fingerprint in to_drop {
            self.drop_resident(fingerprint)?;
        }

        for (priority, _, fingerprint, value) in candidates {
            if !selected.contains(&fingerprint) {
                continue;
            }
            if let Some(entry) = self.residents.get_mut(&fingerprint) {
                entry.priority = priority;
                continue;
            }
            let from = current
                .filter(|(current, _)| current.fingerprint == fingerprint)
                .map(|(_, from)| from)
                .expect("a non-resident available value must be the current value");
            self.emit(EvalOp::CacheStore { value, from })?;
            self.plan
                .attribution
                .entry(value.expr)
                .or_default()
                .cache_stores += 1;
            self.resident_lanes += field_lanes(value.field);
            self.residents.insert(
                fingerprint,
                ResidentEntry {
                    value,
                    priority,
                    replay_owners: BTreeSet::new(),
                },
            );
            if self.trace_residency {
                self.plan.residency_events.push(PlanResidencyEvent {
                    site: None,
                    value,
                    kind: PlanResidencyEventKind::Admit,
                    residents_after: self.residents.values().map(|entry| entry.value).collect(),
                });
            }
            self.update_peak();
        }
        Ok(())
    }

    fn realize_replay_exit(
        &mut self,
        current: Option<(ValueRef, CacheStoreFrom)>,
    ) -> Result<(), PlanError> {
        self.replay_drop_expired()?;

        let Some((value, from)) = current else {
            return Ok(());
        };
        let closes_at = match &self.cache_policy {
            ElaborationCachePolicy::BackwardReplay(replay) => replay.run.retention(value.expr),
            ElaborationCachePolicy::None | ElaborationCachePolicy::Ranked(_) => unreachable!(),
        };
        let Some(closes_at) = closes_at else {
            return Ok(());
        };
        match self.replay_resident_state(value.fingerprint) {
            ReplayResidentState::Visible => {
                self.residents
                    .get_mut(&value.fingerprint)
                    .expect("a visible replay value is physically resident")
                    .retain_for(value.expr, closes_at);
                return Ok(());
            }
            ReplayResidentState::RetiredPinned => return Err(PlanError::ReplayInfeasible),
            ReplayResidentState::Absent => {}
        }

        let need = field_lanes(value.field);
        if !self.replay_evict_expired_to_fit(need)? {
            if let Some(state) = &mut self.backward_demand {
                state.events.push(BwdEvent::Refuse {
                    value: value.expr,
                    need: need as u32,
                });
            }
            return Err(PlanError::ReplayRefused {
                value: value.expr,
                need,
            });
        }
        self.emit(EvalOp::CacheStore { value, from })?;
        self.plan
            .attribution
            .entry(value.expr)
            .or_default()
            .cache_stores += 1;
        self.resident_lanes += need;
        self.residents.insert(
            value.fingerprint,
            ResidentEntry {
                value,
                priority: closes_at as f64,
                replay_owners: BTreeSet::from([value.expr]),
            },
        );
        if let Some(state) = &mut self.backward_demand {
            state.events.push(BwdEvent::Admit {
                value: value.expr,
                width: need as u8,
            });
        }
        self.update_peak();
        Ok(())
    }

    fn replay_drop_expired(&mut self) -> Result<(), PlanError> {
        let mut victims = {
            let ElaborationCachePolicy::BackwardReplay(replay) = &self.cache_policy else {
                unreachable!()
            };
            self.residents
                .iter()
                .filter(|(fingerprint, entry)| {
                    !self.pinned.contains(fingerprint)
                        && entry.replay_closes_at(&replay.run).is_none()
                })
                .map(|(&fingerprint, entry)| {
                    (
                        !entry.replay_dead(&replay.run),
                        entry.priority as usize,
                        entry.value.expr,
                        fingerprint,
                    )
                })
                .collect::<Vec<_>>()
        };
        victims.sort();
        for (_, _, _, fingerprint) in victims {
            self.drop_replay_resident(fingerprint)?;
        }
        Ok(())
    }

    fn replay_evict_expired_to_fit(&mut self, extra_lanes: usize) -> Result<bool, PlanError> {
        loop {
            if self
                .resident_lanes
                .saturating_add(self.live_lanes)
                .saturating_add(extra_lanes)
                <= self.budget_lanes
            {
                return Ok(true);
            }
            let victim = {
                let ElaborationCachePolicy::BackwardReplay(replay) = &self.cache_policy else {
                    unreachable!()
                };
                self.residents
                    .iter()
                    .filter(|(fingerprint, entry)| {
                        !self.pinned.contains(fingerprint)
                            && entry.replay_closes_at(&replay.run).is_none()
                    })
                    .min_by_key(|(fingerprint, entry)| {
                        (
                            !entry.replay_dead(&replay.run),
                            entry.priority as usize,
                            entry.value.expr,
                            **fingerprint,
                        )
                    })
                    .map(|(&fingerprint, _)| fingerprint)
            };
            let Some(victim) = victim else {
                return Ok(false);
            };
            self.drop_replay_resident(victim)?;
        }
    }

    fn drop_replay_resident(&mut self, fingerprint: ValueFingerprint) -> Result<(), PlanError> {
        let Some(value) = self.residents.get(&fingerprint).map(|entry| entry.value) else {
            return Ok(());
        };
        self.drop_resident(fingerprint)?;
        if let Some(state) = &mut self.backward_demand {
            state.events.push(BwdEvent::Evict {
                value: value.expr,
                expired: true,
            });
        }
        Ok(())
    }

    fn drop_resident(&mut self, fingerprint: ValueFingerprint) -> Result<(), PlanError> {
        debug_assert!(
            !self.pinned.contains(&fingerprint),
            "a pending operand must be consumed before its resident can be dropped"
        );
        let Some(entry) = self.residents.remove(&fingerprint) else {
            return Ok(());
        };
        self.replay_logically_retired.remove(&fingerprint);
        self.resident_lanes -= field_lanes(entry.value.field);
        self.emit(EvalOp::CacheDrop(entry.value))?;
        if self.trace_residency {
            self.plan.residency_events.push(PlanResidencyEvent {
                site: None,
                value: entry.value,
                kind: PlanResidencyEventKind::Evict,
                residents_after: self.residents.values().map(|entry| entry.value).collect(),
            });
        }
        Ok(())
    }

    fn ensure_transient_capacity(&mut self, extra_lanes: usize) -> Result<(), PlanError> {
        if matches!(
            &self.cache_policy,
            ElaborationCachePolicy::BackwardReplay(_)
        ) {
            return self
                .replay_evict_expired_to_fit(extra_lanes)?
                .then_some(())
                .ok_or(PlanError::ReplayInfeasible);
        }
        while self
            .resident_lanes
            .saturating_add(self.live_lanes)
            .saturating_add(extra_lanes)
            > self.budget_lanes
        {
            let victim = self
                .residents
                .iter()
                .filter(|(fingerprint, _)| !self.pinned.contains(fingerprint))
                .min_by(|a, b| a.1.priority.total_cmp(&b.1.priority).then(a.0.cmp(b.0)))
                .map(|(&fingerprint, _)| fingerprint);
            let Some(victim) = victim else {
                return Err(PlanError::BudgetExceeded {
                    budget_lanes: self.budget_lanes,
                    required_transient_lanes: self.live_lanes.saturating_add(extra_lanes),
                });
            };
            self.drop_resident(victim)?;
        }
        Ok(())
    }

    fn update_peak(&mut self) {
        debug_assert!(
            matches!(
                &self.cache_policy,
                ElaborationCachePolicy::BackwardReplay(_)
            ) || self.live_lanes.saturating_add(self.resident_lanes) <= self.budget_lanes,
            "symbolic residency exceeded the configured lane budget"
        );
        self.plan.stats.peak_live_lanes = self
            .plan
            .stats
            .peak_live_lanes
            .max(self.live_lanes.saturating_add(self.resident_lanes));
    }

    fn prepare_compiler_temp(&mut self, extra_lanes: usize) -> Result<(), PlanError> {
        if matches!(
            &self.cache_policy,
            ElaborationCachePolicy::BackwardReplay(_)
        ) {
            self.replay_drop_expired()
        } else {
            self.ensure_transient_capacity(extra_lanes)
        }
    }

    fn save_acc(&mut self, field: FieldKind) -> Result<TempRef, PlanError> {
        let temp = TempRef {
            id: TempId(self.next_temp),
            field,
        };
        self.next_temp += 1;
        self.prepare_compiler_temp(field_lanes(field))?;
        self.emit(EvalOp::SaveAcc(temp))?;
        Ok(temp)
    }

    fn emit(&mut self, op: EvalOp) -> Result<(), PlanError> {
        match &op {
            EvalOp::AccInit(operand) => self.count_operand(*operand)?,
            EvalOp::AccAdd { operand, .. } | EvalOp::AccMul(operand) => {
                self.plan.stats.arithmetic_ops += 1;
                self.count_operand(*operand)?;
            }
            EvalOp::AccFma { lhs, rhs, .. } => {
                self.plan.stats.arithmetic_ops += 1;
                self.count_operand(*lhs)?;
                self.count_operand(*rhs)?;
            }
            EvalOp::AccNeg => self.plan.stats.arithmetic_ops += 1,
            EvalOp::SaveAcc(temp) => {
                let width = field_lanes(temp.field);
                self.live_temps.insert(temp.id, width);
                self.live_lanes += width;
                self.plan.stats.stash_stores += 1;
                self.update_peak();
            }
            EvalOp::CacheStore { value, from } => {
                self.plan.stats.cache_stores += 1;
                if *from == CacheStoreFrom::Source {
                    self.record_source_traffic(*value);
                    self.count_operand(Operand::Source(*value))?;
                }
            }
            EvalOp::CacheDrop(_) => self.plan.stats.cache_drops += 1,
            EvalOp::Commit { from, .. } => {
                self.plan.stats.commits += 1;
                if let MaterializeFrom::Source(value) = from {
                    self.record_source_traffic(*value);
                    self.count_operand(Operand::Source(*value))?;
                }
            }
            EvalOp::ReturnAcc { .. } => {}
        }
        self.plan.ops.push(op);
        Ok(())
    }

    fn count_operand(&mut self, operand: Operand) -> Result<(), PlanError> {
        match operand {
            Operand::Source(value) => {
                if self.layer.resolutions.contains_key(&value.expr) {
                    return Ok(());
                }
                let Expr::Source(source) = self.layer.exprs[value.expr.0 as usize] else {
                    return Err(PlanError::ExpectedSource(value.expr));
                };
                if matches!(
                    self.layer.sources[source.0 as usize].kind,
                    SourceKind::Read { .. }
                ) {
                    self.plan.stats.dram_read_lanes += field_lanes(value.field);
                }
            }
            Operand::Resident(_) => {}
            Operand::Temp(temp) => {
                let Some(width) = self.live_temps.remove(&temp.id) else {
                    return Err(PlanError::TempConsumedTwice(temp.id));
                };
                self.live_lanes -= width;
                self.plan.stats.stash_loads += 1;
            }
            Operand::Unit { .. } | Operand::BackwardSpecial { .. } => {}
        }
        Ok(())
    }

    fn value_ref(&self, expr: ExprId) -> ValueRef {
        ValueRef {
            expr,
            fingerprint: self.fingerprint(expr),
            field: self.field(expr),
        }
    }

    fn fingerprint(&self, expr: ExprId) -> ValueFingerprint {
        self.fingerprints[expr.0 as usize]
    }

    fn field(&self, expr: ExprId) -> FieldKind {
        self.expr_fields[expr.0 as usize]
    }
}

fn extended(path: &[PathStep], step: PathStep) -> Vec<PathStep> {
    let mut out = Vec::with_capacity(path.len() + 1);
    out.extend_from_slice(path);
    out.push(step);
    out
}

fn merge_priority(preferences: &mut PreferenceMap, value: ValueFingerprint, priority: f64) {
    match preferences.get_mut(&value) {
        Some(existing) if priority.total_cmp(existing).is_gt() => *existing = priority,
        Some(_) => {}
        None => {
            preferences.insert(value, priority);
        }
    }
}

pub fn field_lanes(field: FieldKind) -> usize {
    match field {
        FieldKind::Base => 1,
        FieldKind::Ext => 4,
    }
}

fn is_zero_expr(layer: &DagLayer, expr: ExprId) -> bool {
    if layer.resolutions.contains_key(&expr) {
        return false;
    }
    match &layer.exprs[expr.0 as usize] {
        Expr::Source(source) => matches!(
            layer.sources[source.0 as usize].kind,
            SourceKind::Constant { value: 0 }
        ),
        Expr::Mul(children) => children.iter().any(|&child| is_zero_expr(layer, child)),
        Expr::Add(_) => false,
    }
}

fn unit_sign_expr(layer: &DagLayer, expr: ExprId) -> Option<bool> {
    if layer.resolutions.contains_key(&expr) {
        return None;
    }
    match &layer.exprs[expr.0 as usize] {
        Expr::Source(source) => match layer.sources[source.0 as usize].kind {
            SourceKind::Constant { value: 1 } => Some(false),
            SourceKind::Constant {
                value: BABYBEAR_NEG_ONE,
            } => Some(true),
            _ => None,
        },
        Expr::Mul(children) if !children.is_empty() => {
            let mut negative = false;
            for &child in children {
                negative ^= unit_sign_expr(layer, child)?;
            }
            Some(negative)
        }
        Expr::Add(_) | Expr::Mul(_) => None,
    }
}

fn product_unit_sign(layer: &DagLayer, expr: ExprId) -> bool {
    let Expr::Mul(children) = &layer.exprs[expr.0 as usize] else {
        return false;
    };
    children
        .iter()
        .filter_map(|&child| unit_sign_expr(layer, child))
        .fold(false, |negative, factor| negative ^ factor)
}

/// Apply algebraic identities before sites, pressure, and instructions are
/// formed. Unit factors contribute only sign parity and never become operands.
fn effective_child_occurrences(
    layer: &DagLayer,
    mut children: Vec<ChildOccurrence>,
    operation: ReductionOp,
) -> Vec<ChildOccurrence> {
    match operation {
        ReductionOp::Add => {
            children.retain(|child| !is_zero_expr(layer, child.expr));
            children
        }
        ReductionOp::Mul => {
            children.retain(|child| unit_sign_expr(layer, child.expr).is_none());
            children
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap, HashSet};

    use cs::definitions::GKRAddress;
    use cs::gkr_compiler::dag_ir::{
        ArenaBuilder, BatchingOrder, Bf, ChallengeKey, ChallengePower, ChallengeRef,
        ChallengeResolver, ClaimInfo, Ext, LookupResolver, LookupValueKind, ReadPlace,
        ReadResolver, ResolutionStrategy, Resolvers, Root, RootGroup, RootSlot, SinkKind, SourceId,
        SourceInfo, SourceKind, VirtualSetupKind, VirtualSetupResolver, eval_layer_root,
        expr_field,
    };
    use field::{FieldExtension, PrimeField};

    use crate::fwd::context::{ForwardAction, RootOutput};
    use crate::fwd::interp::interpret_layer_row;
    use crate::fwd::isa::{Instr, MAX_CELL, OperandLine};

    use crate::bwd::fragment::{FragmentSpec, MergedRecipe};
    use crate::bwd::plan::{BwdOccurrencePlan, PlanEntry, plan_entries_fnv};

    use super::*;

    #[test]
    fn cell_budget_conversion_is_checked_and_lane_exact() {
        assert_eq!(budget_lanes_from_cells(2), Some(8));
        assert_eq!(budget_lanes_from_cells(3), Some(12));
        assert_eq!(budget_lanes_from_cells(4), Some(16));
        assert_eq!(budget_lanes_from_cells(0), None);
        assert_eq!(budget_lanes_from_cells(MAX_CELL as usize / 4 + 1), None,);
        assert_eq!(budget_lanes_from_cells(usize::MAX), None);
    }

    fn read(arena: &mut ArenaBuilder, column: usize) -> ExprId {
        let source = arena.intern_source(SourceKind::Read {
            place: cs::gkr_compiler::dag_ir::ReadPlace::BaseLayerWitness { column },
        });
        arena.source_expr(source)
    }

    fn constant(arena: &mut ArenaBuilder, value: u32) -> ExprId {
        let source = arena.intern_source(SourceKind::Constant { value });
        arena.source_expr(source)
    }

    fn challenge(arena: &mut ArenaBuilder, power: u32) -> ExprId {
        let source = arena.intern_source(SourceKind::Challenge {
            reference: ChallengeRef {
                key: ChallengeKey::ClaimBatching,
                power: if power == 1 {
                    ChallengePower::One
                } else {
                    ChallengePower::Static(power)
                },
            },
        });
        arena.source_expr(source)
    }

    fn root(expr: ExprId, materialize: bool) -> Root {
        root_at(expr, materialize, 0)
    }

    fn root_at(expr: ExprId, materialize: bool, offset: usize) -> Root {
        Root {
            expr,
            materialize: materialize.then_some(SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset },
                field: FieldKind::Base,
            }),
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: offset,
                    slot: RootSlot::Output(0),
                },
            }),
        }
    }

    fn layer(arena: ArenaBuilder, root: Root) -> DagLayer {
        layer_with_roots(arena, vec![root])
    }

    fn layer_with_roots(arena: ArenaBuilder, roots: Vec<Root>) -> DagLayer {
        DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            batching: BatchingOrder {
                roots: (0..roots.len()).map(|i| RootId(i as u32)).collect(),
            },
            roots,
            resolutions: BTreeMap::new(),
        }
    }

    fn fields(layer: &DagLayer) -> Vec<FieldKind> {
        (0..layer.exprs.len())
            .map(|i| expr_field(&layer.exprs, &layer.sources, ExprId(i as u32)).unwrap())
            .collect()
    }

    #[derive(Default)]
    struct StaticOracle {
        responses: HashMap<SiteId, Vec<RetentionPreference>>,
        calls: Vec<SiteId>,
    }

    impl CacheOracle for StaticOracle {
        fn desired_after(
            &mut self,
            site: &SiteId,
            _entry: CacheStateView<'_>,
        ) -> Vec<RetentionPreference> {
            self.calls.push(site.clone());
            self.responses.get(site).cloned().unwrap_or_default()
        }
    }

    fn root_site(plan: &EvalPlan, root_expr: ValueFingerprint) -> SiteId {
        plan.sites
            .iter()
            .find(|site| site.path.is_empty() && site.value == root_expr)
            .unwrap()
            .clone()
    }

    fn ext(value: u32) -> Ext {
        <Ext as FieldExtension<Bf>>::from_base(Bf::from_u32_with_reduction(value))
    }

    struct TestReadResolver;
    impl ReadResolver for TestReadResolver {
        fn read(&self, place: &ReadPlace, row: usize) -> Ext {
            let index = match place {
                ReadPlace::BaseLayerMemory { column }
                | ReadPlace::BaseLayerWitness { column }
                | ReadPlace::Setup { column } => *column,
                ReadPlace::Scratch { slot } => *slot,
                ReadPlace::LayerOutput { layer, offset }
                | ReadPlace::CacheOutput { layer, offset } => layer * 100 + offset,
            };
            ext(2 + index as u32 + 17 * row as u32)
        }
    }

    struct TestLookupResolver;
    impl LookupResolver for TestLookupResolver {
        fn lookup(
            &self,
            _kind: &LookupValueKind,
            set_index: usize,
            _evaluated_query: Ext,
            row: usize,
        ) -> Bf {
            Bf::from_u32_with_reduction(5 + set_index as u32 + row as u32)
        }
    }

    struct TestVirtualSetupResolver;
    impl VirtualSetupResolver for TestVirtualSetupResolver {
        fn virtual_setup(&self, _kind: &VirtualSetupKind, row: usize) -> Bf {
            Bf::from_u32_with_reduction(7 + row as u32)
        }
    }

    struct TestChallengeResolver;
    impl ChallengeResolver for TestChallengeResolver {
        fn challenge(&self, _reference: &ChallengeRef) -> Ext {
            ext(11)
        }
    }

    static TEST_READS: TestReadResolver = TestReadResolver;
    static TEST_LOOKUPS: TestLookupResolver = TestLookupResolver;
    static TEST_VIRTUAL_SETUP: TestVirtualSetupResolver = TestVirtualSetupResolver;
    static TEST_CHALLENGES: TestChallengeResolver = TestChallengeResolver;

    fn test_resolvers() -> Resolvers<'static> {
        Resolvers {
            read: &TEST_READS,
            lookup: &TEST_LOOKUPS,
            virtual_setup: &TEST_VIRTUAL_SETUP,
            challenge: &TEST_CHALLENGES,
        }
    }

    fn assert_plan_matches_roots(
        layer: &DagLayer,
        roots: &[RootId],
        plan: &EvalPlan,
    ) -> PlanExecution {
        let resolvers = test_resolvers();
        let execution = interpret_plan(plan, layer, 3, &resolvers).unwrap();
        let expected: Vec<Ext> = roots
            .iter()
            .map(|&root| eval_layer_root(layer, root, 3, &resolvers))
            .collect();
        let mut returned = execution
            .roots
            .iter()
            .filter(|observation| observation.root_id.is_none());
        let actual: Vec<Ext> = roots
            .iter()
            .map(|&root| {
                execution
                    .roots
                    .iter()
                    .find(|observation| observation.root_id == Some(root))
                    .or_else(|| returned.next())
                    .expect("every requested root must be observed")
                    .value
            })
            .collect();
        assert_eq!(actual, expected);
        execution
    }

    fn assert_packed_matches_plan(layer: &DagLayer, plan: &EvalPlan) -> PackedEvalPlan {
        let packed = pack_plan(plan, layer, PackConfig::default()).unwrap();
        let resolvers = test_resolvers();
        let scalar = interpret_plan(plan, layer, 3, &resolvers).unwrap();
        let grouped = interpret_packed_plan(&packed, layer, 3, &resolvers).unwrap();
        assert_eq!(grouped, scalar);
        assert_eq!(packed.stats.dram_read_lanes, plan.stats.dram_read_lanes);
        assert_eq!(
            packed.stats.scalar_arithmetic_ops + packed.stats.optimized_away_arithmetic_ops,
            plan.stats.arithmetic_ops
        );
        packed
    }

    fn assert_concrete_matches_roots(
        layer: &DagLayer,
        roots: &[RootId],
        plan: &EvalPlan,
        budget_lanes: usize,
    ) -> ConcreteEvalProgram {
        let packed = assert_packed_matches_plan(layer, plan);
        let concrete = bind_packed_plan(&packed, layer, roots, 0, budget_lanes).unwrap();
        let resolvers = test_resolvers();
        let outputs = interpret_layer_row(&concrete.compiled, layer, &resolvers, 3).unwrap();
        for &root in roots {
            assert_eq!(
                outputs.by_root[&root],
                eval_layer_root(layer, root, 3, &resolvers)
            );
        }
        assert!(
            concrete.compiled.stats.program_lanes <= packed.stats.packed_instructions,
            "concrete post-placement optimization may only remove instructions: concrete={} packed={}",
            concrete.compiled.stats.program_lanes,
            packed.stats.packed_instructions,
        );
        assert!(
            concrete.encoded.len() <= packed.stats.encoded_lanes,
            "concrete post-placement optimization may only remove encoded lanes: concrete={} packed={}",
            concrete.encoded.len(),
            packed.stats.encoded_lanes,
        );
        assert_eq!(
            concrete.compiled.stats.dram_traffic,
            packed.stats.dram_read_lanes
        );
        concrete
    }

    #[test]
    fn forward_alias_and_skip_actions_add_no_program_work() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let alias = read(&mut arena, 2);
        let sum = arena.add(vec![a, b]);
        let layer = layer_with_roots(
            arena,
            vec![
                root_at(sum, true, 0),
                root_at(alias, true, 1),
                root_at(alias, true, 2),
            ],
        );
        let roots = [RootId(0)];
        let plan = elaborate_uncached(&layer, &fields(&layer), &roots).unwrap();
        let packed = pack_plan(&plan, &layer, PackConfig::default()).unwrap();
        let plain = bind_packed_plan(&packed, &layer, &roots, 0, 16).unwrap();
        let actions = HashMap::from([
            (RootId(0), ForwardAction::Compute),
            (
                RootId(1),
                ForwardAction::CopyAlias {
                    src_addr: GKRAddress::BaseLayerWitness(2),
                    dst_addr: GKRAddress::BaseLayerWitness(3),
                },
            ),
            (RootId(2), ForwardAction::SkipScratchPrefill),
        ]);
        let with_actions = bind_packed_plan_with_actions(
            &packed,
            &layer,
            &roots,
            0,
            16,
            &actions,
            &HashMap::new(),
        )
        .unwrap();

        assert_eq!(with_actions.compiled.program, plain.compiled.program);
        assert_eq!(with_actions.encoded, plain.encoded);
        assert_eq!(with_actions.compiled.stats, plain.compiled.stats);
        assert_eq!(with_actions.compiled.skipped, vec![RootId(2)]);
        assert!(matches!(
            with_actions
                .compiled
                .root_outputs
                .iter()
                .find(|(root, _)| *root == RootId(1)),
            Some((_, RootOutput::Alias(OperandLine::LogicalGlobal { .. })))
        ));

        let resolvers = test_resolvers();
        let outputs = interpret_layer_row(&with_actions.compiled, &layer, &resolvers, 3).unwrap();
        assert_eq!(
            outputs.by_root[&RootId(0)],
            eval_layer_root(&layer, RootId(0), 3, &resolvers)
        );
        assert_eq!(
            outputs.by_root[&RootId(1)],
            eval_layer_root(&layer, RootId(1), 3, &resolvers)
        );
        assert!(!outputs.by_root.contains_key(&RootId(2)));
    }

    #[test]
    fn ready_binary_product_under_add_becomes_fma() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let product = arena.mul(vec![a, b]);
        let sum = arena.add(vec![product, c]);
        let layer = layer(arena, root(sum, true));

        let plan = elaborate_uncached(&layer, &fields(&layer), &[RootId(0)]).unwrap();
        let execution = assert_plan_matches_roots(&layer, &[RootId(0)], &plan);
        let product_fingerprint = structural_fingerprints(&layer).unwrap()[product.0 as usize];

        assert!(matches!(plan.ops[0], EvalOp::AccInit(Operand::Source(_))));
        assert!(matches!(plan.ops[1], EvalOp::AccFma { .. }));
        assert!(matches!(plan.ops[2], EvalOp::Commit { .. }));
        assert_eq!(plan.stats.dram_read_lanes, 3);
        assert_eq!(plan.stats.arithmetic_ops, 1);
        assert_eq!(plan.stats.peak_live_lanes, 0);
        assert!(
            execution
                .stored_values
                .iter()
                .all(|value| value.fingerprint != product_fingerprint),
            "FMA must not create an independently stored product"
        );
        assert!(!plan.ops.iter().any(|op| matches!(op, EvalOp::SaveAcc(_))));
        assert_eq!(plan.attribution[&product].fma_fusions, 1);
        assert_eq!(plan.attribution[&product].computations, 0);
        assert_eq!(plan.attribution[&product].additive_demands, 1);
        assert_eq!(plan.attribution[&sum].arithmetic_ops, 1);
        assert_eq!(
            plan.attribution
                .values()
                .map(|attribution| attribution.arithmetic_ops)
                .sum::<usize>(),
            plan.stats.arithmetic_ops
        );
    }

    #[test]
    fn computed_staging_can_merge_two_compound_products_into_one_fma_run() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let d = read(&mut arena, 3);
        let f = constant(&mut arena, 2);
        let g = constant(&mut arena, 3);
        let seed = constant(&mut arena, 5);
        let ab = arena.add(vec![a, b]);
        let cd = arena.add(vec![c, d]);
        let first = arena.mul(vec![ab, f]);
        let second = arena.mul(vec![cd, g]);
        let expression = arena.add(vec![seed, first, second]);
        let layer = layer(arena, root(expression, true));
        let natural = elaborate_uncached(&layer, &fields(&layer), &[RootId(0)]).unwrap();
        let natural_packed = pack_plan(&natural, &layer, PackConfig::default()).unwrap();
        let fingerprints = structural_fingerprints(&layer).unwrap();
        let index = StructuralSiteIndex::build(&layer, &fields(&layer), &[RootId(0)]).unwrap();
        let cd_staging_boundaries = index
            .staging_pairs()
            .iter()
            .filter(|pair| pair.staged.value == fingerprints[cd.0 as usize])
            .map(|pair| pair.boundary.path.len())
            .collect::<BTreeSet<_>>();
        assert_eq!(
            cd_staging_boundaries,
            BTreeSet::from([0, 1]),
            "the genome must distinguish ready-before-Add from ready-inside-product"
        );
        let staging_index = index
            .staging_pairs()
            .iter()
            .position(|pair| {
                pair.staged.value == fingerprints[cd.0 as usize] && pair.boundary.path.is_empty()
            })
            .unwrap();
        let cache_genes = vec![0.0; index.len()];
        let mut staging_genes = vec![0.0; index.staging_pairs().len()];
        staging_genes[staging_index] = 1.0;
        let mut oracle = GenomeOracle::new(&index, &cache_genes, &staging_genes).unwrap();
        let staged =
            elaborate_with_oracle(&layer, &fields(&layer), &[RootId(0)], 1, &mut oracle).unwrap();
        let staged_packed = pack_plan(&staged, &layer, PackConfig::default()).unwrap();

        assert_eq!(natural_packed.stats.dram_read_lanes, 4);
        assert_eq!(staged_packed.stats.dram_read_lanes, 4);
        assert_eq!(natural_packed.stats.packed_instructions, 9);
        assert_eq!(staged_packed.stats.packed_instructions, 6);
        assert_eq!(natural_packed.stats.arithmetic_instructions, 5);
        assert_eq!(staged_packed.stats.arithmetic_instructions, 2);
        assert_eq!(natural.stats.stash_stores, 1);
        assert_eq!(staged.stats.stash_stores, 0);
        assert_eq!(staged.stats.cache_stores, 1);
        assert_eq!(staged.stats.cache_hits, 1);
        assert_eq!(oracle.active_site_count(), 0);
        assert_eq!(
            natural.sites.iter().cloned().collect::<HashSet<_>>(),
            staged.sites.iter().cloned().collect::<HashSet<_>>(),
            "staging must reorder each structural demand, not duplicate or skip it"
        );
        assert_plan_matches_roots(&layer, &[RootId(0)], &natural);
        assert_plan_matches_roots(&layer, &[RootId(0)], &staged);
        assert_packed_matches_plan(&layer, &natural);
        assert_packed_matches_plan(&layer, &staged);
        assert_concrete_matches_roots(&layer, &[RootId(0)], &staged, 1);

        let context = PlanSearchContext::build(&layer, &fields(&layer), 0, 1).unwrap();
        let refined = staging_refinement(
            &context,
            &EvaluationGenome::neutral(&context),
            context.site_index().staging_pairs().len(),
        )
        .unwrap();
        assert_eq!(refined.improvements, 1);
        assert_eq!(refined.best.fitness.dram_read_lanes, 4);
        assert_eq!(refined.best.fitness.program_instructions, 6);

        let searched = mutation_search(
            &context,
            MutationSearchConfig {
                population: 1,
                evaluations: 2,
                staging_evaluations: context.site_index().staging_pairs().len(),
                seed: 0,
                cache_mutations: 1,
            },
        )
        .unwrap();
        assert_eq!(searched.best.fitness.program_instructions, 6);
        assert_eq!(searched.telemetry.staging_improvements, 1);
    }

    #[test]
    fn resident_boundary_hit_does_not_query_descendant_staging() {
        struct HitAwareOracle {
            retained: ValueFingerprint,
            boundary_queries: usize,
        }

        impl CacheOracle for HitAwareOracle {
            fn stage_before(&mut self, boundary: &SiteId) -> Vec<StagingPreference> {
                if boundary.value == self.retained {
                    self.boundary_queries += 1;
                }
                Vec::new()
            }

            fn desired_after(
                &mut self,
                _site: &SiteId,
                _entry: CacheStateView<'_>,
            ) -> Vec<RetentionPreference> {
                vec![RetentionPreference {
                    value: self.retained,
                    priority: 1.0,
                }]
            }
        }

        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let shared = arena.add(vec![a, b]);
        let expression = arena.mul(vec![shared, shared]);
        let layer = layer(arena, root(expression, true));
        let retained = structural_fingerprints(&layer).unwrap()[shared.0 as usize];
        let mut oracle = HitAwareOracle {
            retained,
            boundary_queries: 0,
        };

        let plan =
            elaborate_with_oracle(&layer, &fields(&layer), &[RootId(0)], 1, &mut oracle).unwrap();

        assert_plan_matches_roots(&layer, &[RootId(0)], &plan);
        assert_eq!(oracle.boundary_queries, 1);
        assert_eq!(plan.stats.cache_stores, 1);
        assert_eq!(plan.stats.cache_hits, 1);
    }

    #[test]
    fn zero_addends_and_one_factors_are_elided_before_planning() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let zero = constant(&mut arena, 0);
        let one = constant(&mut arena, 1);
        let nested_one = arena.mul(vec![one, one]);
        let zero_product = arena.mul(vec![zero, a]);
        let product = arena.mul(vec![a, nested_one, b, one]);
        let sum = arena.add(vec![zero, zero_product, product, c]);
        let layer = layer(arena, root(sum, true));

        let plan = elaborate_uncached(&layer, &fields(&layer), &[RootId(0)]).unwrap();
        assert_plan_matches_roots(&layer, &[RootId(0)], &plan);
        assert_eq!(plan.stats.arithmetic_ops, 1);
        assert!(!plan.ops.iter().any(|op| matches!(op, EvalOp::AccMul(_))));
        assert!(plan.ops.iter().any(|op| matches!(
            op,
            EvalOp::AccFma {
                lhs: Operand::Source(lhs),
                rhs: Operand::Source(rhs),
                ..
            } if [lhs.expr, rhs.expr].iter().all(|expr| *expr == a || *expr == b)
        )));

        // Concrete binding rejects zero operands and multiplication by one, so
        // success also checks that neither identity leaked past the planner.
        assert_concrete_matches_roots(&layer, &[RootId(0)], &plan, 8);
    }

    #[test]
    fn all_one_product_initializes_without_multiplication() {
        let mut arena = ArenaBuilder::new();
        let one = constant(&mut arena, 1);
        let inner = arena.mul(vec![one, one]);
        let product = arena.mul(vec![inner, one]);
        let layer = layer(arena, root(product, true));

        let plan = elaborate_uncached(&layer, &fields(&layer), &[RootId(0)]).unwrap();
        assert_plan_matches_roots(&layer, &[RootId(0)], &plan);
        assert_eq!(plan.stats.arithmetic_ops, 0);
        assert!(
            !plan
                .ops
                .iter()
                .any(|op| matches!(op, EvalOp::AccMul(_) | EvalOp::AccFma { .. }))
        );
        assert_concrete_matches_roots(&layer, &[RootId(0)], &plan, 8);
    }

    #[test]
    fn even_neg_one_parity_cancels_before_planning() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let neg_one = constant(&mut arena, BABYBEAR_NEG_ONE);
        let product = arena.mul(vec![a, neg_one, neg_one]);
        let layer = layer(arena, root(product, true));

        let plan = elaborate_uncached(&layer, &fields(&layer), &[RootId(0)]).unwrap();
        assert_plan_matches_roots(&layer, &[RootId(0)], &plan);
        assert_eq!(plan.stats.arithmetic_ops, 0);
        assert!(!plan.ops.iter().any(|op| matches!(
            op,
            EvalOp::AccMul(_) | EvalOp::AccNeg | EvalOp::AccFma { .. }
        )));
        assert_concrete_matches_roots(&layer, &[RootId(0)], &plan, 8);
    }

    #[test]
    fn adjacent_nested_negations_cancel_during_packing() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let neg_one = constant(&mut arena, BABYBEAR_NEG_ONE);
        let inner = arena.mul(vec![a, neg_one]);
        let outer = arena.mul(vec![inner, neg_one]);
        let layer = layer(arena, root(outer, true));

        let plan = elaborate_uncached(&layer, &fields(&layer), &[RootId(0)]).unwrap();
        assert_plan_matches_roots(&layer, &[RootId(0)], &plan);
        assert_eq!(plan.stats.arithmetic_ops, 2);
        let packed = assert_packed_matches_plan(&layer, &plan);
        assert_eq!(packed.stats.scalar_arithmetic_ops, 0);
        assert_eq!(packed.stats.optimized_away_arithmetic_ops, 2);
        assert!(!packed.ops.iter().any(|op| matches!(
            op,
            PackedEvalOp::AccMul { .. } | PackedEvalOp::AccFma { .. }
        )));
        assert_concrete_matches_roots(&layer, &[RootId(0)], &plan, 8);
    }

    #[test]
    fn odd_product_sign_folds_into_fma_or_mul_negate_flag() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let d = read(&mut arena, 3);
        let e = read(&mut arena, 4);
        let neg_one = constant(&mut arena, BABYBEAR_NEG_ONE);
        let product = arena.mul(vec![a, neg_one, b]);
        let product_root = arena.mul(vec![d, neg_one, e]);
        let sum = arena.add(vec![c, product]);
        let layer = layer_with_roots(
            arena,
            vec![root_at(sum, true, 0), root_at(product_root, true, 1)],
        );

        let roots = [RootId(0), RootId(1)];
        let plan = elaborate_uncached(&layer, &fields(&layer), &roots).unwrap();
        assert_plan_matches_roots(&layer, &roots, &plan);
        assert!(plan.ops.iter().any(|op| matches!(
            op,
            EvalOp::AccFma {
                sign: Sign::Minus,
                ..
            }
        )));

        let packed = assert_packed_matches_plan(&layer, &plan);
        assert!(packed.ops.iter().any(|op| matches!(
            op,
            PackedEvalOp::AccFma {
                sign: Sign::Minus,
                ..
            }
        )));
        assert!(packed.ops.iter().any(|op| matches!(
            op,
            PackedEvalOp::AccMul {
                sign: Sign::Minus,
                operands,
                ..
            } if operands.len() == 1
        )));

        let concrete = bind_packed_plan(&packed, &layer, &roots, 0, 8).unwrap();
        assert!(
            concrete
                .compiled
                .program
                .instrs
                .iter()
                .any(|instr| matches!(
                    instr,
                    Instr::Fma {
                        sign: Sign::Minus,
                        ..
                    }
                ))
        );
        assert!(
            concrete
                .compiled
                .program
                .instrs
                .iter()
                .any(|instr| matches!(
                    instr,
                    Instr::Mul {
                        negate_acc: true,
                        operands,
                        ..
                    } if operands.len() == 1
                ))
        );
    }

    #[test]
    fn negative_single_factor_folds_into_add_sign() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let c = read(&mut arena, 1);
        let neg_one = constant(&mut arena, BABYBEAR_NEG_ONE);
        let negative_a = arena.mul(vec![neg_one, a]);
        let sum = arena.add(vec![negative_a, c]);
        let layer = layer(arena, root(sum, true));

        let plan = elaborate_uncached(&layer, &fields(&layer), &[RootId(0)]).unwrap();
        assert_plan_matches_roots(&layer, &[RootId(0)], &plan);
        assert!(plan.ops.iter().any(|op| matches!(
            op,
            EvalOp::AccAdd {
                sign: Sign::Minus,
                operand: Operand::Source(value),
            } if value.expr == a
        )));
        assert!(
            !plan
                .ops
                .iter()
                .any(|op| matches!(op, EvalOp::AccNeg | EvalOp::SaveAcc(_)))
        );

        let packed = assert_packed_matches_plan(&layer, &plan);
        assert!(packed.ops.iter().any(|op| matches!(
            op,
            PackedEvalOp::AccAdd {
                sign: Sign::Minus,
                operands,
                ..
            } if operands.len() == 1
        )));
        let concrete = bind_packed_plan(&packed, &layer, &[RootId(0)], 0, 8).unwrap();
        assert!(
            concrete
                .compiled
                .program
                .instrs
                .iter()
                .any(|instr| matches!(
                    instr,
                    Instr::Add {
                        sign: Sign::Minus,
                        operands,
                        ..
                    } if operands.len() == 1
                ))
        );
    }

    #[test]
    fn packer_groups_wide_add_mul_and_fma_without_cost_or_value_drift() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let d = read(&mut arena, 3);
        let e = read(&mut arena, 4);
        let f = read(&mut arena, 5);
        let g = read(&mut arena, 6);
        let wide_add = arena.add(vec![a, b, c, d, e]);
        let wide_mul = arena.mul(vec![a, b, c, d]);
        let ab = arena.mul(vec![a, b]);
        let cd = arena.mul(vec![c, d]);
        let ef = arena.mul(vec![e, f]);
        let dot = arena.add(vec![g, ab, cd, ef]);
        let layer = layer_with_roots(
            arena,
            vec![
                root_at(wide_add, true, 0),
                root_at(wide_mul, true, 1),
                root_at(dot, true, 2),
            ],
        );
        let roots = [RootId(0), RootId(1), RootId(2)];
        let plan = elaborate_uncached(&layer, &fields(&layer), &roots).unwrap();

        let packed = assert_packed_matches_plan(&layer, &plan);

        assert_eq!(plan.stats.arithmetic_ops, 10);
        assert_eq!(packed.stats.unpacked_instructions, 16);
        assert_eq!(packed.stats.packed_instructions, 9);
        assert_eq!(packed.stats.arithmetic_instructions, 3);
        assert!(packed.ops.iter().any(|op| matches!(
            op,
            PackedEvalOp::AccAdd { operands, .. } if operands.len() == 4
        )));
        assert!(packed.ops.iter().any(|op| matches!(
            op,
            PackedEvalOp::AccMul { operands, .. } if operands.len() == 3
        )));
        assert!(packed.ops.iter().any(|op| matches!(
            op,
            PackedEvalOp::AccFma { pairs, .. } if pairs.len() == 3
        )));
        let concrete = assert_concrete_matches_roots(&layer, &roots, &plan, 8);
        assert_eq!(concrete.compiled.program.instrs.len(), 9);
    }

    #[test]
    fn packer_splits_at_configured_arity_without_value_drift() {
        let mut arena = ArenaBuilder::new();
        let values = (0..6).map(|column| read(&mut arena, column)).collect();
        let sum = arena.add(values);
        let layer = layer(arena, root(sum, true));
        let plan = elaborate_uncached(&layer, &fields(&layer), &[RootId(0)]).unwrap();

        let packed = pack_plan(
            &plan,
            &layer,
            PackConfig {
                max_add_operands: 2,
                ..PackConfig::default()
            },
        )
        .unwrap();
        let add_arities: Vec<_> = packed
            .ops
            .iter()
            .filter_map(|op| match op {
                PackedEvalOp::AccAdd { operands, .. } => Some(operands.len()),
                _ => None,
            })
            .collect();
        let resolvers = test_resolvers();

        assert_eq!(add_arities, vec![2, 2, 1]);
        assert_eq!(
            interpret_packed_plan(&packed, &layer, 3, &resolvers).unwrap(),
            interpret_plan(&plan, &layer, 3, &resolvers).unwrap()
        );
    }

    #[test]
    fn second_compound_child_stashes_and_refolds_partial() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let d = read(&mut arena, 3);
        let left = arena.mul(vec![a, b, a]);
        let right = arena.mul(vec![c, d, c]);
        let sum = arena.add(vec![left, right]);
        let layer = layer(arena, root(sum, true));

        let plan = elaborate_uncached(&layer, &fields(&layer), &[RootId(0)]).unwrap();

        assert_eq!(
            plan.ops
                .iter()
                .filter(|op| matches!(op, EvalOp::SaveAcc(_)))
                .count(),
            1
        );
        assert_eq!(plan.stats.stash_stores, 1);
        assert_eq!(plan.stats.stash_loads, 1);
        assert_eq!(plan.stats.peak_live_lanes, 1);
    }

    #[test]
    fn extension_partial_uses_four_stash_lanes() {
        let mut arena = ArenaBuilder::new();
        let a = challenge(&mut arena, 1);
        let b = challenge(&mut arena, 2);
        let c = challenge(&mut arena, 3);
        let d = challenge(&mut arena, 4);
        let left = arena.mul(vec![a, b, a]);
        let right = arena.mul(vec![c, d, c]);
        let sum = arena.add(vec![left, right]);
        let mut output = root(sum, true);
        output.materialize.as_mut().unwrap().field = FieldKind::Ext;
        let layer = layer(arena, output);

        let plan = elaborate_uncached(&layer, &fields(&layer), &[RootId(0)]).unwrap();

        assert_eq!(plan.stats.peak_live_lanes, 4);
        assert!(matches!(plan.ops.last(), Some(EvalOp::Commit { .. })));
        assert_plan_matches_roots(&layer, &[RootId(0)], &plan);
        let concrete = assert_concrete_matches_roots(&layer, &[RootId(0)], &plan, 4);
        assert_eq!(concrete.stats.max_live_lanes, 4);
    }

    #[test]
    fn resolved_cone_is_one_source_like_special_operand() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let resolved = arena.add(vec![a, b]);
        let sum = arena.add(vec![resolved, c]);
        let mut layer = layer(arena, root(sum, true));
        layer
            .resolutions
            .insert(resolved, ResolutionStrategy::PeekSetup);

        let sites = enumerate_structural_sites(&layer, &[RootId(0)]).unwrap();
        let plan = elaborate_uncached(&layer, &fields(&layer), &[RootId(0)]).unwrap();

        assert_eq!(sites.len(), 3, "root, resolved terminal, and direct read");
        assert_eq!(plan.stats.dram_read_lanes, 1);
        assert!(plan.ops.iter().any(|op| matches!(
            op,
            EvalOp::AccInit(Operand::Source(value))
                | EvalOp::AccAdd {
                    operand: Operand::Source(value),
                    ..
                }
                if value.expr == resolved
        )));
        assert_concrete_matches_roots(&layer, &[RootId(0)], &plan, 4);
    }

    #[test]
    fn stable_sites_do_not_depend_on_commutative_child_array_order() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let sum = arena.add(vec![a, b, c]);
        let mut first = layer(arena, root(sum, true));
        let mut second = first.clone();
        let Expr::Add(first_children) = &mut first.exprs[sum.0 as usize] else {
            unreachable!()
        };
        first_children.rotate_left(1);
        let Expr::Add(second_children) = &mut second.exprs[sum.0 as usize] else {
            unreachable!()
        };
        second_children.reverse();

        let first_plan = elaborate_uncached(&first, &fields(&first), &[RootId(0)]).unwrap();
        let second_plan = elaborate_uncached(&second, &fields(&second), &[RootId(0)]).unwrap();
        let first_sites: HashSet<_> = first_plan.sites.into_iter().collect();
        let second_sites: HashSet<_> = second_plan.sites.into_iter().collect();

        assert_eq!(first_sites, second_sites);
        assert_eq!(
            structural_fingerprints(&first).unwrap()[sum.0 as usize],
            structural_fingerprints(&second).unwrap()[sum.0 as usize]
        );
    }

    #[test]
    fn structural_site_domain_survives_root_reordering_and_cache_pruning() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let sum = arena.add(vec![a, b]);
        let layer = layer_with_roots(arena, vec![root_at(sum, true, 0), root_at(sum, true, 1)]);
        let forward = [RootId(0), RootId(1)];
        let reverse = [RootId(1), RootId(0)];
        let domain = enumerate_structural_sites(&layer, &forward).unwrap();

        assert_eq!(
            domain,
            enumerate_structural_sites(&layer, &reverse).unwrap(),
            "the genome domain must not inherit root execution order"
        );

        let expr_fields = fields(&layer);
        let baseline = elaborate_uncached(&layer, &expr_fields, &forward).unwrap();
        let fingerprints = structural_fingerprints(&layer).unwrap();
        let first_root_site = baseline
            .sites
            .iter()
            .find(|site| {
                site.path.is_empty() && site.root.materialize == layer.roots[0].materialize
            })
            .unwrap()
            .clone();
        let mut oracle = StaticOracle::default();
        oracle.responses.insert(
            first_root_site,
            vec![RetentionPreference {
                value: fingerprints[sum.0 as usize],
                priority: 1.0,
            }],
        );

        let plan = elaborate_with_oracle(&layer, &expr_fields, &forward, 1, &mut oracle).unwrap();
        let visited: HashSet<_> = plan.sites.iter().cloned().collect();

        assert!(visited.is_subset(&domain));
        assert!(domain.iter().any(|site| {
            site.root.materialize == layer.roots[1].materialize && !site.path.is_empty()
        }));
        assert!(!plan.sites.iter().any(|site| {
            site.root.materialize == layer.roots[1].materialize && !site.path.is_empty()
        }));
        assert_eq!(plan.stats.cache_hits, 1);
        assert_plan_matches_roots(&layer, &forward, &plan);
    }

    #[test]
    fn structural_site_index_is_stable_across_root_and_child_permutations() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let sum = arena.add(vec![a, b, c]);
        let mut first = layer_with_roots(arena, vec![root_at(sum, true, 0), root_at(sum, true, 1)]);
        let mut second = first.clone();
        let Expr::Add(first_children) = &mut first.exprs[sum.0 as usize] else {
            unreachable!()
        };
        first_children.rotate_left(1);
        let Expr::Add(second_children) = &mut second.exprs[sum.0 as usize] else {
            unreachable!()
        };
        second_children.reverse();

        let first_index =
            StructuralSiteIndex::build(&first, &fields(&first), &[RootId(0), RootId(1)]).unwrap();
        let second_index =
            StructuralSiteIndex::build(&second, &fields(&second), &[RootId(1), RootId(0)]).unwrap();

        assert_eq!(first_index.sites(), second_index.sites());
        for (position, site) in first_index.sites().iter().enumerate() {
            assert_eq!(first_index.position(site), Some(position));
        }
    }

    #[test]
    fn genome_oracle_trades_fma_for_reusable_product_materialization() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let d = read(&mut arena, 3);
        let product = arena.mul(vec![a, b]);
        let first_expr = arena.add(vec![c, product]);
        let second_expr = arena.add(vec![d, product]);
        let layer = layer_with_roots(
            arena,
            vec![root_at(first_expr, true, 0), root_at(second_expr, true, 1)],
        );
        let roots = [RootId(0), RootId(1)];
        let expr_fields = fields(&layer);
        let index = StructuralSiteIndex::build(&layer, &expr_fields, &roots).unwrap();
        let fingerprints = structural_fingerprints(&layer).unwrap();
        let product_fingerprint = fingerprints[product.0 as usize];

        let neutral_genes = vec![0.0; index.len()];
        let staging_genes = vec![0.0; index.staging_pairs().len()];
        let mut neutral_oracle = GenomeOracle::new(&index, &neutral_genes, &staging_genes).unwrap();
        let neutral =
            elaborate_with_oracle(&layer, &expr_fields, &roots, 2, &mut neutral_oracle).unwrap();
        assert_eq!(neutral.stats.dram_read_lanes, 6);
        assert_eq!(neutral.stats.cache_stores, 0);
        assert_eq!(neutral.stats.stash_stores, 0);
        assert_eq!(neutral_oracle.active_site_count(), 0);
        assert_eq!(
            neutral
                .ops
                .iter()
                .filter(|op| matches!(op, EvalOp::AccFma { .. }))
                .count(),
            2
        );
        assert_plan_matches_roots(&layer, &roots, &neutral);
        assert_packed_matches_plan(&layer, &neutral);

        let mut reuse_genes = vec![0.0; index.len()];
        for (position, site) in index.sites().iter().enumerate() {
            if site.root.materialize == layer.roots[1].materialize
                && site.value == product_fingerprint
            {
                reuse_genes[position] = 1.0;
            }
        }
        let mut reuse_oracle = GenomeOracle::new(&index, &reuse_genes, &staging_genes).unwrap();
        let reuse =
            elaborate_with_oracle(&layer, &expr_fields, &roots, 2, &mut reuse_oracle).unwrap();

        assert_eq!(reuse.stats.dram_read_lanes, 4);
        assert_eq!(reuse.stats.cache_stores, 1);
        assert_eq!(reuse.stats.cache_hits, 1);
        assert_eq!(reuse.stats.stash_stores, 1);
        assert_eq!(reuse_oracle.active_site_count(), 0);
        assert!(reuse.ops.iter().any(|op| matches!(
            op,
            EvalOp::CacheStore { value, .. } if value.fingerprint == product_fingerprint
        )));
        assert_plan_matches_roots(&layer, &roots, &reuse);
        assert_packed_matches_plan(&layer, &reuse);
        assert_concrete_matches_roots(&layer, &roots, &reuse, 2);
    }

    #[test]
    fn genome_oracle_rejects_invalid_gene_vectors() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let layer = layer(arena, root(a, true));
        let index = StructuralSiteIndex::build(&layer, &fields(&layer), &[RootId(0)]).unwrap();

        assert!(matches!(
            GenomeOracle::new(&index, &[], &[]),
            Err(GenomeOracleError::GeneCount { .. })
        ));
        assert!(matches!(
            GenomeOracle::new(&index, &[f64::NAN], &[]),
            Err(GenomeOracleError::NonFiniteGene { index: 0, .. })
        ));
    }

    #[test]
    fn forward_evaluation_unit_attaches_cache_sink_without_scheduling_it() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let cached = arena.mul(vec![a, b]);
        let atom = arena.add(vec![cached, a]);
        let cache_root = Root {
            expr: cached,
            materialize: Some(SinkInfo {
                kind: SinkKind::Cache {
                    layer: 0,
                    offset: 0,
                },
                field: FieldKind::Base,
            }),
            claim: None,
        };
        let atom_root = root_at(atom, true, 0);
        let claim_only = Root {
            expr: atom,
            materialize: None,
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                    slot: RootSlot::Constraint(0),
                },
            }),
        };
        let layer = layer_with_roots(arena, vec![cache_root, atom_root, claim_only]);

        let units = adapt_forward_relations(&layer).unwrap();

        assert_eq!(units.len(), 1);
        assert_eq!(units[0].roots, vec![RootId(1)]);
        let context = PlanSearchContext::build(&layer, &fields(&layer), 0, 1).unwrap();
        assert_eq!(context.selected_roots(), &[RootId(0), RootId(1)]);
        let scored = context.score(&EvaluationGenome::neutral(&context)).unwrap();
        let plan = scored.plan.unwrap();
        assert!(plan.sites.iter().all(|site| {
            site.root.claim_origin
                == layer.roots[1]
                    .claim
                    .as_ref()
                    .map(|claim| claim.origin.clone())
        }));
        let committed = plan
            .ops
            .iter()
            .filter_map(|op| match op {
                EvalOp::Commit { root_id, .. } => Some(*root_id),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(committed, vec![RootId(0), RootId(1)]);
        assert_concrete_matches_roots(&layer, &[RootId(0), RootId(1)], &plan, 2);
    }

    #[test]
    fn search_context_can_exclude_non_compute_forward_roots() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let layer = layer_with_roots(arena, vec![root_at(a, true, 0), root_at(b, true, 1)]);

        let context =
            PlanSearchContext::build_for_roots(&layer, &fields(&layer), 0, 1, &[RootId(1)])
                .unwrap();

        assert_eq!(context.selected_roots(), &[RootId(1)]);
        let scored = context.score(&EvaluationGenome::neutral(&context)).unwrap();
        assert_eq!(scored.root_order, vec![RootId(1)]);
    }

    #[test]
    fn fitness_harness_rewards_grouping_reuses_by_root_order() {
        const DOMAIN_BUDGET_CELLS: usize = 1;
        const TEST_BUDGET_LANES: usize = 1;

        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let d = read(&mut arena, 3);
        let x = arena.mul(vec![a, b]);
        let y = arena.mul(vec![c, d]);
        let layer = layer_with_roots(
            arena,
            vec![
                root_at(x, true, 0),
                root_at(y, true, 1),
                root_at(x, true, 2),
                root_at(y, true, 3),
            ],
        );
        let context =
            PlanSearchContext::build(&layer, &fields(&layer), 0, DOMAIN_BUDGET_CELLS).unwrap();
        let score_with_one_lane = |genome: &EvaluationGenome| {
            let root_order = context.decode_root_order(&genome.root_order_key).unwrap();
            let mut oracle = GenomeOracle::new(
                context.site_index(),
                &genome.cache_priority,
                &genome.staging_priority,
            )
            .unwrap();
            let plan = elaborate_with_oracle_and_sinks(
                &layer,
                &fields(&layer),
                &root_order,
                context.materialized_roots(),
                TEST_BUDGET_LANES,
                &mut oracle,
            )
            .unwrap();
            assert_eq!(oracle.active_site_count(), 0);
            let packed = pack_plan(&plan, &layer, PackConfig::default()).unwrap();
            let concrete = bind_packed_plan(
                &packed,
                &layer,
                context.materialized_roots(),
                0,
                TEST_BUDGET_LANES,
            )
            .unwrap();
            let fitness = PlanFitness {
                infeasible: false,
                dram_read_lanes: plan.stats.dram_read_lanes,
                program_instructions: concrete.compiled.stats.program_lanes,
                encoded_lanes: concrete.stats.encoded_lanes,
                arithmetic_ops: packed.stats.scalar_arithmetic_ops,
            };
            (root_order, plan, fitness)
        };
        let fingerprints = structural_fingerprints(&layer).unwrap();
        let mut alternating = EvaluationGenome::neutral(&context);
        for (position, site) in context.site_index().sites().iter().enumerate() {
            if site.root.materialize == layer.roots[2].materialize
                && site.value == fingerprints[x.0 as usize]
            {
                alternating.cache_priority[position] = 0.5;
            }
            if site.root.materialize == layer.roots[3].materialize
                && site.value == fingerprints[y.0 as usize]
            {
                alternating.cache_priority[position] = 1.0;
            }
        }

        let (alternating_order, alternating_plan, alternating_fitness) =
            score_with_one_lane(&alternating);
        assert_eq!(
            alternating_order,
            vec![RootId(0), RootId(1), RootId(2), RootId(3)]
        );
        assert_eq!(alternating_fitness.dram_read_lanes, 6);
        assert_eq!(alternating_fitness.arithmetic_ops, 3);
        assert_plan_matches_roots(&layer, &alternating_order, &alternating_plan);

        let mut grouped = alternating.clone();
        grouped.root_order_key = vec![0.0, 0.5, 0.25, 0.75];
        let (grouped_order, grouped_plan, grouped_fitness) = score_with_one_lane(&grouped);

        assert_eq!(
            grouped_order,
            vec![RootId(0), RootId(2), RootId(1), RootId(3)]
        );
        assert_eq!(grouped_fitness.dram_read_lanes, 4);
        assert_eq!(grouped_fitness.arithmetic_ops, 2);
        assert!(grouped_fitness < alternating_fitness);
        assert_plan_matches_roots(&layer, &grouped_order, &grouped_plan);
    }

    #[test]
    fn retentive_oracle_can_cache_compute_only_shared_cone() {
        let mut arena = ArenaBuilder::new();
        let a = challenge(&mut arena, 1);
        let b = challenge(&mut arena, 2);
        let c = challenge(&mut arena, 3);
        let d = challenge(&mut arena, 4);
        let e = challenge(&mut arena, 5);
        let f = challenge(&mut arena, 6);
        let g = challenge(&mut arena, 7);
        let h = challenge(&mut arena, 8);
        let shared = arena.mul(vec![a, b, c]);
        let left = arena.add(vec![shared, d]);
        let right = arena.add(vec![shared, e]);
        let third = arena.add(vec![shared, f]);
        let fourth = arena.add(vec![shared, g]);
        let fifth = arena.add(vec![shared, h]);
        let layer = layer_with_roots(
            arena,
            vec![
                root_at(left, true, 0),
                root_at(right, true, 1),
                root_at(third, true, 2),
                root_at(fourth, true, 3),
                root_at(fifth, true, 4),
            ],
        );
        let context = PlanSearchContext::build(&layer, &fields(&layer), 0, 2).unwrap();

        let neutral = context.score(&EvaluationGenome::neutral(&context)).unwrap();
        let mut compute_retentive = EvaluationGenome::neutral(&context);
        let shared = structural_fingerprints(&layer).unwrap()[shared.0 as usize];
        for (index, site) in context.site_index().sites().iter().enumerate() {
            if site.value == shared {
                compute_retentive.cache_priority[index] = 1.0;
            }
        }
        let retentive = context.score(&compute_retentive).unwrap();

        assert_eq!(neutral.fitness.dram_read_lanes, 0);
        assert_eq!(retentive.fitness.dram_read_lanes, 0);
        assert!(
            retentive.fitness.program_instructions < neutral.fitness.program_instructions,
            "neutral={:?} retentive={:?}; neutral_stats={:?} retentive_stats={:?}",
            neutral.fitness,
            retentive.fitness,
            neutral.plan.as_ref().unwrap().stats,
            retentive.plan.as_ref().unwrap().stats,
        );
        assert!(retentive.fitness.arithmetic_ops < neutral.fitness.arithmetic_ops);
        assert!(retentive.fitness < neutral.fitness);
    }

    #[test]
    fn search_context_gene_domains_survive_root_array_permutation() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let sum = arena.add(vec![a, b, c]);
        let mut first = layer_with_roots(
            arena,
            vec![
                root_at(sum, true, 2),
                root_at(sum, true, 0),
                root_at(sum, true, 1),
            ],
        );
        let mut second = first.clone();
        first.roots.rotate_left(1);
        second.roots.reverse();

        let first_context = PlanSearchContext::build(&first, &fields(&first), 0, 1).unwrap();
        let second_context = PlanSearchContext::build(&second, &fields(&second), 0, 1).unwrap();

        assert_eq!(
            first_context
                .units()
                .iter()
                .map(|unit| &unit.key)
                .collect::<Vec<_>>(),
            second_context
                .units()
                .iter()
                .map(|unit| &unit.key)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            first_context.site_index().sites(),
            second_context.site_index().sites()
        );
        let first_score = first_context
            .score(&EvaluationGenome::neutral(&first_context))
            .unwrap();
        let second_score = second_context
            .score(&EvaluationGenome::neutral(&second_context))
            .unwrap();
        assert_eq!(first_score.fitness, second_score.fitness);
    }

    #[test]
    fn fitness_harness_reports_transient_floor_as_infeasible() {
        let mut arena = ArenaBuilder::new();
        let a = challenge(&mut arena, 1);
        let b = challenge(&mut arena, 2);
        let c = challenge(&mut arena, 3);
        let d = challenge(&mut arena, 4);
        let left = arena.mul(vec![a, b, a]);
        let right = arena.mul(vec![c, d, c]);
        let sum = arena.add(vec![left, right]);
        let layer = layer(arena, root(sum, true));
        let mut oracle = NoCacheOracle;
        let error = elaborate_with_oracle(&layer, &fields(&layer), &[RootId(0)], 3, &mut oracle)
            .expect_err("three lanes cannot satisfy the transient floor");

        assert!(matches!(error, PlanError::BudgetExceeded { .. }));
    }

    #[test]
    fn mutation_search_is_reproducible_and_finds_grouped_reuse() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let d = read(&mut arena, 3);
        let x = arena.mul(vec![a, b]);
        let y = arena.mul(vec![c, d]);
        let layer = layer_with_roots(
            arena,
            vec![
                root_at(x, true, 0),
                root_at(y, true, 1),
                root_at(x, true, 2),
                root_at(y, true, 3),
            ],
        );
        let context = PlanSearchContext::build(&layer, &fields(&layer), 0, 1).unwrap();
        let config = MutationSearchConfig {
            population: 12,
            evaluations: 512,
            staging_evaluations: 0,
            seed: 7,
            cache_mutations: 2,
        };

        let first = mutation_search(&context, config).unwrap();
        let second = mutation_search(&context, config).unwrap();

        assert_eq!(first.evaluations, config.evaluations);
        assert_eq!(first.telemetry.guided_evaluations, 128);
        assert_eq!(first.neutral_fitness.dram_read_lanes, 8);
        assert_eq!(first.best.fitness.dram_read_lanes, 4);
        assert_eq!(first.best.fitness, second.best.fitness);
        assert_eq!(first.best_genome, second.best_genome);
        assert_eq!(first.best.root_order, second.best.root_order);
        assert_eq!(first.best.placement, PlacementStatus::Concrete);
        assert_eq!(first.telemetry, second.telemetry);
        assert_eq!(
            first.telemetry.greedy_placed
                + first.telemetry.exact_successes
                + first.telemetry.relocation_placed
                + first.telemetry.exact_skipped
                + first.telemetry.placement_infeasible
                + first.telemetry.elaboration_infeasible,
            first.evaluations,
        );
        assert_eq!(
            first.telemetry.exact_attempts,
            first.telemetry.exact_successes + first.telemetry.exact_failures,
        );
        assert_plan_matches_roots(
            &layer,
            &first.best.root_order,
            first.best.plan.as_ref().unwrap(),
        );
    }

    #[test]
    fn first_child_never_needs_a_parent_stash() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let only = arena.add(vec![a, b]);
        let layer = layer(arena, root(only, true));

        let plan = elaborate_uncached(&layer, &fields(&layer), &[RootId(0)]).unwrap();

        assert!(!plan.ops.iter().any(|op| matches!(op, EvalOp::SaveAcc(_))));
    }

    #[test]
    fn oracle_retains_shared_cone_and_second_root_hits_without_replay_drift() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let d = read(&mut arena, 3);
        let shared = arena.mul(vec![a, b, a]);
        let first_expr = arena.add(vec![shared, c]);
        let second_expr = arena.add(vec![shared, d]);
        let layer = layer_with_roots(
            arena,
            vec![root_at(first_expr, true, 0), root_at(second_expr, true, 1)],
        );
        let expr_fields = fields(&layer);
        let roots = [RootId(0), RootId(1)];
        let baseline = elaborate_uncached(&layer, &expr_fields, &roots).unwrap();
        assert_eq!(baseline.stats.dram_read_lanes, 8);

        let fingerprints = structural_fingerprints(&layer).unwrap();
        let shared_fingerprint = fingerprints[shared.0 as usize];
        let mut oracle = StaticOracle::default();
        for root_expr in [first_expr, second_expr] {
            oracle.responses.insert(
                root_site(&baseline, fingerprints[root_expr.0 as usize]),
                vec![RetentionPreference {
                    value: shared_fingerprint,
                    priority: 1.0,
                }],
            );
        }

        let plan = elaborate_with_oracle(&layer, &expr_fields, &roots, 2, &mut oracle).unwrap();
        assert_plan_matches_roots(&layer, &roots, &plan);
        assert_packed_matches_plan(&layer, &plan);

        assert_eq!(plan.stats.dram_read_lanes, 5);
        assert_eq!(plan.stats.cache_stores, 1);
        assert!(plan.stats.cache_hits >= 1);
        assert_eq!(
            plan.sites, oracle.calls,
            "oracle and actual traversal must stay 1:1"
        );
    }

    #[test]
    fn insufficient_parent_headroom_rejects_retention_without_infeasibility() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let d = read(&mut arena, 3);
        let shared = arena.mul(vec![a, b, a]);
        let first_expr = arena.add(vec![shared, c]);
        let second_expr = arena.add(vec![shared, d]);
        let layer = layer_with_roots(
            arena,
            vec![root_at(first_expr, true, 0), root_at(second_expr, true, 1)],
        );
        let expr_fields = fields(&layer);
        let roots = [RootId(0), RootId(1)];
        let baseline = elaborate_uncached(&layer, &expr_fields, &roots).unwrap();
        let fingerprints = structural_fingerprints(&layer).unwrap();
        let mut oracle = StaticOracle::default();
        for root_expr in [first_expr, second_expr] {
            oracle.responses.insert(
                root_site(&baseline, fingerprints[root_expr.0 as usize]),
                vec![RetentionPreference {
                    value: fingerprints[shared.0 as usize],
                    priority: 1.0,
                }],
            );
        }

        let plan = elaborate_with_oracle(&layer, &expr_fields, &roots, 1, &mut oracle).unwrap();

        assert_eq!(plan.stats.cache_stores, 0);
        assert_eq!(plan.stats.cache_hits, 0);
        assert_eq!(plan.stats.dram_read_lanes, baseline.stats.dram_read_lanes);
        assert_eq!(plan.stats.peak_live_lanes, 1);
    }

    #[test]
    fn resident_scheduled_for_eviction_executes_before_new_survivor() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let d = read(&mut arena, 3);
        let old = arena.mul(vec![a, b, a]);
        let new = arena.mul(vec![c, d, c]);
        let combined = arena.add(vec![old, new]);
        let layer = layer_with_roots(
            arena,
            vec![root_at(old, true, 0), root_at(combined, true, 1)],
        );
        let expr_fields = fields(&layer);
        let roots = [RootId(0), RootId(1)];
        let baseline = elaborate_uncached(&layer, &expr_fields, &roots).unwrap();
        let fingerprints = structural_fingerprints(&layer).unwrap();
        let old_fp = fingerprints[old.0 as usize];
        let new_fp = fingerprints[new.0 as usize];
        let mut oracle = StaticOracle::default();
        oracle.responses.insert(
            root_site(&baseline, old_fp),
            vec![RetentionPreference {
                value: old_fp,
                priority: 1.0,
            }],
        );
        oracle.responses.insert(
            root_site(&baseline, fingerprints[combined.0 as usize]),
            vec![RetentionPreference {
                value: new_fp,
                priority: 1.0,
            }],
        );

        let plan = elaborate_with_oracle(&layer, &expr_fields, &roots, 2, &mut oracle).unwrap();
        let second_root = &layer.roots[1];
        let second_root_key = RootKey {
            expr: fingerprints[second_root.expr.0 as usize],
            materialize: second_root.materialize.clone(),
            claim_origin: second_root.claim.as_ref().map(|claim| claim.origin.clone()),
        };
        let first_child = plan
            .sites
            .iter()
            .find(|site| site.root == second_root_key && site.path.len() == 1)
            .unwrap();

        assert_eq!(first_child.value, old_fp);
        assert!(
            plan.ops
                .iter()
                .any(|op| matches!(op, EvalOp::CacheDrop(value) if value.fingerprint == old_fp))
        );
        assert!(plan.ops.iter().any(
            |op| matches!(op, EvalOp::CacheStore { value, .. } if value.fingerprint == new_fp)
        ));
    }

    #[test]
    fn equal_priority_new_value_does_not_displace_resident() {
        let mut arena = ArenaBuilder::new();
        let old = read(&mut arena, 0);
        let new = read(&mut arena, 1);
        let layer = layer_with_roots(arena, vec![root_at(old, true, 0), root_at(new, true, 1)]);
        let expr_fields = fields(&layer);
        let roots = [RootId(0), RootId(1)];
        let baseline = elaborate_uncached(&layer, &expr_fields, &roots).unwrap();
        let fingerprints = structural_fingerprints(&layer).unwrap();
        let old_fp = fingerprints[old.0 as usize];
        let new_fp = fingerprints[new.0 as usize];
        let mut oracle = StaticOracle::default();
        oracle.responses.insert(
            root_site(&baseline, old_fp),
            vec![RetentionPreference {
                value: old_fp,
                priority: 1.0,
            }],
        );
        oracle.responses.insert(
            root_site(&baseline, new_fp),
            vec![
                RetentionPreference {
                    value: old_fp,
                    priority: 1.0,
                },
                RetentionPreference {
                    value: new_fp,
                    priority: 1.0,
                },
            ],
        );

        let plan = elaborate_with_oracle(&layer, &expr_fields, &roots, 1, &mut oracle).unwrap();

        assert!(plan.ops.iter().any(
            |op| matches!(op, EvalOp::CacheStore { value, .. } if value.fingerprint == old_fp)
        ));
        assert!(
            !plan
                .ops
                .iter()
                .any(|op| matches!(op, EvalOp::CacheDrop(value) if value.fingerprint == old_fp))
        );
        assert!(!plan.ops.iter().any(
            |op| matches!(op, EvalOp::CacheStore { value, .. } if value.fingerprint == new_fp)
        ));
    }

    #[test]
    fn mandatory_ext_stash_reports_budget_below_transient_floor() {
        let mut arena = ArenaBuilder::new();
        let a = challenge(&mut arena, 1);
        let b = challenge(&mut arena, 2);
        let c = challenge(&mut arena, 3);
        let d = challenge(&mut arena, 4);
        let left = arena.mul(vec![a, b, a]);
        let right = arena.mul(vec![c, d, c]);
        let sum = arena.add(vec![left, right]);
        let layer = layer(arena, root(sum, false));
        let mut oracle = NoCacheOracle;

        let error = elaborate_with_oracle(&layer, &fields(&layer), &[RootId(0)], 3, &mut oracle)
            .unwrap_err();

        assert_eq!(
            error,
            PlanError::BudgetExceeded {
                budget_lanes: 3,
                required_transient_lanes: 4,
            }
        );
    }

    #[test]
    fn direct_source_is_stored_before_fold_without_double_dram_read() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let sum = arena.add(vec![a, b]);
        let layer = layer(arena, root(sum, true));
        let expr_fields = fields(&layer);
        let baseline = elaborate_uncached(&layer, &expr_fields, &[RootId(0)]).unwrap();
        let fingerprints = structural_fingerprints(&layer).unwrap();
        let mut oracle = StaticOracle::default();
        oracle.responses.insert(
            root_site(&baseline, fingerprints[sum.0 as usize]),
            vec![RetentionPreference {
                value: fingerprints[b.0 as usize],
                priority: 1.0,
            }],
        );

        let plan =
            elaborate_with_oracle(&layer, &expr_fields, &[RootId(0)], 1, &mut oracle).unwrap();
        assert_plan_matches_roots(&layer, &[RootId(0)], &plan);
        let store = plan
            .ops
            .iter()
            .position(|op| {
                matches!(
                    op,
                    EvalOp::CacheStore {
                        value,
                        from: CacheStoreFrom::Source,
                    } if value.fingerprint == fingerprints[b.0 as usize]
                )
            })
            .unwrap();
        let fold = plan
            .ops
            .iter()
            .position(|op| {
                matches!(
                    op,
                    EvalOp::AccAdd {
                        operand: Operand::Resident(value),
                        ..
                    }
                        if value.fingerprint == fingerprints[b.0 as usize]
                )
            })
            .unwrap();

        assert!(store < fold);
        assert_eq!(plan.stats.dram_read_lanes, 2);
        assert_eq!(plan.stats.cache_hits, 0);
    }

    #[test]
    fn cache_aware_empty_oracle_keeps_ready_product_fused() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let product = arena.mul(vec![a, b]);
        let sum = arena.add(vec![product, c]);
        let layer = layer(arena, root(sum, true));
        let mut oracle = NoCacheOracle;

        let plan =
            elaborate_with_oracle(&layer, &fields(&layer), &[RootId(0)], 1, &mut oracle).unwrap();
        let execution = assert_plan_matches_roots(&layer, &[RootId(0)], &plan);

        assert!(
            plan.ops
                .iter()
                .any(|op| matches!(op, EvalOp::AccFma { .. }))
        );
        assert!(!plan.ops.iter().any(|op| matches!(op, EvalOp::SaveAcc(_))));
        assert_eq!(plan.stats.dram_read_lanes, 3);
        assert!(execution.stored_values.is_empty());
    }

    #[test]
    fn requested_product_survivor_disables_fma_and_materializes_product() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let product = arena.mul(vec![a, b]);
        let sum = arena.add(vec![product, c]);
        let layer = layer(arena, root(sum, true));
        let expr_fields = fields(&layer);
        let baseline = elaborate_uncached(&layer, &expr_fields, &[RootId(0)]).unwrap();
        let fingerprints = structural_fingerprints(&layer).unwrap();
        let product_fp = fingerprints[product.0 as usize];
        let mut oracle = StaticOracle::default();
        oracle.responses.insert(
            root_site(&baseline, fingerprints[sum.0 as usize]),
            vec![RetentionPreference {
                value: product_fp,
                priority: 1.0,
            }],
        );

        let plan =
            elaborate_with_oracle(&layer, &expr_fields, &[RootId(0)], 2, &mut oracle).unwrap();
        let execution = assert_plan_matches_roots(&layer, &[RootId(0)], &plan);

        assert!(
            !plan
                .ops
                .iter()
                .any(|op| matches!(op, EvalOp::AccFma { .. }))
        );
        assert_eq!(plan.stats.stash_stores, 1);
        assert!(plan.ops.iter().any(|op| {
            matches!(
                op,
                EvalOp::CacheStore {
                    value,
                    from: CacheStoreFrom::Acc,
                } if value.fingerprint == product_fp
            )
        }));
        assert!(
            execution
                .stored_values
                .iter()
                .any(|value| value.fingerprint == product_fp)
        );
        assert_eq!(plan.sites, oracle.calls);
    }

    #[test]
    fn first_fma_operand_is_pinned_while_second_competes_for_one_lane() {
        let mut arena = ArenaBuilder::new();
        let a = read(&mut arena, 0);
        let b = read(&mut arena, 1);
        let c = read(&mut arena, 2);
        let product = arena.mul(vec![a, b]);
        let sum = arena.add(vec![product, c]);
        let layer = layer(arena, root(sum, true));
        let expr_fields = fields(&layer);
        let baseline = elaborate_uncached(&layer, &expr_fields, &[RootId(0)]).unwrap();
        let fingerprints = structural_fingerprints(&layer).unwrap();
        let mut oracle = StaticOracle::default();
        oracle.responses.insert(
            root_site(&baseline, fingerprints[sum.0 as usize]),
            vec![
                RetentionPreference {
                    value: fingerprints[a.0 as usize],
                    priority: 1.0,
                },
                RetentionPreference {
                    value: fingerprints[b.0 as usize],
                    priority: 1.0,
                },
            ],
        );

        let plan =
            elaborate_with_oracle(&layer, &expr_fields, &[RootId(0)], 1, &mut oracle).unwrap();
        assert_plan_matches_roots(&layer, &[RootId(0)], &plan);
        let fma_index = plan
            .ops
            .iter()
            .position(|op| matches!(op, EvalOp::AccFma { .. }))
            .unwrap();
        let EvalOp::AccFma { lhs, rhs, .. } = plan.ops[fma_index] else {
            unreachable!()
        };

        assert!(matches!(lhs, Operand::Resident(_)) ^ matches!(rhs, Operand::Resident(_)));
        assert!(matches!(lhs, Operand::Source(_)) ^ matches!(rhs, Operand::Source(_)));
        assert_eq!(plan.stats.cache_stores, 1);
        assert_eq!(plan.stats.dram_read_lanes, 3);
        assert_eq!(plan.stats.peak_live_lanes, 1);
        assert!(
            plan.ops[..fma_index]
                .iter()
                .all(|op| !matches!(op, EvalOp::CacheDrop(_))),
            "the selected resident operand must remain pinned until FMA consumes it"
        );
    }

    fn replay_test_layer(
        exprs: Vec<Expr>,
        sources: Vec<SourceInfo>,
        root_expr: ExprId,
    ) -> DagLayer {
        DagLayer {
            sources,
            exprs,
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            roots: vec![root(root_expr, false)],
            resolutions: BTreeMap::new(),
        }
    }

    fn replay_test_fp(term: u32, value: ExprId, consumer: Option<ExprId>) -> BwdFingerprint {
        BwdFingerprint {
            term,
            kind: BwdServeKind::Operand,
            value,
            consumer,
        }
    }

    fn replay_test_run(
        layer: &DagLayer,
        atoms: &[ExprId],
        entries: Vec<PlanEntry>,
        domain: BTreeSet<ExprId>,
        budget_lanes: usize,
    ) -> Result<(EvalPlan, Vec<BwdEvent>), PlanError> {
        replay_test_run_with_reductions(layer, atoms, entries, domain, budget_lanes, false)
    }

    fn replay_test_run_with_reductions(
        layer: &DagLayer,
        atoms: &[ExprId],
        entries: Vec<PlanEntry>,
        domain: BTreeSet<ExprId>,
        budget_lanes: usize,
        stream_reductions: bool,
    ) -> Result<(EvalPlan, Vec<BwdEvent>), PlanError> {
        let occurrence_plan = BwdOccurrencePlan {
            epoch: 0,
            entries_fnv: plan_entries_fnv(&entries),
            stream_reductions,
            entries,
        };
        let mut replay = BackwardReplay::new(PlanRun::new(&occurrence_plan), domain);
        let fragments = atoms
            .iter()
            .map(|&atom| FragmentSpec {
                atoms: vec![atom],
                recipe: MergedRecipe::default(),
            })
            .collect::<Vec<_>>();
        let scheduled_fragments = (0..fragments.len()).collect::<Vec<_>>();
        let coefficient_descs = vec![None; fragments.len()];
        elaborate_backward_fragments_replayed_driver(
            layer,
            RootId(0),
            &fields(layer),
            &fragments,
            &scheduled_fragments,
            &coefficient_descs,
            None,
            budget_lanes,
            stream_reductions,
            &mut replay,
        )
    }

    fn replay_source_fixture(
        actions: &[PlanAction],
        budget_lanes: usize,
    ) -> Result<(EvalPlan, Vec<BwdEvent>, ExprId), PlanError> {
        let value = ExprId(0);
        let layer = replay_test_layer(
            vec![Expr::Source(SourceId(0))],
            vec![SourceInfo {
                kind: SourceKind::Read {
                    place: ReadPlace::BaseLayerWitness { column: 0 },
                },
            }],
            value,
        );
        let entries = actions
            .iter()
            .enumerate()
            .map(|(term, &action)| PlanEntry {
                fp: replay_test_fp(term as u32, value, None),
                action,
            })
            .collect();
        let result = replay_test_run(
            &layer,
            &vec![value; actions.len()],
            entries,
            BTreeSet::from([value]),
            budget_lanes,
        );
        result.map(|(plan, events)| (plan, events, value))
    }

    fn served_from(events: &[BwdEvent], value: ExprId) -> Vec<BwdServedFrom> {
        events
            .iter()
            .filter_map(|event| match event {
                BwdEvent::Serve { fp, from } if fp.value == value => Some(*from),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn replay_action_retain_miss_admits() {
        let (plan, events, value) =
            replay_source_fixture(&[PlanAction::Retain, PlanAction::Bypass], 8).unwrap();

        assert_eq!(
            served_from(&events, value),
            vec![BwdServedFrom::Recomputed, BwdServedFrom::Resident]
        );
        assert!(
            events
                .iter()
                .any(|event| matches!(event, BwdEvent::Admit { value: v, .. } if *v == value))
        );
        assert_eq!(
            plan.ops
                .iter()
                .filter(|op| matches!(op, EvalOp::CacheStore { value: v, .. } if v.expr == value))
                .count(),
            1
        );
    }

    #[test]
    fn replay_action_retain_hit_consumes_and_rearms() {
        let (plan, events, value) = replay_source_fixture(
            &[PlanAction::Retain, PlanAction::Retain, PlanAction::Bypass],
            8,
        )
        .unwrap();

        assert_eq!(
            served_from(&events, value),
            vec![
                BwdServedFrom::Recomputed,
                BwdServedFrom::Resident,
                BwdServedFrom::Resident,
            ]
        );
        assert_eq!(
            events
                .iter()
                .filter(|event| matches!(event, BwdEvent::Admit { value: v, .. } if *v == value))
                .count(),
            1,
            "a resident Retain must re-arm without a second admission"
        );
        assert_eq!(
            plan.ops
                .iter()
                .filter(|op| matches!(op, EvalOp::CacheStore { .. }))
                .count(),
            1
        );
    }

    #[test]
    fn replay_action_bypass_hit_consumes_then_drops() {
        let (plan, events, value) =
            replay_source_fixture(&[PlanAction::Retain, PlanAction::Bypass], 8).unwrap();
        let closing_serve = events
            .iter()
            .rposition(|event| {
                matches!(
                    event,
                    BwdEvent::Serve {
                        fp,
                        from: BwdServedFrom::Resident,
                    } if fp.value == value
                )
            })
            .unwrap();
        let eviction = events
            .iter()
            .position(
                |event| matches!(event, BwdEvent::Evict { value: v, expired: true } if *v == value),
            )
            .unwrap();

        assert!(
            eviction > closing_serve,
            "the resident must be consumed before it is dropped"
        );
        assert_eq!(
            plan.ops
                .iter()
                .filter(|op| matches!(op, EvalOp::CacheDrop(value_ref) if value_ref.expr == value))
                .count(),
            1
        );
    }

    #[test]
    fn replay_action_bypass_miss_recomputes_without_admit() {
        let (plan, events, value) = replay_source_fixture(&[PlanAction::Bypass], 8).unwrap();

        assert_eq!(served_from(&events, value), vec![BwdServedFrom::Recomputed]);
        assert!(
            !events
                .iter()
                .any(|event| matches!(event, BwdEvent::Admit { value: v, .. } if *v == value))
        );
        assert!(
            !plan
                .ops
                .iter()
                .any(|op| matches!(op, EvalOp::CacheStore { .. }))
        );
    }

    #[test]
    fn replay_action_retain_refusal_is_typed_refusal() {
        assert!(matches!(
            replay_source_fixture(&[PlanAction::Retain, PlanAction::Bypass], 0),
            Err(PlanError::ReplayRefused { .. })
        ));
    }

    #[test]
    fn replay_compound_bypass_hit_uses_resident_without_descendant_recompute() {
        let a = ExprId(0);
        let b = ExprId(1);
        let c = ExprId(2);
        let product = ExprId(3);
        let sum = ExprId(4);
        let layer = replay_test_layer(
            vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Mul(vec![a, b]),
                Expr::Add(vec![c, product]),
            ],
            (0..3)
                .map(|column| SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column },
                    },
                })
                .collect(),
            sum,
        );
        let entries = vec![
            PlanEntry {
                fp: replay_test_fp(0, product, None),
                action: PlanAction::Retain,
            },
            PlanEntry {
                fp: replay_test_fp(1, product, Some(sum)),
                action: PlanAction::Bypass,
            },
        ];

        let (plan, events) = replay_test_run(
            &layer,
            &[product, sum],
            entries,
            BTreeSet::from([product]),
            8,
        )
        .unwrap();

        assert_eq!(
            served_from(&events, product),
            vec![BwdServedFrom::Recomputed, BwdServedFrom::Resident]
        );
        for descendant in [a, b] {
            assert_eq!(
                events
                    .iter()
                    .filter(|event| matches!(event, BwdEvent::Serve { fp, .. } if fp.value == descendant))
                    .count(),
                1,
                "a resident compound hit must suppress descendant recomputation"
            );
        }
        assert!(plan.ops.iter().any(|op| {
            matches!(
                op,
                EvalOp::AccAdd {
                    operand: Operand::Resident(value),
                    ..
                } if value.expr == product
            )
        }));
        assert_eq!(
            plan.ops
                .iter()
                .filter(|op| matches!(op, EvalOp::CacheDrop(value) if value.expr == product))
                .count(),
            1
        );
    }

    #[test]
    fn replay_repeated_fma_operand_bypass_hit_is_logically_consumed_once() {
        let value = ExprId(0);
        let seed = ExprId(1);
        let product = ExprId(2);
        let sum = ExprId(3);
        let layer = replay_test_layer(
            vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Mul(vec![value, value]),
                Expr::Add(vec![seed, product]),
            ],
            (0..2)
                .map(|column| SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column },
                    },
                })
                .collect(),
            sum,
        );
        let entries = vec![
            PlanEntry {
                fp: replay_test_fp(0, value, None),
                action: PlanAction::Retain,
            },
            PlanEntry {
                fp: replay_test_fp(1, value, Some(sum)),
                action: PlanAction::Bypass,
            },
            PlanEntry {
                fp: replay_test_fp(1, value, Some(sum)),
                action: PlanAction::Bypass,
            },
        ];

        let (plan, events) =
            replay_test_run(&layer, &[value, sum], entries, BTreeSet::from([value]), 8).unwrap();

        assert_eq!(
            served_from(&events, value),
            vec![
                BwdServedFrom::Recomputed,
                BwdServedFrom::Resident,
                BwdServedFrom::Recomputed,
            ],
            "the closing Bypass hit is unavailable to the sibling FMA operand"
        );
        assert_eq!(
            events
                .iter()
                .filter(|event| {
                    matches!(event, BwdEvent::TrafficRead { value: read, .. } if *read == value)
                })
                .count(),
            2,
            "the opening serve and the second product operand each read the source"
        );

        let fma = plan
            .ops
            .iter()
            .position(|op| matches!(op, EvalOp::AccFma { .. }))
            .unwrap();
        let drop = plan
            .ops
            .iter()
            .position(|op| matches!(op, EvalOp::CacheDrop(value_ref) if value_ref.expr == value))
            .unwrap();
        assert!(
            drop > fma,
            "the physically pinned resident cell cannot be dropped or reused before the FMA"
        );
        assert_eq!(
            plan.ops[..drop]
                .iter()
                .filter(|op| matches!(op, EvalOp::CacheStore { .. }))
                .count(),
            1,
            "the pinned resident cell is not reused before its deferred drop"
        );

        let closing_hit = events
            .iter()
            .position(|event| {
                matches!(
                    event,
                    BwdEvent::Serve {
                        fp,
                        from: BwdServedFrom::Resident,
                    } if fp.value == value
                )
            })
            .unwrap();
        let recomputed_sibling = events
            .iter()
            .rposition(|event| {
                matches!(
                    event,
                    BwdEvent::Serve {
                        fp,
                        from: BwdServedFrom::Recomputed,
                    } if fp.value == value
                )
            })
            .unwrap();
        let eviction = events
            .iter()
            .position(
                |event| matches!(event, BwdEvent::Evict { value: evicted, expired: true } if *evicted == value),
            )
            .unwrap();
        assert!(closing_hit < recomputed_sibling && recomputed_sibling < eviction);
    }

    #[test]
    fn replay_equal_fingerprint_fma_alias_bypass_hit_is_logically_consumed_once() {
        let original = ExprId(0);
        let alias = ExprId(1);
        let seed = ExprId(2);
        let product = ExprId(3);
        let sum = ExprId(4);
        let layer = replay_test_layer(
            vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Mul(vec![original, alias]),
                Expr::Add(vec![seed, product]),
            ],
            (0..2)
                .map(|column| SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column },
                    },
                })
                .collect(),
            sum,
        );
        let fingerprints = structural_fingerprints(&layer).unwrap();
        assert_eq!(
            fingerprints[original.0 as usize],
            fingerprints[alias.0 as usize]
        );
        let entries = vec![
            PlanEntry {
                fp: replay_test_fp(0, original, None),
                action: PlanAction::Retain,
            },
            PlanEntry {
                fp: replay_test_fp(1, original, Some(sum)),
                action: PlanAction::Bypass,
            },
            PlanEntry {
                fp: replay_test_fp(1, alias, Some(sum)),
                action: PlanAction::Bypass,
            },
        ];

        let (plan, events) = replay_test_run(
            &layer,
            &[original, sum],
            entries,
            BTreeSet::from([original, alias]),
            8,
        )
        .unwrap();

        assert_eq!(
            served_from(&events, original),
            vec![BwdServedFrom::Recomputed, BwdServedFrom::Resident]
        );
        assert_eq!(
            served_from(&events, alias),
            vec![BwdServedFrom::Recomputed],
            "a structural alias cannot reuse the logically consumed Bypass hit"
        );
        assert_eq!(
            events
                .iter()
                .filter(|event| {
                    matches!(event, BwdEvent::TrafficRead { value, .. } if *value == alias)
                })
                .count(),
            1
        );
        let fma = plan
            .ops
            .iter()
            .position(|op| matches!(op, EvalOp::AccFma { .. }))
            .unwrap();
        let drop = plan
            .ops
            .iter()
            .position(|op| matches!(op, EvalOp::CacheDrop(value) if value.expr == original))
            .unwrap();
        assert!(drop > fma);
    }

    #[test]
    fn replay_fma_bypass_then_alias_retain_requires_fresh_admission() {
        let original = ExprId(0);
        let alias = ExprId(1);
        let product = ExprId(2);
        let sum = ExprId(3);
        let layer = replay_test_layer(
            vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(0)),
                Expr::Mul(vec![original, alias]),
                Expr::Add(vec![product]),
            ],
            vec![SourceInfo {
                kind: SourceKind::Read {
                    place: ReadPlace::BaseLayerWitness { column: 0 },
                },
            }],
            sum,
        );
        let fingerprints = structural_fingerprints(&layer).unwrap();
        assert_eq!(
            fingerprints[original.0 as usize],
            fingerprints[alias.0 as usize]
        );
        let entries = vec![
            PlanEntry {
                fp: replay_test_fp(0, original, None),
                action: PlanAction::Retain,
            },
            PlanEntry {
                fp: replay_test_fp(1, original, Some(sum)),
                action: PlanAction::Bypass,
            },
            PlanEntry {
                fp: replay_test_fp(1, alias, Some(sum)),
                action: PlanAction::Retain,
            },
            PlanEntry {
                fp: replay_test_fp(2, alias, None),
                action: PlanAction::Bypass,
            },
        ];

        let (plan, events) = replay_test_run(
            &layer,
            &[original, sum, alias],
            entries,
            BTreeSet::from([original, alias]),
            8,
        )
        .unwrap();

        assert_eq!(
            served_from(&events, original),
            vec![BwdServedFrom::Recomputed, BwdServedFrom::Resident]
        );
        assert_eq!(
            served_from(&events, alias),
            vec![BwdServedFrom::Recomputed, BwdServedFrom::Resident]
        );
        let original_evict = events
            .iter()
            .position(|event| {
                matches!(
                    event,
                    BwdEvent::Evict {
                        value,
                        expired: true,
                    } if *value == original
                )
            })
            .unwrap();
        let alias_admits = events
            .iter()
            .enumerate()
            .filter_map(|(index, event)| {
                matches!(event, BwdEvent::Admit { value, .. } if *value == alias).then_some(index)
            })
            .collect::<Vec<_>>();
        assert_eq!(alias_admits.len(), 1);
        assert!(
            original_evict < alias_admits[0],
            "the miss-side Retain must admit only after the retired generation is evicted"
        );

        let original_drop = plan
            .ops
            .iter()
            .position(|op| matches!(op, EvalOp::CacheDrop(value) if value.expr == original))
            .unwrap();
        let alias_store = plan
            .ops
            .iter()
            .position(|op| matches!(op, EvalOp::CacheStore { value, .. } if value.expr == alias))
            .unwrap();
        assert!(
            original_drop < alias_store,
            "operand 2 must not reuse the retired operand-1 cell"
        );
    }

    #[test]
    fn replay_repeated_compound_fma_operand_recomputes_with_tight_headroom() {
        const BUDGET_LANES: usize = 12;

        let mut arena = ArenaBuilder::new();
        let a = challenge(&mut arena, 1);
        let b = challenge(&mut arena, 2);
        let seed = challenge(&mut arena, 3);
        let compound = arena.add(vec![a, b]);
        let product = arena.mul(vec![compound, compound]);
        let sum = arena.add(vec![seed, product]);
        let layer = layer(arena, root(sum, false));
        assert_eq!(fields(&layer)[compound.0 as usize], FieldKind::Ext);
        let entries = vec![
            PlanEntry {
                fp: replay_test_fp(0, compound, None),
                action: PlanAction::Retain,
            },
            PlanEntry {
                fp: replay_test_fp(1, compound, Some(sum)),
                action: PlanAction::Bypass,
            },
            PlanEntry {
                fp: replay_test_fp(1, compound, Some(sum)),
                action: PlanAction::Bypass,
            },
        ];

        let (plan, events) = replay_test_run(
            &layer,
            &[compound, sum],
            entries,
            BTreeSet::from([compound]),
            BUDGET_LANES,
        )
        .unwrap();

        assert_eq!(
            served_from(&events, compound),
            vec![
                BwdServedFrom::Recomputed,
                BwdServedFrom::Resident,
                BwdServedFrom::Recomputed,
            ]
        );
        assert!(plan.stats.peak_live_lanes <= BUDGET_LANES);
        let compound_drop = plan
            .ops
            .iter()
            .position(|op| matches!(op, EvalOp::CacheDrop(value) if value.expr == compound))
            .unwrap();
        let saves = plan
            .ops
            .iter()
            .enumerate()
            .filter_map(|(index, op)| matches!(op, EvalOp::SaveAcc(_)).then_some(index))
            .collect::<Vec<_>>();
        assert_eq!(
            saves.len(),
            3,
            "the fragment total, outer ACC, and one-use square each require one save"
        );
        assert!(
            compound_drop < saves[1],
            "the retired compound must be dropped before the fallback saves the outer ACC"
        );
    }

    #[test]
    fn replay_eliminated_nonresident_product_is_not_a_cacheable_demand() {
        let a = ExprId(0);
        let b = ExprId(1);
        let c = ExprId(2);
        let product = ExprId(3);
        let sum = ExprId(4);
        let layer = replay_test_layer(
            vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Mul(vec![a, b]),
                Expr::Add(vec![c, product]),
            ],
            (0..3)
                .map(|column| SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column },
                    },
                })
                .collect(),
            sum,
        );

        let (plan, events) =
            replay_test_run(&layer, &[sum], Vec::new(), BTreeSet::from([product]), 8)
                .expect("an eliminated product leaves the independently eligible stream empty");

        assert!(
            !events
                .iter()
                .any(|event| matches!(event, BwdEvent::Serve { fp, .. } if fp.value == product))
        );
        assert!(
            !plan
                .ops
                .iter()
                .any(|op| matches!(op, EvalOp::CacheStore { .. }))
        );
    }

    #[test]
    fn replay_all_eliminated_products_leave_actual_domain_stream_empty() {
        let a = ExprId(0);
        let b = ExprId(1);
        let c = ExprId(2);
        let d = ExprId(3);
        let left = ExprId(4);
        let right = ExprId(5);
        let sum = ExprId(6);
        let layer = replay_test_layer(
            vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Source(SourceId(3)),
                Expr::Mul(vec![a, b]),
                Expr::Mul(vec![c, d]),
                Expr::Add(vec![left, right]),
            ],
            (0..4)
                .map(|column| SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column },
                    },
                })
                .collect(),
            sum,
        );

        for stream_reductions in [false, true] {
            let (plan, events) = replay_test_run_with_reductions(
                &layer,
                &[sum],
                Vec::new(),
                BTreeSet::from([left, right]),
                8,
                stream_reductions,
            )
            .unwrap_or_else(|error| {
                panic!(
                    "FMA-eliminated product boundaries must not dispatch replay entries \
                     (stream_reductions={stream_reductions}): {error:?}"
                )
            });

            assert!(!events.iter().any(|event| {
                matches!(event, BwdEvent::Serve { fp, .. } if fp.value == left || fp.value == right)
            }));
            assert!(
                !plan
                    .ops
                    .iter()
                    .any(|op| matches!(op, EvalOp::CacheStore { .. }))
            );
        }
    }

    #[test]
    fn replay_eliminated_product_with_compound_operand_is_not_a_domain_serve() {
        let a = ExprId(0);
        let b = ExprId(1);
        let c = ExprId(2);
        let d = ExprId(3);
        let compound = ExprId(4);
        let product = ExprId(5);
        let direct_product = ExprId(6);
        let sum = ExprId(7);
        let layer = replay_test_layer(
            vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Source(SourceId(3)),
                Expr::Add(vec![a, b]),
                Expr::Mul(vec![compound, c]),
                Expr::Mul(vec![a, d]),
                Expr::Add(vec![product, direct_product]),
            ],
            (0..4)
                .map(|column| SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column },
                    },
                })
                .collect(),
            sum,
        );

        let (_plan, events) =
            replay_test_run(&layer, &[sum], Vec::new(), BTreeSet::from([product]), 8)
                .expect("an FMA-eliminated product remains ineligible with a compound operand");

        assert!(
            !events
                .iter()
                .any(|event| matches!(event, BwdEvent::Serve { fp, .. } if fp.value == product))
        );
    }

    #[test]
    fn replay_positive_single_factor_product_remains_a_domain_serve() {
        let one = ExprId(0);
        let a = ExprId(1);
        let b = ExprId(2);
        let product = ExprId(3);
        let sum = ExprId(4);
        let layer = replay_test_layer(
            vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Mul(vec![one, a]),
                Expr::Add(vec![product, product, b]),
            ],
            vec![
                SourceInfo {
                    kind: SourceKind::Constant { value: 1 },
                },
                SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column: 0 },
                    },
                },
                SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column: 1 },
                    },
                },
            ],
            sum,
        );
        let entries = vec![
            PlanEntry {
                fp: replay_test_fp(0, product, Some(sum)),
                action: PlanAction::Bypass,
            },
            PlanEntry {
                fp: replay_test_fp(0, product, Some(sum)),
                action: PlanAction::Bypass,
            },
        ];

        for stream_reductions in [false, true] {
            let (_plan, events) = replay_test_run_with_reductions(
                &layer,
                &[sum],
                entries.clone(),
                BTreeSet::from([product]),
                8,
                stream_reductions,
            )
            .unwrap_or_else(|error| {
                panic!(
                    "an unsigned single-factor Mul remains an incumbent demand boundary \
                     (stream_reductions={stream_reductions}): {error:?}"
                )
            });

            assert_eq!(
                served_from(&events, product),
                vec![BwdServedFrom::Recomputed, BwdServedFrom::Recomputed]
            );
        }
    }

    #[test]
    fn replay_negated_single_factor_product_is_eliminated_in_both_modes() {
        let negative_one = ExprId(0);
        let a = ExprId(1);
        let b = ExprId(2);
        let product = ExprId(3);
        let sum = ExprId(4);
        let layer = replay_test_layer(
            vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Mul(vec![negative_one, a]),
                Expr::Add(vec![product, product, b]),
            ],
            vec![
                SourceInfo {
                    kind: SourceKind::Constant {
                        value: BABYBEAR_NEG_ONE,
                    },
                },
                SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column: 0 },
                    },
                },
                SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column: 1 },
                    },
                },
            ],
            sum,
        );

        for stream_reductions in [false, true] {
            let (_plan, events) = replay_test_run_with_reductions(
                &layer,
                &[sum],
                Vec::new(),
                BTreeSet::from([product]),
                8,
                stream_reductions,
            )
            .unwrap_or_else(|error| {
                panic!(
                    "a negated single-factor product is an eliminated Add boundary \
                     (stream_reductions={stream_reductions}): {error:?}"
                )
            });

            assert!(
                !events.iter().any(
                    |event| matches!(event, BwdEvent::Serve { fp, .. } if fp.value == product)
                )
            );
            assert_eq!(served_from(&events, a).len(), 2);
        }
    }

    #[test]
    fn replay_positive_single_factor_pressure_selects_feasible_seed() {
        let resident = ExprId(0);
        let one = ExprId(1);
        let a = ExprId(2);
        let b = ExprId(3);
        let product = ExprId(4);
        let sum = ExprId(5);
        let layer = replay_test_layer(
            vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Source(SourceId(3)),
                Expr::Mul(vec![one, a]),
                Expr::Add(vec![product, b]),
            ],
            vec![
                SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column: 0 },
                    },
                },
                SourceInfo {
                    kind: SourceKind::Constant { value: 1 },
                },
                SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column: 1 },
                    },
                },
                SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column: 2 },
                    },
                },
            ],
            sum,
        );
        let entries = vec![
            PlanEntry {
                fp: replay_test_fp(0, resident, None),
                action: PlanAction::Retain,
            },
            PlanEntry {
                fp: replay_test_fp(1, product, Some(sum)),
                action: PlanAction::Bypass,
            },
            PlanEntry {
                fp: replay_test_fp(2, resident, None),
                action: PlanAction::Bypass,
            },
        ];

        for stream_reductions in [false, true] {
            let (_plan, events) = replay_test_run_with_reductions(
                &layer,
                &[resident, sum, resident],
                entries.clone(),
                BTreeSet::from([resident, product]),
                5,
                stream_reductions,
            )
            .unwrap_or_else(|error| {
                panic!(
                    "the preserved unsigned product must seed under tight headroom \
                     (stream_reductions={stream_reductions}): {error:?}"
                )
            });

            assert_eq!(
                served_from(&events, resident),
                vec![BwdServedFrom::Recomputed, BwdServedFrom::Resident]
            );
            assert_eq!(
                served_from(&events, product),
                vec![BwdServedFrom::Recomputed]
            );
        }
    }

    #[test]
    fn replay_equal_fingerprint_alias_retention_waits_for_all_owners() {
        let a = ExprId(0);
        let b = ExprId(1);
        let original = ExprId(2);
        let alias = ExprId(3);
        let layer = replay_test_layer(
            vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Mul(vec![a, b]),
                Expr::Mul(vec![b, a]),
            ],
            (0..2)
                .map(|column| SourceInfo {
                    kind: SourceKind::Read {
                        place: ReadPlace::BaseLayerWitness { column },
                    },
                })
                .collect(),
            original,
        );
        let fingerprints = structural_fingerprints(&layer).unwrap();
        assert_eq!(
            fingerprints[original.0 as usize],
            fingerprints[alias.0 as usize]
        );
        let entries = [
            (original, PlanAction::Retain),
            (alias, PlanAction::Retain),
            (original, PlanAction::Bypass),
            (alias, PlanAction::Bypass),
        ]
        .into_iter()
        .enumerate()
        .map(|(term, (value, action))| PlanEntry {
            fp: replay_test_fp(term as u32, value, None),
            action,
        })
        .collect();

        let (plan, events) = replay_test_run(
            &layer,
            &[original, alias, original, alias],
            entries,
            BTreeSet::from([original, alias]),
            8,
        )
        .unwrap();

        assert_eq!(
            served_from(&events, original),
            vec![BwdServedFrom::Recomputed, BwdServedFrom::Resident]
        );
        assert_eq!(
            served_from(&events, alias),
            vec![BwdServedFrom::Resident, BwdServedFrom::Resident]
        );
        let last_alias_serve = events
            .iter()
            .rposition(|event| matches!(event, BwdEvent::Serve { fp, .. } if fp.value == alias))
            .unwrap();
        let eviction = events
            .iter()
            .position(|event| matches!(event, BwdEvent::Evict { expired: true, .. }))
            .unwrap();
        assert!(eviction > last_alias_serve);
        assert_eq!(
            plan.ops
                .iter()
                .filter(|op| matches!(op, EvalOp::CacheStore { .. }))
                .count(),
            1
        );
        assert_eq!(
            plan.ops
                .iter()
                .filter(|op| matches!(op, EvalOp::CacheDrop(_)))
                .count(),
            1
        );
    }
}
