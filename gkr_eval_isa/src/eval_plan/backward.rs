//! Closed symbolic adapter for normalized backward fragments.

use cs::gkr_compiler::dag_ir::{
    BwdRegime, Expr, ExprId, FieldKind, ReadPlace, RootId, SourceId, SourceKind, join, source_field,
};

use crate::bwd::compile::{BwdCompiledLayer, fragment_descs, tally_bwd_program};
use crate::bwd::distill::{DistilledLayer, distilled_site_domain};
use crate::bwd::plan::{BwdOccurrencePlan, PlanReplayError, PlanRun, plan_entries_fnv};
use crate::bwd::source::BwdSpecialTable;
use crate::bwd::trace::{
    BwdCompileTrace, BwdEvent, certify, live_profile, physical_traffic_events, plan_epoch_fragment,
    retain_physical_traffic_events,
};

use super::{
    BackwardReplay, ConcreteBindError, ConcreteEvalProgram, ConcreteTerminal, EvalPlan, PackConfig,
    PackError, PackedEvalPlan, PlanError, budget_lanes_from_cells,
    concrete::bind_backward_packed_plan, elaborate_backward_fragments_driver,
    elaborate_backward_fragments_replayed_driver, pack_plan,
};

/// Symbolic backward evaluation before descriptor binding. The special table is
/// cloned and extended only with descriptors actually emitted by the fragment
/// plan, leaving the distilled layer's binding namespace unchanged.
#[derive(Clone, Debug)]
pub struct BackwardSymbolicEvaluation {
    pub plan: EvalPlan,
    pub packed: PackedEvalPlan,
    pub specials: BwdSpecialTable,
    pub(crate) demand_events: Vec<BwdEvent>,
}

pub struct CompiledBackwardEvaluation {
    pub symbolic: BackwardSymbolicEvaluation,
    pub compiled: BwdCompiledLayer,
    pub encoded: Vec<u16>,
    pub trace: BwdCompileTrace,
}

#[derive(Clone, Debug, PartialEq)]
pub enum BackwardEvaluationError {
    Plan(PlanError),
    Pack(PackError),
    BudgetCellsOutOfRange {
        budget_cells: usize,
    },
    InvalidFragmentOrder {
        order: Vec<usize>,
        fragment_count: usize,
    },
    EmptyFragmentDecomposition,
    InvalidBackwardRoot {
        root: RootId,
        root_count: usize,
    },
    InvalidRootExpression {
        root: RootId,
        expr: ExprId,
        expression_count: usize,
    },
    InvalidExpressionSource {
        expr: ExprId,
        source: SourceId,
        source_count: usize,
    },
    InvalidExpressionChild {
        expr: ExprId,
        child_index: usize,
        child: ExprId,
        expression_count: usize,
    },
    InvalidLookupQuery {
        expr: ExprId,
        source: SourceId,
        query: ExprId,
        expression_count: usize,
    },
    CyclicExpression {
        expr: ExprId,
    },
    MissingCrossLayerField {
        expr: ExprId,
        place: ReadPlace,
    },
    EmptyFragmentAtoms {
        fragment: usize,
    },
    InvalidFragmentAtom {
        fragment: usize,
        atom_index: usize,
        atom: ExprId,
        expression_count: usize,
    },
    UnresolvedFragmentAtom {
        fragment: usize,
        atom_index: usize,
        atom: ExprId,
    },
    InvalidFragmentRecipeFactor {
        fragment: usize,
        term: usize,
        factor_index: usize,
        factor: ExprId,
        expression_count: usize,
    },
    UnresolvedFragmentRecipeFactor {
        fragment: usize,
        term: usize,
        factor_index: usize,
        factor: ExprId,
    },
    InvalidAccInitFactor {
        term: usize,
        factor_index: usize,
        factor: ExprId,
        expression_count: usize,
    },
    UnresolvedAccInitFactor {
        term: usize,
        factor_index: usize,
        factor: ExprId,
    },
    Concrete(ConcreteBindError),
    UnboundBackwardSource(ExprId),
    BackwardCommit,
    UnexpectedTerminal,
    ForwardDescriptorLeak,
    TrafficSourceMapping,
    TrafficCertificateMismatch {
        symbolic: usize,
        packed: usize,
        concrete: usize,
        traced: usize,
    },
    MalformedReplayPlan {
        entry: usize,
        value: ExprId,
    },
    StaleReplayEpoch {
        expected: u64,
        actual: u64,
    },
    ReplayEntriesFingerprintMismatch,
    ReplayDiverged {
        at_entry: usize,
    },
    ReplayNotFullyConsumed {
        at_entry: usize,
    },
    ReplayInfeasible,
}

impl From<PlanError> for BackwardEvaluationError {
    fn from(value: PlanError) -> Self {
        Self::Plan(value)
    }
}

impl From<PackError> for BackwardEvaluationError {
    fn from(value: PackError) -> Self {
        Self::Pack(value)
    }
}

/// Elaborate the complete normalized backward-fragment expression without
/// cache residency, then pack it. `budget_cells` is converted exactly once to
/// extension-field lane units before it reaches the shared elaborator.
pub fn elaborate_backward_fragments_uncached(
    d: &DistilledLayer,
    order: Option<&[usize]>,
    budget_cells: usize,
    stream_reductions: bool,
) -> Result<BackwardSymbolicEvaluation, BackwardEvaluationError> {
    let expr_fields = validate_and_resolve_backward(d)?;
    let fragments = &d.fragments.fragments;
    let scheduled_fragments = validate_fragment_order(order, fragments.len())?;
    let budget_lanes = budget_lanes_from_cells(budget_cells)
        .ok_or(BackwardEvaluationError::BudgetCellsOutOfRange { budget_cells })?;
    let (specials, coefficient_descs, acc_init_desc) = fragment_descs(d);
    let (plan, demand_events) = elaborate_backward_fragments_driver(
        &d.layer,
        d.root,
        &expr_fields,
        fragments,
        &scheduled_fragments,
        &coefficient_descs,
        acc_init_desc,
        budget_lanes,
        stream_reductions,
    )?;
    let packed = pack_plan(&plan, &d.layer, PackConfig::default())?;
    Ok(BackwardSymbolicEvaluation {
        plan,
        packed,
        specials,
        demand_events,
    })
}

fn elaborate_backward_fragments_replayed(
    d: &DistilledLayer,
    plan: &BwdOccurrencePlan,
    order: Option<&[usize]>,
    budget_cells: usize,
) -> Result<BackwardSymbolicEvaluation, BackwardEvaluationError> {
    let expr_fields = validate_and_resolve_backward(d)?;
    let fragments = &d.fragments.fragments;
    let scheduled_fragments = validate_fragment_order(order, fragments.len())?;
    let budget_lanes = budget_lanes_from_cells(budget_cells)
        .ok_or(BackwardEvaluationError::BudgetCellsOutOfRange { budget_cells })?;
    let expected_epoch = plan_epoch_fragment(d, budget_lanes, plan.stream_reductions);
    if plan.epoch != expected_epoch {
        return Err(BackwardEvaluationError::StaleReplayEpoch {
            expected: expected_epoch,
            actual: plan.epoch,
        });
    }
    if plan.entries_fnv != plan_entries_fnv(&plan.entries) {
        return Err(BackwardEvaluationError::ReplayEntriesFingerprintMismatch);
    }
    let run = PlanRun::try_new(plan).map_err(|error| match error {
        PlanReplayError::RetainWithoutNextServe { entry, value } => {
            BackwardEvaluationError::MalformedReplayPlan { entry, value }
        }
    })?;
    // Replay eligibility is a property of the distilled program, never of the
    // caller-supplied entries. This is the same domain filter used by
    // `FrozenDemand`: every actual shared-elaborator serve for one of these
    // values must advance the matcher, including when the caller deleted all
    // entries for that value (or deleted the complete stream).
    let domain = distilled_site_domain(d)
        .into_iter()
        .map(|site| site.value)
        .collect();
    let mut replay = BackwardReplay::new(run, domain);
    let (specials, coefficient_descs, acc_init_desc) = fragment_descs(d);
    let (eval_plan, demand_events) = elaborate_backward_fragments_replayed_driver(
        &d.layer,
        d.root,
        &expr_fields,
        fragments,
        &scheduled_fragments,
        &coefficient_descs,
        acc_init_desc,
        budget_lanes,
        plan.stream_reductions,
        &mut replay,
    )
    .map_err(map_replay_plan_error)?;
    let packed = pack_plan(&eval_plan, &d.layer, PackConfig::default())?;
    Ok(BackwardSymbolicEvaluation {
        plan: eval_plan,
        packed,
        specials,
        demand_events,
    })
}

/// Compile the full backward fragment decomposition through the shared packed
/// evaluation pipeline. The selected reduction mode is explicit and this
/// entry never retries with a different mode.
pub fn compile_backward_fragments_uncached(
    d: &DistilledLayer,
    order: Option<&[usize]>,
    budget_cells: usize,
    stream_reductions: bool,
) -> Result<CompiledBackwardEvaluation, BackwardEvaluationError> {
    let symbolic =
        elaborate_backward_fragments_uncached(d, order, budget_cells, stream_reductions)?;
    compile_backward_symbolic(d, symbolic, stream_reductions, false)
}

pub fn compile_backward_fragments_replayed(
    d: &DistilledLayer,
    plan: &BwdOccurrencePlan,
    order: Option<&[usize]>,
    budget_cells: usize,
) -> Result<CompiledBackwardEvaluation, BackwardEvaluationError> {
    let symbolic = elaborate_backward_fragments_replayed(d, plan, order, budget_cells)?;
    compile_backward_symbolic(d, symbolic, plan.stream_reductions, true)
}

fn compile_backward_symbolic(
    d: &DistilledLayer,
    symbolic: BackwardSymbolicEvaluation,
    stream_reductions: bool,
    replayed: bool,
) -> Result<CompiledBackwardEvaluation, BackwardEvaluationError> {
    let budget_lanes = symbolic.plan.budget_lanes;
    let bound = bind_backward_packed_plan(
        &symbolic.packed,
        &d.layer,
        d.root,
        budget_lanes,
        &d.leaf_descs,
    )
    .map_err(|error| {
        if replayed && matches!(error, ConcreteBindError::PlacementFailed { .. }) {
            BackwardEvaluationError::ReplayInfeasible
        } else {
            map_concrete_error(error)
        }
    })?;
    let ConcreteEvalProgram {
        compiled: forward,
        encoded,
        terminal,
        ..
    } = bound;
    if !matches!(terminal, ConcreteTerminal::ReturnAcc { .. }) {
        return Err(BackwardEvaluationError::UnexpectedTerminal);
    }
    if forward.ctx.specials.len() != 0 {
        return Err(BackwardEvaluationError::ForwardDescriptorLeak);
    }

    let program = forward.program;
    let specials = symbolic.specials.clone();
    let live = live_profile(&program);
    let max_live_lanes = live.iter().copied().max().unwrap_or(0);
    let (mut stats, stats_ext) = tally_bwd_program(&program, &specials);
    stats.max_live_cells = max_live_lanes;
    let compiled = BwdCompiledLayer {
        program,
        specials,
        backings: forward.ctx.backings,
        consts: forward.ctx.consts,
        challenges: forward.ctx.challenges,
        budget: budget_lanes,
        stats,
        stats_ext,
    };

    let physical_events = physical_traffic_events(
        &d.layer,
        &compiled.program,
        &compiled.specials,
        &d.leaf_descs,
        &compiled.backings,
    )
    .ok_or(BackwardEvaluationError::TrafficSourceMapping)?;
    let events = retain_physical_traffic_events(symbolic.demand_events.clone(), &physical_events)
        .ok_or(BackwardEvaluationError::TrafficSourceMapping)?;
    let trace = BwdCompileTrace {
        epoch: plan_epoch_fragment(d, budget_lanes, stream_reductions),
        budget: budget_lanes,
        stream_reductions,
        events,
        free: live
            .into_iter()
            .map(|occupied| budget_lanes.saturating_sub(occupied))
            .collect(),
    };

    let symbolic_traffic = symbolic.plan.stats.dram_read_lanes;
    let packed_traffic = symbolic.packed.stats.dram_read_lanes;
    let concrete_traffic = compiled.stats_ext.global + compiled.stats_ext.fold_traffic;
    let traced_traffic = trace
        .events
        .iter()
        .filter_map(|event| match event {
            BwdEvent::TrafficRead { cells, .. } => Some(*cells as usize),
            _ => None,
        })
        .sum();
    if symbolic_traffic != packed_traffic
        || packed_traffic != concrete_traffic
        || concrete_traffic != traced_traffic
    {
        return Err(BackwardEvaluationError::TrafficCertificateMismatch {
            symbolic: symbolic_traffic,
            packed: packed_traffic,
            concrete: concrete_traffic,
            traced: traced_traffic,
        });
    }
    if d.regime == BwdRegime::Ext && certify(&compiled, &trace).is_err() {
        return Err(BackwardEvaluationError::TrafficCertificateMismatch {
            symbolic: symbolic_traffic,
            packed: packed_traffic,
            concrete: concrete_traffic,
            traced: traced_traffic,
        });
    }

    Ok(CompiledBackwardEvaluation {
        symbolic,
        compiled,
        encoded,
        trace,
    })
}

fn map_replay_plan_error(error: PlanError) -> BackwardEvaluationError {
    match error {
        PlanError::ReplayDiverged { at_entry } => {
            BackwardEvaluationError::ReplayDiverged { at_entry }
        }
        PlanError::ReplayNotFullyConsumed { at_entry } => {
            BackwardEvaluationError::ReplayNotFullyConsumed { at_entry }
        }
        PlanError::ReplayInfeasible | PlanError::BudgetExceeded { .. } => {
            BackwardEvaluationError::ReplayInfeasible
        }
        other => BackwardEvaluationError::Plan(other),
    }
}

fn map_concrete_error(error: ConcreteBindError) -> BackwardEvaluationError {
    match error {
        ConcreteBindError::UnboundBackwardSource(expr) => {
            BackwardEvaluationError::UnboundBackwardSource(expr)
        }
        ConcreteBindError::BackwardCommit => BackwardEvaluationError::BackwardCommit,
        other => BackwardEvaluationError::Concrete(other),
    }
}

fn validate_fragment_order(
    order: Option<&[usize]>,
    fragment_count: usize,
) -> Result<Vec<usize>, BackwardEvaluationError> {
    let Some(order) = order else {
        return Ok((0..fragment_count).collect());
    };
    let mut sorted = order.to_vec();
    sorted.sort_unstable();
    if order.len() != fragment_count || sorted != (0..fragment_count).collect::<Vec<_>>() {
        return Err(BackwardEvaluationError::InvalidFragmentOrder {
            order: order.to_vec(),
            fragment_count,
        });
    }
    Ok(order.to_vec())
}

fn validate_and_resolve_backward(
    d: &DistilledLayer,
) -> Result<Vec<FieldKind>, BackwardEvaluationError> {
    let root_count = d.layer.roots.len();
    if d.root.0 as usize >= root_count {
        return Err(BackwardEvaluationError::InvalidBackwardRoot {
            root: d.root,
            root_count,
        });
    }

    let expression_count = d.layer.exprs.len();
    for (index, root) in d.layer.roots.iter().enumerate() {
        if root.expr.0 as usize >= expression_count {
            return Err(BackwardEvaluationError::InvalidRootExpression {
                root: RootId(index as u32),
                expr: root.expr,
                expression_count,
            });
        }
    }

    if d.fragments.c_init.terms.is_empty() && d.fragments.fragments.is_empty() {
        return Err(BackwardEvaluationError::EmptyFragmentDecomposition);
    }

    let defaults = backward_expr_defaults(d)?;
    validate_expression_acyclic(d)?;
    let expr_fields = backward_expr_fields(d, &defaults)?;
    let scalar_pure = backward_scalar_purity(d);
    for (fragment_index, fragment) in d.fragments.fragments.iter().enumerate() {
        if fragment.atoms.is_empty() {
            return Err(BackwardEvaluationError::EmptyFragmentAtoms {
                fragment: fragment_index,
            });
        }
        for (atom_index, &atom) in fragment.atoms.iter().enumerate() {
            if atom.0 as usize >= expression_count {
                return Err(BackwardEvaluationError::InvalidFragmentAtom {
                    fragment: fragment_index,
                    atom_index,
                    atom,
                    expression_count,
                });
            }
            if d.stable_key(atom).is_none() {
                return Err(BackwardEvaluationError::UnresolvedFragmentAtom {
                    fragment: fragment_index,
                    atom_index,
                    atom,
                });
            }
        }
        for (term, recipe) in fragment.recipe.terms.iter().enumerate() {
            for (factor_index, &factor) in recipe.factors.iter().enumerate() {
                if factor.0 as usize >= expression_count {
                    return Err(BackwardEvaluationError::InvalidFragmentRecipeFactor {
                        fragment: fragment_index,
                        term,
                        factor_index,
                        factor,
                        expression_count,
                    });
                }
                if !recipe_factor_resolves(d, &scalar_pure, factor) {
                    return Err(BackwardEvaluationError::UnresolvedFragmentRecipeFactor {
                        fragment: fragment_index,
                        term,
                        factor_index,
                        factor,
                    });
                }
            }
        }
    }
    for (term, recipe) in d.fragments.c_init.terms.iter().enumerate() {
        for (factor_index, &factor) in recipe.factors.iter().enumerate() {
            if factor.0 as usize >= expression_count {
                return Err(BackwardEvaluationError::InvalidAccInitFactor {
                    term,
                    factor_index,
                    factor,
                    expression_count,
                });
            }
            if !recipe_factor_resolves(d, &scalar_pure, factor) {
                return Err(BackwardEvaluationError::UnresolvedAccInitFactor {
                    term,
                    factor_index,
                    factor,
                });
            }
        }
    }
    Ok(expr_fields)
}

fn recipe_factor_resolves(d: &DistilledLayer, scalar_pure: &[bool], factor: ExprId) -> bool {
    if !scalar_pure[factor.0 as usize] {
        return false;
    }
    if d.stable_key(factor).is_some() {
        return true;
    }
    let Expr::Source(source) = d.layer.exprs[factor.0 as usize] else {
        return false;
    };
    matches!(
        &d.layer.sources[source.0 as usize].kind,
        SourceKind::Constant { .. } | SourceKind::Challenge { .. }
    )
}

fn backward_scalar_purity(d: &DistilledLayer) -> Vec<bool> {
    fn resolve(d: &DistilledLayer, expr: ExprId, memo: &mut [Option<bool>]) -> bool {
        if let Some(pure) = memo[expr.0 as usize] {
            return pure;
        }
        let pure = match &d.layer.exprs[expr.0 as usize] {
            Expr::Source(source) => matches!(
                &d.layer.sources[source.0 as usize].kind,
                SourceKind::Constant { .. } | SourceKind::Challenge { .. }
            ),
            Expr::Add(children) | Expr::Mul(children) => {
                children.iter().all(|&child| resolve(d, child, memo))
            }
        };
        memo[expr.0 as usize] = Some(pure);
        pure
    }

    let mut memo = vec![None; d.layer.exprs.len()];
    (0..d.layer.exprs.len())
        .map(|index| resolve(d, ExprId(index as u32), &mut memo))
        .collect()
}

fn backward_expr_defaults(d: &DistilledLayer) -> Result<Vec<FieldKind>, BackwardEvaluationError> {
    let expression_count = d.layer.exprs.len();
    let source_count = d.layer.sources.len();
    let mut defaults = Vec::with_capacity(expression_count);
    for (index, node) in d.layer.exprs.iter().enumerate() {
        let expr = ExprId(index as u32);
        let default =
            match node {
                Expr::Source(source) => {
                    let Some(source_info) = d.layer.sources.get(source.0 as usize) else {
                        return Err(BackwardEvaluationError::InvalidExpressionSource {
                            expr,
                            source: *source,
                            source_count,
                        });
                    };
                    if let SourceKind::LookupValue { query, .. } = &source_info.kind {
                        if query.0 as usize >= expression_count {
                            return Err(BackwardEvaluationError::InvalidLookupQuery {
                                expr,
                                source: *source,
                                query: *query,
                                expression_count,
                            });
                        }
                    }
                    match source_field(&source_info.kind) {
                        Ok(field) => field,
                        Err(place) => d.cross_fields.get(&place).copied().ok_or(
                            BackwardEvaluationError::MissingCrossLayerField { expr, place },
                        )?,
                    }
                }
                Expr::Add(children) | Expr::Mul(children) => {
                    for (child_index, &child) in children.iter().enumerate() {
                        if child.0 as usize >= expression_count {
                            return Err(BackwardEvaluationError::InvalidExpressionChild {
                                expr,
                                child_index,
                                child,
                                expression_count,
                            });
                        }
                    }
                    FieldKind::Base
                }
            };
        defaults.push(default);
    }
    Ok(defaults)
}

#[derive(Clone, Copy, PartialEq)]
enum ExpressionVisit {
    New,
    Active,
    Done,
}

fn validate_expression_acyclic(d: &DistilledLayer) -> Result<(), BackwardEvaluationError> {
    fn visit(
        d: &DistilledLayer,
        expr: ExprId,
        state: &mut [ExpressionVisit],
    ) -> Result<(), BackwardEvaluationError> {
        match state[expr.0 as usize] {
            ExpressionVisit::Done => return Ok(()),
            ExpressionVisit::Active => {
                return Err(BackwardEvaluationError::CyclicExpression { expr });
            }
            ExpressionVisit::New => {}
        }
        state[expr.0 as usize] = ExpressionVisit::Active;
        match &d.layer.exprs[expr.0 as usize] {
            Expr::Source(source) => {
                if let SourceKind::LookupValue { query, .. } =
                    &d.layer.sources[source.0 as usize].kind
                {
                    visit(d, *query, state)?;
                }
            }
            Expr::Add(children) | Expr::Mul(children) => {
                for &child in children {
                    visit(d, child, state)?;
                }
            }
        }
        state[expr.0 as usize] = ExpressionVisit::Done;
        Ok(())
    }

    let mut state = vec![ExpressionVisit::New; d.layer.exprs.len()];
    for index in 0..d.layer.exprs.len() {
        visit(d, ExprId(index as u32), &mut state)?;
    }
    Ok(())
}

fn backward_expr_fields(
    d: &DistilledLayer,
    defaults: &[FieldKind],
) -> Result<Vec<FieldKind>, BackwardEvaluationError> {
    let mut fields = vec![None; d.layer.exprs.len()];
    let mut resolved = Vec::with_capacity(d.layer.exprs.len());
    for index in 0..d.layer.exprs.len() {
        resolved.push(backward_expr_field(
            ExprId(index as u32),
            d,
            defaults,
            &mut fields,
        )?);
    }
    Ok(resolved)
}

fn backward_expr_field(
    expr: ExprId,
    d: &DistilledLayer,
    defaults: &[FieldKind],
    fields: &mut [Option<FieldKind>],
) -> Result<FieldKind, BackwardEvaluationError> {
    if let Some(field) = fields[expr.0 as usize] {
        return Ok(field);
    }
    let field = if let Some(&field) = d.field_overrides.get(&expr) {
        field
    } else {
        match &d.layer.exprs[expr.0 as usize] {
            Expr::Source(_) => defaults[expr.0 as usize],
            Expr::Add(children) | Expr::Mul(children) => {
                let mut field = defaults[expr.0 as usize];
                for &child in children {
                    field = join(field, backward_expr_field(child, d, defaults, fields)?);
                }
                field
            }
        }
    };
    fields[expr.0 as usize] = Some(field);
    Ok(field)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashMap};

    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, Bf, BwdRegime, ChallengeKey, ChallengePower, ChallengeRef,
        ChallengeResolver, ClaimInfo, DagLayer, Expr, ExprId, Ext, FieldKind, LookupResolver,
        LookupValueKind, ReadPlace, ReadResolver, Resolvers, Root, RootGroup, RootOrigin, RootSlot,
        SourceId, SourceInfo, SourceKind, VirtualSetupKind, VirtualSetupResolver, eval_layer_expr,
        eval_layer_root,
    };
    use field::{Field, FieldExtension, PrimeField};

    use crate::bwd::distill::{DistilledLayer, distill, distilled_site_domain};
    use crate::bwd::fragment::{FragmentSpec, FragmentTable, MergedRecipe, ProductRecipe};
    use crate::bwd::plan::{BwdOccurrencePlan, PlanAction, PlanEntry, plan_entries_fnv};
    use crate::bwd::source::BwdSpecial;
    use crate::bwd::trace::{BwdEvent, BwdServeKind};
    use crate::fwd::isa::MAX_CELL;

    use super::{
        BackwardEvaluationError, compile_backward_fragments_replayed,
        compile_backward_fragments_uncached, elaborate_backward_fragments_driver,
        elaborate_backward_fragments_uncached,
    };
    use crate::eval_plan::{ConcreteBindError, EvalOp, Operand, TempId, bind_packed_plan};

    fn ext(value: u32) -> Ext {
        <Ext as FieldExtension<Bf>>::from_base(Bf::from_u32_with_reduction(value))
    }

    struct BackwardTestResolver;

    impl ReadResolver for BackwardTestResolver {
        fn read(&self, _place: &ReadPlace, row: usize) -> Ext {
            ext(17 + row as u32)
        }
    }

    impl LookupResolver for BackwardTestResolver {
        fn lookup(
            &self,
            _kind: &LookupValueKind,
            _set_index: usize,
            _evaluated_query: Ext,
            _row: usize,
        ) -> Bf {
            Bf::ZERO
        }
    }

    impl VirtualSetupResolver for BackwardTestResolver {
        fn virtual_setup(&self, _kind: &VirtualSetupKind, _row: usize) -> Bf {
            Bf::ZERO
        }
    }

    impl ChallengeResolver for BackwardTestResolver {
        fn challenge(&self, _reference: &ChallengeRef) -> Ext {
            ext(11)
        }
    }

    static BACKWARD_TEST_RESOLVER: BackwardTestResolver = BackwardTestResolver;

    #[test]
    fn backward_boundaries_reject_invalid_cell_budgets() {
        let d = backward_fixture();
        let replay = replay_plan(&d);
        let invalid = [0, MAX_CELL as usize / 4 + 1, usize::MAX];

        for budget_cells in invalid {
            assert!(matches!(
                compile_backward_fragments_uncached(&d, None, budget_cells, false),
                Err(BackwardEvaluationError::BudgetCellsOutOfRange {
                    budget_cells: actual,
                }) if actual == budget_cells
            ));
            assert!(matches!(
                compile_backward_fragments_replayed(&d, &replay, None, budget_cells),
                Err(BackwardEvaluationError::BudgetCellsOutOfRange {
                    budget_cells: actual,
                }) if actual == budget_cells
            ));
        }
    }

    fn backward_test_resolvers() -> Resolvers<'static> {
        Resolvers {
            read: &BACKWARD_TEST_RESOLVER,
            lookup: &BACKWARD_TEST_RESOLVER,
            virtual_setup: &BACKWARD_TEST_RESOLVER,
            challenge: &BACKWARD_TEST_RESOLVER,
        }
    }

    fn backward_plan_acc(out: &super::BackwardSymbolicEvaluation, d: &DistilledLayer) -> Ext {
        let resolvers = backward_test_resolvers();
        let mut acc = None;
        let mut temps = HashMap::new();
        let mut returned = None;

        for op in &out.plan.ops {
            match op {
                EvalOp::AccInit(operand) => {
                    acc = Some(backward_operand(*operand, out, d, &resolvers, &mut temps));
                }
                EvalOp::AccAdd { sign, operand } => {
                    let rhs = backward_operand(*operand, out, d, &resolvers, &mut temps);
                    let acc = acc.as_mut().expect("accumulator must be initialized");
                    match sign {
                        crate::fwd::isa::Sign::Plus => acc.add_assign(&rhs),
                        crate::fwd::isa::Sign::Minus => acc.sub_assign(&rhs),
                    };
                }
                EvalOp::AccMul(operand) => {
                    let rhs = backward_operand(*operand, out, d, &resolvers, &mut temps);
                    acc.as_mut()
                        .expect("accumulator must be initialized")
                        .mul_assign(&rhs);
                }
                EvalOp::AccFma { sign, lhs, rhs } => {
                    let mut product = backward_operand(*lhs, out, d, &resolvers, &mut temps);
                    product.mul_assign(&backward_operand(*rhs, out, d, &resolvers, &mut temps));
                    let acc = acc.as_mut().expect("accumulator must be initialized");
                    match sign {
                        crate::fwd::isa::Sign::Plus => acc.add_assign(&product),
                        crate::fwd::isa::Sign::Minus => acc.sub_assign(&product),
                    };
                }
                EvalOp::AccNeg => {
                    acc.as_mut()
                        .expect("accumulator must be initialized")
                        .negate();
                }
                EvalOp::SaveAcc(temp) => {
                    assert!(
                        temps
                            .insert(temp.id, acc.expect("accumulator must be initialized"))
                            .is_none(),
                        "temporary must be unique"
                    );
                }
                EvalOp::ReturnAcc { .. } => {
                    returned = Some(acc.expect("terminal must have an accumulator"));
                }
                EvalOp::CacheStore { .. } | EvalOp::CacheDrop(_) | EvalOp::Commit { .. } => {
                    panic!("uncached backward plan must not contain cache or commit operations")
                }
            }
        }

        returned.expect("plan must return its accumulator")
    }

    fn backward_operand(
        operand: Operand,
        out: &super::BackwardSymbolicEvaluation,
        d: &DistilledLayer,
        resolvers: &Resolvers<'_>,
        temps: &mut HashMap<TempId, Ext>,
    ) -> Ext {
        match operand {
            Operand::Source(value) => eval_layer_expr(&d.layer, value.expr, 3, resolvers),
            Operand::Temp(temp) => temps.remove(&temp.id).expect("temporary must be live"),
            Operand::Unit { negative } => {
                let mut value = Ext::ONE;
                if negative {
                    value.negate();
                }
                value
            }
            Operand::BackwardSpecial { desc } => match out.specials.get(desc) {
                Some(BwdSpecial::AccInit) => d.fragments.c_init.evaluate(&d.layer, resolvers),
                Some(BwdSpecial::Coefficient { fragment }) => d.fragments.fragments
                    [*fragment as usize]
                    .recipe
                    .evaluate(&d.layer, resolvers),
                other => {
                    panic!("backward descriptor {desc} is not a coefficient source: {other:?}")
                }
            },
            Operand::Resident(_) => panic!("uncached backward plan must not use residents"),
        }
    }

    fn read_src(column: usize) -> SourceInfo {
        SourceInfo {
            kind: SourceKind::Read {
                place: ReadPlace::BaseLayerWitness { column },
            },
        }
    }

    fn claim_only_root(expr: ExprId, relation_index: usize) -> Root {
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

    fn backward_fixture() -> DistilledLayer {
        let roots = vec![
            claim_only_root(ExprId(0), 0),
            claim_only_root(ExprId(5), 1),
            claim_only_root(ExprId(3), 2),
        ];
        let layer = DagLayer {
            sources: vec![
                read_src(0),
                read_src(1),
                read_src(2),
                SourceInfo {
                    kind: SourceKind::Constant { value: 7 },
                },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Source(SourceId(3)),
                Expr::Add(vec![ExprId(1), ExprId(2)]),
                Expr::Mul(vec![ExprId(0), ExprId(4)]),
            ],
            batching: BatchingOrder {
                roots: (0..roots.len())
                    .map(|i| cs::gkr_compiler::dag_ir::RootId(i as u32))
                    .collect(),
            },
            roots,
            resolutions: BTreeMap::new(),
        };
        distill(&layer, BwdRegime::Ext, &HashMap::new(), None)
    }

    fn backward_two_domain_values_fixture() -> DistilledLayer {
        let roots = vec![
            claim_only_root(ExprId(0), 0),
            claim_only_root(ExprId(1), 1),
            claim_only_root(ExprId(5), 2),
            claim_only_root(ExprId(3), 3),
        ];
        let layer = DagLayer {
            sources: vec![
                read_src(0),
                read_src(1),
                read_src(2),
                SourceInfo {
                    kind: SourceKind::Constant { value: 7 },
                },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Source(SourceId(3)),
                Expr::Add(vec![ExprId(1), ExprId(2)]),
                Expr::Mul(vec![ExprId(0), ExprId(4)]),
            ],
            batching: BatchingOrder {
                roots: (0..roots.len())
                    .map(|i| cs::gkr_compiler::dag_ir::RootId(i as u32))
                    .collect(),
            },
            roots,
            resolutions: BTreeMap::new(),
        };
        distill(&layer, BwdRegime::Ext, &HashMap::new(), None)
    }

    fn replay_plan(d: &DistilledLayer) -> BwdOccurrencePlan {
        let compiled = compile_backward_fragments_uncached(d, None, 4, false).unwrap();
        let domain = distilled_site_domain(d)
            .into_iter()
            .map(|site| site.value)
            .collect::<std::collections::BTreeSet<_>>();
        let entries = compiled
            .trace
            .events
            .iter()
            .filter_map(|event| match event {
                BwdEvent::Serve { fp, .. } if domain.contains(&fp.value) => Some(PlanEntry {
                    fp: *fp,
                    action: PlanAction::Bypass,
                }),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(
            entries.len() >= 2,
            "fixture must expose replayable domain serves"
        );
        BwdOccurrencePlan {
            epoch: compiled.trace.epoch,
            entries_fnv: plan_entries_fnv(&entries),
            stream_reductions: compiled.trace.stream_reductions,
            entries,
        }
    }

    fn malformed_uncached_error(d: &DistilledLayer) -> BackwardEvaluationError {
        match std::panic::catch_unwind(|| elaborate_backward_fragments_uncached(d, None, 4, false))
        {
            Ok(Err(error)) => error,
            Ok(Ok(_)) => panic!("malformed backward layer unexpectedly elaborated"),
            Err(_) => panic!("malformed backward layer panicked instead of returning an error"),
        }
    }

    fn malformed_replayed_error(
        d: &DistilledLayer,
        plan: &BwdOccurrencePlan,
    ) -> BackwardEvaluationError {
        match std::panic::catch_unwind(|| compile_backward_fragments_replayed(d, plan, None, 4)) {
            Ok(Err(error)) => error,
            Ok(Ok(_)) => panic!("malformed backward layer unexpectedly replayed"),
            Err(_) => panic!("malformed backward replay panicked instead of returning an error"),
        }
    }

    fn synthesized_expr(d: &DistilledLayer) -> ExprId {
        (0..d.layer.exprs.len())
            .map(|index| ExprId(index as u32))
            .find(|&expr| d.stable_key(expr).is_none())
            .expect("fixture must contain a synthesized batching factor")
    }

    fn stable_read_expr(d: &DistilledLayer) -> ExprId {
        (0..d.layer.exprs.len())
            .map(|index| ExprId(index as u32))
            .find(|&expr| {
                d.stable_key(expr).is_some()
                    && matches!(
                        d.layer.exprs[expr.0 as usize],
                        Expr::Source(source)
                            if matches!(
                                &d.layer.sources[source.0 as usize].kind,
                                SourceKind::Read { .. }
                            )
                    )
            })
            .expect("fixture must contain a stable canonical Read expression")
    }

    #[test]
    fn malformed_backward_empty_fragment_atoms_returns_attributable_error() {
        let mut d = backward_fixture();
        d.fragments.fragments[0].atoms.clear();

        assert_eq!(
            format!("{:?}", malformed_uncached_error(&d)),
            "EmptyFragmentAtoms { fragment: 0 }"
        );
    }

    #[test]
    fn malformed_backward_invalid_fragment_atom_returns_attributable_error() {
        let mut d = backward_fixture();
        let expression_count = d.layer.exprs.len();
        let atom = ExprId(expression_count as u32);
        d.fragments.fragments[0].atoms[0] = atom;

        assert_eq!(
            format!("{:?}", malformed_uncached_error(&d)),
            format!(
                "InvalidFragmentAtom {{ fragment: 0, atom_index: 0, atom: {atom:?}, expression_count: {expression_count} }}"
            )
        );
    }

    #[test]
    fn malformed_backward_invalid_fragment_recipe_factor_returns_attributable_error() {
        let mut d = backward_fixture();
        let expression_count = d.layer.exprs.len();
        let factor = ExprId(expression_count as u32);
        d.fragments.fragments[0].recipe = MergedRecipe {
            terms: vec![ProductRecipe {
                factors: vec![factor],
            }],
        };

        assert_eq!(
            format!("{:?}", malformed_uncached_error(&d)),
            format!(
                "InvalidFragmentRecipeFactor {{ fragment: 0, term: 0, factor_index: 0, factor: {factor:?}, expression_count: {expression_count} }}"
            )
        );
    }

    #[test]
    fn malformed_backward_invalid_c_init_factor_returns_attributable_error() {
        let mut d = backward_fixture();
        let expression_count = d.layer.exprs.len();
        let factor = ExprId(expression_count as u32);
        d.fragments.c_init = MergedRecipe {
            terms: vec![ProductRecipe {
                factors: vec![factor],
            }],
        };

        assert_eq!(
            format!("{:?}", malformed_uncached_error(&d)),
            format!(
                "InvalidAccInitFactor {{ term: 0, factor_index: 0, factor: {factor:?}, expression_count: {expression_count} }}"
            )
        );
    }

    #[test]
    fn malformed_backward_missing_cross_layer_field_returns_attributable_error() {
        let mut d = backward_fixture();
        let place = ReadPlace::CacheOutput {
            layer: 9,
            offset: 4,
        };
        d.layer.sources[0].kind = SourceKind::Read {
            place: place.clone(),
        };
        let expr = d
            .layer
            .exprs
            .iter()
            .position(|node| matches!(node, Expr::Source(SourceId(0))))
            .map(|index| ExprId(index as u32))
            .expect("fixture must reference source zero");

        assert_eq!(
            format!("{:?}", malformed_uncached_error(&d)),
            format!("MissingCrossLayerField {{ expr: {expr:?}, place: {place:?} }}")
        );
    }

    #[test]
    fn malformed_backward_invalid_root_returns_attributable_error() {
        let mut d = backward_fixture();
        let root_count = d.layer.roots.len();
        d.root = cs::gkr_compiler::dag_ir::RootId(root_count as u32);

        assert_eq!(
            format!("{:?}", malformed_uncached_error(&d)),
            format!(
                "InvalidBackwardRoot {{ root: {:?}, root_count: {root_count} }}",
                d.root
            )
        );
    }

    #[test]
    fn malformed_backward_invalid_root_expression_returns_attributable_error() {
        let mut d = backward_fixture();
        let expression_count = d.layer.exprs.len();
        let expr = ExprId(expression_count as u32);
        d.layer.roots[d.root.0 as usize].expr = expr;

        assert_eq!(
            format!("{:?}", malformed_uncached_error(&d)),
            format!(
                "InvalidRootExpression {{ root: {:?}, expr: {expr:?}, expression_count: {expression_count} }}",
                d.root
            )
        );
    }

    #[test]
    fn malformed_backward_invalid_expression_references_return_attributable_errors() {
        let mut invalid_source = backward_fixture();
        let source_count = invalid_source.layer.sources.len();
        let expr = ExprId(0);
        let source = SourceId(source_count as u32);
        invalid_source.layer.exprs[0] = Expr::Source(source);
        assert_eq!(
            format!("{:?}", malformed_uncached_error(&invalid_source)),
            format!(
                "InvalidExpressionSource {{ expr: {expr:?}, source: {source:?}, source_count: {source_count} }}"
            )
        );

        let mut invalid_child = backward_fixture();
        let expression_count = invalid_child.layer.exprs.len();
        let child = ExprId(expression_count as u32);
        let (parent_index, children) = invalid_child
            .layer
            .exprs
            .iter_mut()
            .enumerate()
            .find_map(|(index, node)| match node {
                Expr::Add(children) if !children.is_empty() => Some((index, children)),
                _ => None,
            })
            .expect("fixture must contain a non-empty add");
        children[0] = child;
        let parent = ExprId(parent_index as u32);
        assert_eq!(
            format!("{:?}", malformed_uncached_error(&invalid_child)),
            format!(
                "InvalidExpressionChild {{ expr: {parent:?}, child_index: 0, child: {child:?}, expression_count: {expression_count} }}"
            )
        );
    }

    #[test]
    fn malformed_backward_invalid_lookup_query_returns_attributable_error() {
        let mut d = backward_fixture();
        let expression_count = d.layer.exprs.len();
        let query = ExprId(expression_count as u32);
        let source = SourceId(0);
        d.layer.sources[source.0 as usize].kind = SourceKind::LookupValue {
            kind: LookupValueKind::RangeCheck16Index,
            set_index: 0,
            query,
        };
        let expr = d
            .layer
            .exprs
            .iter()
            .position(|node| matches!(node, Expr::Source(actual) if *actual == source))
            .map(|index| ExprId(index as u32))
            .expect("fixture must reference source zero");

        assert_eq!(
            format!("{:?}", malformed_uncached_error(&d)),
            format!(
                "InvalidLookupQuery {{ expr: {expr:?}, source: {source:?}, query: {query:?}, expression_count: {expression_count} }}"
            )
        );
    }

    #[test]
    fn malformed_backward_expression_cycle_returns_attributable_error() {
        let mut d = backward_fixture();
        let (parent_index, children) = d
            .layer
            .exprs
            .iter_mut()
            .enumerate()
            .find_map(|(index, node)| match node {
                Expr::Add(children) if !children.is_empty() => Some((index, children)),
                _ => None,
            })
            .expect("fixture must contain a non-empty add");
        let expr = ExprId(parent_index as u32);
        children[0] = expr;
        d.field_overrides.insert(expr, FieldKind::Ext);

        assert_eq!(
            format!("{:?}", malformed_uncached_error(&d)),
            format!("CyclicExpression {{ expr: {expr:?} }}")
        );
    }

    #[test]
    fn malformed_backward_unresolved_fragment_atom_returns_attributable_error() {
        let mut d = backward_fixture();
        let atom = synthesized_expr(&d);
        d.fragments.fragments[0].atoms[0] = atom;

        assert_eq!(
            format!("{:?}", malformed_uncached_error(&d)),
            format!("UnresolvedFragmentAtom {{ fragment: 0, atom_index: 0, atom: {atom:?} }}")
        );
    }

    #[test]
    fn malformed_backward_unresolved_recipe_factors_return_attributable_errors() {
        let mut fragment = backward_fixture();
        let fragment_factor = synthesized_expr(&fragment);
        let Expr::Source(fragment_source) = fragment.layer.exprs[fragment_factor.0 as usize] else {
            panic!("synthesized factor must be a source")
        };
        fragment.layer.sources[fragment_source.0 as usize].kind = SourceKind::Read {
            place: ReadPlace::BaseLayerWitness { column: 99 },
        };
        fragment.fragments.fragments[0].recipe = MergedRecipe {
            terms: vec![ProductRecipe {
                factors: vec![fragment_factor],
            }],
        };
        assert_eq!(
            format!("{:?}", malformed_uncached_error(&fragment)),
            format!(
                "UnresolvedFragmentRecipeFactor {{ fragment: 0, term: 0, factor_index: 0, factor: {fragment_factor:?} }}"
            )
        );

        let mut c_init = backward_fixture();
        let c_init_factor = synthesized_expr(&c_init);
        let Expr::Source(c_init_source) = c_init.layer.exprs[c_init_factor.0 as usize] else {
            panic!("synthesized factor must be a source")
        };
        c_init.layer.sources[c_init_source.0 as usize].kind = SourceKind::Read {
            place: ReadPlace::BaseLayerWitness { column: 100 },
        };
        for fragment in &mut c_init.fragments.fragments {
            fragment.recipe = MergedRecipe {
                terms: vec![ProductRecipe::default()],
            };
        }
        c_init.fragments.c_init = MergedRecipe {
            terms: vec![ProductRecipe {
                factors: vec![c_init_factor],
            }],
        };
        assert_eq!(
            format!("{:?}", malformed_uncached_error(&c_init)),
            format!(
                "UnresolvedAccInitFactor {{ term: 0, factor_index: 0, factor: {c_init_factor:?} }}"
            )
        );
    }

    #[test]
    fn malformed_backward_stable_read_recipe_factor_in_fragment_returns_error() {
        let mut d = backward_fixture();
        let factor = stable_read_expr(&d);
        d.fragments.fragments[0].recipe = MergedRecipe {
            terms: vec![ProductRecipe {
                factors: vec![factor],
            }],
        };

        assert_eq!(
            format!("{:?}", malformed_uncached_error(&d)),
            format!(
                "UnresolvedFragmentRecipeFactor {{ fragment: 0, term: 0, factor_index: 0, factor: {factor:?} }}"
            )
        );
    }

    #[test]
    fn malformed_backward_stable_read_recipe_factor_in_c_init_returns_error() {
        let mut d = backward_fixture();
        let factor = stable_read_expr(&d);
        d.fragments.c_init = MergedRecipe {
            terms: vec![ProductRecipe {
                factors: vec![factor],
            }],
        };

        assert_eq!(
            format!("{:?}", malformed_uncached_error(&d)),
            format!("UnresolvedAccInitFactor {{ term: 0, factor_index: 0, factor: {factor:?} }}")
        );
    }

    #[test]
    fn malformed_backward_replayed_boundary_uses_shared_validation() {
        let mut d = backward_fixture();
        let plan = replay_plan(&d);
        let expression_count = d.layer.exprs.len();
        let atom = ExprId(expression_count as u32);
        d.fragments.fragments[0].atoms[0] = atom;

        assert_eq!(
            format!("{:?}", malformed_replayed_error(&d, &plan)),
            format!(
                "InvalidFragmentAtom {{ fragment: 0, atom_index: 0, atom: {atom:?}, expression_count: {expression_count} }}"
            )
        );
    }

    #[test]
    fn replay_rejects_stale_epoch() {
        let d = backward_fixture();
        let mut plan = replay_plan(&d);
        plan.epoch ^= 1;

        assert!(matches!(
            compile_backward_fragments_replayed(&d, &plan, None, 4),
            Err(BackwardEvaluationError::StaleReplayEpoch { .. })
        ));
    }

    #[test]
    fn replay_rejects_bad_entries_fingerprint() {
        let d = backward_fixture();
        let mut plan = replay_plan(&d);
        plan.entries_fnv ^= 1;

        assert!(matches!(
            compile_backward_fragments_replayed(&d, &plan, None, 4),
            Err(BackwardEvaluationError::ReplayEntriesFingerprintMismatch)
        ));
    }

    #[test]
    fn replay_rejects_reordered_entries() {
        let d = backward_fixture();
        let mut plan = replay_plan(&d);
        plan.entries.swap(0, 1);
        plan.entries_fnv = plan_entries_fnv(&plan.entries);

        assert!(matches!(
            compile_backward_fragments_replayed(&d, &plan, None, 4),
            Err(BackwardEvaluationError::ReplayDiverged { at_entry: 0 })
        ));
    }

    #[test]
    fn replay_rejects_truncated_entries() {
        let d = backward_fixture();
        let mut plan = replay_plan(&d);
        let at_entry = plan.entries.len() - 1;
        plan.entries.pop();
        plan.entries_fnv = plan_entries_fnv(&plan.entries);

        assert!(matches!(
            compile_backward_fragments_replayed(&d, &plan, None, 4),
            Err(BackwardEvaluationError::ReplayDiverged { at_entry: at }) if at == at_entry
        ));
    }

    #[test]
    fn replay_rejects_all_entries_for_one_value_removed() {
        let d = backward_two_domain_values_fixture();
        let mut plan = replay_plan(&d);
        let removed = plan.entries[0].fp.value;
        plan.entries.retain(|entry| entry.fp.value != removed);
        assert!(
            !plan.entries.is_empty(),
            "fixture must retain another replay-domain value"
        );
        plan.entries_fnv = plan_entries_fnv(&plan.entries);

        assert!(matches!(
            compile_backward_fragments_replayed(&d, &plan, None, 4),
            Err(BackwardEvaluationError::ReplayDiverged { at_entry: 0 })
        ));
    }

    #[test]
    fn replay_rejects_empty_entries_for_nonempty_actual_stream() {
        let d = backward_fixture();
        let mut plan = replay_plan(&d);
        assert!(!plan.entries.is_empty());
        plan.entries.clear();
        plan.entries_fnv = plan_entries_fnv(&plan.entries);

        assert!(matches!(
            compile_backward_fragments_replayed(&d, &plan, None, 4),
            Err(BackwardEvaluationError::ReplayDiverged { at_entry: 0 })
        ));
    }

    #[test]
    fn replay_rejects_appended_entries() {
        let d = backward_fixture();
        let mut plan = replay_plan(&d);
        let at_entry = plan.entries.len();
        plan.entries.push(*plan.entries.last().unwrap());
        plan.entries_fnv = plan_entries_fnv(&plan.entries);

        assert!(matches!(
            compile_backward_fragments_replayed(&d, &plan, None, 4),
            Err(BackwardEvaluationError::ReplayNotFullyConsumed { at_entry: at })
                if at == at_entry
        ));
    }

    #[test]
    fn replay_rejects_terminal_retain() {
        let d = backward_fixture();
        let mut plan = replay_plan(&d);
        let entry = plan.entries.len() - 1;
        let value = plan.entries[entry].fp.value;
        plan.entries[entry].action = PlanAction::Retain;
        plan.entries_fnv = plan_entries_fnv(&plan.entries);

        assert!(matches!(
            compile_backward_fragments_replayed(&d, &plan, None, 4),
            Err(BackwardEvaluationError::MalformedReplayPlan {
                entry: actual_entry,
                value: actual_value,
            }) if actual_entry == entry && actual_value == value
        ));
    }

    fn assert_single_uncached_terminal(out: &super::BackwardSymbolicEvaluation) {
        assert!(matches!(
            out.plan.ops.last(),
            Some(EvalOp::ReturnAcc { .. })
        ));
        assert_eq!(out.plan.stats.cache_stores, 0);
        assert_eq!(out.plan.stats.cache_hits, 0);
        assert_eq!(out.plan.stats.cache_drops, 0);
        assert_eq!(
            out.plan
                .ops
                .iter()
                .filter(|op| matches!(op, EvalOp::ReturnAcc { .. }))
                .count(),
            1
        );
    }

    #[test]
    fn backward_uncached_fragment_shape() {
        let d = backward_fixture();
        let identity: Vec<_> = (0..d.fragments.fragments.len()).collect();
        let out = elaborate_backward_fragments_uncached(&d, Some(&identity), 4, false).unwrap();
        assert_single_uncached_terminal(&out);

        let streamed = elaborate_backward_fragments_uncached(&d, Some(&identity), 4, true).unwrap();
        assert_single_uncached_terminal(&streamed);
        assert_eq!(
            out.plan.stats.dram_read_lanes,
            streamed.plan.stats.dram_read_lanes
        );
        assert_ne!(out.plan.ops, streamed.plan.ops);
        let legacy_acc = backward_plan_acc(&out, &d);
        let streamed_acc = backward_plan_acc(&streamed, &d);
        assert_eq!(legacy_acc, streamed_acc);
        let resolvers = backward_test_resolvers();
        assert_eq!(legacy_acc, eval_layer_root(&d.layer, d.root, 3, &resolvers));

        let mut reversed = identity;
        reversed.reverse();
        let out = elaborate_backward_fragments_uncached(&d, Some(&reversed), 4, false).unwrap();
        assert_single_uncached_terminal(&out);
    }

    #[test]
    fn backward_uncached_coeff_and_c_init() {
        let d = backward_fixture();
        assert!(!d.fragments.c_init.terms.is_empty());
        assert!(
            d.fragments
                .fragments
                .iter()
                .any(|fragment| !fragment.recipe.is_trivial())
        );

        let out = elaborate_backward_fragments_uncached(&d, None, 4, false).unwrap();
        let EvalOp::AccInit(Operand::BackwardSpecial { desc }) = out.plan.ops[0] else {
            panic!("non-empty c_init must initialize the accumulator through its descriptor")
        };
        assert_eq!(out.specials.get(desc), Some(&BwdSpecial::AccInit));
        assert_eq!(
            out.plan
                .ops
                .iter()
                .filter(|op| matches!(
                    op,
                    EvalOp::AccMul(Operand::BackwardSpecial { desc })
                        if matches!(out.specials.get(*desc), Some(BwdSpecial::Coefficient { .. }))
                ))
                .count(),
            1,
            "the non-trivial fragment recipe must use one coefficient operand"
        );
        assert!(matches!(
            bind_packed_plan(&out.packed, &d.layer, &[d.root], 0, 16),
            Err(ConcreteBindError::BackwardSpecialRequiresBindings { .. })
        ));
    }

    #[test]
    fn backward_uncached_binds_coefficient_specials() {
        let d = backward_fixture();

        let out = compile_backward_fragments_uncached(&d, None, 4, false).unwrap();

        assert!(
            out.compiled
                .program
                .instrs
                .iter()
                .any(|instruction| match instruction {
                    crate::fwd::isa::Instr::Mov {
                        src: Some(crate::fwd::isa::OperandLine::Special { desc }),
                        ..
                    } => matches!(out.compiled.specials.get(*desc), Some(BwdSpecial::AccInit)),
                    _ => false,
                })
        );
        assert!(
            out.compiled
                .program
                .instrs
                .iter()
                .any(|instruction| match instruction {
                    crate::fwd::isa::Instr::Mul { operands, .. } =>
                        operands.iter().any(|operand| {
                            matches!(
                                operand,
                                crate::fwd::isa::OperandLine::Special { desc }
                                    if matches!(
                                        out.compiled.specials.get(*desc),
                                        Some(BwdSpecial::Coefficient { .. })
                                    )
                            )
                        }),
                    _ => false,
                })
        );
    }

    #[test]
    fn backward_uncached_rejects_invalid_order() {
        let d = backward_fixture();
        assert!(matches!(
            elaborate_backward_fragments_uncached(&d, Some(&[0, 0]), 4, false),
            Err(BackwardEvaluationError::InvalidFragmentOrder { .. })
        ));
        assert!(matches!(
            elaborate_backward_fragments_uncached(&d, Some(&[0, 2]), 4, false),
            Err(BackwardEvaluationError::InvalidFragmentOrder { .. })
        ));
    }

    #[test]
    fn backward_uncached_rejects_empty_decomposition() {
        let mut d = backward_fixture();
        d.fragments = FragmentTable::default();
        assert!(matches!(
            elaborate_backward_fragments_uncached(&d, None, 4, false),
            Err(BackwardEvaluationError::EmptyFragmentDecomposition)
        ));
    }

    #[test]
    fn backward_uncached_infers_cross_layer_read_field() {
        let place = ReadPlace::CacheOutput {
            layer: 0,
            offset: 0,
        };
        let layer = DagLayer {
            sources: vec![SourceInfo {
                kind: SourceKind::Read {
                    place: place.clone(),
                },
            }],
            exprs: vec![Expr::Source(SourceId(0))],
            batching: BatchingOrder {
                roots: vec![cs::gkr_compiler::dag_ir::RootId(0)],
            },
            roots: vec![claim_only_root(ExprId(0), 0)],
            resolutions: BTreeMap::new(),
        };
        let cross = HashMap::from([(place, FieldKind::Ext)]);
        let d = distill(&layer, BwdRegime::R0, &cross, None);

        let out = compile_backward_fragments_uncached(&d, None, 4, false).unwrap();
        let EvalOp::AccInit(Operand::Source(value)) = out.symbolic.plan.ops[0] else {
            panic!("single read fragment must initialize from its source")
        };
        assert_eq!(value.field, FieldKind::Ext);
    }

    #[test]
    fn backward_legacy_reduction_keeps_final_child_in_accumulator() {
        let sources = (0..5)
            .map(|column| SourceInfo {
                kind: SourceKind::Read {
                    place: ReadPlace::CacheOutput {
                        layer: 0,
                        offset: column,
                    },
                },
            })
            .collect::<Vec<_>>();
        let mut exprs = (0..5)
            .map(|source| Expr::Source(SourceId(source)))
            .collect::<Vec<_>>();
        exprs.push(Expr::Add((0..5).map(ExprId).collect()));
        let layer = DagLayer {
            sources,
            exprs,
            batching: BatchingOrder {
                roots: vec![cs::gkr_compiler::dag_ir::RootId(0)],
            },
            roots: vec![claim_only_root(ExprId(5), 0)],
            resolutions: BTreeMap::new(),
        };
        let cross = (0..5)
            .map(|offset| (ReadPlace::CacheOutput { layer: 0, offset }, FieldKind::Ext))
            .collect();
        let mut d = distill(&layer, BwdRegime::R0, &cross, None);
        let root_expr = d.layer.roots[d.root.0 as usize].expr;
        d.fragments = FragmentTable {
            fragments: vec![FragmentSpec {
                atoms: vec![root_expr],
                recipe: MergedRecipe {
                    terms: vec![ProductRecipe::default()],
                },
            }],
            c_init: MergedRecipe::default(),
        };

        let out = compile_backward_fragments_uncached(&d, None, 4, false).unwrap();

        assert!(out.compiled.stats.max_live_cells <= 16);
    }

    #[test]
    fn backward_legacy_reduction_evaluates_deep_cone_before_stash() {
        let challenge = || SourceInfo {
            kind: SourceKind::Challenge {
                reference: ChallengeRef {
                    key: ChallengeKey::ClaimBatching,
                    power: ChallengePower::One,
                },
            },
        };
        let sources = vec![
            challenge(),
            SourceInfo {
                kind: SourceKind::Constant { value: 1 },
            },
            SourceInfo {
                kind: SourceKind::VirtualSetup {
                    kind: VirtualSetupKind::InitsAndTeardownsLow,
                },
            },
            challenge(),
            SourceInfo {
                kind: SourceKind::VirtualSetup {
                    kind: VirtualSetupKind::InitsAndTeardownsHigh,
                },
            },
            challenge(),
            SourceInfo {
                kind: SourceKind::Constant { value: 1024 },
            },
        ];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Source(SourceId(2)),
            Expr::Source(SourceId(3)),
            Expr::Mul(vec![ExprId(2), ExprId(3)]),
            Expr::Source(SourceId(4)),
            Expr::Source(SourceId(5)),
            Expr::Mul(vec![ExprId(5), ExprId(6)]),
            Expr::Add(vec![ExprId(0), ExprId(1), ExprId(4), ExprId(7)]),
            Expr::Source(SourceId(6)),
            Expr::Add(vec![ExprId(5), ExprId(9)]),
            Expr::Mul(vec![ExprId(6), ExprId(10)]),
            Expr::Add(vec![ExprId(0), ExprId(1), ExprId(4), ExprId(11)]),
        ];
        let root_expr = ExprId(12);
        let layer = DagLayer {
            sources,
            exprs,
            batching: BatchingOrder {
                roots: vec![cs::gkr_compiler::dag_ir::RootId(0)],
            },
            roots: vec![claim_only_root(root_expr, 0)],
            resolutions: BTreeMap::new(),
        };
        let fields = vec![
            FieldKind::Ext,
            FieldKind::Base,
            FieldKind::Base,
            FieldKind::Ext,
            FieldKind::Ext,
            FieldKind::Base,
            FieldKind::Ext,
            FieldKind::Ext,
            FieldKind::Ext,
            FieldKind::Base,
            FieldKind::Base,
            FieldKind::Ext,
            FieldKind::Ext,
        ];
        let fragments = [FragmentSpec {
            atoms: vec![root_expr],
            recipe: MergedRecipe {
                terms: vec![ProductRecipe::default()],
            },
        }];

        let out = elaborate_backward_fragments_driver(
            &layer,
            cs::gkr_compiler::dag_ir::RootId(0),
            &fields,
            &fragments,
            &[0],
            &[None],
            Some(0),
            16,
            false,
        );

        assert!(out.is_ok(), "legacy reduction should fit b16: {out:?}");
    }

    #[test]
    fn backward_trace_names_fused_product_consumers() {
        let layer = DagLayer {
            sources: (0..4).map(read_src).collect(),
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Source(SourceId(3)),
                Expr::Mul(vec![ExprId(2), ExprId(3)]),
                Expr::Add(vec![ExprId(1), ExprId(4)]),
                Expr::Mul(vec![ExprId(0), ExprId(5)]),
            ],
            batching: BatchingOrder {
                roots: vec![cs::gkr_compiler::dag_ir::RootId(0)],
            },
            roots: vec![claim_only_root(ExprId(6), 0)],
            resolutions: BTreeMap::new(),
        };
        let d = distill(&layer, BwdRegime::R0, &HashMap::new(), None);
        let (term, add) = d
            .fragments
            .fragments
            .iter()
            .enumerate()
            .flat_map(|(term, fragment)| fragment.atoms.iter().map(move |&atom| (term, atom)))
            .find(|(_, atom)| matches!(d.layer.exprs[atom.0 as usize], Expr::Add(_)))
            .expect("the opaque product keeps its nested add atom");
        let Expr::Add(add_children) = &d.layer.exprs[add.0 as usize] else {
            unreachable!()
        };
        let product = *add_children
            .iter()
            .find(|child| matches!(d.layer.exprs[child.0 as usize], Expr::Mul(_)))
            .expect("the nested add has a direct binary product");
        let Expr::Mul(product_children) = &d.layer.exprs[product.0 as usize] else {
            unreachable!()
        };

        let out = compile_backward_fragments_uncached(&d, None, 4, true).unwrap();
        let serves = out
            .trace
            .events
            .iter()
            .filter_map(|event| match event {
                BwdEvent::Serve { fp, .. } => Some(*fp),
                _ => None,
            })
            .collect::<Vec<_>>();

        assert!(serves.iter().any(|fp| {
            fp.term == term as u32
                && fp.kind == BwdServeKind::Operand
                && fp.value == add
                && fp.consumer.is_none()
        }));
        assert!(serves.iter().any(|fp| {
            fp.term == term as u32 && fp.value == product && fp.consumer == Some(add)
        }));
        for child in product_children {
            assert!(serves.iter().any(|fp| {
                fp.term == term as u32 && fp.value == *child && fp.consumer == Some(product)
            }));
        }
    }

    #[test]
    fn backward_trace_interleaves_physical_reads_with_matching_serves() {
        let d = backward_fixture();

        let out = compile_backward_fragments_uncached(&d, None, 4, true).unwrap();
        let events = &out.trace.events;
        let traffic_positions = events
            .iter()
            .enumerate()
            .filter_map(|(index, event)| {
                matches!(event, BwdEvent::TrafficRead { .. }).then_some(index)
            })
            .collect::<Vec<_>>();

        assert!(
            traffic_positions.len() > 1,
            "fixture must perform multiple reads"
        );
        assert!(
            traffic_positions[0]
                < events
                    .iter()
                    .rposition(|event| matches!(event, BwdEvent::Serve { .. }))
                    .expect("fixture must record serves"),
            "physical reads must not be appended after the complete serve stream"
        );
        for position in traffic_positions {
            let BwdEvent::TrafficRead { value, .. } = events[position] else {
                unreachable!()
            };
            assert!(
                matches!(
                    events.get(position.wrapping_sub(1)),
                    Some(BwdEvent::Serve { fp, .. }) if fp.value == value
                ),
                "traffic for {value:?} must immediately follow its matching serve"
            );
        }
    }
}
