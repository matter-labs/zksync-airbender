use std::collections::{BTreeMap, BTreeSet, VecDeque};

use cs::gkr_compiler::dag_ir::{DagLayer, Expr, ExprId, FieldKind, SourceKind, source_field};

use crate::bwd::construct::construct_fragment_order;
use crate::bwd::distill::{
    DistilledLayer, StableBwdConsumer, StableBwdExprKey, StableBwdSiteKey,
    stable_distilled_site_domain,
};
use crate::bwd::fragment::FactorKey;
use crate::bwd::plan::{BwdOccurrencePlan, PlanAction, PlanEntry, plan_entries_fnv};
use crate::bwd::source::{BwdSpecial, OriginLeaf};
use crate::bwd::trace::{
    BwdFingerprint, BwdServeKind, DirectTopCorrection, freeze_demand_with, plan_epoch_fragment,
};
use crate::eval_plan::backward::{
    BackwardEvaluationError, CompiledBackwardEvaluation, compile_backward_fragments_replayed,
    compile_backward_fragments_uncached, validate_and_resolve_backward,
};
use crate::eval_plan::budget_lanes_from_cells;

use super::{
    BackwardScore, BackwardSearchError, RoundProfile, SourceCost, SourceOriginKind, SourceRoundUse,
    StaticMaterialization, build_static_materialization, miss_cost, native_read_cost,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StableFragmentKey {
    pub atoms: Vec<StableBwdExprKey>,
    pub recipe: Vec<Vec<FactorKey>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StableLeafDemandKey {
    pub fragment: StableFragmentKey,
    pub site: StableBwdSiteKey,
    pub occurrence_in_fragment: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BackwardDemand {
    pub key: StableLeafDemandKey,
    pub fp: BwdFingerprint,
    pub expr: ExprId,
    pub source_desc: Option<u16>,
    pub instruction: usize,
    pub physical_ordinal: usize,
    pub width_lanes: u8,
    pub gap_capacity_lanes: u8,
    pub miss_cost: SourceCost,
    pub has_next: bool,
}

#[derive(Clone, Debug)]
pub struct BackwardSearchProblem {
    pub fragment_domain: Vec<StableFragmentKey>,
    pub leaf_domain: Vec<StableLeafDemandKey>,
    pub constructive_order: Vec<StableFragmentKey>,
    pub selected_order: Vec<StableFragmentKey>,
    pub(crate) selected_order_indices: Vec<usize>,
    pub demands: Vec<BackwardDemand>,
    pub all_domain_serves: Vec<BwdFingerprint>,
    pub budget_cells: usize,
    pub budget_lanes: usize,
    pub stream_reductions: bool,
    pub epoch: u64,
    pub materialization: StaticMaterialization,
    pub fixed_cost: SourceCost,
    pub(crate) round_profiles: Vec<RoundProfile>,
    pub(crate) source_round_uses: Vec<SourceRoundUse>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProblemClassification {
    Ready,
    Trivial {
        reason: &'static str,
    },
    Infeasible {
        false_floor: usize,
        true_floor: usize,
    },
}

struct ModeEvaluation {
    stream_reductions: bool,
    score: BackwardScore,
    compiled: Option<CompiledBackwardEvaluation>,
}

struct SelectedMode {
    stream_reductions: bool,
    compiled: Option<CompiledBackwardEvaluation>,
}

impl core::fmt::Debug for SelectedMode {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("SelectedMode")
            .field("stream_reductions", &self.stream_reductions)
            .finish_non_exhaustive()
    }
}

pub fn build_backward_search_problem(
    canonical: &DagLayer,
    d: &DistilledLayer,
    trace_len: usize,
    budget_cells: usize,
) -> Result<(ProblemClassification, Option<BackwardSearchProblem>), BackwardSearchError> {
    let budget_lanes =
        budget_lanes_from_cells(budget_cells).ok_or(BackwardSearchError::BackwardEvaluation(
            BackwardEvaluationError::BudgetCellsOutOfRange { budget_cells },
        ))?;
    let fragment_keys = stable_fragment_keys(d)?;
    let stable_sites = stable_distilled_site_domain(d);
    let constructive = construct_fragment_order(canonical, d, &stable_sites);
    validate_and_resolve_backward(d).map_err(BackwardSearchError::BackwardEvaluation)?;
    let (materialization, fixed_cost, source_costs, round_profiles, source_round_uses) =
        source_model(d, trace_len)?;

    let false_eval = mode_compile(d, &constructive, budget_cells, false, 0)?;
    let true_eval = mode_compile(d, &constructive, budget_cells, true, 1)?;
    let selected = match select_reduction_mode(false_eval, true_eval) {
        Ok(selected) => selected,
        Err(classification) => return Ok((classification, None)),
    };
    let compiled = selected
        .compiled
        .expect("compiled modes always carry their evaluation");
    let problem = build_problem_from_compiled(
        d,
        &fragment_keys,
        &constructive,
        budget_cells,
        budget_lanes,
        selected.stream_reductions,
        materialization,
        fixed_cost,
        source_costs,
        round_profiles,
        source_round_uses,
        compiled,
    )?;
    let classification = classify_problem(&problem);
    Ok((classification, Some(problem)))
}

pub(crate) fn build_problem_for_order(
    _canonical: &DagLayer,
    d: &DistilledLayer,
    order: &[usize],
    trace_len: usize,
    budget_cells: usize,
    stream_reductions: bool,
) -> Result<BackwardSearchProblem, BackwardSearchError> {
    let budget_lanes =
        budget_lanes_from_cells(budget_cells).ok_or(BackwardSearchError::BackwardEvaluation(
            BackwardEvaluationError::BudgetCellsOutOfRange { budget_cells },
        ))?;
    let fragment_keys = stable_fragment_keys(d)?;
    validate_and_resolve_backward(d).map_err(BackwardSearchError::BackwardEvaluation)?;
    let (materialization, fixed_cost, source_costs, round_profiles, source_round_uses) =
        source_model(d, trace_len)?;
    let compiled =
        compile_backward_fragments_uncached(d, Some(order), budget_cells, stream_reductions)
            .map_err(BackwardSearchError::BackwardEvaluation)?;
    build_problem_from_compiled(
        d,
        &fragment_keys,
        order,
        budget_cells,
        budget_lanes,
        stream_reductions,
        materialization,
        fixed_cost,
        source_costs,
        round_profiles,
        source_round_uses,
        compiled,
    )
}

pub(crate) fn decode_order_indices(
    problem: &BackwardSearchProblem,
    order: &[usize],
) -> Result<Vec<StableFragmentKey>, BackwardSearchError> {
    if order.len() != problem.fragment_domain.len() {
        return Err(BackwardSearchError::InvalidFragmentPermutation);
    }
    let mut seen = vec![false; order.len()];
    let mut decoded = Vec::with_capacity(order.len());
    for &index in order {
        let Some(fragment) = problem.fragment_domain.get(index) else {
            return Err(BackwardSearchError::InvalidFragmentPermutation);
        };
        if core::mem::replace(&mut seen[index], true) {
            return Err(BackwardSearchError::InvalidFragmentPermutation);
        }
        decoded.push(fragment.clone());
    }
    Ok(decoded)
}

#[allow(clippy::too_many_arguments)]
fn build_problem_from_compiled(
    d: &DistilledLayer,
    fragment_keys: &[StableFragmentKey],
    order: &[usize],
    budget_cells: usize,
    budget_lanes: usize,
    stream_reductions: bool,
    materialization: StaticMaterialization,
    fixed_cost: SourceCost,
    source_costs: BTreeMap<u16, SourceCost>,
    round_profiles: Vec<RoundProfile>,
    source_round_uses: Vec<SourceRoundUse>,
    compiled: CompiledBackwardEvaluation,
) -> Result<BackwardSearchProblem, BackwardSearchError> {
    let frozen = freeze_demand_with(
        d,
        &compiled.trace,
        &compiled.compiled.program,
        &compiled.compiled.specials,
        &compiled.compiled.backings,
        DirectTopCorrection::None,
    );
    let frozen = frozen.ok_or(BackwardSearchError::PagingCertificateMismatch {
        observable: "frozen physical traffic",
    })?;
    let plan = bypass_plan(
        &frozen.domain_serves,
        compiled.trace.epoch,
        stream_reductions,
    );
    let replayed = compile_backward_fragments_replayed(d, &plan, Some(order), budget_cells)
        .map_err(BackwardSearchError::BackwardEvaluation)?;
    let frozen = freeze_demand_with(
        d,
        &replayed.trace,
        &replayed.compiled.program,
        &replayed.compiled.specials,
        &replayed.compiled.backings,
        DirectTopCorrection::None,
    );
    let frozen = frozen.ok_or(BackwardSearchError::PagingCertificateMismatch {
        observable: "frozen replay physical traffic",
    })?;
    let fields =
        validate_and_resolve_backward(d).map_err(BackwardSearchError::BackwardEvaluation)?;
    let stable_sites = stable_distilled_site_domain(d);
    let mut accesses: BTreeMap<ExprId, VecDeque<(usize, usize)>> = frozen
        .leaf_accesses
        .into_iter()
        .map(|(expr, positions)| (expr, positions.into()))
        .collect();
    let mut site_ordinals = BTreeMap::new();
    let mut occurrences = BTreeMap::<(StableFragmentKey, StableBwdSiteKey), u32>::new();
    let mut positioned = Vec::new();

    for (fp, _) in &frozen.domain_serves {
        let Some(source_desc) = real_read_desc(d, fp.value) else {
            continue;
        };
        let (fragment_index, fragment) = scheduled_fragment_key(fragment_keys, order, fp)?;
        let site = stable_site_for_fingerprint(
            d,
            &stable_sites,
            fragment_index,
            &fragment,
            fp,
            &mut site_ordinals,
        )?;
        let occurrence = occurrences.entry((fragment.clone(), site)).or_default();
        let key = StableLeafDemandKey {
            fragment,
            site,
            occurrence_in_fragment: *occurrence,
        };
        *occurrence = occurrence
            .checked_add(1)
            .ok_or(BackwardSearchError::CostOverflow)?;
        let (instruction, physical_ordinal) = accesses
            .get_mut(&fp.value)
            .and_then(VecDeque::pop_front)
            .ok_or(BackwardSearchError::MissingLeafInstant { expr: fp.value })?;
        let width_lanes = match fields[fp.value.0 as usize] {
            FieldKind::Base => 1,
            FieldKind::Ext => 4,
        };
        let miss_cost = match source_desc {
            Some(desc) => source_costs
                .get(&desc)
                .copied()
                .ok_or(BackwardSearchError::MissingSourceRound { desc, round: 0 })?,
            None => native_read_cost(fields[fp.value.0 as usize], &round_profiles)?,
        };
        positioned.push((
            instruction,
            BackwardDemand {
                key,
                fp: *fp,
                expr: fp.value,
                source_desc,
                instruction,
                physical_ordinal,
                width_lanes,
                gap_capacity_lanes: 0,
                miss_cost,
                has_next: false,
            },
        ));
    }
    positioned.sort_by(|(left_pos, left), (right_pos, right)| {
        left_pos
            .cmp(right_pos)
            .then_with(|| left.physical_ordinal.cmp(&right.physical_ordinal))
            .then_with(|| left.key.cmp(&right.key))
    });
    let positions: Vec<usize> = positioned.iter().map(|(position, _)| *position).collect();
    let capacities = gap_capacities(&positions, &frozen.free);
    let mut later = BTreeSet::new();
    for ((_, demand), capacity) in positioned
        .iter_mut()
        .rev()
        .zip(capacities.into_iter().rev())
    {
        demand.gap_capacity_lanes = capacity;
        demand.has_next = later.contains(&demand.expr);
        later.insert(demand.expr);
    }
    let demands: Vec<_> = positioned.into_iter().map(|(_, demand)| demand).collect();
    let mut fragment_domain = fragment_keys.to_vec();
    fragment_domain.sort();
    let leaf_domain = demands
        .iter()
        .map(|demand| demand.key.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let selected_order: Vec<StableFragmentKey> = order
        .iter()
        .map(|&index| fragment_keys[index].clone())
        .collect();
    Ok(BackwardSearchProblem {
        fragment_domain,
        leaf_domain,
        constructive_order: selected_order.clone(),
        selected_order,
        selected_order_indices: order.to_vec(),
        demands,
        all_domain_serves: frozen.domain_serves.into_iter().map(|(fp, _)| fp).collect(),
        budget_cells,
        budget_lanes,
        stream_reductions,
        epoch: plan_epoch_fragment(d, budget_lanes, stream_reductions),
        materialization,
        fixed_cost,
        round_profiles,
        source_round_uses,
    })
}

fn mode_compile(
    d: &DistilledLayer,
    order: &[usize],
    budget_cells: usize,
    stream_reductions: bool,
    ordinal: usize,
) -> Result<Result<ModeEvaluation, usize>, BackwardSearchError> {
    match compile_backward_fragments_uncached(d, Some(order), budget_cells, stream_reductions) {
        Ok(compiled) => Ok(Ok(ModeEvaluation {
            stream_reductions,
            score: score_compiled(&compiled, ordinal),
            compiled: Some(compiled),
        })),
        Err(error) => match floor(&error) {
            Some(floor) => Ok(Err(floor)),
            None => Err(BackwardSearchError::BackwardEvaluation(error)),
        },
    }
}

fn select_reduction_mode(
    false_mode: Result<ModeEvaluation, usize>,
    true_mode: Result<ModeEvaluation, usize>,
) -> Result<SelectedMode, ProblemClassification> {
    match (false_mode, true_mode) {
        (Ok(false_mode), Ok(true_mode)) => {
            if false_mode.score <= true_mode.score {
                Ok(SelectedMode {
                    stream_reductions: false_mode.stream_reductions,
                    compiled: false_mode.compiled,
                })
            } else {
                Ok(SelectedMode {
                    stream_reductions: true_mode.stream_reductions,
                    compiled: true_mode.compiled,
                })
            }
        }
        (Ok(mode), Err(_)) | (Err(_), Ok(mode)) => Ok(SelectedMode {
            stream_reductions: mode.stream_reductions,
            compiled: mode.compiled,
        }),
        (Err(false_floor), Err(true_floor)) => Err(ProblemClassification::Infeasible {
            false_floor,
            true_floor,
        }),
    }
}

fn stable_fragment_keys(d: &DistilledLayer) -> Result<Vec<StableFragmentKey>, BackwardSearchError> {
    let mut seen = BTreeSet::new();
    d.fragments
        .stable_view(d)
        .into_iter()
        .map(|(atoms, recipe)| StableFragmentKey { atoms, recipe })
        .map(|key| {
            if !seen.insert(key.clone()) {
                return Err(BackwardSearchError::DuplicateStableFragment);
            }
            Ok(key)
        })
        .collect()
}

fn scheduled_fragment_key(
    fragment_keys: &[StableFragmentKey],
    order: &[usize],
    fp: &BwdFingerprint,
) -> Result<(usize, StableFragmentKey), BackwardSearchError> {
    let scheduled = order
        .get(fp.term as usize)
        .ok_or(BackwardSearchError::MissingStableValue)?;
    fragment_keys
        .get(*scheduled)
        .cloned()
        .map(|key| (*scheduled, key))
        .ok_or(BackwardSearchError::MissingStableValue)
}

fn stable_site_for_fingerprint(
    d: &DistilledLayer,
    stable_sites: &BTreeMap<StableBwdSiteKey, cs::gkr_compiler::dag_ir::SiteKey>,
    fragment_index: usize,
    fragment: &StableFragmentKey,
    fp: &BwdFingerprint,
    ordinals: &mut BTreeMap<(StableFragmentKey, StableBwdExprKey, StableBwdExprKey), usize>,
) -> Result<StableBwdSiteKey, BackwardSearchError> {
    let value = d
        .stable_key(fp.value)
        .ok_or(BackwardSearchError::MissingStableValue)?;
    let candidates: Vec<_> = stable_sites
        .keys()
        .filter(|site| {
            if site.value != value {
                return false;
            }
            match fp.consumer {
                Some(consumer) => matches!(
                    site.consumer,
                    StableBwdConsumer::Expr { expr, .. } if d.stable_key(consumer) == Some(expr)
                ),
                None if fp.kind == BwdServeKind::RootOutput => {
                    site.consumer == StableBwdConsumer::RootOutput
                }
                None => matches!(
                    site.consumer,
                    StableBwdConsumer::Expr { expr, .. }
                        if fragment_contains_consumer(d, fragment_index, expr)
                ),
            }
        })
        .copied()
        .collect();
    let consumer = match candidates.first().map(|site| site.consumer) {
        Some(StableBwdConsumer::Expr { expr, .. }) => expr,
        Some(StableBwdConsumer::RootOutput) => StableBwdExprKey::CombinedSpine,
        None => return Err(BackwardSearchError::MissingStableSite),
    };
    let ordinal = ordinals
        .entry((fragment.clone(), consumer, value))
        .or_default();
    let site = candidates
        .get(*ordinal)
        .copied()
        .ok_or(BackwardSearchError::MissingStableSite)?;
    *ordinal = ordinal
        .checked_add(1)
        .ok_or(BackwardSearchError::CostOverflow)?;
    Ok(site)
}

fn fragment_contains_consumer(
    d: &DistilledLayer,
    fragment_index: usize,
    target: StableBwdExprKey,
) -> bool {
    let Some(fragment) = d.fragments.fragments.get(fragment_index) else {
        return false;
    };
    let fragment_atoms: BTreeSet<_> = fragment
        .atoms
        .iter()
        .filter_map(|&atom| d.stable_key(atom))
        .collect();
    let Some(consumer) = d.layer.exprs.iter().enumerate().find_map(|(index, _)| {
        (d.stable_key(ExprId(index as u32)) == Some(target)).then_some(ExprId(index as u32))
    }) else {
        return false;
    };
    let mut seen = BTreeSet::new();
    let mut stable_descendants = BTreeSet::new();
    let mut stack = vec![consumer];
    while let Some(expr) = stack.pop() {
        if !seen.insert(expr) {
            continue;
        }
        if let Some(key) = d.stable_key(expr) {
            stable_descendants.insert(key);
        }
        if let Expr::Add(children) | Expr::Mul(children) = &d.layer.exprs[expr.0 as usize] {
            stack.extend(children);
        }
    }
    fragment_atoms.is_subset(&stable_descendants)
}

fn real_read_desc(d: &DistilledLayer, expr: ExprId) -> Option<Option<u16>> {
    if let Some(&desc) = d.leaf_descs.get(&expr) {
        return match d.specials.get(desc) {
            Some(BwdSpecial::FoldSource {
                origin: OriginLeaf::Read(_),
            }) => Some(Some(desc)),
            Some(BwdSpecial::FoldSource {
                origin: OriginLeaf::VirtualSetup { .. },
            }) => None,
            _ => None,
        };
    }
    let Expr::Source(source) = d.layer.exprs[expr.0 as usize] else {
        return None;
    };
    matches!(
        d.layer.sources[source.0 as usize].kind,
        SourceKind::Read { .. }
    )
    .then_some(None)
}

fn gap_capacities(demand_positions: &[usize], free: &[usize]) -> Vec<u8> {
    demand_positions
        .iter()
        .enumerate()
        .map(|(index, &position)| {
            let range = match demand_positions.get(index + 1) {
                Some(&next) => position.saturating_add(1)..next.saturating_add(1),
                None => position.saturating_add(1)..free.len(),
            };
            range
                .filter_map(|position| free.get(position).copied())
                .min()
                .unwrap_or(0)
                .try_into()
                .unwrap_or(u8::MAX)
        })
        .collect()
}

fn bypass_plan(
    serves: &[(BwdFingerprint, crate::bwd::trace::BwdServedFrom)],
    epoch: u64,
    stream_reductions: bool,
) -> BwdOccurrencePlan {
    let entries: Vec<_> = serves
        .iter()
        .map(|(fp, _)| PlanEntry {
            fp: *fp,
            action: PlanAction::Bypass,
        })
        .collect();
    BwdOccurrencePlan {
        epoch,
        entries_fnv: plan_entries_fnv(&entries),
        stream_reductions,
        entries,
    }
}

fn source_model(
    d: &DistilledLayer,
    trace_len: usize,
) -> Result<
    (
        StaticMaterialization,
        SourceCost,
        BTreeMap<u16, SourceCost>,
        Vec<RoundProfile>,
        Vec<SourceRoundUse>,
    ),
    BackwardSearchError,
> {
    let rounds = round_profiles(trace_len)?;
    let uses = source_round_uses(d, &rounds)?;
    let materialization = build_static_materialization(&uses, &rounds)?;
    let mut source_costs = BTreeMap::new();
    for &desc in d.leaf_descs.values() {
        if source_costs.contains_key(&desc) {
            continue;
        }
        let one_source: Vec<_> = uses
            .iter()
            .copied()
            .filter(|use_| use_.desc == desc)
            .collect();
        if !one_source.is_empty() {
            let mut cost = miss_cost(&one_source, &rounds, &materialization)?;
            cost.materialization_write_bytes = cost
                .materialization_write_bytes
                .checked_sub(materialization.fixed_writes.materialization_write_bytes)
                .ok_or(BackwardSearchError::CostOverflow)?;
            source_costs.insert(desc, cost);
        }
    }
    Ok((
        materialization.clone(),
        materialization.fixed_writes,
        source_costs,
        rounds,
        uses,
    ))
}

fn round_profiles(trace_len: usize) -> Result<Vec<RoundProfile>, BackwardSearchError> {
    if trace_len == 0 {
        return Err(BackwardSearchError::CostOverflow);
    }
    let mut rows = trace_len as u64;
    let mut round = 0u8;
    let mut profiles = Vec::new();
    loop {
        profiles.push(RoundProfile { round, rows });
        if rows == 1 {
            break;
        }
        rows /= 2;
        round = round
            .checked_add(1)
            .ok_or(BackwardSearchError::CostOverflow)?;
    }
    Ok(profiles)
}

fn source_round_uses(
    d: &DistilledLayer,
    rounds: &[RoundProfile],
) -> Result<Vec<SourceRoundUse>, BackwardSearchError> {
    let mut uses = Vec::new();
    for (&expr, &desc) in &d.leaf_descs {
        let Some(BwdSpecial::FoldSource {
            origin: OriginLeaf::Read(place),
        }) = d.specials.get(desc)
        else {
            continue;
        };
        let field = source_field(&SourceKind::Read {
            place: place.clone(),
        })
        .unwrap_or_else(|place| {
            *d.cross_fields
                .get(&place)
                .expect("validated backward field")
        });
        let structural_occurrences = structural_source_occurrences(d, expr)
            .try_into()
            .map_err(|_| BackwardSearchError::CostOverflow)?;
        for profile in rounds {
            uses.push(SourceRoundUse {
                desc,
                round: profile.round,
                structural_occurrences,
                origin: SourceOriginKind::Read { field },
            });
        }
    }
    Ok(uses)
}

fn structural_source_occurrences(d: &DistilledLayer, source: ExprId) -> usize {
    fn count(d: &DistilledLayer, expr: ExprId, source: ExprId) -> usize {
        if expr == source {
            return 1;
        }
        match &d.layer.exprs[expr.0 as usize] {
            Expr::Source(_) => 0,
            Expr::Add(children) | Expr::Mul(children) => {
                children.iter().map(|&child| count(d, child, source)).sum()
            }
        }
    }

    d.fragments
        .fragments
        .iter()
        .flat_map(|fragment| fragment.atoms.iter().copied())
        .map(|atom| count(d, atom, source))
        .sum()
}

fn score_compiled(compiled: &CompiledBackwardEvaluation, ordinal: usize) -> BackwardScore {
    BackwardScore {
        infeasible: false,
        whole_pass_dram_bytes: (compiled.compiled.stats_ext.global
            + compiled.compiled.stats_ext.fold_traffic) as u128
            * 4,
        primitive_source_ops: 0,
        instructions: compiled.compiled.program.instrs.len(),
        encoded_lanes: compiled.encoded.len(),
        arithmetic_ops: compiled.compiled.stats.program_lanes,
        ordinal,
    }
}

fn floor(error: &BackwardEvaluationError) -> Option<usize> {
    match error {
        BackwardEvaluationError::Plan(crate::eval_plan::PlanError::BudgetExceeded {
            required_transient_lanes,
            ..
        }) => Some(*required_transient_lanes),
        BackwardEvaluationError::Concrete(
            crate::eval_plan::ConcreteBindError::PlacementFailed {
                peak_live_lanes, ..
            },
        ) => Some(*peak_live_lanes),
        _ => None,
    }
}

fn classify_problem(problem: &BackwardSearchProblem) -> ProblemClassification {
    if problem.fragment_domain.len() <= 1 {
        ProblemClassification::Trivial {
            reason: "one fragment",
        }
    } else if problem.leaf_domain.is_empty() {
        ProblemClassification::Trivial {
            reason: "no reusable real leaf",
        }
    } else if problem
        .demands
        .iter()
        .filter(|demand| demand.has_next)
        .count()
        <= 1
    {
        ProblemClassification::Trivial {
            reason: "single decodable action",
        }
    } else {
        ProblemClassification::Ready
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet, HashMap};

    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, BwdRegime, ClaimInfo, ReadPlace, Root, RootGroup, RootId, RootOrigin,
        RootSlot, SourceId, SourceInfo, VirtualSetupKind,
    };

    use crate::bwd::distill::distill;

    use super::*;

    #[test]
    fn stable_fragment_and_leaf_demand_keys_survive_fragment_permutation() {
        let (canonical, d) = synthetic_backward_problem_layer();
        let (_, built) = build_backward_search_problem(&canonical, &d, 8, 4).unwrap();
        assert!(built.is_some());
        let a = build_problem_for_order(&canonical, &d, &[0, 1], 8, 4, false).unwrap();
        let b = build_problem_for_order(&canonical, &d, &[1, 0], 8, 4, false).unwrap();
        assert_eq!(a.fragment_domain, b.fragment_domain);
        assert_eq!(
            a.demands
                .iter()
                .map(|d| d.key.clone())
                .collect::<BTreeSet<_>>(),
            b.demands
                .iter()
                .map(|d| d.key.clone())
                .collect::<BTreeSet<_>>()
        );
    }

    #[test]
    fn only_real_read_leaves_enter_the_paging_domain() {
        let canonical = synthetic_read_filter_problem_layer();
        let d = distill(&canonical, BwdRegime::Ext, &HashMap::new(), None);
        let stable_values = stable_distilled_site_domain(&d)
            .into_keys()
            .map(|site| site.value)
            .collect::<BTreeSet<_>>();
        assert!(stable_values.contains(&StableBwdExprKey::Canonical(ExprId(0))));
        assert!(stable_values.contains(&StableBwdExprKey::Canonical(ExprId(3))));
        assert!(stable_values.contains(&StableBwdExprKey::Canonical(ExprId(10))));
        assert!(!stable_values.contains(&StableBwdExprKey::Canonical(ExprId(4))));
        assert!(!stable_values.contains(&StableBwdExprKey::Canonical(ExprId(5))));

        let (_, problem) = build_backward_search_problem(&canonical, &d, 8, 4).unwrap();
        let problem = problem.expect("the real fixture remains reportable even if trivial");
        assert!(!problem.demands.is_empty());
        assert!(
            problem
                .demands
                .iter()
                .all(|demand| demand.source_desc.is_some())
        );
        let read_values = BTreeSet::from([
            StableBwdExprKey::Canonical(ExprId(0)),
            StableBwdExprKey::Canonical(ExprId(1)),
            StableBwdExprKey::Canonical(ExprId(2)),
        ]);
        assert!(problem.demands.iter().all(|demand| {
            read_values.contains(&demand.key.site.value)
                && matches!(real_read_desc(&d, demand.expr), Some(Some(_)))
        }));
        assert_eq!(
            problem.leaf_domain,
            problem
                .demands
                .iter()
                .map(|demand| demand.key.clone())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn gap_capacity_is_the_minimum_free_lane_envelope_between_demands() {
        let demand_positions = [1usize, 5, 8];
        let free = [8usize, 7, 6, 5, 4, 8, 8, 3, 8];
        assert_eq!(gap_capacities(&demand_positions, &free), vec![4, 3, 0]);
    }

    #[test]
    fn final_gap_starts_strictly_after_the_demand_instruction() {
        let demand_positions = [1usize];
        let free = [8usize, 1, 7, 6];
        assert_eq!(gap_capacities(&demand_positions, &free), vec![6]);
    }

    #[test]
    fn demand_at_eof_has_zero_length_gap_capacity() {
        let demand_positions = [2usize];
        let free = [8usize, 7, 1];
        assert_eq!(gap_capacities(&demand_positions, &free), vec![0]);
    }

    #[test]
    fn reduction_mode_uses_fitness_and_false_wins_an_exact_tie() {
        let false_eval = synthetic_mode_eval(false, score(100, 20, 10));
        let true_eval = synthetic_mode_eval(true, score(100, 20, 10));
        assert!(
            !select_reduction_mode(Ok(false_eval), Ok(true_eval))
                .unwrap()
                .stream_reductions
        );
    }

    #[test]
    fn both_infeasible_modes_classify_before_search() {
        assert_eq!(
            select_reduction_mode(Err(floor(12)), Err(floor(16))).unwrap_err(),
            ProblemClassification::Infeasible {
                false_floor: 12,
                true_floor: 16
            }
        );
    }

    fn synthetic_backward_problem_layer() -> (DagLayer, DistilledLayer) {
        let layer = DagLayer {
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
        };
        let d = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
        (layer, d)
    }

    fn synthetic_read_filter_problem_layer() -> DagLayer {
        DagLayer {
            sources: vec![
                read_source(0),
                read_source(1),
                read_source(2),
                SourceInfo {
                    kind: SourceKind::VirtualSetup {
                        kind: VirtualSetupKind::RangeCheck16Bits,
                    },
                },
                SourceInfo {
                    kind: SourceKind::Constant { value: 7 },
                },
                SourceInfo {
                    kind: SourceKind::Constant { value: 11 },
                },
            ],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Source(SourceId(3)),
                Expr::Source(SourceId(4)),
                Expr::Source(SourceId(5)),
                Expr::Mul(vec![ExprId(0), ExprId(1)]),
                Expr::Mul(vec![ExprId(0), ExprId(2)]),
                Expr::Mul(vec![ExprId(3), ExprId(4)]),
                Expr::Mul(vec![ExprId(3), ExprId(5)]),
                Expr::Add(vec![ExprId(3), ExprId(4)]),
                Expr::Mul(vec![ExprId(1), ExprId(10)]),
                Expr::Mul(vec![ExprId(2), ExprId(10)]),
            ],
            batching: BatchingOrder {
                roots: (0..6).map(RootId).collect(),
            },
            roots: [6u32, 7, 8, 9, 11, 12]
                .into_iter()
                .enumerate()
                .map(|(relation_index, expr)| claim_root(ExprId(expr), relation_index))
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

    fn score(dram: u128, source_ops: u128, instructions: usize) -> BackwardScore {
        BackwardScore {
            infeasible: false,
            whole_pass_dram_bytes: dram,
            primitive_source_ops: source_ops,
            instructions,
            encoded_lanes: 0,
            arithmetic_ops: 0,
            ordinal: 0,
        }
    }

    fn synthetic_mode_eval(stream_reductions: bool, score: BackwardScore) -> ModeEvaluation {
        ModeEvaluation {
            stream_reductions,
            score,
            compiled: None,
        }
    }

    fn floor(value: usize) -> usize {
        value
    }
}
