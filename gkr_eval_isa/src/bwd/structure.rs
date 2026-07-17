//! Structure-aware seed model for backward schedule search.
//!
//! The exact compiler remains the scorer. This module only builds deterministic
//! warm starts from information random genomes otherwise have to rediscover:
//! which canonical relation units share a stable value, the uncached DRAM cost
//! of that value's cone, its residency width, and its lifetime under the guided
//! order.

use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};

use cs::gkr_compiler::dag_ir::{
    bwd_cache_fences, join, source_field, DagLayer, Expr, ExprId, FieldKind, SiteKey, SourceKind,
};

use super::distill::{DistilledLayer, StableBwdExprKey, StableBwdSiteKey};
use super::source::BwdSpecial;

/// Deterministic warm-start data, index-aligned with the canonical stable site
/// domain supplied to the search genome.
pub(super) struct ReuseStructure {
    pub order: Vec<usize>,
    pub cache_priorities: Vec<f64>,
    pub weighted_edges: Vec<ReuseEdge>,
    /// Value↔unit incidence for every canonical value reached by at least one
    /// relation unit: `(width lanes, uncached DRAM cost, consuming unit
    /// indices, ascending)`. Populated by the SAME `attach_canonical_unit_uses`
    /// walk that fills `ValueReuse.units` above — pure exposure (no new
    /// analysis), added for Task 7's constructive order
    /// (`construct::construct_unit_order`'s projected greedy needs the raw
    /// incidence; `weighted_edges` alone only carries pairwise unit sums).
    pub value_units: Vec<(usize, usize, Vec<usize>)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ReuseEdge {
    pub left: usize,
    pub right: usize,
    pub weight: usize,
}

struct ValueReuse {
    site_indices: Vec<usize>,
    representative: ExprId,
    units: Vec<usize>,
    dram_cells: usize,
    width: usize,
}

impl ReuseStructure {
    pub fn build(
        canonical: &DagLayer,
        distilled: &DistilledLayer,
        stable_domain: &BTreeMap<StableBwdSiteKey, SiteKey>,
    ) -> Self {
        let mut values: BTreeMap<StableBwdExprKey, ValueReuse> = BTreeMap::new();
        for (site_index, (stable, concrete)) in stable_domain.iter().enumerate() {
            values
                .entry(stable.value)
                .and_modify(|value| value.site_indices.push(site_index))
                .or_insert_with(|| ValueReuse {
                    site_indices: vec![site_index],
                    representative: concrete.value,
                    units: Vec::new(),
                    dram_cells: 0,
                    width: 1,
                });
        }

        attach_canonical_unit_uses(canonical, distilled, &mut values);

        let mut field_memo = vec![None; distilled.layer.exprs.len()];
        let mut traffic_memo = vec![None; distilled.layer.exprs.len()];
        for value in values.values_mut() {
            value.width = expr_width(distilled, value.representative, &mut field_memo);
            value.dram_cells = cone_dram_cells(
                distilled,
                value.representative,
                &mut traffic_memo,
                &mut field_memo,
            );
        }

        let edges = reuse_edges(&values);
        let weighted_edges = edges
            .iter()
            .map(|(&(left, right), &weight)| ReuseEdge {
                left,
                right,
                weight,
            })
            .collect();
        let order = guided_order(distilled.unit_order.len(), &edges);
        let cache_priorities = interval_priorities(stable_domain.len(), &values, &order);
        let value_units = values
            .values()
            .filter(|value| !value.units.is_empty())
            .map(|value| (value.width, value.dram_cells, value.units.clone()))
            .collect();
        Self {
            order,
            cache_priorities,
            weighted_edges,
            value_units,
        }
    }

    /// CS-M5a Task 7: fragment-granular sibling of [`build`](Self::build). Every
    /// downstream stage is identical — only the incidence is keyed by the
    /// distilled `FragmentTable`'s FRAGMENT index instead of the canonical
    /// relation-unit index, so `weighted_edges` / `value_units` / `order` all
    /// range over `0..d.fragments.fragments.len()`. `construct::construct_fragment_order`
    /// then drives the SAME index-generic `match_blocks`/`chain_blocks`/
    /// `projected_greedy` stages over this structure.
    ///
    /// `canonical` is accepted for signature parity with [`build`](Self::build)
    /// (so the two are drop-in siblings for the Task-8/10 caller), but the
    /// fragment incidence is a pure function of the DISTILLED layer: a fragment's
    /// identity and its atoms both live only in `d`, unlike the term path whose
    /// unit grouping had to be recovered from the canonical layer.
    pub fn build_fragments(
        canonical: &DagLayer,
        d: &DistilledLayer,
        stable_domain: &BTreeMap<StableBwdSiteKey, SiteKey>,
    ) -> Self {
        let _ = canonical; // incidence is distilled-only; see the doc above.

        let mut values: BTreeMap<StableBwdExprKey, ValueReuse> = BTreeMap::new();
        for (site_index, (stable, concrete)) in stable_domain.iter().enumerate() {
            values
                .entry(stable.value)
                .and_modify(|value| value.site_indices.push(site_index))
                .or_insert_with(|| ValueReuse {
                    site_indices: vec![site_index],
                    representative: concrete.value,
                    units: Vec::new(),
                    dram_cells: 0,
                    width: 1,
                });
        }

        attach_fragment_uses(d, &mut values);

        let mut field_memo = vec![None; d.layer.exprs.len()];
        let mut traffic_memo = vec![None; d.layer.exprs.len()];
        for value in values.values_mut() {
            value.width = expr_width(d, value.representative, &mut field_memo);
            value.dram_cells =
                cone_dram_cells(d, value.representative, &mut traffic_memo, &mut field_memo);
        }

        let edges = reuse_edges(&values);
        let weighted_edges = edges
            .iter()
            .map(|(&(left, right), &weight)| ReuseEdge {
                left,
                right,
                weight,
            })
            .collect();
        let order = guided_order(d.fragments.fragments.len(), &edges);
        let cache_priorities = interval_priorities(stable_domain.len(), &values, &order);
        let value_units = values
            .values()
            .filter(|value| !value.units.is_empty())
            .map(|value| (value.width, value.dram_cells, value.units.clone()))
            .collect();
        Self {
            order,
            cache_priorities,
            weighted_edges,
            value_units,
        }
    }
}

/// Recover exact canonical unit membership for stable canonical values. This is
/// deliberately computed on the canonical layer rather than inferred from the
/// distilled one-root DAG, where the original root identity has been erased.
fn attach_canonical_unit_uses(
    canonical: &DagLayer,
    distilled: &DistilledLayer,
    values: &mut BTreeMap<StableBwdExprKey, ValueReuse>,
) {
    let targets: BTreeSet<ExprId> = values
        .keys()
        .filter_map(|key| match key {
            StableBwdExprKey::Canonical(expr) => Some(*expr),
            StableBwdExprKey::BatchingTerm(_) | StableBwdExprKey::CombinedSpine => None,
        })
        .collect();
    let fences = bwd_cache_fences(canonical);

    for (unit_index, roots) in distilled.unit_order.iter().enumerate() {
        let mut reached = BTreeSet::new();
        let mut seen = HashSet::new();
        let mut work: Vec<ExprId> = roots
            .iter()
            .map(|root| canonical.roots[root.0 as usize].expr)
            .collect();
        while let Some(expr) = work.pop() {
            if !seen.insert(expr) {
                continue;
            }
            if targets.contains(&expr) {
                reached.insert(expr);
            }
            if fences.contains_key(&expr) {
                continue;
            }
            match &canonical.exprs[expr.0 as usize] {
                Expr::Add(children) | Expr::Mul(children) => {
                    work.extend(children.iter().copied());
                }
                Expr::Source(source) => {
                    if let SourceKind::LookupValue { query, .. } =
                        canonical.sources[source.0 as usize].kind
                    {
                        work.push(query);
                    }
                }
            }
        }
        for expr in reached {
            values
                .get_mut(&StableBwdExprKey::Canonical(expr))
                .expect("target canonical value must have a reuse record")
                .units
                .push(unit_index);
        }
    }
}

/// CS-M5a Task 7: fragment-granular value incidence, the sibling of
/// [`attach_canonical_unit_uses`]. For each distilled fragment, DFS its atom
/// cones over the DISTILLED layer and record the fragment index against every
/// stable value it reaches that is already in the reuse-value domain.
///
/// Two deliberate differences from the term-path walk:
///  * It walks `d.layer` (the distilled cones the fragment atoms name), not the
///    canonical layer — a fragment's identity lives only in `d.fragments`, so
///    there is no canonical unit grouping to recover. Distilled `ExprId`s are
///    mapped to their order-independent `StableBwdExprKey` via `d.stable_key`,
///    which is exactly the domain the `values` map is keyed by.
///  * It counts the ATOM NODE ITSELF as a use (the walk seeds from the atoms and
///    checks them on pop). Fragment top atoms are servable values post-Task-5,
///    and a value shared as one fragment's top atom and inside another
///    fragment's cone is precisely the reuse the order must co-locate — so, unlike
///    the term walk (whose batching-term tops are never in the value domain and
///    thus fall out on their own), the tops here must NOT be skipped.
///
/// Fences need no explicit handling: same-layer cache roots were rebuilt into
/// `Read(CacheOutput)` leaves during distillation (and `LookupValue` was erased
/// to its query), so every distilled `Source` is a childless leaf and the DFS
/// stops there naturally — mirroring the canonical walk's explicit fence cut.
fn attach_fragment_uses(d: &DistilledLayer, values: &mut BTreeMap<StableBwdExprKey, ValueReuse>) {
    for (frag_index, fragment) in d.fragments.fragments.iter().enumerate() {
        let mut reached: BTreeSet<StableBwdExprKey> = BTreeSet::new();
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut work: Vec<ExprId> = fragment.atoms.clone();
        while let Some(expr) = work.pop() {
            if !seen.insert(expr) {
                continue;
            }
            if let Some(key) = d.stable_key(expr) {
                if values.contains_key(&key) {
                    reached.insert(key);
                }
            }
            match &d.layer.exprs[expr.0 as usize] {
                Expr::Add(children) | Expr::Mul(children) => {
                    work.extend(children.iter().copied());
                }
                // Distilled sources are leaves: Read/Constant/Challenge/VirtualSetup
                // have no operands, fenced cache roots are already `Read` leaves, and
                // `LookupValue` was erased to its query — nothing to descend.
                Expr::Source(_) => {}
            }
        }
        for key in reached {
            values
                .get_mut(&key)
                .expect("reached value must have a reuse record (checked in-domain above)")
                .units
                .push(frag_index);
        }
    }
}

/// Full uncached-cone traffic in the same role-neutral cells used by the search
/// objective. This is an initialization weight, not a claim that marginal cone
/// costs remain independent once several intermediates are cached.
fn cone_dram_cells(
    d: &DistilledLayer,
    expr: ExprId,
    memo: &mut [Option<usize>],
    field_memo: &mut [Option<FieldKind>],
) -> usize {
    if let Some(cost) = memo[expr.0 as usize] {
        return cost;
    }
    let cost = match &d.layer.exprs[expr.0 as usize] {
        Expr::Source(source) => match d.regime {
            cs::gkr_compiler::dag_ir::BwdRegime::R0 => {
                if matches!(
                    d.layer.sources[source.0 as usize].kind,
                    SourceKind::Read { .. }
                ) {
                    expr_width(d, expr, field_memo)
                } else {
                    0
                }
            }
            cs::gkr_compiler::dag_ir::BwdRegime::Ext => d
                .leaf_descs
                .get(&expr)
                .and_then(|desc| d.specials.get(*desc))
                .map(|special| match special {
                    BwdSpecial::FoldSource { origin } if !origin.is_vs() => 4,
                    BwdSpecial::FoldSource { .. } | BwdSpecial::VirtualSetup { .. } => 0,
                    // CS-M5a Task 3: Coefficient/AccInit are scalar-pure recipe
                    // values, never a fold leaf's DRAM width, and only ever live
                    // in a compiled layer's cloned table — never in the
                    // `d.specials` this walk consults.
                    BwdSpecial::Coefficient { .. } | BwdSpecial::AccInit => {
                        unreachable!("Coefficient/AccInit descriptors never appear in d.specials")
                    }
                })
                .unwrap_or(0),
        },
        Expr::Add(children) | Expr::Mul(children) => {
            children.iter().fold(0usize, |total, child| {
                total.saturating_add(cone_dram_cells(d, *child, memo, field_memo))
            })
        }
    };
    memo[expr.0 as usize] = Some(cost);
    cost
}

pub(super) fn expr_width(d: &DistilledLayer, expr: ExprId, memo: &mut [Option<FieldKind>]) -> usize {
    match expr_field(d, expr, memo) {
        FieldKind::Base => 1,
        FieldKind::Ext => 4,
    }
}

fn expr_field(d: &DistilledLayer, expr: ExprId, memo: &mut [Option<FieldKind>]) -> FieldKind {
    if let Some(field) = memo[expr.0 as usize] {
        return field;
    }
    if let Some(&field) = d.field_overrides.get(&expr) {
        memo[expr.0 as usize] = Some(field);
        return field;
    }
    let field = match &d.layer.exprs[expr.0 as usize] {
        Expr::Source(source) => {
            let kind = &d.layer.sources[source.0 as usize].kind;
            source_field(kind).unwrap_or_else(|place| {
                *d.cross_fields
                    .get(&place)
                    .unwrap_or_else(|| panic!("missing cross-layer field for {place:?}"))
            })
        }
        Expr::Add(children) | Expr::Mul(children) => {
            children.iter().fold(FieldKind::Base, |field, child| {
                join(field, expr_field(d, *child, memo))
            })
        }
    };
    memo[expr.0 as usize] = Some(field);
    field
}

/// Pairwise edge weights for the unit-reuse graph. A pairwise reuse contributes
/// its whole estimated benefit. Hub values divide their benefit across the
/// induced clique so they do not gain an accidental quadratic advantage.
fn reuse_edges(values: &BTreeMap<StableBwdExprKey, ValueReuse>) -> BTreeMap<(usize, usize), usize> {
    let mut edges: BTreeMap<(usize, usize), usize> = BTreeMap::new();
    for value in values.values() {
        let unit_count = value.units.len();
        if unit_count < 2 || value.dram_cells == 0 {
            continue;
        }
        let saved_uses = value.site_indices.len().max(unit_count).saturating_sub(1);
        let benefit = value.dram_cells.saturating_mul(saved_uses);
        let pair_count = unit_count.saturating_mul(unit_count - 1) / 2;
        let share = benefit.checked_div(pair_count).unwrap_or(0).max(1);
        for left in 0..unit_count {
            for right in left + 1..unit_count {
                let edge = (value.units[left], value.units[right]);
                edges
                    .entry(edge)
                    .and_modify(|weight| *weight = weight.saturating_add(share))
                    .or_insert(share);
            }
        }
    }
    edges
}

fn edge_weight(edges: &BTreeMap<(usize, usize), usize>, a: usize, b: usize) -> usize {
    let edge = if a < b { (a, b) } else { (b, a) };
    edges.get(&edge).copied().unwrap_or(0)
}

/// Greedy maximum-adjacency path. Start at the heaviest reuse edge, then attach
/// the unused unit with the strongest endpoint connection. Total connection to
/// the current path breaks endpoint ties; canonical unit index is the final
/// deterministic tie-break.
fn guided_order(n_units: usize, edges: &BTreeMap<(usize, usize), usize>) -> Vec<usize> {
    if n_units <= 1 {
        return (0..n_units).collect();
    }
    let mut start = None;
    for (&edge, &weight) in edges {
        if start.map(|(_, best)| weight > best).unwrap_or(true) {
            start = Some((edge, weight));
        }
    }
    let Some(((left, right), _)) = start else {
        return (0..n_units).collect();
    };

    let mut path = VecDeque::from([left, right]);
    let mut used = vec![false; n_units];
    used[left] = true;
    used[right] = true;

    while path.len() < n_units {
        let left = *path.front().expect("non-empty guided path");
        let right = *path.back().expect("non-empty guided path");
        let mut best: Option<(usize, usize, usize, bool)> = None;
        for unit in 0..n_units {
            if used[unit] {
                continue;
            }
            let left_weight = edge_weight(edges, unit, left);
            let right_weight = edge_weight(edges, unit, right);
            let endpoint_weight = left_weight.max(right_weight);
            let total_weight = path.iter().fold(0usize, |total, member| {
                total.saturating_add(edge_weight(edges, unit, *member))
            });
            let attach_left = left_weight >= right_weight;
            let candidate = (endpoint_weight, total_weight, unit, attach_left);
            let replace = best
                .map(|current| {
                    candidate.0 > current.0
                        || (candidate.0 == current.0 && candidate.1 > current.1)
                        || (candidate.0 == current.0
                            && candidate.1 == current.1
                            && candidate.2 < current.2)
                })
                .unwrap_or(true);
            if replace {
                best = Some(candidate);
            }
        }
        let (_, _, unit, attach_left) = best.expect("an unused unit must remain");
        if attach_left {
            path.push_front(unit);
        } else {
            path.push_back(unit);
        }
        used[unit] = true;
    }
    path.into_iter().collect()
}

/// Assign every site of one stable value the same initial priority. Benefit is
/// estimated DRAM avoided per width×lifetime lane; priorities are normalized to
/// `[-1, 1]` and remain only relative hints for the greedy compiler.
fn interval_priorities(
    n_sites: usize,
    values: &BTreeMap<StableBwdExprKey, ValueReuse>,
    order: &[usize],
) -> Vec<f64> {
    let mut position = vec![0usize; order.len()];
    for (index, &unit) in order.iter().enumerate() {
        position[unit] = index;
    }

    let mut scored = Vec::with_capacity(values.len());
    let mut max_score = 0.0f64;
    for value in values.values() {
        let uses = value.site_indices.len().max(value.units.len());
        let avoided = value.dram_cells.saturating_mul(uses.saturating_sub(1));
        let lifetime = if value.units.len() < 2 {
            1
        } else {
            let min = value
                .units
                .iter()
                .map(|unit| position[*unit])
                .min()
                .unwrap();
            let max = value
                .units
                .iter()
                .map(|unit| position[*unit])
                .max()
                .unwrap();
            (max - min).max(1)
        };
        let lane_time = value.width.saturating_mul(lifetime).max(1);
        let score = avoided as f64 / lane_time as f64;
        max_score = max_score.max(score);
        scored.push((value, score));
    }

    let mut priorities = vec![-1.0; n_sites];
    for (value, score) in scored {
        let priority = if score == 0.0 || max_score == 0.0 {
            -1.0
        } else {
            2.0 * (score / max_score).sqrt() - 1.0
        };
        for &site_index in &value.site_indices {
            priorities[site_index] = priority;
        }
    }
    priorities
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn guided_order_makes_the_heaviest_reuse_pair_adjacent() {
        let edges = BTreeMap::from([((0, 3), 100), ((0, 1), 5), ((1, 2), 4)]);
        let order = guided_order(4, &edges);
        let p0 = order.iter().position(|unit| *unit == 0).unwrap();
        let p3 = order.iter().position(|unit| *unit == 3).unwrap();
        assert_eq!(p0.abs_diff(p3), 1);
        assert_eq!(
            order.iter().copied().collect::<BTreeSet<_>>(),
            BTreeSet::from([0, 1, 2, 3])
        );
    }

    #[test]
    fn guided_order_is_identity_without_reuse_edges() {
        assert_eq!(guided_order(4, &BTreeMap::new()), vec![0, 1, 2, 3]);
    }

    #[test]
    fn interval_priority_is_grouped_by_stable_value() {
        let values = BTreeMap::from([
            (
                StableBwdExprKey::Canonical(ExprId(0)),
                ValueReuse {
                    site_indices: vec![0, 2],
                    representative: ExprId(0),
                    units: vec![0, 1],
                    dram_cells: 8,
                    width: 1,
                },
            ),
            (
                StableBwdExprKey::Canonical(ExprId(1)),
                ValueReuse {
                    site_indices: vec![1],
                    representative: ExprId(1),
                    units: vec![0],
                    dram_cells: 0,
                    width: 1,
                },
            ),
        ]);
        let priorities = interval_priorities(3, &values, &[0, 1]);
        assert_eq!(priorities[0], priorities[2]);
        assert_eq!(priorities[0], 1.0);
        assert_eq!(priorities[1], -1.0);
    }
}
