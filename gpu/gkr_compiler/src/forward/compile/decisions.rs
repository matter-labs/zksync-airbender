//! Scorer decisions and demand-order occurrence streams.

use super::arith::{
    classify_additive_child, is_constant_one, is_neg_one_factor, is_zero_expr, AdditiveChild,
};
use gkr_eval_ir::{DagLayer, Expr, ExprId, RootId, SourceKind};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::forward::artifact::{SiteConsumer, SiteKey};

// ── SiteDecisions ────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub(crate) struct SiteDecisions {
    map: BTreeMap<SiteKey, f64>,
}

impl SiteDecisions {
    pub(crate) fn new(sites: impl IntoIterator<Item = (SiteKey, f64)>) -> Self {
        Self {
            map: sites.into_iter().collect(),
        }
    }

    fn get(&self, key: &SiteKey) -> Option<f64> {
        self.map.get(key).copied()
    }
}

// ── OccurrenceStreams ────────────────────────────────────────────────────────

/// Remaining site priorities in lowering order.
pub(crate) struct OccurrenceStreams {
    streams: BTreeMap<ExprId, VecDeque<f64>>,
}

impl OccurrenceStreams {
    pub(crate) fn build(
        layer: &DagLayer,
        order: &[RootId],
        compute_roots: &BTreeSet<RootId>,
        decisions: &SiteDecisions,
    ) -> Self {
        let flat = demand_sites(layer, order, compute_roots);
        let domain = site_domain(layer, &flat);
        let mut streams: BTreeMap<ExprId, VecDeque<f64>> = BTreeMap::new();
        for key in flat {
            if !domain.contains(&key) {
                continue;
            }
            let priority = decisions
                .get(&key)
                .unwrap_or_else(|| panic!("missing priority for admitted site {key:?}"));
            streams.entry(key.value).or_default().push_back(priority);
        }
        Self { streams }
    }

    pub(crate) fn effective_priority(&self, v: ExprId) -> Option<f64> {
        self.streams.get(&v).and_then(|q| q.front()).copied()
    }

    pub(crate) fn serve(&mut self, v: ExprId) {
        if let Some(q) = self.streams.get_mut(&v) {
            q.pop_front();
        }
    }
}

pub(crate) fn enumerate_site_domain(
    layer: &DagLayer,
    order: &[RootId],
    compute_roots: &BTreeSet<RootId>,
) -> BTreeSet<SiteKey> {
    site_domain(layer, &demand_sites(layer, order, compute_roots))
}

fn site_domain(layer: &DagLayer, demands: &[SiteKey]) -> BTreeSet<SiteKey> {
    let mut counts = BTreeMap::<ExprId, usize>::new();
    let mut operand_reads = BTreeMap::<ExprId, usize>::new();
    for demand in demands {
        *counts.entry(demand.value).or_default() += 1;
        if matches!(demand.consumer, SiteConsumer::Expr { .. }) {
            *operand_reads.entry(demand.value).or_default() += 1;
        }
    }
    let reaches_dram = compute_reaches_dram(layer);
    demands
        .iter()
        .filter(|demand| {
            counts[&demand.value] >= 2
                && is_cacheable(layer, demand.value)
                && (reaches_dram.contains(&demand.value)
                    || operand_reads.get(&demand.value).copied().unwrap_or(0) >= 2)
        })
        .copied()
        .collect()
}

fn is_cacheable(layer: &DagLayer, value: ExprId) -> bool {
    if layer.resolutions.contains_key(&value) {
        return false;
    }
    if layer.roots.iter().any(|root| root.expr == value) {
        return true;
    }
    match &layer.exprs[value.0 as usize] {
        Expr::Add(_) | Expr::Mul(_) => true,
        Expr::Source(source) => matches!(layer.sources[source.0 as usize], SourceKind::Read { .. }),
    }
}

fn demand_sites(
    layer: &DagLayer,
    order: &[RootId],
    compute_roots: &BTreeSet<RootId>,
) -> Vec<SiteKey> {
    let representatives: BTreeMap<ExprId, RootId> = layer
        .roots
        .iter()
        .enumerate()
        .filter_map(|(index, root)| {
            let root_id = RootId(index as u32);
            compute_roots
                .contains(&root_id)
                .then_some((root.expr, root_id))
        })
        .fold(BTreeMap::new(), |mut representatives, (expr, root)| {
            representatives
                .entry(expr)
                .and_modify(|current| *current = (*current).min(root))
                .or_insert(root);
            representatives
        });
    let mut demands = Vec::new();
    let mut seen_compute_exprs = BTreeSet::new();
    for &root_id in order {
        if compute_roots.contains(&root_id) {
            let root_expr = layer.roots[root_id.0 as usize].expr;
            if !seen_compute_exprs.insert(root_expr) {
                continue;
            }
            let site_root = representatives[&root_expr];
            demands.push(SiteKey {
                root: site_root,
                consumer: SiteConsumer::RootOutput,
                value: root_expr,
            });
            demand_expand(layer, site_root, root_expr, &mut demands);
        }
    }
    demands
}

fn compute_reaches_dram(layer: &DagLayer) -> BTreeSet<ExprId> {
    fn visit(layer: &DagLayer, e: u32, memo: &mut [Option<bool>]) -> bool {
        if let Some(v) = memo[e as usize] {
            return v;
        }
        memo[e as usize] = Some(false);
        let r = if layer.resolutions.contains_key(&ExprId(e)) {
            false
        } else {
            match &layer.exprs[e as usize] {
                Expr::Source(sid) => {
                    matches!(layer.sources[sid.0 as usize], SourceKind::Read { .. })
                }
                Expr::Add(children) | Expr::Mul(children) => children
                    .iter()
                    .fold(false, |acc, c| visit(layer, c.0, memo) || acc),
            }
        };
        memo[e as usize] = Some(r);
        r
    }
    let mut memo: Vec<Option<bool>> = vec![None; layer.exprs.len()];
    let mut out = BTreeSet::new();
    for e in 0..layer.exprs.len() as u32 {
        if visit(layer, e, &mut memo) {
            out.insert(ExprId(e));
        }
    }
    out
}

/// Enumerate the operand sites produced by lowering `value`.
fn demand_expand(layer: &DagLayer, root_id: RootId, value: ExprId, out: &mut Vec<SiteKey>) {
    if layer.resolutions.contains_key(&value) {
        return;
    }
    match &layer.exprs[value.0 as usize] {
        Expr::Source(src_id) => {
            if let SourceKind::LookupValue { query, .. } = &layer.sources[src_id.0 as usize] {
                let q = *query;
                push_and_expand(
                    layer,
                    root_id,
                    SiteConsumer::Expr {
                        expr: value,
                        input_index: 0,
                    },
                    q,
                    out,
                );
            }
        }
        Expr::Add(children) => {
            if children.is_empty() {
                return;
            }
            let mut addends: Vec<ExprId> = Vec::new();
            let mut products: Vec<(ExprId, ExprId)> = Vec::new();
            for &c in children {
                match classify_additive_child(layer, c) {
                    AdditiveChild::Product { lhs, rhs, .. } => products.push((lhs, rhs)),
                    AdditiveChild::Addend { id, .. } => addends.push(id),
                }
            }
            let mut idx: u32 = 0;
            for id in addends {
                push_and_expand(
                    layer,
                    root_id,
                    SiteConsumer::Expr {
                        expr: value,
                        input_index: idx,
                    },
                    id,
                    out,
                );
                idx += 1;
            }
            for (lhs, rhs) in products {
                push_and_expand(
                    layer,
                    root_id,
                    SiteConsumer::Expr {
                        expr: value,
                        input_index: idx,
                    },
                    lhs,
                    out,
                );
                idx += 1;
                push_and_expand(
                    layer,
                    root_id,
                    SiteConsumer::Expr {
                        expr: value,
                        input_index: idx,
                    },
                    rhs,
                    out,
                );
                idx += 1;
            }
        }
        Expr::Mul(children) => {
            if children.iter().any(|&c| is_zero_expr(layer, c)) {
                return;
            }
            let factors: Vec<ExprId> = children
                .iter()
                .copied()
                .filter(|&c| !is_constant_one(layer, c))
                .collect();
            if factors.is_empty() {
                return;
            }
            let surviving: Vec<ExprId> = factors
                .into_iter()
                .filter(|&f| !is_neg_one_factor(layer, f))
                .collect();
            for (idx, f) in surviving.into_iter().enumerate() {
                push_and_expand(
                    layer,
                    root_id,
                    SiteConsumer::Expr {
                        expr: value,
                        input_index: idx as u32,
                    },
                    f,
                    out,
                );
            }
        }
    }
}

/// Push one demand site for `value` (consumed at `consumer`), then recurse
/// into `value`'s own children if it is compound.
fn push_and_expand(
    layer: &DagLayer,
    root_id: RootId,
    consumer: SiteConsumer,
    value: ExprId,
    out: &mut Vec<SiteKey>,
) {
    out.push(SiteKey {
        root: root_id,
        consumer,
        value,
    });
    demand_expand(layer, root_id, value, out);
}
