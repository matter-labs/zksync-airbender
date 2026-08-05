//! Canonical traversal of the expressions that contribute to claim-bearing roots.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::{
    DagLayer, Expr, ExprId, FieldKind, ReadPlace, RootGroup, RootId, SinkKind, SourceKind,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CacheBoundary {
    pub place: ReadPlace,
    pub field: FieldKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimCone {
    roots: Vec<RootId>,
    reachable: BTreeSet<ExprId>,
    consumer_counts: Vec<u32>,
    cache_boundaries: BTreeMap<ExprId, CacheBoundary>,
}

impl ClaimCone {
    pub fn roots(&self) -> &[RootId] {
        &self.roots
    }

    pub fn is_reachable(&self, expr: ExprId) -> bool {
        self.reachable.contains(&expr)
    }

    pub fn consumer_count(&self, expr: ExprId) -> u32 {
        self.consumer_counts
            .get(expr.0 as usize)
            .copied()
            .unwrap_or(0)
    }

    pub fn cache_boundary(&self, expr: ExprId) -> Option<&CacheBoundary> {
        self.cache_boundaries.get(&expr)
    }
}

pub fn analyze_claim_cone(layer: &DagLayer) -> ClaimCone {
    let cache_boundaries = cache_boundaries(layer);
    let roots = claim_roots(layer).to_vec();
    let mut reachable = BTreeSet::new();
    let mut stack: Vec<ExprId> = roots
        .iter()
        .map(|root| layer.roots[root.0 as usize].expr)
        .collect();

    while let Some(expr) = stack.pop() {
        if !reachable.insert(expr) || cache_boundaries.contains_key(&expr) {
            continue;
        }
        match &layer.exprs[expr.0 as usize] {
            Expr::Source(source) => {
                if let SourceKind::LookupValue { query, .. } =
                    &layer.sources[source.0 as usize].kind
                {
                    stack.push(*query);
                }
            }
            Expr::Add(children) | Expr::Mul(children) => {
                stack.extend(children.iter().copied());
            }
        }
    }

    let mut consumer_counts = vec![0; layer.exprs.len()];
    for &expr in &reachable {
        if cache_boundaries.contains_key(&expr) {
            continue;
        }
        match &layer.exprs[expr.0 as usize] {
            Expr::Source(source) => {
                if let SourceKind::LookupValue { query, .. } =
                    &layer.sources[source.0 as usize].kind
                {
                    consumer_counts[query.0 as usize] += 1;
                }
            }
            Expr::Add(children) | Expr::Mul(children) => {
                for child in children {
                    consumer_counts[child.0 as usize] += 1;
                }
            }
        }
    }
    for root in &roots {
        let expr = layer.roots[root.0 as usize].expr;
        consumer_counts[expr.0 as usize] += 1;
    }

    ClaimCone {
        roots,
        reachable,
        consumer_counts,
        cache_boundaries,
    }
}

pub fn claim_roots(layer: &DagLayer) -> &[RootId] {
    let expected: BTreeSet<RootId> = layer
        .roots
        .iter()
        .enumerate()
        .filter(|(_, root)| root.claim.is_some())
        .map(|(index, _)| RootId(index as u32))
        .collect();
    let actual: BTreeSet<RootId> = layer.batching.roots.iter().copied().collect();
    assert_eq!(
        actual.len(),
        layer.batching.roots.len(),
        "batching roots must not contain duplicates"
    );
    assert_eq!(
        actual, expected,
        "batching roots must be exactly the claim-bearing roots"
    );
    &layer.batching.roots
}

pub fn claim_relation_units(layer: &DagLayer) -> Vec<Vec<RootId>> {
    let mut groups = Vec::<Vec<RootId>>::new();
    let mut indices = HashMap::<(RootGroup, usize), usize>::new();
    for &root in claim_roots(layer) {
        let claim = layer.roots[root.0 as usize]
            .claim
            .as_ref()
            .expect("claim_roots only returns claim-bearing roots");
        let key = (claim.origin.group.clone(), claim.origin.relation_index);
        let index = *indices.entry(key).or_insert_with(|| {
            groups.push(Vec::new());
            groups.len() - 1
        });
        groups[index].push(root);
    }
    groups
}

fn cache_boundaries(layer: &DagLayer) -> BTreeMap<ExprId, CacheBoundary> {
    let mut boundaries = BTreeMap::new();
    for root in &layer.roots {
        if root.claim.is_some() {
            continue;
        }
        let Some(sink) = &root.materialize else {
            continue;
        };
        if let SinkKind::Cache { layer, offset } = sink.kind {
            boundaries.entry(root.expr).or_insert(CacheBoundary {
                place: ReadPlace::CacheOutput { layer, offset },
                field: sink.field,
            });
        }
    }
    boundaries
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::{
        BatchingOrder, ClaimInfo, Expr, LookupValueKind, Root, RootGroup, RootOrigin, RootSlot,
        SinkInfo, SinkKind, SourceId, SourceInfo, SourceKind,
    };

    fn claim() -> ClaimInfo {
        ClaimInfo {
            origin: RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Output(0),
            },
        }
    }

    #[test]
    fn a_cache_sink_is_a_claim_cone_boundary() {
        let below_cache = ExprId(0);
        let cache_expr = ExprId(1);
        let layer = DagLayer {
            sources: vec![SourceInfo {
                kind: SourceKind::Read {
                    place: ReadPlace::BaseLayerMemory { column: 0 },
                },
            }],
            exprs: vec![Expr::Source(SourceId(0)), Expr::Add(vec![below_cache])],
            roots: vec![
                Root {
                    expr: cache_expr,
                    materialize: Some(SinkInfo {
                        kind: SinkKind::Cache {
                            layer: 0,
                            offset: 3,
                        },
                        field: FieldKind::Base,
                    }),
                    claim: None,
                },
                Root {
                    expr: cache_expr,
                    materialize: Some(SinkInfo {
                        kind: SinkKind::Export { slot: 0 },
                        field: FieldKind::Base,
                    }),
                    claim: Some(claim()),
                },
            ],
            batching: BatchingOrder {
                roots: vec![RootId(1)],
            },
            resolutions: BTreeMap::new(),
        };

        let cone = analyze_claim_cone(&layer);
        assert!(cone.is_reachable(cache_expr));
        assert_eq!(
            cone.cache_boundary(cache_expr),
            Some(&CacheBoundary {
                place: ReadPlace::CacheOutput {
                    layer: 0,
                    offset: 3
                },
                field: FieldKind::Base,
            })
        );
        assert!(!cone.is_reachable(below_cache));
    }

    #[test]
    fn lookup_query_edges_belong_to_the_claim_cone() {
        let query = ExprId(0);
        let lookup = ExprId(1);
        let layer = DagLayer {
            sources: vec![
                SourceInfo {
                    kind: SourceKind::Constant { value: 7 },
                },
                SourceInfo {
                    kind: SourceKind::LookupValue {
                        kind: LookupValueKind::GenericColumn { column: 0 },
                        set_index: 0,
                        query,
                    },
                },
            ],
            exprs: vec![Expr::Source(SourceId(0)), Expr::Source(SourceId(1))],
            roots: vec![Root {
                expr: lookup,
                materialize: None,
                claim: Some(claim()),
            }],
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            resolutions: BTreeMap::new(),
        };

        let cone = analyze_claim_cone(&layer);
        assert!(cone.is_reachable(query));
    }
}
