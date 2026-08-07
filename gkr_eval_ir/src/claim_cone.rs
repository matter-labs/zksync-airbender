//! Canonical traversal of the expressions that contribute to claim-bearing roots.

use std::collections::{BTreeMap, HashMap};

use crate::{DagLayer, ExprId, FieldKind, ReadPlace, RootGroup, RootId, SinkKind};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CacheBoundary {
    pub place: ReadPlace,
    pub field: FieldKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimCone {
    cache_boundaries: BTreeMap<ExprId, CacheBoundary>,
}

impl ClaimCone {
    pub fn cache_boundary(&self, expr: ExprId) -> Option<&CacheBoundary> {
        self.cache_boundaries.get(&expr)
    }
}

pub fn analyze_claim_cone(layer: &DagLayer) -> ClaimCone {
    ClaimCone {
        cache_boundaries: cache_boundaries(layer),
    }
}

pub fn claim_roots(layer: &DagLayer) -> &[RootId] {
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
        let key = (claim.group, claim.relation_index);
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
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;
    use crate::{
        BatchingOrder, Expr, Root, RootGroup, RootOrigin, SinkInfo, SinkKind, SourceId, SourceKind,
    };

    fn claim() -> RootOrigin {
        RootOrigin {
            group: RootGroup::Gates,
            relation_index: 0,
        }
    }

    #[test]
    fn a_cache_sink_is_a_claim_cone_boundary() {
        let below_cache = ExprId(0);
        let cache_expr = ExprId(1);
        let layer = DagLayer {
            sources: vec![SourceKind::Read {
                place: ReadPlace::BaseLayerMemory { column: 0 },
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
                        kind: SinkKind::Inner {
                            layer: 0,
                            offset: 0,
                        },
                        field: FieldKind::Base,
                    }),
                    claim: Some(claim()),
                },
            ],
            batching: BatchingOrder {
                roots: vec![RootId(1)],
            },
            resolutions: BTreeMap::new(),
            forward_skip_roots: BTreeSet::new(),
        };

        let cone = analyze_claim_cone(&layer);
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
    }
}
