//! DagLayer-native site enumeration + relation-unit grouping (Task 5).
//!
//! `enumerate_sites` is a thin wrapper over cs's `enumerate_site_domain` (Task 4's
//! structural site domain — the single source of truth for which values qualify as
//! demand sites). It adds only a deterministic `Vec` ordering for search-side
//! consumption; it does NOT re-derive which values qualify.
//!
//! `relation_units` groups atom-roots (`materialize.is_some() && claim.is_some()`) by
//! their `Root.claim.origin` relation identity `(group, relation_index)` — num/den
//! (and any privately-shared fold) of one gate relation form one atomic scheduling
//! unit. This mirrors the grouped-genome keying in
//! `gkr_eval_isa/tests/s3_planner/metaheuristic.rs` (via its
//! `gkr_eval_isa/tests/s3_gap/instance.rs::relation_units`, whose `Vec<u32>`
//! unit-id-per-occurrence form this promotes to the `Vec<Vec<RootId>>`
//! grouped-members form the production scheduler wants).

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{enumerate_site_domain, DagLayer, RootGroup, RootId, SiteKey};

/// All cacheable reuse occurrences of `layer`, as a deterministically ordered `Vec`
/// (`SiteKey`'s `Ord`; cs's `enumerate_site_domain` returns a `BTreeSet`, so the
/// natural iteration order is already this order — `.collect()` is the whole wrap).
pub fn enumerate_sites(layer: &DagLayer) -> Vec<SiteKey> {
    enumerate_site_domain(layer).into_iter().collect()
}

/// Atom-root scheduling units: every materialize+claim-bearing root in `layer`,
/// grouped by `claim.origin`'s `(group, relation_index)` identity. Units are
/// returned in order of first occurrence; members within a unit are in
/// `layer.roots` order. Non-atom roots (claim-only `Constraint` roots,
/// materialize-only `Cache` roots) are not occurrences and are skipped — the same
/// atom-root predicate `enumerate_site_domain` uses.
pub fn relation_units(layer: &DagLayer) -> Vec<Vec<RootId>> {
    let mut units: Vec<Vec<RootId>> = Vec::new();
    let mut key_to_unit: HashMap<(RootGroup, usize), usize> = HashMap::new();
    for (i, root) in layer.roots.iter().enumerate() {
        if root.materialize.is_none() {
            continue;
        }
        let Some(claim) = root.claim.as_ref() else {
            continue;
        };
        let rid = RootId(i as u32);
        let key = (claim.origin.group.clone(), claim.origin.relation_index);
        let idx = *key_to_unit.entry(key).or_insert_with(|| {
            units.push(Vec::new());
            units.len() - 1
        });
        units[idx].push(rid);
    }
    units
}

#[cfg(test)]
mod tests {
    use super::*;
    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, ClaimInfo, Expr, ExprId, FieldKind, Root, RootOrigin, RootSlot, SinkInfo,
        SinkKind, SourceId, SourceInfo, SourceKind,
    };
    use std::collections::BTreeMap;

    fn read_source(col: usize) -> SourceInfo {
        SourceInfo {
            kind: SourceKind::Read {
                place: cs::gkr_compiler::dag_ir::ReadPlace::BaseLayerWitness { column: col },
            },
        }
    }

    fn claim_out(expr: ExprId, offset: usize, group: RootGroup, rel: usize) -> Root {
        Root {
            expr,
            materialize: Some(SinkInfo {
                kind: SinkKind::Inner { layer: 0, offset },
                field: FieldKind::Base,
            }),
            claim: Some(ClaimInfo {
                origin: RootOrigin { group, relation_index: rel, slot: RootSlot::Output(0) },
            }),
        }
    }

    #[test]
    fn relation_units_groups_same_relation_and_keeps_others_singleton() {
        // roots: (Gates,0), (Gates,0), (Gates,1), (GatesExternal,0)
        let layer = DagLayer {
            sources: vec![read_source(0), read_source(1), read_source(2), read_source(3)],
            exprs: vec![
                Expr::Source(SourceId(0)),
                Expr::Source(SourceId(1)),
                Expr::Source(SourceId(2)),
                Expr::Source(SourceId(3)),
            ],
            roots: vec![
                claim_out(ExprId(0), 0, RootGroup::Gates, 0),
                claim_out(ExprId(1), 1, RootGroup::Gates, 0),
                claim_out(ExprId(2), 2, RootGroup::Gates, 1),
                claim_out(ExprId(3), 3, RootGroup::GatesExternal, 0),
            ],
            batching: BatchingOrder { roots: vec![] },
            resolutions: BTreeMap::new(),
        };
        let units = relation_units(&layer);
        assert_eq!(
            units,
            vec![
                vec![RootId(0), RootId(1)],
                vec![RootId(2)],
                vec![RootId(3)],
            ]
        );
    }

    #[test]
    fn relation_units_skips_non_atom_roots() {
        // root0: Cache (materialize-only, no claim) — skipped.
        // root1: Constraint (claim-only, no materialize) — skipped.
        // root2: atom.
        let layer = DagLayer {
            sources: vec![read_source(0)],
            exprs: vec![Expr::Source(SourceId(0))],
            roots: vec![
                Root {
                    expr: ExprId(0),
                    materialize: Some(SinkInfo {
                        kind: SinkKind::Cache { layer: 0, offset: 0 },
                        field: FieldKind::Base,
                    }),
                    claim: None,
                },
                Root {
                    expr: ExprId(0),
                    materialize: None,
                    claim: Some(ClaimInfo {
                        origin: RootOrigin {
                            group: RootGroup::Gates,
                            relation_index: 0,
                            slot: RootSlot::Constraint(0),
                        },
                    }),
                },
                claim_out(ExprId(0), 0, RootGroup::Gates, 5),
            ],
            batching: BatchingOrder { roots: vec![] },
            resolutions: BTreeMap::new(),
        };
        assert_eq!(relation_units(&layer), vec![vec![RootId(2)]]);
    }
}
