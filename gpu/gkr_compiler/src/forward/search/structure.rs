//! DAG-native site enumeration and relation-unit grouping.
//!
//! `enumerate_sites` is a thin wrapper over cs's `enumerate_site_domain` (Task 4's
//! structural site domain — the single source of truth for which values qualify as
//! demand sites). It adds only a deterministic `Vec` ordering for search-side
//! consumption; it does NOT re-derive which values qualify.
//!
//! `relation_units` groups atom-roots (`materialize.is_some() && claim.is_some()`) by
//! their `Root.claim.origin` relation identity `(group, relation_index)` — num/den
//! (and any privately-shared fold) of one gate relation form one atomic scheduling
//! unit.

use std::collections::HashMap;

use gkr_eval_ir::{DagLayer, RootGroup, RootId};

use crate::schedule::{RelationUnit, SiteKey, enumerate_site_domain};

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

/// Canonical relation units with cache ownership — cs-owned single source of
/// truth ([`crate::schedule::relation_units_with_caches`]); wrapped here
/// for the search. Panics on the unsupported cross-layer/cache-only cache class
/// (a producer-time invariant, not a search-tunable outcome).
pub fn relation_units_with_caches(layer: &DagLayer) -> Vec<RelationUnit> {
    crate::schedule::relation_units_with_caches(layer)
        .unwrap_or_else(|e| panic!("relation_units_with_caches: {e}"))
}
