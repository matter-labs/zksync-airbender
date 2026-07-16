//! The `Oracle` trait: pluggable root-visitation order and cache-admission
//! priority for the demand-driven walker (`crate::walk::flatten`/
//! `flatten_budgeted`).
//!
//! [`NeutralOracle`] — identity root order, never caches (`keep_priority` is
//! always `None`) — is the M1 baseline every other oracle is measured
//! against: with no caching decision ever taken, the walker degenerates to
//! exactly the all-recompute model `analysis::size_layer`'s DP prices (every
//! shared sub-expr is recomputed once per path that reaches it, never reused
//! across sites), and its stats compare 1:1 against that DP
//! (`neutral_stats_match_dp`) and stay byte-identical to M1 at any cache
//! budget (`all_refuse_is_byte_identical_to_m1`).
//!
//! [`SiteTable`] is the M2 site-domain enumeration: one all-refuse
//! `NeutralOracle`-driven recording walk over a layer lists every node
//! OCCURRENCE (`SitePath` + `SiteObs`) the walker will ever visit, indexed by
//! [`path_key`]. It is the sole authority a search needs to build an oracle
//! over — `crate::genome::Genome`/`decode` turns a per-site keep-gene vector
//! (indexed by the same table) into a [`crate::genome::GenomeOracle`] that
//! implements this trait and drives `flatten_budgeted` exactly like
//! `NeutralOracle` or any other oracle here.

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{DagLayer, ExprId, RootId};

/// One step of a [`SitePath`]: the child visited, and `dup` — its index
/// among equal-`ExprId` siblings, assigned BEFORE the walker's SU/oracle
/// reordering of those siblings. This keeps a `SitePath` order-invariant:
/// which occurrence a `dup` index names never changes if the walker's
/// child-visitation order changes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SiteStep {
    pub child: ExprId,
    pub dup: u8,
}

/// The path taken from a root down to the node currently being finished:
/// which root, and the sequence of `(child, dup)` steps below it. Identifies
/// a specific OCCURRENCE of a node in the all-recompute tree, not just its
/// `ExprId` — a shared sub-expr reached via two different paths gets two
/// distinct `SitePath`s, so a caching oracle can price them independently.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SitePath {
    pub root: RootId,
    pub steps: Vec<SiteStep>,
}

/// A single observation the walker hands to `Oracle::observe_site`: which
/// `ExprId` the site computes and whether its standalone value is
/// admissible for caching. `admissible = false` marks a Free leaf (0 traffic,
/// never worth a cell) or a streamed fma/mul-chain product (no standalone
/// value ever materializes in the accumulator to cache).
#[derive(Clone, Copy, Debug)]
pub struct SiteObs {
    pub value: ExprId,
    pub admissible: bool,
}

/// Pluggable walker policy: root visitation order, cache-keep priority, and
/// an observation hook that fires once per site OCCURRENCE the walker
/// processes (1:1 with `WalkStats::sites_visited`).
pub trait Oracle {
    /// Root visitation order. `RootId`s keep their ORIGINAL indices (they
    /// index `DagLayer::roots` directly) — this reorders VISITATION, it
    /// never re-keys roots.
    fn root_order(&self, layer: &DagLayer) -> Vec<RootId>;

    /// Keep-priority for the value computed at `site`; `None` = never
    /// cache. Higher is more worth keeping — M2's walker will rank
    /// admission candidates by this under a cell budget.
    fn keep_priority(&self, site: &SitePath) -> Option<u32>;

    /// Fires once per site occurrence the walker processes, carrying the
    /// live `SitePath` and a [`SiteObs`]. The default is a no-op (the walker
    /// emits identically whether or not anyone observes); `SiteTable`'s
    /// `RecordingOracle` overrides it to enumerate the site domain. The
    /// `SitePath` handed here is the SAME one `keep_priority` will later see
    /// at that site — the invariant M2's coverage rests on.
    fn observe_site(&self, _site: &SitePath, _obs: SiteObs) {}

    /// Per-child order-bias for the walker's `DerivedBiased`/`Searched` fold
    /// ordering (spec M3): an additive integer nudge on a child's order key,
    /// keyed by the child's own `SitePath`. Higher biases sort the child
    /// earlier. The default `0` leaves the derived key untouched (so plain
    /// `Derived` and every M1/M2 oracle ignore ordering bias); a search-driven
    /// oracle (Task 6) overrides it to steer visitation order from its
    /// genome. Inert under [`OrderPolicy::Su`](crate::order::OrderPolicy) and
    /// plain `Derived` — `Walker::ordered_children` only ever calls this
    /// method from the `DerivedBiased`/`Searched` match arms.
    fn order_bias(&self, _site: &SitePath) -> i32 {
        0
    }
}

/// The M1 baseline oracle: identity root order, never caches anything.
pub struct NeutralOracle;

impl Oracle for NeutralOracle {
    fn root_order(&self, layer: &DagLayer) -> Vec<RootId> {
        (0..layer.roots.len() as u32).map(RootId).collect()
    }

    fn keep_priority(&self, _site: &SitePath) -> Option<u32> {
        None
    }
}

/// Test oracle: explicit per-path priorities (keyed by `path_key`), identity
/// root order.
#[cfg(test)]
pub(crate) struct MapOracle {
    pub priorities: std::collections::HashMap<PathKey, u32>,
}

#[cfg(test)]
impl Oracle for MapOracle {
    fn root_order(&self, layer: &DagLayer) -> Vec<RootId> {
        (0..layer.roots.len() as u32).map(RootId).collect()
    }
    fn keep_priority(&self, site: &SitePath) -> Option<u32> {
        self.priorities.get(&path_key(site)).copied()
    }
}

/// Test oracle: admit-everything at a fixed priority (bracket floor when the
/// budget is unbounded; naive-fill when finite).
#[cfg(test)]
pub(crate) struct AdmitAll;

#[cfg(test)]
impl Oracle for AdmitAll {
    fn root_order(&self, layer: &DagLayer) -> Vec<RootId> {
        (0..layer.roots.len() as u32).map(RootId).collect()
    }
    fn keep_priority(&self, _site: &SitePath) -> Option<u32> {
        Some(1)
    }
}

/// A `SitePath` flattened into an owned, hashable/equatable key. Encodes the
/// route as `(root index, [(child ExprId, dup)])` — value-identical to the
/// `SitePath` it came from, so two occurrences collide iff they name the same
/// route (which the walker never revisits — see `SiteTable::enumerate`).
pub type PathKey = (u32, Vec<(u32, u8)>);

/// Flattens a [`SitePath`] into its [`PathKey`].
pub fn path_key(p: &SitePath) -> PathKey {
    (p.root.0, p.steps.iter().map(|s| (s.child.0, s.dup)).collect())
}

/// One recorded site: its full [`SitePath`], the `ExprId` it computes, and
/// whether that value is cache-admissible (see [`SiteObs`]).
pub struct SiteInfo {
    pub path: SitePath,
    pub value: ExprId,
    pub admissible: bool,
}

/// The site-domain enumeration (spec M2 §4): every node OCCURRENCE the
/// neutral walker processes, one row each, in walk order. Built by
/// [`SiteTable::enumerate`] from a single all-refuse recording walk — the
/// walker is the sole enumeration authority (there is no second walk).
pub struct SiteTable {
    pub sites: Vec<SiteInfo>,
    /// `path_key(site.path) -> row index`. Private: the insert-time collision
    /// assert in `enumerate` is what guarantees it stays a bijection over the
    /// recorded rows.
    index: HashMap<PathKey, u32>,
}

/// Records every site occurrence of one neutral (all-refuse) walk — the
/// site-domain enumeration authority (spec M2 §4). Never caches.
#[derive(Default)]
struct RecordingOracle {
    seen: std::cell::RefCell<Vec<(SitePath, SiteObs)>>,
}

impl Oracle for RecordingOracle {
    fn root_order(&self, layer: &DagLayer) -> Vec<RootId> {
        (0..layer.roots.len() as u32).map(RootId).collect()
    }
    fn keep_priority(&self, _site: &SitePath) -> Option<u32> {
        None
    }
    fn observe_site(&self, site: &SitePath, obs: SiteObs) {
        self.seen.borrow_mut().push((site.clone(), obs));
    }
}

impl SiteTable {
    /// Enumerates the site domain of `view` by running one neutral recording
    /// walk (`walk::flatten` with a `RecordingOracle`) and indexing every
    /// observed occurrence. The insert-time collision assert enforces that
    /// each `path_key` is unique — i.e. that `dup` disambiguation keeps every
    /// occurrence's route distinct.
    pub fn enumerate(view: &crate::dag::LayerView<'_>) -> SiteTable {
        let rec = RecordingOracle::default();
        let _ = crate::walk::flatten(view, &rec);
        let mut table = SiteTable { sites: Vec::new(), index: HashMap::new() };
        for (path, obs) in rec.seen.into_inner() {
            let locus = table.sites.len() as u32;
            let prev = table.index.insert(path_key(&path), locus);
            assert!(prev.is_none(), "gkr_flatten: site path collision — dup indexing broken");
            table.sites.push(SiteInfo { path, value: obs.value, admissible: obs.admissible });
        }
        table
    }

    /// The row index of `path`'s site, if it was recorded.
    pub fn locus(&self, path: &SitePath) -> Option<u32> {
        self.index.get(&path_key(path)).copied()
    }

    /// Total recorded site occurrences (equals `WalkStats::sites_visited`).
    pub fn len(&self) -> usize {
        self.sites.len()
    }

    /// Whether the table recorded no sites.
    pub fn is_empty(&self) -> bool {
        self.sites.is_empty()
    }

    /// Counts total site occurrences per value: one pass over `sites`,
    /// bumping `totals[value]` per row (every row, admissible or not — a
    /// streamed fma/mul-chain product is still a use of its `ExprId`). This
    /// is the all-recompute-tree "how many times is this value reached"
    /// figure the M3 walker ticks its per-value countdown against
    /// (`crate::walk::Walker::note_use`); `n_exprs` sizes the totals vector
    /// to the layer's expr arena.
    pub fn use_counts(&self, n_exprs: usize) -> UseCounts {
        let mut totals = vec![0u32; n_exprs];
        for s in &self.sites {
            totals[s.value.0 as usize] += 1;
        }
        UseCounts { totals }
    }
}

/// Per-value total use counts (spec M3 §2): `totals[e]` is the number of
/// times `e` is reached across the whole all-recompute tree — i.e. its
/// `SiteTable` row count — the fixed total the walker's per-value use
/// countdown (`Walker::note_use`) counts down from. Built by
/// [`SiteTable::use_counts`].
pub struct UseCounts {
    totals: Vec<u32>,
}

impl UseCounts {
    /// `e`'s total use count (0 if `e` was never recorded as a site value).
    pub fn total(&self, e: ExprId) -> u32 {
        self.totals[e.0 as usize]
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use cs::gkr_compiler::dag_ir::{Expr, ExprId, SourceId};

    use super::*;
    use crate::dag::testdag::{self, shared_diamond, tiny_fma_layer};
    use crate::dag::LayerView;
    use crate::walk::flatten;

    fn table_of(layer: &cs::gkr_compiler::dag_ir::DagLayer) -> (SiteTable, crate::walk::WalkStats) {
        let cross = HashMap::new();
        let v = LayerView::new(layer, &cross, None);
        let t = SiteTable::enumerate(&v);
        let stats = flatten(&v, &NeutralOracle).stats;
        (t, stats)
    }

    #[test]
    fn table_covers_every_occurrence_exactly_once() {
        for layer in [tiny_fma_layer(), shared_diamond()] {
            let (t, stats) = table_of(&layer);
            assert_eq!(t.len() as u64, stats.sites_visited, "one table row per occurrence");
            // No key collisions: every path resolves back to its own locus.
            for (i, s) in t.sites.iter().enumerate() {
                assert_eq!(t.locus(&s.path), Some(i as u32));
            }
        }
    }

    #[test]
    fn tiny_fma_admissibility_flags() {
        // tiny_fma_layer: root = Add(w0, Mul(w1, w2)), all Dram leaves.
        // 5 occurrences: root Add (admissible), leaf w0 (admissible, Dram),
        // fused Mul (NOT admissible — streamed product), operands w1, w2
        // (admissible, Dram).
        let layer = tiny_fma_layer();
        let (t, _) = table_of(&layer);
        assert_eq!(t.len(), 5);
        // Exactly one inadmissible site: the streamed Mul product (do not
        // hardcode its ExprId — identify it by node kind).
        let cross = HashMap::new();
        let v = LayerView::new(&layer, &cross, None);
        let inadmissible: Vec<&SiteInfo> = t.sites.iter().filter(|s| !s.admissible).collect();
        assert_eq!(inadmissible.len(), 1, "only the streamed Mul product is inadmissible");
        assert!(
            matches!(v.kind(inadmissible[0].value), crate::dag::NodeKind::Mul(_)),
            "the inadmissible site must be the fused Mul"
        );
    }

    #[test]
    fn free_leaves_are_inadmissible() {
        // Add(challenge, challenge): Free-class leaves must be admissible=false.
        let sources = vec![testdag::challenge_source(), testdag::challenge_source()];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Add(vec![ExprId(0), ExprId(1)]),
        ];
        let layer = testdag::layer(sources, exprs, vec![testdag::root(ExprId(2))]);
        let (t, _) = table_of(&layer);
        for s in &t.sites {
            if matches!(s.value, ExprId(0) | ExprId(1)) {
                assert!(!s.admissible, "Free leaf {:?} must be inadmissible", s.value);
            }
        }
    }

    #[test]
    fn duplicate_operands_get_distinct_paths() {
        // root = Add(w0, Mul(w1, w1)): x*x operands are the same ExprId — the
        // pair dup indices (0, 1) must keep their two SitePaths distinct.
        let sources = vec![testdag::base_read(0), testdag::base_read(1)];
        let exprs = vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Mul(vec![ExprId(1), ExprId(1)]),
            Expr::Add(vec![ExprId(0), ExprId(2)]),
        ];
        let layer = testdag::layer(sources, exprs, vec![testdag::root(ExprId(3))]);
        let (t, stats) = table_of(&layer);
        assert_eq!(t.len() as u64, stats.sites_visited, "x*x operands must not collide");
    }

    #[test]
    fn site_path_value_semantics() {
        // Deferred M1 hygiene: SitePath equality/clone is by-value over
        // (root, steps incl. dup).
        let a = SitePath { root: cs::gkr_compiler::dag_ir::RootId(0),
            steps: vec![SiteStep { child: ExprId(3), dup: 0 }] };
        let b = a.clone();
        assert_eq!(a, b);
        let c = SitePath { root: cs::gkr_compiler::dag_ir::RootId(0),
            steps: vec![SiteStep { child: ExprId(3), dup: 1 }] };
        assert_ne!(a, c);
        assert_ne!(path_key(&a), path_key(&c));
    }

    #[test]
    fn enumeration_is_deterministic() {
        let layer = shared_diamond();
        let cross = HashMap::new();
        let v = LayerView::new(&layer, &cross, None);
        let t1 = SiteTable::enumerate(&v);
        let t2 = SiteTable::enumerate(&v);
        assert_eq!(t1.len(), t2.len());
        for (a, b) in t1.sites.iter().zip(t2.sites.iter()) {
            assert_eq!(a.path, b.path);
            assert_eq!(a.value, b.value);
            assert_eq!(a.admissible, b.admissible);
        }
    }
}
