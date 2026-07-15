//! The `Oracle` trait: pluggable root-visitation order and cache-admission
//! priority for the demand-driven walker (`crate::walk::flatten`).
//!
//! M1 ships only [`NeutralOracle`] — identity root order, never caches
//! (`keep_priority` is always `None`). This is what makes the walker's
//! neutral stats (`crate::walk::WalkStats`) comparable 1:1 against
//! `analysis::size_layer`'s all-recompute DP: with no caching decision ever
//! taken, the walker degenerates to exactly the all-recompute model the DP
//! prices (every shared sub-expr is recomputed once per path that reaches
//! it, never reused across sites).

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

/// Pluggable walker policy: root visitation order, and whether a given
/// site's computed value is worth caching.
pub trait Oracle {
    /// Root visitation order. `RootId`s keep their ORIGINAL indices (they
    /// index `DagLayer::roots` directly) — this reorders VISITATION, it
    /// never re-keys roots.
    fn root_order(&self, layer: &DagLayer) -> Vec<RootId>;

    /// Keep-priority for the value computed at `site`; `None` = never
    /// cache. Higher is more worth keeping — M2's walker will rank
    /// admission candidates by this under a cell budget.
    fn keep_priority(&self, site: &SitePath) -> Option<f64>;
}

/// The M1 baseline oracle: identity root order, never caches anything.
pub struct NeutralOracle;

impl Oracle for NeutralOracle {
    fn root_order(&self, layer: &DagLayer) -> Vec<RootId> {
        (0..layer.roots.len() as u32).map(RootId).collect()
    }

    fn keep_priority(&self, _site: &SitePath) -> Option<f64> {
        None
    }
}
