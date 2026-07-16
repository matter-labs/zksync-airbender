//! Order context (spec M3): the per-value path data, dies-in / fills queries,
//! static-peak feasibility test, and the [`OrderPolicy`] selector the walker
//! (`crate::walk`, Task 5) consults when choosing a fold's child order and
//! deciding what to keep resident. Nothing here touches the walker — this is
//! the read-only order channel it will consume.
//!
//! # Three precomputed structures ([`OrderCtx`])
//!
//! Built once per layer from its [`SiteTable`] (the neutral site-domain
//! enumeration — one row / "locus" per node occurrence the walker visits):
//!
//! - `value_loci[e]` — the loci of every site computing `ExprId` `e`, in table
//!   order. Lets [`dies_in`](OrderCtx::dies_in) find all occurrences of a value
//!   without scanning the whole table.
//! - `locus_prefix[l]` — for locus `l`, the rolling hash of every path prefix
//!   from depth 0 (root only) to the full path, built by
//!   [`root_hash`](OrderCtx::root_hash) / [`step_hash`](OrderCtx::step_hash).
//!   `locus_prefix[l][d]` keys the length-`d` prefix of `l`'s route, so a
//!   walker at a live path can name "the subtree under this child" by a single
//!   `u64` and ask `dies_in` an O(1)-per-locus geometric question.
//! - `fills` — a genome-dependent `prefix -> width-weighted count` map of the
//!   above-threshold admissible sites strictly UNDER each prefix, rebuilt per
//!   evaluated genome by [`set_fills`](OrderCtx::set_fills) (only needed when a
//!   policy's `fill_weight != 0`).
//!
//! # Rolling prefix hash
//!
//! [`root_hash`] / [`step_hash`] are stateless splitmix64-style mixes (the
//! avalanche shape of `genome::SplitMix64`, no `Hasher` state), so the walker
//! keys its current path by mirroring these exact functions incrementally. A
//! `SitePath`'s `dup` byte rides the step mix, so the two operands of `x*x`
//! (same `ExprId`, dup 0/1) get distinct prefixes.
//!
//! # Conservative direction & hash collisions
//!
//! [`dies_in`] answers only the geometric "are all of `v`'s unconsumed
//! occurrences inside this child subtree" question; the walker owns the
//! `remaining > 0` liveness filter. Hashes are 64-bit and never compared for
//! structural equality, so a collision can only make a locus LOOK inside a
//! subtree it is not (a `dies_in` key slightly off) or inflate a `fills`
//! count — it steers a heuristic (child order / keep priority), never the
//! walker's authoritative consumed-count liveness or op emission, and
//! [`order_feasible`] uses STATIC su peaks, so feasibility is unaffected. The
//! conservative invariant the walker relies on — never "dead when live" — is
//! carried by the walker's exact consumed counts, not by these hashes.

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{ExprId, RootId};

use crate::dag::LayerView;
use crate::genome::Genome;
use crate::oracle::{SitePath, SiteTable, UseCounts};
use crate::su;

/// The splitmix64 avalanche (finalizer) — the mixing shape reused from
/// `genome::SplitMix64::next_u64`, minus the golden-ratio counter step. Pure
/// and stateless, so both this module and the walker fold identical rolling
/// hashes.
fn mix(x: u64) -> u64 {
    let mut z = x;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Tunable order-policy knobs (spec M3): `fill_weight` biases child order
/// toward (or, if negative, away from) subtrees that fill more resident cells;
/// `peak_first` toggles the SU peak-descending tie-break. Both feed the
/// walker's `Derived*` ordering — inert under [`OrderPolicy::Su`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DerivedParams {
    pub fill_weight: i8,
    pub peak_first: bool,
}

/// Which order channel the walker follows at a fold (spec M3). `Su` is the M1
/// baseline (SU peak-descending, no fills); `Derived` applies
/// [`DerivedParams`] deterministically; `DerivedBiased` additionally consults a
/// per-genome order-bias gene (Task 6); `Searched` is a fully search-driven
/// order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OrderPolicy {
    Su,
    Derived(DerivedParams),
    DerivedBiased(DerivedParams),
    Searched,
}

/// Per-layer order context: per-value loci, per-locus rolling prefix hashes,
/// the per-value use totals, and the genome-dependent `fills` map. Borrows the
/// [`SiteTable`] it was built against. See the module doc for the three
/// structures and the conservative/collision contract.
pub struct OrderCtx<'t> {
    table: &'t SiteTable,
    counts: UseCounts,
    value_loci: Vec<Vec<u32>>,
    locus_prefix: Vec<Vec<u64>>,
    fills: HashMap<u64, u64>,
    k_cap: u32,
}

impl<'t> OrderCtx<'t> {
    /// Builds the order context for a layer with `n_exprs` expressions from its
    /// site `table`: bins each site's locus by the value it computes, folds the
    /// rolling prefix hash of every locus's path, and takes the per-value use
    /// totals. `fills` starts empty (populate it with [`set_fills`] per genome).
    /// `k_cap` defaults to 4.
    pub fn new(table: &'t SiteTable, n_exprs: usize) -> OrderCtx<'t> {
        let mut value_loci = vec![Vec::new(); n_exprs];
        let mut locus_prefix = Vec::with_capacity(table.len());
        for (l, s) in table.sites.iter().enumerate() {
            value_loci[s.value.0 as usize].push(l as u32);
            let mut h = Self::root_hash(s.path.root);
            let mut prefixes = Vec::with_capacity(s.path.steps.len() + 1);
            prefixes.push(h);
            for step in &s.path.steps {
                h = Self::step_hash(h, step.child, step.dup);
                prefixes.push(h);
            }
            locus_prefix.push(prefixes);
        }
        OrderCtx {
            table,
            counts: table.use_counts(n_exprs),
            value_loci,
            locus_prefix,
            fills: HashMap::new(),
            k_cap: 4,
        }
    }

    /// The per-value use totals of the underlying table (spec M3 §2 — the
    /// walker's per-value countdown source).
    pub fn counts(&self) -> &UseCounts {
        &self.counts
    }

    /// Rebuilds the genome-dependent [`fills`](OrderCtx::fills) map (call per
    /// evaluated genome; only needed when a policy's `fill_weight != 0`). A
    /// site at locus `l` contributes `view.width(value)` to EVERY proper prefix
    /// of its path (depths `0..len-1`, i.e. every strict ancestor — never its
    /// own full path) iff it is admissible and its keep gene strictly exceeds
    /// the threshold (the decode rule of `genome::decode`).
    pub fn set_fills(&mut self, g: &Genome, view: &LayerView<'_>) {
        self.fills.clear();
        for (l, s) in self.table.sites.iter().enumerate() {
            if !(s.admissible && g.keep[l] > g.threshold) {
                continue;
            }
            let w = view.width(s.value) as u64;
            let prefixes = &self.locus_prefix[l];
            // Proper prefixes only: every strict ancestor, never the site itself.
            for &prefix in &prefixes[..prefixes.len() - 1] {
                *self.fills.entry(prefix).or_insert(0) += w;
            }
        }
    }

    /// Rolling-hash seed for a root: the splitmix64 avalanche of the root index
    /// offset by the golden-ratio increment (mirrors `SplitMix64`'s first step,
    /// avoiding the `mix(0) == 0` degenerate). `locus_prefix[l][0]` for every
    /// locus under this root.
    pub fn root_hash(root: RootId) -> u64 {
        mix((root.0 as u64).wrapping_add(0x9E37_79B9_7F4A_7C15))
    }

    /// Extends a prefix hash by one `(child, dup)` step. The `dup` byte rides
    /// the mix (in the high word) so equal-`ExprId` siblings stay distinct. The
    /// walker mirrors this exactly to key its live path.
    pub fn step_hash(parent: u64, child: ExprId, dup: u8) -> u64 {
        let leg = mix((child.0 as u64) | ((dup as u64) << 32));
        mix(parent ^ leg)
    }

    /// Width-weighted count of above-threshold admissible sites strictly under
    /// `prefix` (0 if none) — see [`set_fills`](OrderCtx::set_fills).
    pub fn fills(&self, prefix: u64) -> u64 {
        self.fills.get(&prefix).copied().unwrap_or(0)
    }

    /// Does value `v` die inside the child subtree keyed by `child_prefix`
    /// (`depth` = the number of steps taken, including the child step)? True iff
    /// `v` has at least one unconsumed occurrence and EVERY unconsumed
    /// occurrence's depth-`depth` prefix equals `child_prefix` — i.e. all of
    /// `v`'s remaining uses fall within that subtree. `consumed_loci` are the
    /// walker's per-locus consumed marks; the `remaining > 0` liveness filter is
    /// the caller's job. Conservative: a still-live occurrence outside the
    /// subtree makes this false (never falsely claims death).
    pub fn dies_in(&self, v: ExprId, child_prefix: u64, depth: usize, consumed_loci: &[bool]) -> bool {
        let mut any_live = false;
        for &l in &self.value_loci[v.0 as usize] {
            if consumed_loci[l as usize] {
                continue;
            }
            any_live = true;
            if self.locus_prefix[l as usize].get(depth) != Some(&child_prefix) {
                return false;
            }
        }
        any_live
    }

    /// The locus (site-table row) of `path`, if it was recorded — forwards to
    /// the underlying [`SiteTable::locus`]. The walker marks
    /// `consumed_loci[locus]` as it ticks each site so [`dies_in`](OrderCtx::dies_in)
    /// can tell which of a value's occurrences remain unconsumed. Deterministic
    /// (a pure `path_key` lookup); returns `None` for a path the neutral
    /// enumeration never recorded (a model bug the walker debug-asserts against).
    pub fn locus(&self, path: &SitePath) -> Option<u32> {
        self.table.locus(path)
    }

    /// The fold arity cap for order search (default 4 via [`new`](OrderCtx::new)).
    pub fn k_cap(&self) -> u32 {
        self.k_cap
    }

    /// The number of loci (site-table rows) this context covers.
    pub fn n_loci(&self) -> usize {
        self.locus_prefix.len()
    }
}

/// Static-peak feasibility of a candidate fold order (spec Global Constraints):
/// at a fold of node `n` with headroom `H = headroom`, order `o₁..o_k` is
/// feasible iff `su_peak(o₁) ≤ H` and, when `k ≥ 2`,
/// `width_n + max_{i≥2} su_peak(o_i) ≤ H` — while a later child computes in the
/// accumulator, the fold's partial value sits stashed at `width_n`. Uses STATIC
/// su peaks (`peaks`, the walker's SU memo); an empty order is trivially
/// feasible.
pub fn order_feasible(
    order: &[(u8, ExprId)],
    width_n: u32,
    headroom: u32,
    view: &LayerView<'_>,
    peaks: &mut su::Memo,
) -> bool {
    let Some(((_, first), rest)) = order.split_first() else {
        return true;
    };
    if peaks.peak(view, *first) > headroom {
        return false;
    }
    if let Some(max_rest) = rest.iter().map(|&(_, o)| peaks.peak(view, o)).max() {
        if width_n + max_rest > headroom {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use cs::gkr_compiler::dag_ir::{Expr, ExprId, RootId, SourceId};

    use super::*;
    use crate::dag::testdag::{self, shared_diamond, tiny_fma_layer};
    use crate::dag::LayerView;
    use crate::genome::Genome;
    use crate::oracle::SiteTable;

    fn view_of(layer: &cs::gkr_compiler::dag_ir::DagLayer) -> (SiteTable, usize) {
        let cross = HashMap::new();
        let v = LayerView::new(layer, &cross, None);
        let t = SiteTable::enumerate(&v);
        (t, layer.exprs.len())
    }

    #[test]
    fn prefix_hashes_match_incremental_walk() {
        let layer = shared_diamond();
        let (table, n) = view_of(&layer);
        let ctx = OrderCtx::new(&table, n);
        for (l, s) in table.sites.iter().enumerate() {
            let mut h = OrderCtx::root_hash(s.path.root);
            let mut expected = vec![h];
            for step in &s.path.steps {
                h = OrderCtx::step_hash(h, step.child, step.dup);
                expected.push(h);
            }
            assert_eq!(ctx.locus_prefix[l], expected, "locus {l} rolling hash mismatch");
        }
    }

    #[test]
    fn dies_in_shared_diamond() {
        // shared_diamond: s = Mul(w,w2) shared under r0 = Add(s,a), r1 = Add(s,b).
        let layer = shared_diamond();
        let cross = HashMap::new();
        let v = LayerView::new(&layer, &cross, None);
        let table = SiteTable::enumerate(&v);
        let ctx = OrderCtx::new(&table, layer.exprs.len());
        let s = ExprId(4); // shared Mul
        let b = ExprId(3); // r1's sibling leaf
        // Consume every locus recorded under root 0.
        let mut consumed = vec![false; ctx.n_loci()];
        for (l, si) in table.sites.iter().enumerate() {
            if si.path.root == RootId(0) {
                consumed[l] = true;
            }
        }
        // Independently rebuild the depth-1 child prefixes under root 1.
        let seed = OrderCtx::root_hash(RootId(1));
        let s_prefix = OrderCtx::step_hash(seed, s, 0);
        let b_prefix = OrderCtx::step_hash(seed, b, 0);
        assert!(ctx.dies_in(s, s_prefix, 1, &consumed), "s's only live locus is under root-1's s child");
        assert!(!ctx.dies_in(s, b_prefix, 1, &consumed), "s is not under root-1's b sibling");
    }

    #[test]
    fn dies_in_is_conservative_on_phantoms() {
        let layer = shared_diamond();
        let cross = HashMap::new();
        let v = LayerView::new(&layer, &cross, None);
        let table = SiteTable::enumerate(&v);
        let ctx = OrderCtx::new(&table, layer.exprs.len());
        let s = ExprId(4);
        // Nothing consumed: s's root-0 occurrence is a live phantom OUTSIDE the
        // root-1 child subtree, so dies_in must not claim death.
        let consumed = vec![false; ctx.n_loci()];
        let seed = OrderCtx::root_hash(RootId(1));
        let s_prefix = OrderCtx::step_hash(seed, s, 0);
        assert!(!ctx.dies_in(s, s_prefix, 1, &consumed), "a live occurrence outside keeps s alive");
    }

    #[test]
    fn fills_counts_above_threshold_admissible_only() {
        // tiny_fma_layer: root = Add(w0, Mul(w1,w2)); sites in walk order are
        // [E4 Add root, E0 w0, E3 Mul (inadmissible), E1 w1, E2 w2].
        let layer = tiny_fma_layer();
        let cross = HashMap::new();
        let v = LayerView::new(&layer, &cross, None);
        let table = SiteTable::enumerate(&v);
        let mut ctx = OrderCtx::new(&table, layer.exprs.len());
        // Genome: threshold 0. Give the inadmissible Mul (locus 2) a high gene
        // to prove admissibility gates it; give w2 (locus 4) gene 0 to prove
        // the strict threshold gates it.
        let mut g = Genome { root_keys: vec![0], keep: vec![0, 5, 9, 5, 0], threshold: 0 };
        ctx.set_fills(&g, &v);
        let root_seed = OrderCtx::root_hash(RootId(0));
        let e3_prefix = OrderCtx::step_hash(root_seed, ExprId(3), 0);
        // w0 (L1) and w1 (L3) qualify (width 1 each) under the root; the Mul
        // (L2, inadmissible) and w2 (L4, below threshold) do not.
        assert_eq!(ctx.fills(root_seed), 2, "only above-threshold admissible sites, width-weighted");
        // w1's proper prefixes are root AND E3 — the deeper prefix must get it.
        assert_eq!(ctx.fills(e3_prefix), 1, "contribution lands at EVERY proper prefix, not just the root");
        // Raise w2 above threshold: it's admissible and its path is (r0,[E3,w2]),
        // so it now adds 1 to both the root prefix and the E3 prefix.
        g.keep[4] = 9;
        ctx.set_fills(&g, &v);
        assert_eq!(ctx.fills(root_seed), 3, "w2 crossing the threshold adds its width");
        assert_eq!(ctx.fills(e3_prefix), 2, "w2 sits under E3 too");

        // Width-weighting, exercised where widths actually differ: an Ext inner
        // Add (width 4) vs a Base leaf (width 1), both admissible under a root.
        let sources = vec![testdag::challenge_source(), testdag::challenge_source(), testdag::base_read(0)];
        let exprs = vec![
            Expr::Source(SourceId(0)),             // c1 (Ext, Free)
            Expr::Source(SourceId(1)),             // c2 (Ext, Free)
            Expr::Source(SourceId(2)),             // w  (Base, Dram)
            Expr::Add(vec![ExprId(0), ExprId(1)]), // inner Ext Add (width 4, admissible)
            Expr::Add(vec![ExprId(3), ExprId(2)]), // root (Ext)
        ];
        let wl = testdag::layer(sources, exprs, vec![testdag::root(ExprId(4))]);
        let wcross = HashMap::new();
        let wv = LayerView::new(&wl, &wcross, None);
        let wt = SiteTable::enumerate(&wv);
        let mut wctx = OrderCtx::new(&wt, wl.exprs.len());
        // Sites: [E4 root, E3 inner Add (width 4), E0 c1 (Free), E1 c2 (Free), E2 w (width 1)].
        // Every gene above threshold; only admissibles (E3, E2) should count.
        let wg = Genome { root_keys: vec![0], keep: vec![0, 5, 5, 5, 5], threshold: 0 };
        wctx.set_fills(&wg, &wv);
        let wroot = OrderCtx::root_hash(RootId(0));
        assert_eq!(wctx.fills(wroot), 5, "width 4 (inner Ext Add) + width 1 (base leaf); Free leaves excluded");
    }

    #[test]
    fn order_feasible_formula() {
        // mixed_peak_layer: root0 = flat Base Add (peak 0), root1 = Ext
        // nested-fold spill (peak 4).
        let layer = testdag::mixed_peak_layer();
        let cross = HashMap::new();
        let v = LayerView::new(&layer, &cross, None);
        let mut peaks = su::Memo::new(layer.exprs.len());
        let a = ExprId(15); // su_peak 4
        let c = ExprId(4); // su_peak 0
        // Single child, first-position free: su_peak(o1) = H passes (inclusive).
        assert!(order_feasible(&[(0, a)], 4, 4, &v, &mut peaks), "su_peak(o1) == H is feasible");
        assert!(!order_feasible(&[(0, a)], 4, 3, &v, &mut peaks), "su_peak(o1) > H is not");
        // Two children with headroom H = 4 (as if budget 8 minus a width-4
        // stash): first ok (peak 0 <= 4), second bound width_n + peak(a) = 8 > 4.
        assert!(!order_feasible(&[(0, c), (0, a)], 4, 4, &v, &mut peaks), "second-position bound fails");
        // Same order, H = 8: 4 + 4 <= 8 -> feasible.
        assert!(order_feasible(&[(0, c), (0, a)], 4, 8, &v, &mut peaks), "second-position bound satisfied");
        // First position dominates: a peak-4 child first fails at H = 3 no
        // matter what follows.
        assert!(!order_feasible(&[(0, a), (0, c)], 4, 3, &v, &mut peaks), "first-position violation");
    }

    #[test]
    fn duplicate_operand_loci_stay_distinct() {
        // root = Add(w0, Mul(w1, w1)) — the x*x operands share ExprId(1) but get
        // dup indices 0 and 1, so their full prefix rows must differ at the dup.
        let sources = vec![testdag::base_read(0), testdag::base_read(1)];
        let exprs = vec![
            Expr::Source(SourceId(0)),             // w0
            Expr::Source(SourceId(1)),             // w1
            Expr::Mul(vec![ExprId(1), ExprId(1)]), // w1 * w1
            Expr::Add(vec![ExprId(0), ExprId(2)]), // root
        ];
        let layer = testdag::layer(sources, exprs, vec![testdag::root(ExprId(3))]);
        let cross = HashMap::new();
        let v = LayerView::new(&layer, &cross, None);
        let table = SiteTable::enumerate(&v);
        let ctx = OrderCtx::new(&table, layer.exprs.len());
        let loci = &ctx.value_loci[1]; // w1
        assert_eq!(loci.len(), 2, "x*x yields two distinct operand loci for w1");
        let (l0, l1) = (loci[0] as usize, loci[1] as usize);
        // Same route down to the Mul parent (depths 0 and 1)...
        assert_eq!(ctx.locus_prefix[l0][0], ctx.locus_prefix[l1][0]);
        assert_eq!(ctx.locus_prefix[l0][1], ctx.locus_prefix[l1][1]);
        // ...distinguished only by the final dup byte (depth 2).
        assert_ne!(ctx.locus_prefix[l0][2], ctx.locus_prefix[l1][2], "the dup byte separates x from x");
    }
}
