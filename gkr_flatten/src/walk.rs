//! The demand-driven walker (spec §2): flattens one `DagLayer`'s roots into
//! a single `LinearIR` `Program` under an `Oracle`, emitting ops so that on
//! return from `emit(e, ..)` the accumulator holds `value(e)` — exactly once
//! per node OCCURRENCE in the all-recompute tree (never per distinct
//! `ExprId`; a shared sub-expr is recomputed at every site that reaches it).
//!
//! M2 adds the simulated cache (`residency::Residency`): a value the oracle
//! wishes to keep is admitted (`Op::CacheStore` for an accumulator value,
//! `Op::CacheLoad` for an operand-position Dram leaf) under a lane budget,
//! and reused at its later occurrences as `Op::Load(Cached)`/`Operand::Cached`
//! — a HIT that prunes the whole recompute cone and charges no traffic.
//! Admissions and stash reservations evict the lowest-priority residents when
//! the budget is tight, each eviction emitting an `Op::Evict` before the op
//! that displaced it. See `flatten_budgeted`.
//!
//! `NeutralOracle` (identity root order, `None`-everywhere `keep_priority`)
//! recovers the M1 all-recompute baseline exactly: the residency check always
//! misses and no value is ever admitted, so every non-leaf node is folded
//! straight into the accumulator (leaves, fma-able Muls) or fully recomputed
//! via the stash-discipline general branch. This is what makes the neutral
//! walker's stats compare 1:1 against `analysis::size_layer`'s all-recompute
//! DP (`neutral_stats_match_dp`) and byte-identical across budgets
//! (`all_refuse_is_byte_identical_to_m1`).

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{Expr, ExprId, SourceId};

use crate::dag::{LayerView, LeafClass, NodeKind};
use crate::ir::{Op, Operand, Program, SlotId};
use crate::oracle::{Oracle, SiteObs, SitePath, SiteStep};
use crate::residency::{Admit, Residency};
use crate::su;

/// Aggregate cost counters produced by one `flatten()`/`flatten_budgeted()`
/// call.
///
/// - `traffic`: width-weighted Dram-leaf TOUCHES. A plain Dram-leaf `Load`/
///   `Add`/`Mul`/`Fma` operand charges its width, as does the `CacheLoad`
///   that ADMITS an operand-position Dram leaf (charged exactly once — the
///   `CacheLoad` REPLACES the plain leaf touch it stands in for, it does not
///   add to it). A cache HIT (`Operand::Cached`/`Op::Load(Cached)`) charges
///   NO traffic — this is how caching prunes the all-recompute ceiling toward
///   the distinct-leaf floor. Free leaves charge 0. Under `NeutralOracle`
///   (nothing ever resident, no hit/admission taken), equals
///   `analysis::SizingReport::ceiling`.
/// - `instrs`: total `Op`s emitted.
/// - `peak`: max concurrent STASH lanes (`residency.stash_lanes()` max) —
///   stash-only, never stash+resident. Cached residents occupy a separate
///   lane pool that never counts toward `peak`. Under `NeutralOracle`, equals
///   `su::cone_peak`/`analysis::SizingReport::peak` — the load-bearing
///   invariant this walker exists to realize. Caching only ever PRUNES stashes
///   (a resident fold child hits instead of recursing), so `peak` under any
///   oracle never exceeds the neutral (all-recompute) model.
/// - `sites_visited`: total node OCCURRENCES processed (every recursed
///   compound, every streamed leaf operand, every fused-fma Mul child PLUS
///   its two operands — see `Walker::emit`). Under `NeutralOracle`, equals
///   `analysis::SizingReport::sites`.
/// - `hits`: cache HITS — a resident value reused (at the `emit` entry as
///   `Load(Cached)`, or in operand position as `Operand::Cached`) instead of
///   being recomputed. Zero under `NeutralOracle`.
/// - `cache_stores`: admissions into the simulated cache — one per
///   `Op::CacheStore` (compound/leaf-root value in the accumulator) PLUS one
///   per `Op::CacheLoad` (operand-position leaf admitted straight from DRAM).
///   Zero under `NeutralOracle`.
/// - `evictions`: victims displaced from the cache — one per `Op::Evict`,
///   whether displaced by an admission (`try_admit` victims) or by a stash
///   reservation (`charge_stash` victims). Zero under `NeutralOracle`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct WalkStats {
    pub traffic: u64,
    pub instrs: u64,
    pub peak: u32,
    pub sites_visited: u64,
    pub hits: u64,
    pub cache_stores: u64,
    pub evictions: u64,
}

/// A flattened `Program` plus the stats accumulated while producing it.
pub struct WalkOutput {
    pub program: Program,
    pub stats: WalkStats,
}

/// Flattens every root of `view`'s layer (in `oracle.root_order` order) into
/// one linear `Program`, sinking each root's value via `Op::SinkMaterialize`
/// immediately after its cone is emitted. Multiple roots may share the same
/// underlying expr — each still gets its own `SinkMaterialize` (and, under
/// `NeutralOracle`, its own full recompute).
pub fn flatten(view: &LayerView<'_>, oracle: &dyn Oracle) -> WalkOutput {
    flatten_budgeted(view, oracle, None)
}

/// Like [`flatten`], but with an explicit cell `budget` (lanes) for the
/// simulated cache/stash pool. `None` = unbounded (never evicts, always
/// admits on an oracle wish); `Some(b)` caps `stash_lanes + resident_lanes`
/// at `b`, evicting the lowest-priority residents under pressure. Under
/// `NeutralOracle` (no wish ever, nothing resident) the budget is inert and
/// the output is byte-identical to M1 regardless of `budget` — the regression
/// net for the entire caching surgery.
pub fn flatten_budgeted(
    view: &LayerView<'_>,
    oracle: &dyn Oracle,
    budget: Option<u32>,
) -> WalkOutput {
    let mut walker = Walker {
        view,
        oracle,
        program: Program { ops: Vec::new(), width_of_slot: Default::default() },
        stats: WalkStats::default(),
        residency: Residency::new(budget),
    };
    for root_id in oracle.root_order(view.layer) {
        let root_expr = view.layer.roots[root_id.0 as usize].expr;
        let mut path = SitePath { root: root_id, steps: Vec::new() };
        walker.emit(root_expr, &mut path, 0);
        debug_assert_eq!(
            walker.residency.stash_lanes(),
            0,
            "gkr_flatten: stash lanes leaked past the end of root {root_id:?} — every slot \
             stashed inside a root's cone must be consumed before its SinkMaterialize (stack \
             discipline violated)"
        );
        walker.push(Op::SinkMaterialize(root_id));
    }
    WalkOutput { program: walker.program, stats: walker.stats }
}

/// Walker state threaded through the recursive `emit`.
struct Walker<'v, 'o> {
    view: &'v LayerView<'v>,
    oracle: &'o dyn Oracle,
    program: Program,
    stats: WalkStats,
    /// The simulated cache/stash lane pool (spec M2 §2). Owns the running
    /// stash-lane count (whose max is `stats.peak`), the resident value set
    /// (hit-tested at every `emit` entry and operand resolution), and the
    /// `budget`/eviction tripwire — superseding M1's bare `live_stash_lanes`
    /// counter and `budget_hint` feasibility hook.
    residency: Residency,
}

impl<'v, 'o> Walker<'v, 'o> {
    /// Emits ops so that, on return, `acc` holds `value(e)`. `depth` doubles
    /// as the stack-disciplined `SlotId` allocator: a stash at recursion
    /// depth `d` always uses `SlotId(d)`, and the LIFO stash/consume nesting
    /// guarantees no two simultaneously-live slots ever share a depth.
    fn emit(&mut self, e: ExprId, path: &mut SitePath, depth: u32) {
        self.stats.sites_visited += 1;
        // Placement 1 (spec M2 §4): every `emit` occurrence — roots, leaf
        // roots, and every compound reached by recursion. Its `SiteStep` (if
        // any) is already on `path`; observed as a standalone value.
        self.observe(e, path, false);
        // Cache hit (M2): a value already resident is reused straight from the
        // cache — its whole cone is pruned (no recursion, no traffic). Under
        // `NeutralOracle` nothing is ever resident, so this is never taken and
        // the walker degenerates to the M1 all-recompute tree.
        if self.residency.is_resident(e) {
            self.stats.hits += 1;
            self.push(Op::Load(Operand::Cached(e)));
            return;
        }
        match self.view.kind(e) {
            NodeKind::Leaf(class) => {
                self.charge_leaf(class);
                self.push(Op::Load(Operand::Leaf(self.source_id(e))));
                // Leaf-root admission (M2): the leaf's value is now in acc, so
                // `CacheStore` (acc-based) is the right admission op here — the
                // operand-position `CacheLoad` path is only for leaves consumed
                // as Add/Mul/Fma operands (see `ready_operand`). No-op under
                // `NeutralOracle`; skips Free leaves.
                self.maybe_cache(e, path);
            }
            NodeKind::Add(children) | NodeKind::Mul(children) => {
                let is_add = matches!(self.view.kind(e), NodeKind::Add(_));
                let ordered = self.order_children(children);
                let mut first = true;
                for (dup, child) in ordered {
                    path.steps.push(SiteStep { child, dup });
                    if self.is_ready(child) {
                        // leaf (M1) or resident (M2). Checked BEFORE
                        // `is_ready_product`: a *resident* streamable-Mul
                        // product resolves here as `Operand::Cached` (a hit)
                        // rather than being recomputed as an Fma. Under M1 this
                        // reorder is behavior-preserving — leaves are never
                        // products, and (all-refuse) nothing is ever resident,
                        // so a Mul child never satisfies `is_ready` in M1.
                        //
                        // Placement 3 (spec M2 §4): the ready child (its
                        // `SiteStep` already pushed above), observed as a
                        // standalone value before `ready_operand` resolves it.
                        self.observe(child, path, false);
                        // Single operand: resolved and pushed immediately, so
                        // nothing is in flight — no protection needed.
                        let op = self.ready_operand(child, path, &[]);
                        self.push(if first {
                            Op::Load(op)
                        } else if is_add {
                            Op::Add(op)
                        } else {
                            Op::Mul(op)
                        });
                    } else if self.is_ready_product(child) {
                        // 2-arity Mul with both operands ready (M1: leaf):
                        // the product streams into acc — no temp, no stash
                        // (spec §2 Rev 1). Under an Add parent it fuses as
                        // an Fma; under a Mul parent it chains
                        // associatively (acc *= a; acc *= b). This arm is
                        // exactly what `su::streamable` prices as free for
                        // a Mul node, in ANY fold.
                        let (a, b) = self.mul_operands(child);
                        self.stats.sites_visited += 1; // the fused Mul child's own occurrence
                        // Placement 2 (spec M2 §4): the fused Mul child (its
                        // `SiteStep` already pushed above) is a STREAMED
                        // product — no standalone value ever lands in acc, so
                        // it is inadmissible. Then each operand gets its own
                        // pushed step (dup = 1 for the second iff it equals
                        // the first), observed at the SitePath `keep_priority`
                        // will later see, before `ready_operand` resolves it.
                        self.observe(child, path, true);
                        path.steps.push(SiteStep { child: a, dup: 0 });
                        self.observe(a, path, false);
                        let oa = self.ready_operand(a, path, &[]);
                        path.steps.pop();
                        path.steps.push(SiteStep { child: b, dup: u8::from(b == a) });
                        self.observe(b, path, false);
                        // If `a` resolved to a cached value, it is in flight —
                        // it will be read by the not-yet-pushed op below
                        // (Load/Mul/Fma). Protect it so admitting `b` can never
                        // evict it out from under that read (the fma-operand
                        // mutual-eviction bug). The window is exactly this
                        // resolution; nothing stays pinned after the push.
                        let guard = [a];
                        let protect: &[ExprId] =
                            if matches!(oa, Operand::Cached(_)) { &guard } else { &[] };
                        let ob = self.ready_operand(b, path, protect);
                        path.steps.pop();
                        if first {
                            self.push(Op::Load(oa));
                            self.push(Op::Mul(ob));
                        } else if is_add {
                            self.push(Op::Fma(oa, ob));
                        } else {
                            self.push(Op::Mul(oa));
                            self.push(Op::Mul(ob));
                        }
                    } else {
                        // Non-ready compound child: stash acc (unless
                        // first), recurse, combine.
                        if !first {
                            let slot = SlotId(depth);
                            // Charge the stash BEFORE pushing `Op::Stash`: the
                            // reservation may evict cache residents, and every
                            // such `Op::Evict` must precede the `Stash` that
                            // displaced them (spec eviction ordering).
                            let w = self.charge_stash(e, depth);
                            self.push(Op::Stash(slot));
                            self.emit(child, path, depth + 1);
                            self.push(if is_add {
                                Op::Add(Operand::Stashed(slot))
                            } else {
                                Op::Mul(Operand::Stashed(slot))
                            });
                            self.residency.release_stash(w);
                        } else {
                            self.emit(child, path, depth);
                        }
                    }
                    path.steps.pop();
                    first = false;
                }
                self.maybe_cache(e, path); // M2; no-op under NeutralOracle
            }
        }
    }

    /// M1 convention (binding, from the Task-3 review): NON-STREAMABLE
    /// children first, descending `su::cone_peak` (ties: original arena
    /// order), then streamable children in original arena order — the
    /// `|F|=1` zero-charge premise (a streamable child consumed first would
    /// force a stash the model doesn't price). `dup` indices are assigned
    /// among equal-`ExprId` siblings BEFORE this reordering, so `SitePath`
    /// stays order-invariant.
    fn order_children(&self, children: &[ExprId]) -> Vec<(u8, ExprId)> {
        let mut dup_counts: HashMap<ExprId, u8> = HashMap::new();
        let indexed: Vec<(u8, ExprId)> = children
            .iter()
            .map(|&c| {
                let counter = dup_counts.entry(c).or_insert(0);
                let dup = *counter;
                *counter += 1;
                (dup, c)
            })
            .collect();

        let (mut non_stream, stream): (Vec<(u8, ExprId)>, Vec<(u8, ExprId)>) =
            indexed.into_iter().partition(|&(_, c)| !su::streamable(self.view, c));
        // Stable sort: ties keep the relative order they already have
        // (original arena order, preserved by `partition`).
        non_stream.sort_by_key(|&(_, c)| std::cmp::Reverse(su::cone_peak(self.view, c)));
        non_stream.extend(stream);
        non_stream
    }

    /// Readiness: `e` resolves to an `Operand` without recursion — a leaf, or
    /// (M2) a value already resident in the simulated cache. A resident
    /// compound is "ready" too: it resolves as `Operand::Cached`, its cone
    /// pruned. Under `NeutralOracle` nothing is resident, so this degenerates
    /// to the M1 leaf-only predicate.
    fn is_ready(&self, e: ExprId) -> bool {
        self.residency.is_resident(e) || matches!(self.view.kind(e), NodeKind::Leaf(_))
    }

    /// `e` is a 2-arity `Mul` with BOTH operands ready (M1: leaf) — spec §2
    /// Rev 1's recognition rule, generalized to any fold parent: under an
    /// Add it lowers as an `Fma`, under a Mul as an associative mul-chain.
    ///
    /// Checked via `is_ready` on the two operands rather than by calling
    /// `su::streamable(child)` because `is_ready`-on-operands is the check
    /// that is sound against `ready_operand`'s contract: an `Operand` can
    /// only name a leaf/cached/stashed value, never an unevaluated
    /// sub-expression. Since `su::streamable`'s Mul case is now also
    /// leaf-operands-only, the two predicates coincide exactly in M1 — the
    /// model prices free precisely what this arm can emit.
    fn is_ready_product(&self, e: ExprId) -> bool {
        match self.view.kind(e) {
            NodeKind::Mul(args) if args.len() == 2 => {
                self.is_ready(args[0]) && self.is_ready(args[1])
            }
            _ => false,
        }
    }

    /// Splits a (known) 2-arity `Mul` into its two operands.
    fn mul_operands(&self, e: ExprId) -> (ExprId, ExprId) {
        match self.view.kind(e) {
            NodeKind::Mul(args) if args.len() == 2 => (args[0], args[1]),
            _ => unreachable!(
                "gkr_flatten: mul_operands called on {e:?}, which is not a 2-arity Mul"
            ),
        }
    }

    /// Resolves a ready expr straight to an `Operand`. Three cases:
    ///
    /// - **resident** → a cache HIT: `Operand::Cached(e)`, `hits += 1`, no
    ///   traffic, no recompute. (Checked first, so `try_admit`'s
    ///   already-resident assert can never fire from here.)
    /// - **Dram leaf** with an oracle wish (`Some(priority)`) that
    ///   `residency.admit` accepts → admit it in operand position via
    ///   `Op::CacheLoad`: emit the displaced residents' `Evict`s first, charge
    ///   the leaf's traffic exactly ONCE (the `CacheLoad` REPLACES the plain
    ///   leaf touch, not adds to it), `cache_stores += 1`, and return
    ///   `Operand::Cached(e)` so the caller folds the now-resident value.
    /// - otherwise (Free leaf, no wish, or admission refused) → M1 leaf
    ///   behavior: charge the leaf's traffic, return `Operand::Leaf`.
    ///
    /// The non-hit paths each count exactly one node occurrence
    /// (`sites_visited`), a node that never recurses through `emit`.
    fn ready_operand(&mut self, e: ExprId, path: &SitePath, protected: &[ExprId]) -> Operand {
        if self.residency.is_resident(e) {
            self.stats.hits += 1;
            return Operand::Cached(e);
        }
        match self.view.kind(e) {
            NodeKind::Leaf(class) => {
                self.stats.sites_visited += 1;
                if let LeafClass::Dram { .. } = class {
                    if let Some(victims) = self.try_admit(e, path, protected) {
                        for victim in victims {
                            self.push(Op::Evict(victim));
                            self.stats.evictions += 1;
                        }
                        self.charge_leaf(class); // the leaf touch, charged once
                        self.push(Op::CacheLoad { src: self.source_id(e), id: e });
                        self.stats.cache_stores += 1;
                        return Operand::Cached(e);
                    }
                }
                // Free leaf, no oracle wish, or admission refused: plain touch.
                self.charge_leaf(class);
                Operand::Leaf(self.source_id(e))
            }
            _ => unreachable!(
                "gkr_flatten: ready_operand called on non-ready expr {e:?} (caller must check \
                 is_ready first)"
            ),
        }
    }

    /// Consults the oracle for `e`'s site and, on a wish (`Some(priority)`),
    /// asks `residency` to admit `e` at `view.width(e)` lanes. `protected`
    /// pins residents that must not be evicted for this admission — a sibling
    /// operand already resolved to `Operand::Cached` and pending an emit (see
    /// `ready_operand`'s second-operand call). Returns the displaced victims
    /// (possibly empty) on admission, or `None` when there is no wish OR the
    /// residency refuses (the incomer would be lowest-priority, or every
    /// viable victim is protected). Shared by `ready_operand` (leaf,
    /// `CacheLoad`) and `maybe_cache` (compound/leaf-root, `CacheStore`). The
    /// caller must have hit-checked `e` first — `residency.admit` asserts
    /// `!is_resident`.
    fn try_admit(&mut self, e: ExprId, path: &SitePath, protected: &[ExprId]) -> Option<Vec<ExprId>> {
        let priority = self.oracle.keep_priority(path)?;
        match self.residency.admit(e, self.view.width(e), priority, protected) {
            Admit::Admitted { victims } => Some(victims),
            Admit::Refused => None,
        }
    }

    /// `e`'s underlying `SourceId` (only valid for `Leaf` exprs).
    fn source_id(&self, e: ExprId) -> SourceId {
        match &self.view.layer.exprs[e.0 as usize] {
            Expr::Source(sid) => *sid,
            _ => unreachable!("gkr_flatten: source_id called on non-Source expr {e:?}"),
        }
    }

    /// Dram leaf touches charge their width in traffic; Free leaves charge
    /// nothing.
    fn charge_leaf(&mut self, class: LeafClass) {
        if let LeafClass::Dram { width } = class {
            self.stats.traffic += width as u64;
        }
    }

    /// Charges stashing fold node `e`'s partial: `view.width(e)` lanes,
    /// recorded in `Program.width_of_slot[depth]` and reserved through
    /// `residency.reserve_stash`, whose running `stash_lanes()` max is
    /// `stats.peak` (must equal `su::cone_peak` under `NeutralOracle` — the
    /// load-bearing invariant). Stashes are unevictable and outrank every
    /// cached value, so the reservation evicts the lowest-priority residents
    /// as needed — each such victim gets an `Op::Evict` emitted HERE, before
    /// the caller pushes the displacing `Op::Stash`. Returns the charged
    /// width so the caller can release it again once the slot is consumed.
    ///
    /// `width_of_slot` is max-write: slots are keyed by depth and reused
    /// across sibling subtrees/roots whose fold widths may differ, so the
    /// recorded width is the WIDEST value ever stashed at that depth — a
    /// safe (conservative) per-slot sizing for M2's DP, where
    /// last-write-wins would silently under-size.
    fn charge_stash(&mut self, e: ExprId, depth: u32) -> u32 {
        let w = self.view.width(e);
        self.program
            .width_of_slot
            .entry(depth)
            .and_modify(|v| *v = (*v).max(w))
            .or_insert(w);
        for victim in self.residency.reserve_stash(w) {
            self.push(Op::Evict(victim));
            self.stats.evictions += 1;
        }
        self.stats.peak = self.stats.peak.max(self.residency.stash_lanes());
        w
    }

    /// M2 accumulator-position caching hook, invoked after a compound's fold
    /// (value in acc) and after a leaf-root's `Load` (leaf value in acc). On
    /// an oracle wish that `residency.admit` accepts, emits the displaced
    /// residents' `Op::Evict`s and then an `Op::CacheStore(e)` marking `e`'s
    /// accumulator value admitted (`cache_stores += 1`). Skips Free leaves
    /// (inadmissible: 0 traffic, never worth a cell). A no-op under
    /// `NeutralOracle` (`keep_priority` always `None`), which is what keeps the
    /// neutral walk byte-identical to M1.
    ///
    /// The caller guarantees `e` is not resident on entry: a compound cannot
    /// be admitted during its own fold (DAG acyclicity), and a resident value
    /// would have hit at the `emit` entry and returned before reaching here.
    fn maybe_cache(&mut self, e: ExprId, path: &SitePath) {
        if let NodeKind::Leaf(LeafClass::Free) = self.view.kind(e) {
            return;
        }
        if let Some(victims) = self.try_admit(e, path, &[]) {
            for victim in victims {
                self.push(Op::Evict(victim));
                self.stats.evictions += 1;
            }
            self.push(Op::CacheStore(e));
            self.stats.cache_stores += 1;
        }
    }

    /// Hands one site occurrence to the oracle. `admissible` folds the
    /// streamed flag with `classify`: a streamed fma/mul-chain product never
    /// has a standalone value to cache (`admissible = false` regardless of
    /// `e`'s kind), and otherwise a value is admissible iff `classify(e)`
    /// (Dram leaves and compounds; Free leaves are not). This is the single
    /// entry point behind all three walker placement points, and a pure
    /// observation — it neither emits ops nor moves any counter.
    fn observe(&self, e: ExprId, path: &SitePath, streamed: bool) {
        let admissible = !streamed && Self::classify(self.view.kind(e));
        self.oracle.observe_site(path, SiteObs { value: e, admissible });
    }

    /// Cache-admissibility by node kind: `Leaf(Dram)` and `Add`/`Mul` → true;
    /// `Leaf(Free)` (const/challenge/virtual-setup/lookup-value) → false.
    fn classify(kind: NodeKind<'_>) -> bool {
        match kind {
            NodeKind::Leaf(LeafClass::Dram { .. }) => true,
            NodeKind::Leaf(LeafClass::Free) => false,
            NodeKind::Add(_) | NodeKind::Mul(_) => true,
        }
    }

    fn push(&mut self, op: Op) {
        self.program.ops.push(op);
        self.stats.instrs += 1;
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use cs::gkr_compiler::dag_ir::{DagLayer, RootId, SourceId};

    use super::*;
    use crate::analysis::size_layer;
    use crate::dag::testdag::{self, mixed_peak_layer, shared_diamond, tiny_fma_layer};
    use crate::oracle::NeutralOracle;

    fn view<'a>(
        l: &'a DagLayer,
        cross: &'a HashMap<cs::gkr_compiler::dag_ir::ReadPlace, cs::gkr_compiler::dag_ir::FieldKind>,
    ) -> LayerView<'a> {
        LayerView::new(l, cross, None)
    }

    /// Structural cache-liveness invariant (independent of arithmetic):
    /// replays `program.ops`, tracking the set of live cache ids, and asserts
    /// every `Operand::Cached` read names a currently-live entry, no admission
    /// (`CacheStore`/`CacheLoad`) overwrites a live entry, and no `Evict`
    /// drops an absent one. A dead `Cached` read (the fma-operand
    /// mutual-eviction bug) trips the first assert here — before the
    /// interpreter would panic and before any hit could be miscounted.
    fn assert_cache_reads_live(program: &Program) {
        use std::collections::HashSet;
        let live_read = |o: &Operand, live: &HashSet<ExprId>| {
            if let Operand::Cached(id) = o {
                assert!(live.contains(id), "Operand::Cached({id:?}) read while not live");
            }
        };
        let mut live: HashSet<ExprId> = HashSet::new();
        for op in &program.ops {
            match op {
                Op::Load(o) | Op::Add(o) | Op::Mul(o) => live_read(o, &live),
                Op::Fma(a, b) => {
                    live_read(a, &live);
                    live_read(b, &live);
                }
                Op::CacheStore(id) => {
                    assert!(live.insert(*id), "CacheStore({id:?}) overwrote a live entry");
                }
                Op::CacheLoad { id, .. } => {
                    assert!(live.insert(*id), "CacheLoad({id:?}) overwrote a live entry");
                }
                Op::Evict(id) => {
                    assert!(live.remove(id), "Evict of non-live {id:?}");
                }
                Op::Stash(_) | Op::SinkMaterialize(_) => {}
            }
        }
    }

    // ── Non-canonical / hardening layer builders ──────────────────────────
    //
    // Arena-built DAGs flatten Mul-under-Mul, so production never constructs
    // the nested-Mul shapes; testdag can, and the walker/model invariant
    // must hold unconditionally on any accepted input (review of d6bb1de6).

    /// Counterexample B: `Mul(x, Mul(a,b))`, all Base leaves. The inner Mul
    /// is streamable (leaf operands) but sits under a MUL parent — must
    /// lower as an associative mul-chain, never a stash.
    fn nested_mul_under_mul_layer() -> DagLayer {
        let sources = vec![testdag::base_read(0), testdag::base_read(1), testdag::base_read(2)];
        let exprs = vec![
            Expr::Source(SourceId(0)),             // x
            Expr::Source(SourceId(1)),             // a
            Expr::Source(SourceId(2)),             // b
            Expr::Mul(vec![ExprId(1), ExprId(2)]), // inner = Mul(a,b)
            Expr::Mul(vec![ExprId(0), ExprId(3)]), // root = Mul(x, inner)
        ];
        testdag::layer(sources, exprs, vec![testdag::root(ExprId(4))])
    }

    /// Counterexample A: `Add(C, Mul(Mul(x,y), z))` at Ext widths, with
    /// C = Add(c1,c2) computed. The outer Mul has a nested-Mul operand —
    /// not streamable (post-fix) on EITHER side — so both the model and the
    /// walker route it through the general fold branch, and the root's TWO
    /// non-streamable children make the stash real and priced: peak 4.
    fn nested_mul_under_add_layer() -> DagLayer {
        let sources = vec![testdag::challenge_source(); 5];
        let exprs = vec![
            Expr::Source(SourceId(0)),             // c1
            Expr::Source(SourceId(1)),             // c2
            Expr::Source(SourceId(2)),             // x
            Expr::Source(SourceId(3)),             // y
            Expr::Source(SourceId(4)),             // z
            Expr::Add(vec![ExprId(0), ExprId(1)]), // C = Add(c1,c2)          (5)
            Expr::Mul(vec![ExprId(2), ExprId(3)]), // inner = Mul(x,y)        (6)
            Expr::Mul(vec![ExprId(6), ExprId(4)]), // M = Mul(inner, z)       (7)
            Expr::Add(vec![ExprId(5), ExprId(7)]), // root = Add(C, M)        (8)
        ];
        testdag::layer(sources, exprs, vec![testdag::root(ExprId(8))])
    }

    /// Hardening (c): a shape with TWO simultaneously-live stash slots.
    /// root = Add(M1, M2); M1 = Add(Mul(Add(s0,s1),s2), Mul(Add(s3,s4),s5))
    /// is the standard Ext spill cone (peak 4); M2 = Mul(Add(X, D), y) with
    /// X = Add(x1,x2), D = Add(d1,d2) both computed, so M2's inner Add
    /// stashes internally (peak 4) WHILE the root's partial is stashed.
    /// cone_peak(root) = max(4, 4+4) = 8.
    fn two_live_slots_layer() -> DagLayer {
        let sources = vec![testdag::challenge_source(); 11];
        let exprs = vec![
            Expr::Source(SourceId(0)),               // s0
            Expr::Source(SourceId(1)),               // s1
            Expr::Source(SourceId(2)),               // s2
            Expr::Source(SourceId(3)),               // s3
            Expr::Source(SourceId(4)),               // s4
            Expr::Source(SourceId(5)),               // s5
            Expr::Add(vec![ExprId(0), ExprId(1)]),   // A1                    (6)
            Expr::Mul(vec![ExprId(6), ExprId(2)]),   // P1 = A1*s2            (7)
            Expr::Add(vec![ExprId(3), ExprId(4)]),   // A2                    (8)
            Expr::Mul(vec![ExprId(8), ExprId(5)]),   // P2 = A2*s5            (9)
            Expr::Add(vec![ExprId(7), ExprId(9)]),   // M1 (peak 4)           (10)
            Expr::Source(SourceId(6)),               // x1                    (11)
            Expr::Source(SourceId(7)),               // x2                    (12)
            Expr::Source(SourceId(8)),               // d1                    (13)
            Expr::Source(SourceId(9)),               // d2                    (14)
            Expr::Source(SourceId(10)),              // y                     (15)
            Expr::Add(vec![ExprId(11), ExprId(12)]), // X                     (16)
            Expr::Add(vec![ExprId(13), ExprId(14)]), // D                     (17)
            Expr::Add(vec![ExprId(16), ExprId(17)]), // inner (peak 4)        (18)
            Expr::Mul(vec![ExprId(18), ExprId(15)]), // M2 (peak 4)           (19)
            Expr::Add(vec![ExprId(10), ExprId(19)]), // root (peak 8)         (20)
        ];
        testdag::layer(sources, exprs, vec![testdag::root(ExprId(20))])
    }

    /// Hardening (d): the desc-by-cone_peak child sort is load-bearing.
    /// root = Add(L, H) with L = Add(c1,c2) (peak 0) listed FIRST in arena
    /// order and H = the Ext spill cone (peak 4) second. Sorted (H first)
    /// the realized peak is 4 == cone_peak; unsorted (arena order) H's
    /// internal stash would land under the root's live stash → 8.
    fn peak_ordered_children_layer() -> DagLayer {
        let sources = vec![testdag::challenge_source(); 8];
        let exprs = vec![
            Expr::Source(SourceId(0)),               // s0
            Expr::Source(SourceId(1)),               // s1
            Expr::Source(SourceId(2)),               // s2
            Expr::Source(SourceId(3)),               // s3
            Expr::Source(SourceId(4)),               // s4
            Expr::Source(SourceId(5)),               // s5
            Expr::Add(vec![ExprId(0), ExprId(1)]),   // A1                    (6)
            Expr::Mul(vec![ExprId(6), ExprId(2)]),   // P1                    (7)
            Expr::Add(vec![ExprId(3), ExprId(4)]),   // A2                    (8)
            Expr::Mul(vec![ExprId(8), ExprId(5)]),   // P2                    (9)
            Expr::Add(vec![ExprId(7), ExprId(9)]),   // H (peak 4)            (10)
            Expr::Source(SourceId(6)),               // c1                    (11)
            Expr::Source(SourceId(7)),               // c2                    (12)
            Expr::Add(vec![ExprId(11), ExprId(12)]), // L (peak 0)            (13)
            Expr::Add(vec![ExprId(13), ExprId(10)]), // root: arena [L, H]!   (14)
        ];
        testdag::layer(sources, exprs, vec![testdag::root(ExprId(14))])
    }

    #[test]
    fn tiny_fma_golden() {
        // roots=[Add(w0, Mul(w1,w2))]; w0/w1/w2 = SourceId(0/1/2). Both
        // children of the root Add are streamable (w0 is a leaf, Mul(w1,w2)
        // is a streamable fma), so they keep original arena order; the Mul
        // fuses into a single Fma with no temp and no stash.
        let layer = tiny_fma_layer();
        let cross = HashMap::new();
        let v = view(&layer, &cross);
        let out = flatten(&v, &NeutralOracle);

        match out.program.ops.as_slice() {
            [Op::Load(Operand::Leaf(SourceId(0))), Op::Fma(Operand::Leaf(SourceId(1)), Operand::Leaf(SourceId(2))), Op::SinkMaterialize(RootId(0))] =>
                {}
            other => panic!("unexpected op sequence: {other:?}"),
        }
        assert_eq!(out.stats.peak, 0);
        assert_eq!(out.stats.instrs, 3);
        assert_eq!(out.stats.sites_visited, 5, "1 root + 1 leaf + 1 mul + 2 operands");
    }

    #[test]
    fn nested_compound_stashes() {
        // Sum-of-computed-products, all Ext widths (challenge leaves):
        // root = Add(M1, M2), M1 = Mul(Add(a,b), c), M2 = Mul(Add(d,e), f).
        // Neither Mul child is an fma candidate (their first operand is a
        // computed Add, not a leaf), and both are non-streamable with equal
        // (zero) cone_peak, so they keep original arena order: M1 first.
        //
        // M1 computes fully in the accumulator (Load a; Add b; Mul c) with
        // NO stash (it's the `first` child of the root Add). M2 is the
        // second child, so the root's running partial (M1's value) is
        // stashed first, at the root's own (Ext, width-4) join width.
        let sources = vec![testdag::challenge_source(); 6];
        let exprs = vec![
            Expr::Source(SourceId(0)), // a
            Expr::Source(SourceId(1)), // b
            Expr::Source(SourceId(2)), // c
            Expr::Source(SourceId(3)), // d
            Expr::Source(SourceId(4)), // e
            Expr::Source(SourceId(5)), // f
            Expr::Add(vec![ExprId(0), ExprId(1)]), // Add(a,b) = 6
            Expr::Mul(vec![ExprId(6), ExprId(2)]), // M1 = Mul(Add(a,b), c) = 7
            Expr::Add(vec![ExprId(3), ExprId(4)]), // Add(d,e) = 8
            Expr::Mul(vec![ExprId(8), ExprId(5)]), // M2 = Mul(Add(d,e), f) = 9
            Expr::Add(vec![ExprId(7), ExprId(9)]), // root = Add(M1, M2) = 10
        ];
        let layer = testdag::layer(sources, exprs, vec![testdag::root(ExprId(10))]);
        let cross = HashMap::new();
        let v = view(&layer, &cross);

        let expected_peak = su::cone_peak(&v, ExprId(10));
        assert_eq!(expected_peak, 4, "precondition: Ext-width spill cone peaks at 4");

        let out = flatten(&v, &NeutralOracle);
        match out.program.ops.as_slice() {
            [
                Op::Load(Operand::Leaf(SourceId(0))),
                Op::Add(Operand::Leaf(SourceId(1))),
                Op::Mul(Operand::Leaf(SourceId(2))),
                Op::Stash(SlotId(0)),
                Op::Load(Operand::Leaf(SourceId(3))),
                Op::Add(Operand::Leaf(SourceId(4))),
                Op::Mul(Operand::Leaf(SourceId(5))),
                Op::Add(Operand::Stashed(SlotId(0))),
                Op::SinkMaterialize(RootId(0)),
            ] => {}
            other => panic!("unexpected op sequence: {other:#?}"),
        }
        assert_eq!(out.program.width_of_slot.get(&0), Some(&4));
        assert_eq!(out.stats.peak, expected_peak);
    }

    #[test]
    fn non_ready_product_lowers_as_mul_fold() {
        // Add(w, Mul(Add(a,b), c)): the Mul child's first operand (Add(a,b))
        // is not ready, so it's NOT an fma candidate -> general compound
        // (Mul-fold) lowering. The ordering convention puts the
        // non-streamable Mul child FIRST (even though `w` is listed first in
        // the source), so the Mul cone computes entirely in the accumulator
        // (no stash forced) and `w` is consumed last via a plain Add.
        let sources = vec![
            testdag::base_read(0), // w
            testdag::base_read(1), // a
            testdag::base_read(2), // b
            testdag::base_read(3), // c
        ];
        let exprs = vec![
            Expr::Source(SourceId(0)), // w
            Expr::Source(SourceId(1)), // a
            Expr::Source(SourceId(2)), // b
            Expr::Source(SourceId(3)), // c
            Expr::Add(vec![ExprId(1), ExprId(2)]), // Add(a,b) = 4
            Expr::Mul(vec![ExprId(4), ExprId(3)]), // Mul(Add(a,b), c) = 5
            Expr::Add(vec![ExprId(0), ExprId(5)]), // root = Add(w, Mul) = 6
        ];
        let layer = testdag::layer(sources, exprs, vec![testdag::root(ExprId(6))]);
        let cross = HashMap::new();
        let v = view(&layer, &cross);

        let out = flatten(&v, &NeutralOracle);
        match out.program.ops.as_slice() {
            [
                Op::Load(Operand::Leaf(SourceId(1))),
                Op::Add(Operand::Leaf(SourceId(2))),
                Op::Mul(Operand::Leaf(SourceId(3))),
                Op::Add(Operand::Leaf(SourceId(0))),
                Op::SinkMaterialize(RootId(0)),
            ] => {}
            other => panic!("unexpected op sequence: {other:#?}"),
        }
        assert!(out.program.width_of_slot.is_empty(), "no stash should ever be emitted");
        assert_eq!(out.stats.peak, 0);
        for op in &out.program.ops {
            assert!(!matches!(op, Op::Fma(..)), "no fma expected: {op:?}");
            assert!(!matches!(op, Op::Stash(..)), "no stash expected: {op:?}");
        }
    }

    /// Counterexample B (review of d6bb1de6): `Mul(x, Mul(a,b))`, all
    /// leaves. The inner Mul is streamable and sits under a MUL parent —
    /// it must chain associatively (`Mul(a); Mul(b)`) with zero stash,
    /// matching the model's peak of 0.
    ///
    /// Trace: root's children are both streamable (x is a leaf; inner is a
    /// leaf-operand 2-arity Mul) → arena order kept → x first (`Load x`),
    /// inner second under a Mul parent (`Mul a; Mul b`). Model:
    /// root is non-streamable (nested-Mul operand) but F = ∅ → peak 0.
    #[test]
    fn nested_mul_chains_under_mul_parent() {
        let layer = nested_mul_under_mul_layer();
        let cross = HashMap::new();
        let v = view(&layer, &cross);
        assert!(!su::streamable(&v, ExprId(4)), "root must not be streamable (nested Mul)");
        assert_eq!(su::cone_peak(&v, ExprId(4)), 0);

        let out = flatten(&v, &NeutralOracle);
        match out.program.ops.as_slice() {
            [
                Op::Load(Operand::Leaf(SourceId(0))),
                Op::Mul(Operand::Leaf(SourceId(1))),
                Op::Mul(Operand::Leaf(SourceId(2))),
                Op::SinkMaterialize(RootId(0)),
            ] => {}
            other => panic!("unexpected op sequence: {other:#?}"),
        }
        assert_eq!(out.stats.peak, 0, "walker peak must equal the model's 0");
        assert!(out.program.width_of_slot.is_empty(), "no stash anywhere");
        assert_eq!(out.stats.sites_visited, 5, "1 root + 1 leaf + 1 mul + 2 operands");
        assert_eq!(out.stats.traffic, 3, "x, a, b Base touches");
    }

    /// Counterexample A (review of d6bb1de6): `Add(C, Mul(Mul(x,y), z))` at
    /// Ext widths, C = Add(c1,c2). Pre-fix the model called the outer Mul
    /// "streamable" (recursing through Mul operands → priced 0) while the
    /// walker couldn't fma it (operand not ready) and stashed → realized 4 >
    /// 0, the forbidden direction. Post-fix BOTH sides route it through the
    /// general fold branch and BOTH price the stash: equality at 4, not 0.
    ///
    /// Hand-derived trace (documenting the re-derivation):
    /// - model: M = Mul(inner, z) is non-streamable (inner = Mul(x,y) is not
    ///   a leaf), but its children are both streamable → F(M) = ∅ → peak(M)
    ///   = 0; C is non-streamable, peak 0. Root F = {C, M}, peaks (0,0),
    ///   width(root) = 4 (Ext) → max(0, 4+0) = 4.
    /// - walker: C and M tie at peak 0 → arena order (C first). C computes
    ///   in acc (Load c1; Add c2); M is second → Stash s0 (4 lanes); M's
    ///   cone: inner is a ready product under a MUL parent, first child →
    ///   Load x; Mul y; then z streams (Mul z); combine Add(Stashed s0).
    ///   Realized peak 4 == model 4.
    #[test]
    fn nested_mul_nonready_product_matches_model() {
        let layer = nested_mul_under_add_layer();
        let cross = HashMap::new();
        let v = view(&layer, &cross);
        assert!(!su::streamable(&v, ExprId(7)), "outer Mul must not be streamable post-fix");
        let model_peak = su::cone_peak(&v, ExprId(8));
        assert_eq!(model_peak, 4, "model prices the root stash (re-derived by hand above)");

        let out = flatten(&v, &NeutralOracle);
        match out.program.ops.as_slice() {
            [
                Op::Load(Operand::Leaf(SourceId(0))),
                Op::Add(Operand::Leaf(SourceId(1))),
                Op::Stash(SlotId(0)),
                Op::Load(Operand::Leaf(SourceId(2))),
                Op::Mul(Operand::Leaf(SourceId(3))),
                Op::Mul(Operand::Leaf(SourceId(4))),
                Op::Add(Operand::Stashed(SlotId(0))),
                Op::SinkMaterialize(RootId(0)),
            ] => {}
            other => panic!("unexpected op sequence: {other:#?}"),
        }
        assert_eq!(out.stats.peak, model_peak, "walker == model, equality at 4 not 0");
        assert_eq!(out.program.width_of_slot.get(&0), Some(&4));
        for op in &out.program.ops {
            assert!(!matches!(op, Op::Fma(..)), "no fma: the product operand is not ready");
        }
    }

    /// Hardening (c): two SIMULTANEOUSLY-live stash slots with distinct ids.
    /// root = Add(M1, M2), both peak 4 (tie → arena keeps M1 first), so
    /// M2's internal stash (SlotId(1), depth 1) happens while the root's
    /// partial sits in SlotId(0) (depth 0): live = 8 = cone_peak(root).
    ///
    /// Trace: M1's spill cone runs first and fully releases its own
    /// (reused) SlotId(0); then the root stashes SlotId(0) and, inside M2's
    /// inner Add, X computes in acc and D forces Stash SlotId(1) → live 8.
    #[test]
    fn two_simultaneous_stash_slots() {
        let layer = two_live_slots_layer();
        let cross = HashMap::new();
        let v = view(&layer, &cross);
        let model_peak = su::cone_peak(&v, ExprId(20));
        assert_eq!(model_peak, 8, "max(4, 4+4): inner stash under live root stash");

        let out = flatten(&v, &NeutralOracle);
        match out.program.ops.as_slice() {
            [
                // M1's spill cone (its own transient SlotId(0) use):
                Op::Load(Operand::Leaf(SourceId(0))),
                Op::Add(Operand::Leaf(SourceId(1))),
                Op::Mul(Operand::Leaf(SourceId(2))),
                Op::Stash(SlotId(0)),
                Op::Load(Operand::Leaf(SourceId(3))),
                Op::Add(Operand::Leaf(SourceId(4))),
                Op::Mul(Operand::Leaf(SourceId(5))),
                Op::Add(Operand::Stashed(SlotId(0))),
                // Root partial stashed; M2's cone with the SECOND live slot:
                Op::Stash(SlotId(0)),
                Op::Load(Operand::Leaf(SourceId(6))),
                Op::Add(Operand::Leaf(SourceId(7))),
                Op::Stash(SlotId(1)), // stashed while SlotId(0) is live → live 8
                Op::Load(Operand::Leaf(SourceId(8))),
                Op::Add(Operand::Leaf(SourceId(9))),
                Op::Add(Operand::Stashed(SlotId(1))),
                Op::Mul(Operand::Leaf(SourceId(10))),
                Op::Add(Operand::Stashed(SlotId(0))),
                Op::SinkMaterialize(RootId(0)),
            ] => {}
            other => panic!("unexpected op sequence: {other:#?}"),
        }
        assert_eq!(out.stats.peak, model_peak);
        assert_eq!(out.program.width_of_slot.get(&0), Some(&4));
        assert_eq!(out.program.width_of_slot.get(&1), Some(&4));
    }

    /// Hardening (d): the desc-by-cone_peak sort among non-streamable
    /// children is load-bearing. Arena order lists L (peak 0) BEFORE H
    /// (peak 4); emitting in arena order would put H's internal stash under
    /// the root's live stash (realized 8), while the model prices
    /// max(4, 4+0) = 4. The sort must emit H first.
    #[test]
    fn peak_desc_order_is_load_bearing() {
        let layer = peak_ordered_children_layer();
        let cross = HashMap::new();
        let v = view(&layer, &cross);
        let model_peak = su::cone_peak(&v, ExprId(14));
        assert_eq!(model_peak, 4, "max(peak(H)=4, width 4 + peak(L)=0)");

        let out = flatten(&v, &NeutralOracle);
        // H's cone must come first: its first leaf is SourceId(0).
        match out.program.ops.first() {
            Some(Op::Load(Operand::Leaf(SourceId(0)))) => {}
            other => panic!("peak-4 child must be emitted first, got {other:?}"),
        }
        match out.program.ops.as_slice() {
            [
                // H's spill cone, root partial not yet stashed:
                Op::Load(Operand::Leaf(SourceId(0))),
                Op::Add(Operand::Leaf(SourceId(1))),
                Op::Mul(Operand::Leaf(SourceId(2))),
                Op::Stash(SlotId(0)),
                Op::Load(Operand::Leaf(SourceId(3))),
                Op::Add(Operand::Leaf(SourceId(4))),
                Op::Mul(Operand::Leaf(SourceId(5))),
                Op::Add(Operand::Stashed(SlotId(0))),
                // L second: root partial stashed only for L's cheap cone:
                Op::Stash(SlotId(0)),
                Op::Load(Operand::Leaf(SourceId(6))),
                Op::Add(Operand::Leaf(SourceId(7))),
                Op::Add(Operand::Stashed(SlotId(0))),
                Op::SinkMaterialize(RootId(0)),
            ] => {}
            other => panic!("unexpected op sequence: {other:#?}"),
        }
        assert_eq!(out.stats.peak, model_peak, "unsorted emission would realize 8");
    }

    /// The M2 site-domain coverage invariant on a real fixture: the neutral
    /// recording walk (`SiteTable::enumerate`) records exactly one site per
    /// node occurrence the walker's `sites_visited` counter charges. This is
    /// the placement contract's 1:1 statement, checked on the real add_sub L0
    /// (many roots, deep cones) in addition to the synthetic layers.
    #[test]
    fn site_table_covers_real_fixture() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let v = LayerView::new(&dag.layers[0], &cross, None);
        let t = crate::oracle::SiteTable::enumerate(&v);
        let stats = flatten(&v, &NeutralOracle).stats;
        assert_eq!(t.len() as u64, stats.sites_visited);
    }

    /// Runs `flatten` twice over the same view and checks the emitted
    /// program (via its `Debug` rendering — `Op`/`Operand` are not
    /// `PartialEq`) and stats are byte-identical, on both a small synthetic
    /// layer and a real fixture layer with many roots.
    #[test]
    fn determinism() {
        let layer = tiny_fma_layer();
        let cross = HashMap::new();
        let v = view(&layer, &cross);
        let a = flatten(&v, &NeutralOracle);
        let b = flatten(&v, &NeutralOracle);
        assert_eq!(format!("{:?}", a.program.ops), format!("{:?}", b.program.ops));
        assert_eq!(a.stats, b.stats);

        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let real_layer = &dag.layers[0];
        let rv = LayerView::new(real_layer, &cross, None);
        let ra = flatten(&rv, &NeutralOracle);
        let rb = flatten(&rv, &NeutralOracle);
        assert_eq!(format!("{:?}", ra.program.ops), format!("{:?}", rb.program.ops));
        assert_eq!(ra.stats, rb.stats);

        // While the real fixture is loaded: the walker's realized peak must
        // reproduce the SU model exactly here too, not just on the synthetic
        // layers `neutral_stats_match_dp` covers.
        let su_peak =
            real_layer.roots.iter().map(|r| su::cone_peak(&rv, r.expr)).max().unwrap();
        assert_eq!(ra.stats.peak, su_peak, "walker peak vs su::cone_peak on add_sub L0");
    }

    /// Ties the neutral walker's stats to Task 4's all-recompute DP
    /// (`analysis::size_layer`) — the load-bearing invariant: under
    /// `NeutralOracle` (no caching), the walker's traffic/sites/peak must
    /// equal the DP's ceiling/sites/peak exactly, across a no-sharing tree
    /// (`tiny_fma_layer`), a fan-in-shared layer (`shared_diamond`), a
    /// layer with a non-degenerate root-dependent peak (`mixed_peak_layer`),
    /// and the non-canonical/hardening shapes (nested Muls, two live slots,
    /// order-sensitive peaks).
    #[test]
    fn neutral_stats_match_dp() {
        for layer in [
            tiny_fma_layer(),
            shared_diamond(),
            mixed_peak_layer(),
            nested_mul_under_mul_layer(),
            nested_mul_under_add_layer(),
            two_live_slots_layer(),
            peak_ordered_children_layer(),
        ] {
            let cross = HashMap::new();
            let v = view(&layer, &cross);
            let roots: Vec<ExprId> = layer.roots.iter().map(|r| r.expr).collect();
            let report = size_layer(&v, &roots);
            let out = flatten(&v, &NeutralOracle);

            assert_eq!(out.stats.traffic as u128, report.ceiling, "traffic vs ceiling");
            assert_eq!(out.stats.sites_visited as u128, report.sites, "sites_visited vs sites");
            assert_eq!(out.stats.peak, report.peak, "peak vs DP peak");
        }
    }

    /// Self-review addition beyond the brief's five named tests: the emitted
    /// `Program` must actually EVALUATE to the same value as the DAG-walking
    /// reference evaluator, not just have the right op-sequence shape. Runs
    /// every root of the real `add_sub` L0 fixture through `ir::interpret`
    /// at a few rows and diffs against `eval_layer_root` — this is what
    /// actually exercises the stash/fma/mul-fold lowering's arithmetic.
    #[test]
    fn emitted_program_evaluates_correctly_on_real_fixture() {
        use cs::gkr_compiler::dag_ir::eval::{
            Bf, ChallengeResolver, Ext, LookupResolver, ReadResolver, Resolvers,
            VirtualSetupResolver, eval_layer_root,
        };
        use cs::gkr_compiler::dag_ir::{ChallengeRef, LookupValueKind, VirtualSetupKind};
        use field::{FieldExtension, PrimeField};

        fn mix(a: u32, b: u32) -> u32 {
            a.wrapping_mul(2_654_435_761)
                .wrapping_add(b.wrapping_mul(2_246_822_519))
                .wrapping_add(0x9E3779B9)
        }
        fn lift(b: Bf) -> Ext {
            <Ext as FieldExtension<Bf>>::from_base(b)
        }

        struct DetResolver;
        impl ReadResolver for DetResolver {
            fn read(&self, place: &cs::gkr_compiler::dag_ir::ReadPlace, row: usize) -> Ext {
                use cs::gkr_compiler::dag_ir::ReadPlace;
                let col = match place {
                    ReadPlace::BaseLayerWitness { column } => *column as u32,
                    ReadPlace::BaseLayerMemory { column } => (*column as u32).wrapping_add(1_000),
                    ReadPlace::Setup { column } => (*column as u32).wrapping_add(2_000),
                    ReadPlace::Scratch { slot } => (*slot as u32).wrapping_add(3_000),
                    ReadPlace::LayerOutput { layer, offset } => (*layer as u32)
                        .wrapping_mul(100)
                        .wrapping_add(*offset as u32)
                        .wrapping_add(4_000),
                    ReadPlace::CacheOutput { layer, offset } => (*layer as u32)
                        .wrapping_mul(100)
                        .wrapping_add(*offset as u32)
                        .wrapping_add(5_000),
                };
                lift(Bf::from_u32_with_reduction(mix(col, row as u32)))
            }
        }
        impl LookupResolver for DetResolver {
            fn lookup(&self, _kind: &LookupValueKind, set_index: usize, _q: Ext, row: usize) -> Bf {
                Bf::from_u32_with_reduction(mix((set_index as u32).wrapping_add(6_000), row as u32))
            }
        }
        impl VirtualSetupResolver for DetResolver {
            fn virtual_setup(&self, _kind: &VirtualSetupKind, row: usize) -> Bf {
                Bf::from_u32_with_reduction(mix(7_001, row as u32))
            }
        }
        impl ChallengeResolver for DetResolver {
            fn challenge(&self, _reference: &ChallengeRef) -> Ext {
                lift(Bf::from_u32_with_reduction(mix(8_001, 0)))
            }
        }

        let d = DetResolver;
        let r = Resolvers { read: &d, lookup: &d, virtual_setup: &d, challenge: &d };

        let check = |layer: &DagLayer, cross: &HashMap<_, _>, label: &str| {
            let v = LayerView::new(layer, cross, None);
            let out = flatten(&v, &NeutralOracle);
            for row in [0usize, 1, 7] {
                let got = crate::ir::interpret(&out.program, layer, row, &r);
                for (i, root) in layer.roots.iter().enumerate() {
                    let root_id = RootId(i as u32);
                    let expected = eval_layer_root(layer, root_id, row, &r);
                    assert_eq!(
                        got[&root_id], expected,
                        "[{label}] root {i} (expr {:?}) mismatched reference eval at row {row}",
                        root.expr
                    );
                }
            }
        };

        // The synthetic layers exercise arms the real fixture can't reach
        // (arena-canonical DAGs have no nested Muls): the mul-chain lowering
        // and the two-simultaneous-slot stash discipline.
        let empty_cross = HashMap::new();
        for (layer, label) in [
            (tiny_fma_layer(), "tiny_fma"),
            (nested_mul_under_mul_layer(), "mul_chain"),
            (nested_mul_under_add_layer(), "nested_mul_general"),
            (two_live_slots_layer(), "two_live_slots"),
            (peak_ordered_children_layer(), "peak_ordered"),
        ] {
            check(&layer, &empty_cross, label);
        }

        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        check(&dag.layers[0], &cross, "add_sub L0");
    }

    // ── M2 caching walker (Task 4) ────────────────────────────────────────

    #[test]
    fn all_refuse_is_byte_identical_to_m1() {
        // NeutralOracle under any budget must reproduce the M1 walker exactly.
        for layer in [tiny_fma_layer(), shared_diamond(), mixed_peak_layer()] {
            let cross = HashMap::new();
            let v = view(&layer, &cross);
            let m1 = flatten(&v, &NeutralOracle);
            let m2 = flatten_budgeted(&v, &NeutralOracle, Some(64));
            assert_eq!(m1.program, m2.program);
            assert_eq!(m1.stats, m2.stats);
        }
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let rv = LayerView::new(&dag.layers[0], &cross, None);
        let m1 = flatten(&rv, &NeutralOracle);
        let m2 = flatten_budgeted(&rv, &NeutralOracle, Some(64));
        assert_eq!(m1.program, m2.program);
        assert_eq!(m1.stats, m2.stats);
    }

    #[test]
    fn shared_compound_hit_prunes_recursion() {
        // shared_diamond: two roots sharing one compound. Admit it at its first
        // (root-0) occurrence; root 1's walk must hit (Load(Cached)) instead of
        // recomputing, and traffic must drop to the floor.
        let layer = shared_diamond();
        let cross = HashMap::new();
        let v = view(&layer, &cross);
        let roots: Vec<ExprId> = layer.roots.iter().map(|r| r.expr).collect();
        let report = size_layer(&v, &roots);

        let out = flatten_budgeted(&v, &crate::oracle::AdmitAll, None);
        assert_cache_reads_live(&out.program);
        assert!(out.stats.hits > 0, "second occurrence must hit");
        assert_eq!(out.stats.traffic, report.floor, "all-admit @ unbounded reaches the floor");
        assert!(out.program.ops.iter().any(|op| matches!(op, Op::CacheStore(_))));
        assert!(out.program.ops.iter().any(|op| matches!(op, Op::Load(Operand::Cached(_)))));
        // Bracket sanity on the same walker:
        let ceiling = flatten(&v, &NeutralOracle).stats.traffic;
        assert!(out.stats.traffic <= ceiling);
    }

    #[test]
    fn operand_position_leaf_caching_uses_cache_load() {
        // root0 = Add(a, Mul(b, c)); root1 = Add(a, Mul(b, c)) again (two roots,
        // same expr): admitting operand-position leaf b must emit CacheLoad at
        // its first touch and Cached at the second, charging b's traffic once.
        let sources = vec![testdag::base_read(0), testdag::base_read(1), testdag::base_read(2)];
        let exprs = vec![
            Expr::Source(SourceId(0)),             // a
            Expr::Source(SourceId(1)),             // b
            Expr::Source(SourceId(2)),             // c
            Expr::Mul(vec![ExprId(1), ExprId(2)]), // Mul(b, c)
            Expr::Add(vec![ExprId(0), ExprId(3)]), // Add(a, Mul)
        ];
        let layer = testdag::layer(
            sources, exprs,
            vec![testdag::root(ExprId(4)), testdag::root(ExprId(4))],
        );
        let cross = HashMap::new();
        let v = view(&layer, &cross);

        // Enable ONLY root-0's b-operand site.
        let table = crate::oracle::SiteTable::enumerate(&v);
        let b_site = table.sites.iter()
            .find(|s| s.value == ExprId(1) && s.path.root == RootId(0) && s.admissible)
            .expect("b operand site under root 0");
        let oracle = crate::oracle::MapOracle {
            priorities: [(crate::oracle::path_key(&b_site.path), 5)].into_iter().collect(),
        };
        let out = flatten_budgeted(&v, &oracle, Some(8));
        assert_cache_reads_live(&out.program);

        let cache_loads = out.program.ops.iter()
            .filter(|op| matches!(op, Op::CacheLoad { src: SourceId(1), .. })).count();
        assert_eq!(cache_loads, 1, "b admitted via CacheLoad exactly once");
        assert_eq!(out.stats.hits, 1, "root 1's b touch hits");
        let neutral = flatten(&v, &NeutralOracle).stats.traffic;
        assert_eq!(out.stats.traffic, neutral - 1, "b (Base, width 1) charged once instead of twice");
    }

    #[test]
    fn eviction_under_pressure_emits_evict() {
        // Budget 1 lane (Base widths): admit a at priority 1, then b at
        // priority 9 -> a evicted, Evict(a) emitted BEFORE b's CacheLoad.
        let sources = vec![testdag::base_read(0), testdag::base_read(1)];
        let exprs = vec![
            Expr::Source(SourceId(0)),             // a
            Expr::Source(SourceId(1)),             // b
            Expr::Add(vec![ExprId(0), ExprId(1)]), // r0 = Add(a, b)
            Expr::Add(vec![ExprId(0), ExprId(1)]), // r1 (recompute: fresh sites)
        ];
        let layer = testdag::layer(
            sources, exprs,
            vec![testdag::root(ExprId(2)), testdag::root(ExprId(3))],
        );
        let cross = HashMap::new();
        let v = view(&layer, &cross);
        let table = crate::oracle::SiteTable::enumerate(&v);
        // Under root 0: a's site gets priority 1, b's site priority 9.
        let mut priorities = std::collections::HashMap::new();
        for s in &table.sites {
            if s.path.root == RootId(0) && s.admissible {
                if s.value == ExprId(0) { priorities.insert(crate::oracle::path_key(&s.path), 1); }
                if s.value == ExprId(1) { priorities.insert(crate::oracle::path_key(&s.path), 9); }
            }
        }
        let oracle = crate::oracle::MapOracle { priorities };
        let out = flatten_budgeted(&v, &oracle, Some(1));
        assert_cache_reads_live(&out.program);

        assert_eq!(out.stats.evictions, 1);
        let evict_pos = out.program.ops.iter()
            .position(|op| matches!(op, Op::Evict(ExprId(0)))).expect("Evict(a) present");
        let b_load_pos = out.program.ops.iter()
            .position(|op| matches!(op, Op::CacheLoad { src: SourceId(1), .. }))
            .expect("CacheLoad(b) present");
        assert!(evict_pos < b_load_pos, "Evict precedes the displacing CacheLoad");
    }

    #[test]
    fn caching_walks_never_exceed_model_peak() {
        for layer in [
            shared_diamond(), mixed_peak_layer(),
            nested_mul_under_add_layer(), two_live_slots_layer(),
        ] {
            let cross = HashMap::new();
            let v = view(&layer, &cross);
            let model: u32 = layer.roots.iter().map(|r| su::cone_peak(&v, r.expr)).max().unwrap();
            let out = flatten_budgeted(&v, &crate::oracle::AdmitAll, Some(model + 8));
            assert_cache_reads_live(&out.program);
            assert!(out.stats.peak <= model, "hits only ever prune: peak {} > model {model}", out.stats.peak);
        }
    }

    #[test]
    fn caching_program_still_evaluates_correctly() {
        // Value parity under caching: AdmitAll (finite + unbounded budgets) on
        // synthetic layers and the real add_sub L0, vs eval_layer_root, via the
        // shared HashResolvers.
        let r = crate::resolvers::HashResolvers { seed: 7 };
        let rb = r.bundle();
        let check = |layer: &DagLayer, cross: &HashMap<_, _>, budget: Option<u32>, label: &str| {
            let v = LayerView::new(layer, cross, None);
            let out = flatten_budgeted(&v, &crate::oracle::AdmitAll, budget);
            assert_cache_reads_live(&out.program);
            for row in [0usize, 1, 7] {
                let got = crate::ir::interpret(&out.program, layer, row, &rb);
                for (i, _) in layer.roots.iter().enumerate() {
                    let want = cs::gkr_compiler::dag_ir::eval::eval_layer_root(
                        layer, RootId(i as u32), row, &rb);
                    assert_eq!(got[&RootId(i as u32)], want, "[{label}] root {i} row {row}");
                }
            }
        };
        let empty = HashMap::new();
        for (layer, label) in [
            (shared_diamond(), "diamond"),
            (two_live_slots_layer(), "two_live_slots"),
            (mixed_peak_layer(), "mixed_peak"),
        ] {
            check(&layer, &empty, None, label);
            check(&layer, &empty, Some(9), label);
        }
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let report = {
            let v = LayerView::new(&dag.layers[0], &cross, None);
            let roots: Vec<ExprId> = dag.layers[0].roots.iter().map(|r| r.expr).collect();
            size_layer(&v, &roots)
        };
        check(&dag.layers[0], &cross, None, "add_sub L0 unbounded");
        check(&dag.layers[0], &cross, Some(report.peak + 2), "add_sub L0 tight");
    }

    #[test]
    fn sibling_admission_never_evicts_in_flight_operand() {
        // root = Add(w0, Mul(a, b)); a, b Dram leaves; budget 1 lane. Oracle
        // gives a's operand site priority 1 and b's priority 9. Without the
        // in-flight protection, resolving b would evict the just-admitted a
        // (Evict(a), CacheLoad(b)) and the fused Fma(Cached(a), Cached(b))
        // would read a DEAD cache entry — an interpreter panic at parity time
        // and a miscounted hit. Protection makes b's admission refuse (its
        // only viable victim is the pinned a), so b stays a plain leaf touch.
        let sources = vec![testdag::base_read(0), testdag::base_read(1), testdag::base_read(2)];
        let exprs = vec![
            Expr::Source(SourceId(0)),             // w0
            Expr::Source(SourceId(1)),             // a
            Expr::Source(SourceId(2)),             // b
            Expr::Mul(vec![ExprId(1), ExprId(2)]), // Mul(a, b)
            Expr::Add(vec![ExprId(0), ExprId(3)]), // Add(w0, Mul)
        ];
        let layer = testdag::layer(sources, exprs, vec![testdag::root(ExprId(4))]);
        let cross = HashMap::new();
        let v = view(&layer, &cross);

        let table = crate::oracle::SiteTable::enumerate(&v);
        let mut priorities = std::collections::HashMap::new();
        for s in &table.sites {
            if s.path.root == RootId(0) && s.admissible {
                if s.value == ExprId(1) { priorities.insert(crate::oracle::path_key(&s.path), 1); }
                if s.value == ExprId(2) { priorities.insert(crate::oracle::path_key(&s.path), 9); }
            }
        }
        let oracle = crate::oracle::MapOracle { priorities };
        let out = flatten_budgeted(&v, &oracle, Some(1));

        // The in-flight operand `a` must never be evicted while its `Cached`
        // read is pending: no Evict may sit between its CacheLoad and a later
        // Cached read of it. The structural checker captures exactly that.
        assert_cache_reads_live(&out.program);

        // And the emitted program must still evaluate bit-exact.
        let r = crate::resolvers::HashResolvers { seed: 7 };
        let rb = r.bundle();
        for row in [0usize, 1] {
            let got = crate::ir::interpret(&out.program, &layer, row, &rb);
            let want = cs::gkr_compiler::dag_ir::eval::eval_layer_root(&layer, RootId(0), row, &rb);
            assert_eq!(got[&RootId(0)], want, "row {row}");
        }
    }
}
