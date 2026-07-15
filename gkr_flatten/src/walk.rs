//! The demand-driven walker (spec §2): flattens one `DagLayer`'s roots into
//! a single `LinearIR` `Program` under an `Oracle`, emitting ops so that on
//! return from `emit(e, ..)` the accumulator holds `value(e)` — exactly once
//! per node OCCURRENCE in the all-recompute tree (never per distinct
//! `ExprId`; a shared sub-expr is recomputed at every site that reaches it).
//!
//! M1 ships only `NeutralOracle` (identity root order, never caches): the
//! walker's residency check always misses, so every non-leaf node is either
//! folded straight into the accumulator (leaves, fma-able Muls) or fully
//! recomputed via the stash-discipline general branch. `maybe_cache` is
//! wired (the hook is invoked with a live `SitePath`) but is a no-op under
//! `NeutralOracle`'s `None`-everywhere `keep_priority` — this is exactly
//! what makes the neutral walker's stats compare 1:1 against
//! `analysis::size_layer`'s all-recompute DP (`neutral_stats_match_dp`).

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{Expr, ExprId, SourceId};

use crate::dag::{LayerView, LeafClass, NodeKind};
use crate::ir::{Op, Operand, Program, SlotId};
use crate::oracle::{Oracle, SitePath, SiteStep};
use crate::su;

/// Aggregate cost counters produced by one `flatten()` call.
///
/// - `traffic`: width-weighted Dram-leaf TOUCHES (every `Load`/`Add`/`Mul`/
///   `Fma` operand that is a Dram leaf charges its width; Free leaves charge
///   0). Under `NeutralOracle`, equals `analysis::SizingReport::ceiling`.
/// - `instrs`: total `Op`s emitted.
/// - `peak`: max concurrent stash lanes. Under `NeutralOracle`, equals
///   `su::cone_peak`/`analysis::SizingReport::peak` — the load-bearing
///   invariant this walker exists to realize.
/// - `sites_visited`: total node OCCURRENCES processed (every recursed
///   compound, every streamed leaf operand, every fused-fma Mul child PLUS
///   its two operands — see `Walker::emit`). Under `NeutralOracle`, equals
///   `analysis::SizingReport::sites`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct WalkStats {
    pub traffic: u64,
    pub instrs: u64,
    pub peak: u32,
    pub sites_visited: u64,
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
    let mut walker = Walker {
        view,
        oracle,
        program: Program { ops: Vec::new(), width_of_slot: Default::default() },
        stats: WalkStats::default(),
        live_stash_lanes: 0,
        budget_hint: None,
    };
    for root_id in oracle.root_order(view.layer) {
        let root_expr = view.layer.roots[root_id.0 as usize].expr;
        let mut path = SitePath { root: root_id, steps: Vec::new() };
        walker.emit(root_expr, &mut path, 0);
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
    /// Sum of `width_of_slot` over currently-live (stashed, not yet
    /// consumed) slots — the running value whose max is `stats.peak`.
    live_stash_lanes: u32,
    /// M2 feasibility tripwire (spec §5): when set, every `charge_stash`
    /// asserts `live_stash_lanes <= budget_hint`. Unset (`None`) in M1 —
    /// nothing enforces a cell budget yet.
    budget_hint: Option<u32>,
}

impl<'v, 'o> Walker<'v, 'o> {
    /// Emits ops so that, on return, `acc` holds `value(e)`. `depth` doubles
    /// as the stack-disciplined `SlotId` allocator: a stash at recursion
    /// depth `d` always uses `SlotId(d)`, and the LIFO stash/consume nesting
    /// guarantees no two simultaneously-live slots ever share a depth.
    fn emit(&mut self, e: ExprId, path: &mut SitePath, depth: u32) {
        self.stats.sites_visited += 1;
        match self.view.kind(e) {
            NodeKind::Leaf(class) => {
                self.charge_leaf(class);
                self.push(Op::Load(Operand::Leaf(self.source_id(e))));
            }
            NodeKind::Add(children) | NodeKind::Mul(children) => {
                let is_add = matches!(self.view.kind(e), NodeKind::Add(_));
                let ordered = self.order_children(children);
                let mut first = true;
                for (dup, child) in ordered {
                    path.steps.push(SiteStep { child, dup });
                    if is_add && self.is_fma_candidate(child) {
                        // 2-arity Mul under Add, both operands ready (M1:
                        // leaf): the product streams into acc — no temp,
                        // no stash (spec §2 Rev 1).
                        let (a, b) = self.mul_operands(child);
                        self.stats.sites_visited += 1; // the fma Mul child's own occurrence
                        let oa = self.ready_operand(a);
                        let ob = self.ready_operand(b);
                        if first {
                            self.push(Op::Load(oa));
                            self.push(Op::Mul(ob));
                        } else {
                            self.push(Op::Fma(oa, ob));
                        }
                    } else if self.is_ready(child) {
                        // leaf (M1) or resident (M2)
                        let op = self.ready_operand(child);
                        self.push(if first {
                            Op::Load(op)
                        } else if is_add {
                            Op::Add(op)
                        } else {
                            Op::Mul(op)
                        });
                    } else {
                        // Non-ready compound child: stash acc (unless
                        // first), recurse, combine.
                        if !first {
                            let slot = SlotId(depth);
                            self.push(Op::Stash(slot));
                            let w = self.charge_stash(e, depth);
                            self.emit(child, path, depth + 1);
                            self.push(if is_add {
                                Op::Add(Operand::Stashed(slot))
                            } else {
                                Op::Mul(Operand::Stashed(slot))
                            });
                            self.live_stash_lanes -= w;
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

    /// M1 readiness: a leaf. (M2 will extend this to "leaf or resident in
    /// the simulated cache.")
    fn is_ready(&self, e: ExprId) -> bool {
        matches!(self.view.kind(e), NodeKind::Leaf(_))
    }

    /// `child` is a 2-arity `Mul` with BOTH operands ready (M1: leaf) — spec
    /// §2 Rev 1's fma-recognition rule.
    ///
    /// Checked directly via `is_ready` on the two operands rather than by
    /// calling `su::streamable(child)` (which would be recursively true for
    /// the same M1 shapes, since `streamable`'s own Mul case is defined the
    /// same way) — `is_ready`-on-operands is the one that is actually sound
    /// against `ready_operand`'s contract: an `Operand` can only name a
    /// leaf/cached/stashed value, never an unevaluated sub-expression, so a
    /// hypothetical nested streamable-Mul operand (which `su::streamable`
    /// would also call "streamable") could never legally become an `Fma`
    /// operand this way. The two checks agree on every shape these M1
    /// fixtures exercise.
    fn is_fma_candidate(&self, e: ExprId) -> bool {
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

    /// Resolves a ready (M1: leaf) expr straight to an `Operand`, charging
    /// its Dram traffic and counting its site occurrence. Every call site is
    /// exactly one node occurrence that never recurses through `emit`.
    fn ready_operand(&mut self, e: ExprId) -> Operand {
        match self.view.kind(e) {
            NodeKind::Leaf(class) => {
                self.charge_leaf(class);
                self.stats.sites_visited += 1;
                Operand::Leaf(self.source_id(e))
            }
            _ => unreachable!(
                "gkr_flatten: ready_operand called on non-ready expr {e:?} (caller must check \
                 is_ready first)"
            ),
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
    /// recorded in `Program.width_of_slot[depth]` and added to the running
    /// `live_stash_lanes`, whose running max is `stats.peak` (must equal
    /// `su::cone_peak` — the load-bearing invariant). Returns the charged
    /// width so the caller can free it again once the slot is consumed.
    fn charge_stash(&mut self, e: ExprId, depth: u32) -> u32 {
        let w = self.view.width(e);
        self.program.width_of_slot.insert(depth, w);
        self.live_stash_lanes += w;
        self.stats.peak = self.stats.peak.max(self.live_stash_lanes);
        if let Some(budget) = self.budget_hint {
            debug_assert!(
                self.live_stash_lanes <= budget,
                "gkr_flatten: live stash lanes {} exceed budget hint {} at expr {e:?}, depth {depth}",
                self.live_stash_lanes,
                budget
            );
        }
        w
    }

    /// M2 caching hook: consults `oracle.keep_priority(path)` for `e`'s
    /// site. A no-op under `NeutralOracle` (always `None`) — M2 will act on
    /// `Some(priority)` by admitting `e` into the simulated cache
    /// (`Op::CacheStore`) and scheduling its eventual `Op::Evict`.
    fn maybe_cache(&mut self, e: ExprId, path: &SitePath) {
        let _ = e;
        let _ = self.oracle.keep_priority(path);
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
    /// (`tiny_fma_layer`), a fan-in-shared layer (`shared_diamond`), and a
    /// layer with a non-degenerate root-dependent peak (`mixed_peak_layer`).
    #[test]
    fn neutral_stats_match_dp() {
        for layer in [tiny_fma_layer(), shared_diamond(), mixed_peak_layer()] {
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

        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let layer = &dag.layers[0];
        let v = LayerView::new(layer, &cross, None);
        let out = flatten(&v, &NeutralOracle);

        let d = DetResolver;
        let r = Resolvers { read: &d, lookup: &d, virtual_setup: &d, challenge: &d };
        for row in [0usize, 1, 7] {
            let got = crate::ir::interpret(&out.program, layer, row, &r);
            for (i, root) in layer.roots.iter().enumerate() {
                let root_id = RootId(i as u32);
                let expected = eval_layer_root(layer, root_id, row, &r);
                assert_eq!(
                    got[&root_id], expected,
                    "root {i} (expr {:?}) mismatched reference eval at row {row}",
                    root.expr
                );
            }
        }
    }
}
