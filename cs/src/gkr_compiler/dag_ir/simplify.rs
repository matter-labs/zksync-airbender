//! Value-preserving DAG simplification (spec:
//! .agents/specs/2026-07-04-gkr-dag-simplify-design.md). Memoized bottom-up
//! rebuild into a fresh unflattened arena; reachability and remapping include
//! the `SourceKind::LookupValue::query` edge. Fenced = `resolutions` keys.

use std::collections::{BTreeMap, HashMap, HashSet};

use super::{
    field_infer::source_field, ArenaBuilder, DagCircuit, DagLayer, Expr, ExprId, FieldKind, Root,
    SourceKind,
};

/// BabyBear field modulus (matches `eval.rs`'s concrete field).
const P: u64 = 2013265921;

/// BabyBear addition mod `P`.
fn fold_add(a: u32, b: u32) -> u32 {
    ((a as u64 + b as u64) % P) as u32
}

/// BabyBear multiplication mod `P`.
fn fold_mul(a: u32, b: u32) -> u32 {
    ((a as u64 * b as u64) % P) as u32
}

pub fn simplify_circuit(dag: DagCircuit) -> DagCircuit {
    DagCircuit {
        layers: dag.layers.iter().map(simplify_layer_fixpoint).collect(),
        globals: dag.globals,
    }
}

/// Iterate `simplify_layer` to a fixpoint: each pass can expose a further
/// rewrite (e.g. a flatten that lands two constants adjacent, enabling another
/// const-fold pass), so a single call is not guaranteed maximally simplified.
/// `DagLayer: PartialEq` covers `sources`, `exprs`, `roots`, and
/// `resolutions`, so equality is a genuine fixpoint check. The `iters < 16`
/// guard catches a runaway (non-terminating or oscillating) rewrite rather
/// than looping forever.
pub(crate) fn simplify_layer_fixpoint(layer: &DagLayer) -> DagLayer {
    let mut prev = layer.clone();
    let mut iters = 0;
    loop {
        let next = simplify_layer(&prev);
        iters += 1;
        assert!(
            iters < 16,
            "simplify_layer_fixpoint: exceeded 16 iterations without converging"
        );
        if next == prev {
            return next;
        }
        prev = next;
    }
}

/// Consumer-edge fan-out over root-reachable nodes only: per-edge counts
/// (repeats count) for Add/Mul parent→child edges, each `Root.expr`
/// occurrence (once per root), and each reachable `LookupValue.query` edge.
/// Reachability traverses children AND query edges; dead arena nodes never
/// appear in the result.
pub(crate) fn fan_out(layer: &DagLayer) -> HashMap<ExprId, usize> {
    let mut counts: HashMap<ExprId, usize> = HashMap::new();
    let mut seen: HashSet<ExprId> = HashSet::new();
    let mut worklist: Vec<ExprId> = Vec::new();
    for root in &layer.roots {
        *counts.entry(root.expr).or_insert(0) += 1;
        if seen.insert(root.expr) {
            worklist.push(root.expr);
        }
    }
    while let Some(id) = worklist.pop() {
        match &layer.exprs[id.0 as usize] {
            Expr::Add(children) | Expr::Mul(children) => {
                for &c in children {
                    *counts.entry(c).or_insert(0) += 1;
                    if seen.insert(c) {
                        worklist.push(c);
                    }
                }
            }
            Expr::Source(sid) => {
                if let SourceKind::LookupValue { query, .. } = &layer.sources[sid.0 as usize].kind {
                    *counts.entry(*query).or_insert(0) += 1;
                    if seen.insert(*query) {
                        worklist.push(*query);
                    }
                }
            }
        }
    }
    counts
}

pub(crate) fn simplify_layer(layer: &DagLayer) -> DagLayer {
    let mut rb = Rebuild {
        arena: ArenaBuilder::with_flatten(false),
        map: HashMap::new(),
        layer,
        // Fence set = the layer's own `resolutions` keys (the arena's private
        // fence set does not survive lowering). No rewrites read this yet
        // (Task 5); it is populated here so the field exists on `Rebuild`
        // ahead of that use.
        fenced: layer.resolutions.keys().copied().collect(),
        fan_out: fan_out(layer),
        provably_base_memo: HashMap::new(),
    };
    let roots: Vec<Root> = layer
        .roots
        .iter()
        .map(|r| Root {
            expr: rb.rebuild(r.expr),
            materialize: r.materialize.clone(),
            claim: r.claim.clone(),
        })
        .collect();
    let mut resolutions = BTreeMap::new();
    for (old, strat) in &layer.resolutions {
        // Fenced keys must be root-reachable to survive rewrites; if a key
        // is NOT in the memo map, its subtree was never rebuilt (dead
        // resolution) — drop it rather than panicking.
        let Some(&new) = rb.map.get(old) else {
            continue;
        };
        if let Some(existing) = resolutions.insert(new, strat.clone()) {
            assert_eq!(
                &existing, strat,
                "dag_ir simplify: resolution CSE collision at {:?}",
                new
            );
        }
    }
    DagLayer {
        sources: rb.arena.sources().to_vec(),
        exprs: rb.arena.exprs().to_vec(),
        roots,
        batching: layer.batching.clone(),
        resolutions,
    }
}

struct Rebuild<'a> {
    arena: ArenaBuilder,
    map: HashMap<ExprId, ExprId>,
    layer: &'a DagLayer,
    /// Fenced (resolution-keyed) old `ExprId`s: rewrites must not cross a
    /// resolution-keyed fold-leaf boundary (self-fence guard in Add/Mul, plus
    /// later tasks' const-fold/collapse rewrites).
    fenced: HashSet<ExprId>,
    /// Consumer-edge counts over the OLD layer, used to decide fan-out==1
    /// flatten in the Add/Mul arms below.
    fan_out: HashMap<ExprId, usize>,
    /// Memoized `provably_base` results, keyed by OLD `ExprId`.
    provably_base_memo: HashMap<ExprId, bool>,
}

/// Bottom-up, memoized: is the subtree at `old` (in `layer`) guaranteed to be
/// Base-field-valued? A `Read{LayerOutput|CacheOutput}` source is `Err(_)`
/// from `source_field` — NOT provably base (conservative). `Challenge`
/// sources are `Ok(Ext)` — NOT provably base. Add/Mul are provably base iff
/// every child is. Shared between `simplify`'s annihilator/collapse rewrites
/// and `validate_simplified`'s Mul-retains-Constant(0) exception, so both
/// sides agree on what "provably Base" means.
pub(crate) fn provably_base(
    layer: &DagLayer,
    memo: &mut HashMap<ExprId, bool>,
    old: ExprId,
) -> bool {
    if let Some(&v) = memo.get(&old) {
        return v;
    }
    let result = match &layer.exprs[old.0 as usize] {
        Expr::Source(sid) => source_field(&layer.sources[sid.0 as usize].kind)
            .map(|f| f == FieldKind::Base)
            .unwrap_or(false),
        Expr::Add(children) | Expr::Mul(children) => {
            children.iter().all(|&c| provably_base(layer, memo, c))
        }
    };
    memo.insert(old, result);
    result
}

impl Rebuild<'_> {
    fn provably_base(&mut self, old: ExprId) -> bool {
        provably_base(self.layer, &mut self.provably_base_memo, old)
    }

    /// If the rebuilt (NEW) node `new` is `Source(Constant { value })`, return
    /// `value`.
    fn as_const(&self, new: ExprId) -> Option<u32> {
        match &self.arena.exprs()[new.0 as usize] {
            Expr::Source(sid) => match &self.arena.sources()[sid.0 as usize].kind {
                SourceKind::Constant { value } => Some(*value),
                _ => None,
            },
            _ => None,
        }
    }

    /// Intern a fresh `Constant` source expr in the NEW arena.
    fn const_expr(&mut self, v: u32) -> ExprId {
        let s = self.arena.intern_source(SourceKind::Constant { value: v });
        self.arena.source_expr(s)
    }

    fn rebuild(&mut self, old: ExprId) -> ExprId {
        if let Some(&new) = self.map.get(&old) {
            return new;
        }
        let new = match self.layer.exprs[old.0 as usize].clone() {
            Expr::Source(sid) => {
                let kind = match self.layer.sources[sid.0 as usize].kind.clone() {
                    SourceKind::LookupValue {
                        kind,
                        set_index,
                        query,
                    } => {
                        let query = self.rebuild(query);
                        SourceKind::LookupValue {
                            kind,
                            set_index,
                            query,
                        }
                    }
                    other => other,
                };
                let sid = self.arena.intern_source(kind);
                self.arena.source_expr(sid)
            }
            Expr::Add(children) => {
                // SELF-FENCE GUARD: a fenced node skips all rewrites (later
                // tasks add more here) — rebuild children only, no flatten.
                if self.fenced.contains(&old) {
                    let ch: Vec<ExprId> = children.iter().map(|&c| self.rebuild(c)).collect();
                    self.arena.add(ch)
                } else {
                    let mut flat: Vec<ExprId> = Vec::with_capacity(children.len());
                    for &c in &children {
                        let inline = matches!(self.layer.exprs[c.0 as usize], Expr::Add(_))
                            && self.fan_out[&c] == 1
                            && !self.fenced.contains(&c);
                        if inline {
                            if let Expr::Add(gc) = self.layer.exprs[c.0 as usize].clone() {
                                // Rebuild grandchildren directly; the child
                                // node is DCE'd (never inserted into the new
                                // arena).
                                flat.extend(gc.iter().map(|&g| self.rebuild(g)));
                            }
                        } else {
                            flat.push(self.rebuild(c));
                        }
                    }
                    // const-fold: merge all Constant operands
                    let mut acc: Option<u32> = None;
                    let mut rest: Vec<ExprId> = Vec::with_capacity(flat.len());
                    for id in flat {
                        match self.as_const(id) {
                            Some(v) => acc = Some(match acc {
                                Some(a) => fold_add(a, v),
                                None => v,
                            }),
                            None => rest.push(id),
                        }
                    }
                    // identity: drop a folded 0 when other operands remain
                    match acc {
                        Some(0) if !rest.is_empty() => {}
                        Some(v) => rest.push(self.const_expr(v)),
                        None => {}
                    }
                    // collapse (Add unit = 0)
                    match rest.len() {
                        0 => {
                            let v = acc.unwrap_or(0);
                            if self.provably_base(old) {
                                self.const_expr(v)
                            } else {
                                let c = self.const_expr(v);
                                self.arena.add(vec![c])
                            }
                        }
                        1 => {
                            // All-constant fold implies provably-base today; assert protects
                            // against future as_const/source_field drift.
                            debug_assert!(self.as_const(rest[0]).is_none() || self.provably_base(old),
                                "constant replacement must be provably base");
                            rest[0]
                        }
                        _ => self.arena.add(rest),
                    }
                }
            }
            Expr::Mul(children) => {
                if self.fenced.contains(&old) {
                    let ch: Vec<ExprId> = children.iter().map(|&c| self.rebuild(c)).collect();
                    self.arena.mul(ch)
                } else {
                    let mut flat: Vec<ExprId> = Vec::with_capacity(children.len());
                    for &c in &children {
                        let inline = matches!(self.layer.exprs[c.0 as usize], Expr::Mul(_))
                            && self.fan_out[&c] == 1
                            && !self.fenced.contains(&c);
                        if inline {
                            if let Expr::Mul(gc) = self.layer.exprs[c.0 as usize].clone() {
                                flat.extend(gc.iter().map(|&g| self.rebuild(g)));
                            }
                        } else {
                            flat.push(self.rebuild(c));
                        }
                    }
                    // const-fold: merge all Constant operands
                    let mut acc: Option<u32> = None;
                    let mut rest: Vec<ExprId> = Vec::with_capacity(flat.len());
                    for id in flat {
                        match self.as_const(id) {
                            Some(v) => acc = Some(match acc {
                                Some(a) => fold_mul(a, v),
                                None => v,
                            }),
                            None => rest.push(id),
                        }
                    }
                    // annihilator: folded const 0 AND the OLD node is provably
                    // base → the whole product is Constant(0). Otherwise (not
                    // provably base — e.g. an Ext factor present) keep the
                    // folded Constant(0) as an operand: replacing an Ext-valued
                    // node with a Base constant would break field preservation.
                    if acc == Some(0) && self.provably_base(old) {
                        self.const_expr(0)
                    } else {
                        // identity: drop a folded 1 when other operands remain
                        match acc {
                            Some(1) if !rest.is_empty() => {}
                            Some(v) => rest.push(self.const_expr(v)),
                            None => {}
                        }
                        // collapse (Mul unit = 1)
                        match rest.len() {
                            0 => {
                                let v = acc.unwrap_or(1);
                                if self.provably_base(old) {
                                    self.const_expr(v)
                                } else {
                                    let c = self.const_expr(v);
                                    self.arena.mul(vec![c])
                                }
                            }
                            1 => {
                                // All-constant fold implies provably-base today; assert protects
                                // against future as_const/source_field drift.
                                debug_assert!(self.as_const(rest[0]).is_none() || self.provably_base(old),
                                    "constant replacement must be provably base");
                                rest[0]
                            }
                            _ => self.arena.mul(rest),
                        }
                    }
                }
            }
        };
        self.map.insert(old, new);
        new
    }
}

// ── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr_compiler::dag_ir::{
        validate_simplified, BatchingOrder, ChallengeKey, ChallengePower, ChallengeRef, ClaimInfo,
        DagCircuit, DagGlobals, LookupValueKind, ReadPlace, ResolutionStrategy, RootGroup,
        RootOrigin, RootSlot, SinkInfo, SinkKind,
    };

    /// Build a `Constant` source expr with the given BabyBear value.
    fn const_expr(a: &mut ArenaBuilder, value: u32) -> ExprId {
        let s = a.intern_source(SourceKind::Constant { value });
        a.source_expr(s)
    }

    /// Build a `Challenge` source expr (Ext field) — used to test the
    /// field-preservation guard on the annihilator/collapse rewrites.
    fn challenge_expr(a: &mut ArenaBuilder) -> ExprId {
        let s = a.intern_source(SourceKind::Challenge {
            reference: ChallengeRef {
                key: ChallengeKey::LookupAdditive,
                power: ChallengePower::One,
            },
        });
        a.source_expr(s)
    }

    /// Build a `Read{LayerOutput}` source expr — `source_field` returns `Err`
    /// for this place, so `provably_base` is `false` (NOT provably base).
    fn read_like(a: &mut ArenaBuilder, offset: usize) -> ExprId {
        let s = a.intern_source(SourceKind::Read {
            place: ReadPlace::LayerOutput { layer: 0, offset },
        });
        a.source_expr(s)
    }

    /// Wrap a single `DagLayer` in a minimal `DagCircuit`.
    fn circuit_of(layer: DagLayer) -> DagCircuit {
        DagCircuit {
            layers: vec![layer],
            globals: Default::default(),
        }
    }

    /// Hand-build a `DagLayer` from an in-progress `ArenaBuilder` plus roots and
    /// resolutions; `batching` is irrelevant to these tests so it's left empty.
    fn layer_of(
        arena: ArenaBuilder,
        roots: Vec<Root>,
        resolutions: BTreeMap<ExprId, ResolutionStrategy>,
    ) -> DagLayer {
        DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots,
            batching: BatchingOrder { roots: vec![] },
            resolutions,
        }
    }

    /// DCE: an expr unreachable from any root/query edge does not survive the rebuild.
    #[test]
    fn rebuild_drops_unreachable() {
        let mut a = ArenaBuilder::with_flatten(false);
        let c1 = {
            let s = a.intern_source(SourceKind::Constant { value: 7 });
            a.source_expr(s)
        };
        let dead = {
            let s = a.intern_source(SourceKind::Constant { value: 9 });
            a.source_expr(s)
        };
        let _ = a.add(vec![dead, dead]); // unreachable
        let root = Root {
            expr: c1,
            materialize: None,
            claim: None,
        };
        let layer = layer_of(a, vec![root], BTreeMap::new());
        let out = simplify_layer(&layer);
        assert_eq!(out.exprs.len(), 1, "only the root constant survives: {:?}", out.exprs);
        assert_eq!(out.roots.len(), 1);
    }

    /// Three distinct `Read` sources standing in for read-like leaves. Task 4
    /// added const-folding, so these must NOT be `Constant` sources (folding
    /// would collapse the flatten/CSE fixtures below into a single constant).
    fn three_read_like_sources(a: &mut ArenaBuilder) -> (ExprId, ExprId, ExprId) {
        let mut mk = |offset: usize| {
            let s = a.intern_source(SourceKind::Read {
                place: ReadPlace::LayerOutput { layer: 0, offset },
            });
            a.source_expr(s)
        };
        (mk(101), mk(102), mk(103))
    }

    /// fan-out==1 nested Add flattens; the association-invariant dup merges via CSE.
    #[test]
    fn flatten_fanout1_and_cse_associations() {
        let mut a = ArenaBuilder::with_flatten(false);
        let (x, y, z) = three_read_like_sources(&mut a);
        let xy = a.add(vec![x, y]);
        let n1 = a.add(vec![xy, z]); // Add(Add(x,y), z)
        let yz = a.add(vec![y, z]);
        let n2 = a.add(vec![x, yz]); // Add(x, Add(y,z))
        let roots = vec![
            Root {
                expr: n1,
                materialize: None,
                claim: None,
            },
            Root {
                expr: n2,
                materialize: None,
                claim: None,
            },
        ];
        let layer = layer_of(a, roots, BTreeMap::new());
        let out = simplify_layer(&layer);
        assert_eq!(
            out.roots[0].expr, out.roots[1].expr,
            "both associations flatten to Add(x,y,z) and CSE-merge"
        );
    }

    /// fan-out>=2 nested Add is PRESERVED (sharing wins over flatten).
    #[test]
    fn shared_nested_add_is_preserved() {
        let mut a = ArenaBuilder::with_flatten(false);
        let (x, y, z) = three_read_like_sources(&mut a);
        let xy = a.add(vec![x, y]);
        let n1 = a.add(vec![xy, z]);
        let n2 = a.mul(vec![xy, xy]); // second+third consumers of xy
        let roots = vec![
            Root {
                expr: n1,
                materialize: None,
                claim: None,
            },
            Root {
                expr: n2,
                materialize: None,
                claim: None,
            },
        ];
        let layer = layer_of(a, roots, BTreeMap::new());
        let out = simplify_layer(&layer);
        match &out.exprs[out.roots[0].expr.0 as usize] {
            Expr::Add(ops) => assert_eq!(ops.len(), 2, "Add(xy, z) must keep nested xy, got {:?}", ops),
            other => panic!("expected Add, got {:?}", other),
        }
    }

    /// A fenced (resolution-keyed) Add child is never flattened even at fan-out 1.
    #[test]
    fn fenced_child_never_flattens() {
        let mut a = ArenaBuilder::with_flatten(false);
        let (x, y, z) = three_read_like_sources(&mut a);
        let leaf = a.add(vec![y, z]);
        let top = a.add(vec![x, leaf]);
        let mut res = BTreeMap::new();
        res.insert(leaf, ResolutionStrategy::PeekSetup);
        let layer = layer_of(
            a,
            vec![Root {
                expr: top,
                materialize: None,
                claim: None,
            }],
            res,
        );
        let out = simplify_layer(&layer);
        match &out.exprs[out.roots[0].expr.0 as usize] {
            Expr::Add(ops) => assert_eq!(ops.len(), 2, "fenced leaf survives as one operand"),
            other => panic!("expected Add, got {:?}", other),
        }
        assert_eq!(out.resolutions.len(), 1, "resolution key remapped, not dropped");
    }

    /// The fenced node ITSELF skips rewrites: a same-op fan-out-1 child INSIDE a
    /// fenced Add must not be flattened (spec §3: fenced = child-rebuild only).
    #[test]
    fn fenced_node_own_children_not_flattened() {
        let mut a = ArenaBuilder::with_flatten(false);
        let (x, y, z) = three_read_like_sources(&mut a);
        let inner = a.add(vec![y, z]); // fan-out 1 — would flatten if unfenced
        let leaf = a.add(vec![x, inner]); // the fenced fold leaf
        let mut res = BTreeMap::new();
        res.insert(leaf, ResolutionStrategy::PeekSetup);
        let layer = layer_of(
            a,
            vec![Root {
                expr: leaf,
                materialize: None,
                claim: None,
            }],
            res,
        );
        let out = simplify_layer(&layer);
        match &out.exprs[out.roots[0].expr.0 as usize] {
            Expr::Add(ops) => assert_eq!(ops.len(), 2, "fenced node keeps nested child, got {:?}", ops),
            other => panic!("expected fenced Add to survive, got {:?}", other),
        }
    }

    /// A `LookupValue.query` reference counts toward fan-out: a nested Add consumed
    /// once as a normal child and once as a query has fan-out 2 → must NOT flatten.
    #[test]
    fn query_edge_counts_toward_fanout() {
        let mut a = ArenaBuilder::with_flatten(false);
        let (x, y, z) = three_read_like_sources(&mut a);
        let shared = a.add(vec![y, z]);
        let top = a.add(vec![x, shared]); // consumer 1 (would flatten alone)
        let lv = {
            let s = a.intern_source(SourceKind::LookupValue {
                kind: LookupValueKind::RangeCheck16Index,
                set_index: 0,
                query: shared, // consumer 2
            });
            a.source_expr(s)
        };
        let roots = vec![
            Root {
                expr: top,
                materialize: None,
                claim: None,
            },
            Root {
                expr: lv,
                materialize: None,
                claim: None,
            },
        ];
        let layer = layer_of(a, roots, BTreeMap::new());
        let out = simplify_layer(&layer);
        match &out.exprs[out.roots[0].expr.0 as usize] {
            Expr::Add(ops) => assert_eq!(ops.len(), 2, "query edge must keep fan-out at 2, got {:?}", ops),
            other => panic!("expected Add, got {:?}", other),
        }
    }

    /// Sign-pair cancellation = flatten + const-fold + identity: -1 * -1 * x → x.
    #[test]
    fn double_negation_cancels() {
        let mut a = ArenaBuilder::with_flatten(false);
        let neg1 = const_expr(&mut a, 2013265920); // p-1
        let x = read_like(&mut a, 101); // NOT provably base is fine here
        let inner = a.mul(vec![neg1, x]);
        let outer = a.mul(vec![neg1, inner]); // inner fan-out 1 → flattens
        let layer = layer_of(
            a,
            vec![Root {
                expr: outer,
                materialize: None,
                claim: None,
            }],
            BTreeMap::new(),
        );
        let out = simplify_layer_fixpoint(&layer); // Task 5 wrapper; until then two manual passes
        assert!(
            matches!(&out.exprs[out.roots[0].expr.0 as usize], Expr::Source(_)),
            "Mul(-1, Mul(-1, x)) must collapse to x, got {:?}",
            out.exprs
        );
    }

    /// Base annihilator: Mul(0, base) → Constant(0).
    #[test]
    fn base_zero_annihilates() {
        let mut a = ArenaBuilder::with_flatten(false);
        let zero = const_expr(&mut a, 0);
        let five = const_expr(&mut a, 5);
        let m = a.mul(vec![zero, five]);
        let layer = layer_of(
            a,
            vec![Root {
                expr: m,
                materialize: None,
                claim: None,
            }],
            BTreeMap::new(),
        );
        let out = simplify_layer(&layer);
        match &out.exprs[out.roots[0].expr.0 as usize] {
            Expr::Source(sid) => assert_eq!(
                out.sources[sid.0 as usize].kind,
                SourceKind::Constant { value: 0 },
                "Mul(0, 5) must collapse to Constant(0)"
            ),
            other => panic!("expected a single Constant(0) source expr, got {:?}", other),
        }
    }

    /// Ext-guard: Mul(0, challenge) is NOT rewritten to a constant.
    #[test]
    fn ext_zero_product_is_suppressed() {
        let mut a = ArenaBuilder::with_flatten(false);
        let zero = const_expr(&mut a, 0);
        let ch = challenge_expr(&mut a); // SourceKind::Challenge → Ext
        let m = a.mul(vec![zero, ch]);
        let layer = layer_of(
            a,
            vec![Root {
                expr: m,
                materialize: None,
                claim: None,
            }],
            BTreeMap::new(),
        );
        let out = simplify_layer(&layer);
        match &out.exprs[out.roots[0].expr.0 as usize] {
            Expr::Mul(ops) => assert_eq!(ops.len(), 2, "Ext zero product must stay a Mul"),
            other => panic!("field-preservation violated: {:?}", other),
        }
    }

    /// Identity drops + collapse: Add(0, x) → x; Mul(1, x) → x; constants fold pairwise.
    #[test]
    fn identities_and_folding() {
        let mut a = ArenaBuilder::with_flatten(false);
        // Add(const 2, const 3, x) → Add(const 5, x)
        let c2 = const_expr(&mut a, 2);
        let c3 = const_expr(&mut a, 3);
        let x = read_like(&mut a, 101);
        let add_node = a.add(vec![c2, c3, x]);

        // Mul(1, x) → x
        let one = const_expr(&mut a, 1);
        let y = read_like(&mut a, 102);
        let mul_node = a.mul(vec![one, y]);

        // Add(0, x) → x
        let zero = const_expr(&mut a, 0);
        let z = read_like(&mut a, 103);
        let add_zero_node = a.add(vec![zero, z]);

        let layer = layer_of(
            a,
            vec![
                Root {
                    expr: add_node,
                    materialize: None,
                    claim: None,
                },
                Root {
                    expr: mul_node,
                    materialize: None,
                    claim: None,
                },
                Root {
                    expr: add_zero_node,
                    materialize: None,
                    claim: None,
                },
            ],
            BTreeMap::new(),
        );
        let out = simplify_layer(&layer);

        match &out.exprs[out.roots[0].expr.0 as usize] {
            Expr::Add(ops) => {
                assert_eq!(ops.len(), 2, "Add(2,3,x) → Add(5, x), got {:?}", ops);
                let has_five = ops.iter().any(|&id| match &out.exprs[id.0 as usize] {
                    Expr::Source(sid) => {
                        out.sources[sid.0 as usize].kind == SourceKind::Constant { value: 5 }
                    }
                    _ => false,
                });
                assert!(has_five, "folded constant must be 5, got {:?}", ops);
            }
            other => panic!("expected Add, got {:?}", other),
        }

        // Both Mul(1,y) and Add(0,z) collapse to their respective non-identity operands.
        // Since y and z are distinct nodes (different read offsets), they collapse to distinct IDs.
        match &out.exprs[out.roots[1].expr.0 as usize] {
            Expr::Source(sid) => assert!(
                matches!(&out.sources[sid.0 as usize].kind, SourceKind::Read { .. }),
                "Mul(1,y) must collapse to y (a Read source)"
            ),
            other => panic!("expected Mul(1,y) to collapse to a source, got {:?}", other),
        }
        match &out.exprs[out.roots[2].expr.0 as usize] {
            Expr::Source(sid) => assert!(
                matches!(&out.sources[sid.0 as usize].kind, SourceKind::Read { .. }),
                "Add(0,z) must collapse to z (a Read source)"
            ),
            other => panic!("expected Add(0,z) to collapse to a source, got {:?}", other),
        }
    }

    /// LookupValue.query is remapped AND keeps its subtree alive.
    #[test]
    fn lookup_query_is_remapped_and_reachable() {
        let mut a = ArenaBuilder::with_flatten(false);
        let q = {
            let s = a.intern_source(SourceKind::Constant { value: 3 });
            a.source_expr(s)
        };
        let lv = {
            let s = a.intern_source(SourceKind::LookupValue {
                kind: LookupValueKind::RangeCheck16Index,
                set_index: 0,
                query: q,
            });
            a.source_expr(s)
        };
        let root = Root {
            expr: lv,
            materialize: None,
            claim: None,
        };
        let layer = layer_of(a, vec![root], BTreeMap::new());
        let out = simplify_layer(&layer);
        // Both the Constant source and the LookupValue source survive.
        assert_eq!(out.sources.len(), 2, "query subtree stays alive: {:?}", out.sources);
        // Find the LookupValue source in the output and follow its query edge.
        let query = out
            .sources
            .iter()
            .find_map(|s| match &s.kind {
                SourceKind::LookupValue { query, .. } => Some(*query),
                _ => None,
            })
            .expect("LookupValue survives");
        // The rebuilt query edge must point at a genuinely-rebuilt Constant(3)
        // — not a stale old ExprId copied through without rebuild(query),
        // which in this layout would self-refer to the LookupValue node.
        assert_ne!(
            query, out.roots[0].expr,
            "query must not point at the LookupValue node itself"
        );
        let sid = match &out.exprs[query.0 as usize] {
            Expr::Source(sid) => *sid,
            other => panic!("query edge must point at a Source expr, got {:?}", other),
        };
        assert_eq!(
            out.sources[sid.0 as usize].kind,
            SourceKind::Constant { value: 3 },
            "query edge points at the rebuilt constant"
        );
    }

    /// Task 5: `simplify_circuit` (via `simplify_layer_fixpoint`) drives the
    /// double-negation layer to a form that satisfies `validate_simplified`.
    #[test]
    fn fixpoint_output_validates_as_simplified() {
        let mut a = ArenaBuilder::with_flatten(false);
        let neg1 = const_expr(&mut a, 2013265920); // p-1
        let x = read_like(&mut a, 101);
        let inner = a.mul(vec![neg1, x]);
        let outer = a.mul(vec![neg1, inner]); // inner fan-out 1 → flattens
        let layer = layer_of(
            a,
            vec![Root {
                expr: outer,
                materialize: None,
                claim: Some(ClaimInfo {
                    origin: RootOrigin {
                        group: RootGroup::Gates,
                        relation_index: 0,
                        slot: RootSlot::Constraint(0),
                    },
                }),
            }],
            BTreeMap::new(),
        );
        let mut circuit = circuit_of(layer);
        circuit.layers[0].batching = BatchingOrder {
            roots: vec![super::super::RootId(0)],
        };
        let out = simplify_circuit(circuit);
        validate_simplified(&out).unwrap();
    }

    /// The field-suppression exception is part of the invariant: an Ext-valued
    /// zero product survives simplify as a Mul retaining Constant(0) and must
    /// pass `validate_simplified` (codex finding 5 — do not defer this to
    /// Task 8; the Task 7 corpus gate depends on the exception being right).
    #[test]
    fn ext_zero_product_passes_validate_simplified() {
        let mut a = ArenaBuilder::with_flatten(false);
        let zero = const_expr(&mut a, 0);
        let ch = challenge_expr(&mut a); // SourceKind::Challenge → Ext
        let m = a.mul(vec![zero, ch]);
        let layer = layer_of(
            a,
            vec![Root {
                expr: m,
                materialize: None,
                claim: Some(ClaimInfo {
                    origin: RootOrigin {
                        group: RootGroup::Gates,
                        relation_index: 0,
                        slot: RootSlot::Constraint(0),
                    },
                }),
            }],
            BTreeMap::new(),
        );
        let mut circuit = circuit_of(layer);
        circuit.layers[0].batching = BatchingOrder {
            roots: vec![super::super::RootId(0)],
        };
        let out = simplify_circuit(circuit);
        match &out.layers[0].exprs[out.layers[0].roots[0].expr.0 as usize] {
            Expr::Mul(ops) => assert_eq!(ops.len(), 2, "Ext zero product must stay a Mul"),
            other => panic!("field-preservation violated: {:?}", other),
        }
        assert!(
            super::super::validate(&out).is_ok(),
            "plain validate must accept the Ext zero-product circuit"
        );
        validate_simplified(&out).unwrap();
    }

    /// Task 8: the Ext-zero-sink variant of the field-suppression exception — a
    /// MATERIALIZED (not just claimed) Ext-field root over `Mul(0, challenge)`
    /// must also keep its `Mul` shape (spec §3 field constraint) and pass
    /// `validate_simplified`. `ext_zero_product_passes_validate_simplified`
    /// above pins the claim-root case; this pins the `SinkInfo`-materialize
    /// case (a `Scratch` sink), which exercises a different code path in
    /// `validate`/`validate_simplified` (sink field vs. claim field checks).
    #[test]
    fn ext_zero_materialized_sink_passes_validate_simplified() {
        let mut a = ArenaBuilder::with_flatten(false);
        let zero = const_expr(&mut a, 0);
        let ch = challenge_expr(&mut a); // SourceKind::Challenge → Ext
        let m = a.mul(vec![zero, ch]);
        let layer = layer_of(
            a,
            vec![Root {
                expr: m,
                materialize: Some(SinkInfo {
                    kind: SinkKind::Scratch { slot: 0 },
                    field: FieldKind::Ext,
                }),
                claim: None,
            }],
            BTreeMap::new(),
        );
        let circuit = circuit_of(layer);
        let out = simplify_circuit(circuit);
        match &out.layers[0].exprs[out.layers[0].roots[0].expr.0 as usize] {
            Expr::Mul(ops) => assert_eq!(ops.len(), 2, "Ext zero product must stay a Mul"),
            other => panic!("field-preservation violated: {:?}", other),
        }
        assert!(
            super::super::validate(&out).is_ok(),
            "plain validate must accept the Ext zero-product materialized-sink circuit"
        );
        validate_simplified(&out).unwrap();
    }
}
