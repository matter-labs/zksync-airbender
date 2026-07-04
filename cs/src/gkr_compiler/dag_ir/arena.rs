use std::collections::{HashMap, HashSet};

use crate::definitions::GKRAddress;

use super::{Expr, ExprId, SourceId, SourceInfo, SourceKind};

// ── ArenaBuilder ─────────────────────────────────────────────────────────────

/// An interning arena for DAG IR nodes.
///
/// `intern_source` deduplicates `SourceKind` values.
/// `add` / `mul` sort operands by `ExprId` (ascending), keep repeated
/// operands, and intern the canonical `Expr`. Nested same-op children are
/// flattened only under the legacy `with_flatten(true)` knob (test-support);
/// the default (`new()`) keeps them nested for the simplify pipeline.
///
/// `cache_aliases` maps each `GKRAddress::Cached` address materialized as a
/// cache value in THIS layer to the **shared `ExprId`** of that value (in-layer
/// reuse = DAG sharing). The lowering read helpers consult it via
/// [`ArenaBuilder::cache_alias`] so a same-layer cache read IS the materialized
/// value's expr — not a `Read(CacheOutput)` compatibility leaf and not a
/// separate root reference (see the `lower` module docs and the design doc's
/// "Roots" section).
pub struct ArenaBuilder {
    sources: Vec<SourceInfo>,
    source_map: HashMap<SourceKind, SourceId>,

    exprs: Vec<Expr>,
    expr_map: HashMap<Expr, ExprId>,

    cache_aliases: HashMap<GKRAddress, ExprId>,

    /// Set of `ExprId`s that `canonicalize` must NOT flatten into their parent
    /// `Add`/`Mul`. Used for multi-column fold-leaf `Add` nodes whose `ExprId`
    /// is recorded in the `resolutions` side-table; they must survive as single
    /// operands in root-reachable expressions so the validator can find them.
    fenced: HashSet<ExprId>,

    /// Controls whether `canonicalize` flattens nested same-op children.
    /// When `false` (the default via `new()`), nested children survive as
    /// operands — the unflattened shape the simplify pipeline expects.
    /// When `true` (the legacy build-time-flatten knob, test-support only),
    /// nested same-kind children are flattened into their parent.
    flatten_nested: bool,
}

impl ArenaBuilder {
    /// Default constructor: unflattened arena (`with_flatten(false)`).
    ///
    /// This is the production shape `simplify_circuit`'s fan-out-aware rewrites
    /// expect (see `lower::LowerMode::Simplified`). Build-time flattening
    /// (`with_flatten(true)`) is now a legacy knob kept for the pre-simplification
    /// reference pipeline (`lower_dag_legacy`) and tests that document it.
    pub fn new() -> Self {
        Self::with_flatten(false)
    }

    /// Create an `ArenaBuilder` with a configurable flattening behavior.
    ///
    /// When `flatten_nested` is `false` (the default via `new()`), nested
    /// children survive as operands, allowing fan-out-aware simplification
    /// passes to work on the unflattened DAG. When `true` (the legacy
    /// build-time-flatten knob, test-support only — see `lower_dag_legacy`),
    /// nested same-op children are flattened into their parent.
    pub fn with_flatten(flatten_nested: bool) -> Self {
        Self {
            sources: Vec::new(),
            source_map: HashMap::new(),
            exprs: Vec::new(),
            expr_map: HashMap::new(),
            cache_aliases: HashMap::new(),
            fenced: HashSet::new(),
            flatten_nested,
        }
    }

    /// Register the in-layer cache-address → shared-value-`ExprId` alias map.
    ///
    /// Called once, after all cache values are materialized and before any gate
    /// is lowered, so a subsequent read of a same-layer cache address IS the
    /// materialized value's shared `ExprId` (DAG sharing, not a `Prior` root).
    ///
    /// Build-time-only: this map lives on the `ArenaBuilder` and is never
    /// consulted or remapped by `simplify_circuit` — it is fully consumed by
    /// the time `lower_layer` returns the `DagLayer`.
    pub fn set_cache_aliases(&mut self, aliases: HashMap<GKRAddress, ExprId>) {
        self.cache_aliases = aliases;
    }

    /// The shared `ExprId` of the cache value at `addr`, if `addr` was
    /// materialized as a cache value in THIS layer. `None` for any non-cache or
    /// external/compat address.
    pub fn cache_alias(&self, addr: GKRAddress) -> Option<ExprId> {
        self.cache_aliases.get(&addr).copied()
    }

    /// Intern a `SourceKind`, returning an existing `SourceId` if an identical
    /// source was already added.
    pub fn intern_source(&mut self, kind: SourceKind) -> SourceId {
        if let Some(&id) = self.source_map.get(&kind) {
            return id;
        }
        let id = SourceId(self.sources.len() as u32);
        self.sources.push(SourceInfo { kind: kind.clone() });
        self.source_map.insert(kind, id);
        id
    }

    /// Intern `Expr::Source(id)`.
    pub fn source_expr(&mut self, id: SourceId) -> ExprId {
        self.intern_expr(Expr::Source(id))
    }

    /// Intern an `Expr::Add`.
    ///
    /// Canonicalization steps (applied in order):
    /// 1. Flatten: any child that is itself an `Add` is replaced by its operands,
    ///    **unless** the child is fenced (see [`fenced_add`]). A fenced child is
    ///    kept as a single operand, so a canonical `Add` MAY contain an `Add`
    ///    child at the lookup/setup fold-leaf boundary.
    /// 2. Sort operands ascending by `ExprId`.
    /// 3. Keep repeated operands (no dedup).
    pub fn add(&mut self, terms: Vec<ExprId>) -> ExprId {
        let canonical = self.canonicalize(terms, /* is_add */ true);
        self.intern_expr(Expr::Add(canonical))
    }

    /// Intern an `Expr::Mul`.
    ///
    /// Same canonicalization rules as `add`, but flattens nested `Mul` children.
    /// A fenced `Mul` child (see [`fenced_add`]) would similarly survive, though
    /// `fenced_add` only fences `Add` nodes in practice.
    pub fn mul(&mut self, factors: Vec<ExprId>) -> ExprId {
        let canonical = self.canonicalize(factors, /* is_add */ false);
        self.intern_expr(Expr::Mul(canonical))
    }

    /// Like [`add`], but marks the resulting `Add` non-flattenable: a later `add`
    /// that takes this id as an operand keeps it as a single operand instead of
    /// flattening its children. Used for lookup/setup fold leaves whose `ExprId`
    /// is recorded in `resolutions` and must survive into root-reachable nodes.
    pub(super) fn fenced_add(&mut self, terms: Vec<ExprId>) -> ExprId {
        let id = self.add(terms);
        self.fenced.insert(id);
        id
    }

    // ── accessors ────────────────────────────────────────────────────────────

    pub fn sources(&self) -> &[SourceInfo] {
        &self.sources
    }

    pub fn exprs(&self) -> &[Expr] {
        &self.exprs
    }

    /// The set of `ExprId`s marked non-flattenable via [`fenced_add`].
    ///
    /// Used by `lower_layer`'s derived-fence assertion: every fenced node must
    /// be a key in the layer's `resolutions` map (fencing exists only to keep
    /// resolution-driven fold leaves single-operand and findable).
    pub(super) fn fenced(&self) -> &HashSet<ExprId> {
        &self.fenced
    }

    // ── internals ────────────────────────────────────────────────────────────

    fn intern_expr(&mut self, expr: Expr) -> ExprId {
        if let Some(&id) = self.expr_map.get(&expr) {
            return id;
        }
        let id = ExprId(self.exprs.len() as u32);
        self.exprs.push(expr.clone());
        self.expr_map.insert(expr, id);
        id
    }

    /// Flatten nested same-op children, then sort ascending by `ExprId`.
    ///
    /// `is_add == true`  → flatten `Expr::Add` children.
    /// `is_add == false` → flatten `Expr::Mul` children.
    ///
    /// Because each child was itself interned-and-canonicalized, it is already
    /// flat; one level of recursion is sufficient (when flattening is enabled).
    ///
    /// **Exception**: a *fenced* child (marked via [`fenced_add`]) is never
    /// flattened — it survives as a single operand. This is the deliberate
    /// lookup/setup fold-leaf boundary; a canonical `Add`/`Mul` MAY contain a
    /// same-kind child at that boundary.
    ///
    /// When `self.flatten_nested` is `false`, nested same-op children are NOT
    /// flattened, allowing simplification passes to analyze fan-out structure.
    fn canonicalize(&self, operands: Vec<ExprId>, is_add: bool) -> Vec<ExprId> {
        let mut flat: Vec<ExprId> = Vec::with_capacity(operands.len());
        for id in operands {
            let expr = &self.exprs[id.0 as usize];
            let same_kind = if is_add {
                matches!(expr, Expr::Add(_))
            } else {
                matches!(expr, Expr::Mul(_))
            };
            let should_flatten = self.flatten_nested && same_kind && !self.fenced.contains(&id);
            if should_flatten {
                match expr {
                    Expr::Add(children) | Expr::Mul(children) => {
                        flat.extend_from_slice(children);
                    }
                    _ => unreachable!(),
                }
            } else {
                flat.push(id);
            }
        }
        flat.sort_unstable();
        flat
    }
}

impl Default for ArenaBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// ── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn make_sources(arena: &mut ArenaBuilder) -> (ExprId, ExprId, ExprId) {
        let sa = arena.intern_source(SourceKind::Constant { value: 1 });
        let sb = arena.intern_source(SourceKind::Constant { value: 2 });
        let sc = arena.intern_source(SourceKind::Constant { value: 3 });
        let a = arena.source_expr(sa);
        let b = arena.source_expr(sb);
        let c = arena.source_expr(sc);
        (a, b, c)
    }

    /// `add([a, b])` and `add([b, a])` must intern to the same `ExprId`.
    #[test]
    fn add_commutativity() {
        let mut arena = ArenaBuilder::new();
        let (a, b, _) = make_sources(&mut arena);

        let ab = arena.add(vec![a, b]);
        let ba = arena.add(vec![b, a]);
        assert_eq!(ab, ba, "add([a,b]) and add([b,a]) should be the same ExprId");
    }

    /// `add([a, add([b, c])])` must intern to the same `ExprId` as `add([a, b, c])`
    /// under the legacy build-time-flattening knob (`with_flatten(true)`).
    #[test]
    fn add_flatten_nested() {
        let mut arena = ArenaBuilder::with_flatten(true);
        let (a, b, c) = make_sources(&mut arena);

        let bc = arena.add(vec![b, c]);
        let nested = arena.add(vec![a, bc]);
        let flat = arena.add(vec![a, b, c]);
        assert_eq!(
            nested, flat,
            "add([a, add([b,c])]) and add([a,b,c]) should be the same ExprId"
        );
    }

    /// `ArenaBuilder::new()` (default, unflattened) must PRESERVE nested `Add`
    /// structure: `add([a, add([b,c])])` stays a 2-operand `Add`, distinct from
    /// the fully-flattened `add([a,b,c])`.
    #[test]
    fn add_new_preserves_nesting() {
        let mut arena = ArenaBuilder::new();
        let (a, b, c) = make_sources(&mut arena);

        let bc = arena.add(vec![b, c]);
        let nested = arena.add(vec![a, bc]);
        let flat = arena.add(vec![a, b, c]);
        assert_ne!(
            nested, flat,
            "new() must NOT flatten nested Add children (legacy knob is with_flatten(true))"
        );
        match &arena.exprs()[nested.0 as usize] {
            Expr::Add(ops) => {
                assert_eq!(ops.len(), 2, "nested Add must survive as 2 operands, got {:?}", ops);
                assert!(ops.contains(&bc), "the nested Add itself must be a direct operand");
            }
            other => panic!("expected Add, got {:?}", other),
        }
    }

    /// Two `intern_source` calls with identical `Constant` must return the same `SourceId`.
    #[test]
    fn source_intern_dedup() {
        let mut arena = ArenaBuilder::new();
        let id1 = arena.intern_source(SourceKind::Constant { value: 42 });
        let id2 = arena.intern_source(SourceKind::Constant { value: 42 });
        assert_eq!(id1, id2, "identical Constant sources should intern to one SourceId");
        assert_eq!(arena.sources().len(), 1, "only one SourceInfo should be stored");
    }

    /// `mul([a, a])` must stay length-2 and be distinct from `mul([a])`.
    #[test]
    fn mul_keeps_repeats() {
        let mut arena = ArenaBuilder::new();
        let (a, _, _) = make_sources(&mut arena);

        let aa = arena.mul(vec![a, a]);
        let a_single = arena.mul(vec![a]);
        assert_ne!(aa, a_single, "mul([a,a]) should be distinct from mul([a])");

        // Verify the stored Expr really has two operands.
        match &arena.exprs()[aa.0 as usize] {
            Expr::Mul(ops) => assert_eq!(ops.len(), 2, "mul([a,a]) must keep both copies"),
            other => panic!("expected Mul, got {:?}", other),
        }
    }

    /// `mul([a, b])` and `mul([b, a])` must intern to the same `ExprId`.
    #[test]
    fn mul_commutativity() {
        let mut arena = ArenaBuilder::new();
        let (a, b, _) = make_sources(&mut arena);

        let ab = arena.mul(vec![a, b]);
        let ba = arena.mul(vec![b, a]);
        assert_eq!(ab, ba, "mul([a,b]) and mul([b,a]) should be the same ExprId");
    }

    /// `mul([a, mul([b, c])])` must intern to the same `ExprId` as `mul([a, b, c])`
    /// under the legacy build-time-flattening knob (`with_flatten(true)`).
    #[test]
    fn mul_flatten_nested() {
        let mut arena = ArenaBuilder::with_flatten(true);
        let (a, b, c) = make_sources(&mut arena);

        let bc = arena.mul(vec![b, c]);
        let nested = arena.mul(vec![a, bc]);
        let flat = arena.mul(vec![a, b, c]);
        assert_eq!(
            nested, flat,
            "mul([a, mul([b,c])]) and mul([a,b,c]) should be the same ExprId"
        );
    }

    /// `ArenaBuilder::new()` (default, unflattened) must PRESERVE nested `Mul`
    /// structure: `mul([a, mul([b,c])])` stays a 2-operand `Mul`, distinct from
    /// the fully-flattened `mul([a,b,c])`.
    #[test]
    fn mul_new_preserves_nesting() {
        let mut arena = ArenaBuilder::new();
        let (a, b, c) = make_sources(&mut arena);

        let bc = arena.mul(vec![b, c]);
        let nested = arena.mul(vec![a, bc]);
        let flat = arena.mul(vec![a, b, c]);
        assert_ne!(
            nested, flat,
            "new() must NOT flatten nested Mul children (legacy knob is with_flatten(true))"
        );
        match &arena.exprs()[nested.0 as usize] {
            Expr::Mul(ops) => {
                assert_eq!(ops.len(), 2, "nested Mul must survive as 2 operands, got {:?}", ops);
                assert!(ops.contains(&bc), "the nested Mul itself must be a direct operand");
            }
            other => panic!("expected Mul, got {:?}", other),
        }
    }

    /// Cross-kind: `add` and `mul` do NOT flatten each other.
    #[test]
    fn add_does_not_flatten_mul() {
        let mut arena = ArenaBuilder::new();
        let (a, b, c) = make_sources(&mut arena);

        let bc_mul = arena.mul(vec![b, c]);
        let result = arena.add(vec![a, bc_mul]);

        // Should stay as Add([a, bc_mul]) — two operands.
        match &arena.exprs()[result.0 as usize] {
            Expr::Add(ops) => assert_eq!(ops.len(), 2, "add should not flatten a Mul child"),
            other => panic!("expected Add, got {:?}", other),
        }
    }

    /// A fenced `Add` child must NOT be flattened by a subsequent `add`.
    ///
    /// `fenced_add([y, z])` returns an `Add([y,z])` marked non-flattenable.
    /// `add([x, fenced])` must produce `Add([x, fenced])` — two operands — instead
    /// of the normal `Add([x, y, z])` that unfenced flattening would yield.
    #[test]
    fn fenced_add_child_is_not_flattened() {
        let mut a = ArenaBuilder::new();
        let x = a.intern_source(SourceKind::Constant { value: 1 });
        let y = a.intern_source(SourceKind::Constant { value: 2 });
        let z = a.intern_source(SourceKind::Constant { value: 3 });
        let (ex, ey, ez) = (a.source_expr(x), a.source_expr(y), a.source_expr(z));
        let bc = a.fenced_add(vec![ey, ez]); // fenced Add([y, z])
        let nested = a.add(vec![ex, bc]);    // add([x, fenced]) must NOT flatten bc
        match &a.exprs()[nested.0 as usize] {
            Expr::Add(ops) => {
                assert_eq!(ops.len(), 2, "fenced child must survive as one operand, got {:?}", ops);
                assert!(ops.contains(&bc), "the fenced node itself must be a direct operand, got {:?}", ops);
            }
            other => panic!("expected Add, got {:?}", other),
        }
    }

    /// Under `with_flatten(false)`, a nested same-op child survives as one operand.
    #[test]
    fn unflattened_add_keeps_nested_child() {
        let mut arena = ArenaBuilder::with_flatten(false);
        let (a, b, c) = make_sources(&mut arena);
        let bc = arena.add(vec![b, c]);
        let nested = arena.add(vec![a, bc]);
        match &arena.exprs()[nested.0 as usize] {
            Expr::Add(ops) => {
                assert_eq!(ops.len(), 2, "nested Add must survive, got {:?}", ops);
                assert!(ops.contains(&bc));
            }
            other => panic!("expected Add, got {:?}", other),
        }
    }
}
