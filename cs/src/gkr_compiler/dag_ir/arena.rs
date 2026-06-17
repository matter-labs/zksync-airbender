use std::collections::HashMap;

use crate::definitions::GKRAddress;

use super::{Expr, ExprId, RootId, SourceId, SourceInfo, SourceKind};

// ── ArenaBuilder ─────────────────────────────────────────────────────────────

/// An interning arena for DAG IR nodes.
///
/// `intern_source` deduplicates `SourceKind` values.
/// `add` / `mul` flatten nested same-op children, sort operands by `ExprId`
/// (ascending), keep repeated operands, and then intern the canonical `Expr`.
///
/// `cache_aliases` maps each `GKRAddress::Cached` address materialized as a
/// cache root in THIS layer to that root's `RootId`. The lowering read helpers
/// consult it via [`ArenaBuilder::cache_alias`] so a same-layer cache read
/// becomes `SourceKind::Prior` instead of a `Read(CacheOutput)` compatibility
/// read (see the `lower` module docs and the design doc's "Roots" section).
pub struct ArenaBuilder {
    sources: Vec<SourceInfo>,
    source_map: HashMap<SourceKind, SourceId>,

    exprs: Vec<Expr>,
    expr_map: HashMap<Expr, ExprId>,

    cache_aliases: HashMap<GKRAddress, RootId>,
}

impl ArenaBuilder {
    pub fn new() -> Self {
        Self {
            sources: Vec::new(),
            source_map: HashMap::new(),
            exprs: Vec::new(),
            expr_map: HashMap::new(),
            cache_aliases: HashMap::new(),
        }
    }

    /// Register the in-layer cache-address → cache-root alias map.
    ///
    /// Called once, after all cache roots are materialized and before any gate
    /// is lowered, so subsequent reads of a same-layer cache address alias to
    /// the materializing root through `Prior`.
    pub fn set_cache_aliases(&mut self, aliases: HashMap<GKRAddress, RootId>) {
        self.cache_aliases = aliases;
    }

    /// The cache root aliasing `addr`, if `addr` was materialized as a cache
    /// root in THIS layer. `None` for any non-cache or external/compat address.
    pub fn cache_alias(&self, addr: GKRAddress) -> Option<RootId> {
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
    /// 1. Flatten: any child that is itself an `Add` is replaced by its operands.
    /// 2. Sort operands ascending by `ExprId`.
    /// 3. Keep repeated operands (no dedup).
    pub fn add(&mut self, terms: Vec<ExprId>) -> ExprId {
        let canonical = self.canonicalize(terms, /* is_add */ true);
        self.intern_expr(Expr::Add(canonical))
    }

    /// Intern an `Expr::Mul`.
    ///
    /// Same canonicalization rules as `add`, but flattens nested `Mul` children.
    pub fn mul(&mut self, factors: Vec<ExprId>) -> ExprId {
        let canonical = self.canonicalize(factors, /* is_add */ false);
        self.intern_expr(Expr::Mul(canonical))
    }

    // ── accessors ────────────────────────────────────────────────────────────

    pub fn sources(&self) -> &[SourceInfo] {
        &self.sources
    }

    pub fn exprs(&self) -> &[Expr] {
        &self.exprs
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
    /// flat; one level of recursion is sufficient.
    fn canonicalize(&self, operands: Vec<ExprId>, is_add: bool) -> Vec<ExprId> {
        let mut flat: Vec<ExprId> = Vec::with_capacity(operands.len());
        for id in operands {
            let expr = &self.exprs[id.0 as usize];
            let should_flatten = if is_add {
                matches!(expr, Expr::Add(_))
            } else {
                matches!(expr, Expr::Mul(_))
            };
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

    /// `add([a, add([b, c])])` must intern to the same `ExprId` as `add([a, b, c])`.
    #[test]
    fn add_flatten_nested() {
        let mut arena = ArenaBuilder::new();
        let (a, b, c) = make_sources(&mut arena);

        let bc = arena.add(vec![b, c]);
        let nested = arena.add(vec![a, bc]);
        let flat = arena.add(vec![a, b, c]);
        assert_eq!(
            nested, flat,
            "add([a, add([b,c])]) and add([a,b,c]) should be the same ExprId"
        );
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

    /// `mul([a, mul([b, c])])` must intern to the same `ExprId` as `mul([a, b, c])`.
    #[test]
    fn mul_flatten_nested() {
        let mut arena = ArenaBuilder::new();
        let (a, b, c) = make_sources(&mut arena);

        let bc = arena.mul(vec![b, c]);
        let nested = arena.mul(vec![a, bc]);
        let flat = arena.mul(vec![a, b, c]);
        assert_eq!(
            nested, flat,
            "mul([a, mul([b,c])]) and mul([a,b,c]) should be the same ExprId"
        );
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
}
