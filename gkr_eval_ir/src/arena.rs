use std::collections::HashMap;

use cs::definitions::GKRAddress;

use super::{Expr, ExprId, SourceId, SourceKind};

// ── ArenaBuilder ─────────────────────────────────────────────────────────────

/// Interning arena for canonical DAG sources and expressions.
pub struct ArenaBuilder {
    sources: Vec<SourceKind>,
    source_map: HashMap<SourceKind, SourceId>,

    exprs: Vec<Expr>,
    expr_map: HashMap<Expr, ExprId>,

    cache_aliases: HashMap<GKRAddress, ExprId>,
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

    /// Register same-layer cache-address aliases.
    pub(crate) fn set_cache_aliases(&mut self, aliases: HashMap<GKRAddress, ExprId>) {
        self.cache_aliases = aliases;
    }

    /// Return the shared expression for a same-layer cache address.
    pub(crate) fn cache_alias(&self, addr: GKRAddress) -> Option<ExprId> {
        self.cache_aliases.get(&addr).copied()
    }

    /// Intern a `SourceKind`, returning an existing `SourceId` if an identical
    /// source was already added.
    pub fn intern_source(&mut self, kind: SourceKind) -> SourceId {
        if let Some(&id) = self.source_map.get(&kind) {
            return id;
        }
        let id = SourceId(self.sources.len() as u32);
        self.sources.push(kind);
        self.source_map.insert(kind, id);
        id
    }

    /// Intern `Expr::Source(id)`.
    pub fn source_expr(&mut self, id: SourceId) -> ExprId {
        self.intern_expr(Expr::Source(id))
    }

    /// Intern an `Expr::Add`.
    ///
    /// Operands are sorted and repeated operands are retained.
    pub fn add(&mut self, terms: Vec<ExprId>) -> ExprId {
        let canonical = self.canonicalize(terms);
        self.intern_expr(Expr::Add(canonical))
    }

    /// Intern an `Expr::Mul`.
    ///
    /// Operands are sorted and repeated operands are retained.
    pub fn mul(&mut self, factors: Vec<ExprId>) -> ExprId {
        let canonical = self.canonicalize(factors);
        self.intern_expr(Expr::Mul(canonical))
    }

    // ── accessors ────────────────────────────────────────────────────────────

    pub fn sources(&self) -> &[SourceKind] {
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

    fn canonicalize(&self, mut operands: Vec<ExprId>) -> Vec<ExprId> {
        operands.sort_unstable();
        operands
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
        assert_eq!(
            ab, ba,
            "add([a,b]) and add([b,a]) should be the same ExprId"
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
        assert_ne!(nested, flat, "new() must not flatten nested Add children");
        match &arena.exprs()[nested.0 as usize] {
            Expr::Add(ops) => {
                assert_eq!(
                    ops.len(),
                    2,
                    "nested Add must survive as 2 operands, got {:?}",
                    ops
                );
                assert!(
                    ops.contains(&bc),
                    "the nested Add itself must be a direct operand"
                );
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
        assert_eq!(
            id1, id2,
            "identical Constant sources should intern to one SourceId"
        );
        assert_eq!(arena.sources().len(), 1, "only one source should be stored");
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
        assert_eq!(
            ab, ba,
            "mul([a,b]) and mul([b,a]) should be the same ExprId"
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
        assert_ne!(nested, flat, "new() must not flatten nested Mul children");
        match &arena.exprs()[nested.0 as usize] {
            Expr::Mul(ops) => {
                assert_eq!(
                    ops.len(),
                    2,
                    "nested Mul must survive as 2 operands, got {:?}",
                    ops
                );
                assert!(
                    ops.contains(&bc),
                    "the nested Mul itself must be a direct operand"
                );
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
}
