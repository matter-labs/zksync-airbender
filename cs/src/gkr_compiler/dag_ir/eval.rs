//! Row-bound reference evaluator for the DAG IR.
//!
//! Evaluates one row of a [`DagLayer`] root, lifting everything into `Ext`.
//! Materialization-only roots (those absent from [`BatchingOrder`]) are evaluated
//! eagerly in topological (index) order so that `Prior(id)` can read their result.

use std::collections::HashMap;

use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::{Field, FieldExtension, PrimeField};

use super::{
    ChallengeRef, DagLayer, Expr, ExprId, LookupValueKind, ReadPlace, Root, RootId, SourceKind,
    VirtualSetupKind,
};

// ── Field type aliases ────────────────────────────────────────────────────────

pub type Bf = BabyBearField;
pub type Ext = BabyBearExt4;

// ── Lift helper ───────────────────────────────────────────────────────────────

#[inline(always)]
fn lift(b: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(b)
}

// ── Resolver traits ───────────────────────────────────────────────────────────

/// Resolves a `ReadPlace` to an `Ext` value for a given row.
pub trait ReadResolver {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext;
}

/// Resolves a lookup table value.
///
/// `evaluated_query` is the already-evaluated query expression (in `Ext`).
/// Returns a `Bf` value that the evaluator lifts to `Ext`.
pub trait LookupResolver {
    fn lookup(
        &self,
        kind: &LookupValueKind,
        set_index: usize,
        evaluated_query: Ext,
        row: usize,
    ) -> Bf;
}

/// Resolves a virtual setup column value.
/// Returns a `Bf` value that the evaluator lifts to `Ext`.
pub trait VirtualSetupResolver {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> Bf;
}

/// Resolves a challenge reference to an `Ext` value.
pub trait ChallengeResolver {
    fn challenge(&self, r: &ChallengeRef) -> Ext;
}

// ── Resolvers bundle ──────────────────────────────────────────────────────────

/// Bundles the four resolver trait objects needed by the evaluator.
pub struct Resolvers<'a> {
    pub read: &'a dyn ReadResolver,
    pub lookup: &'a dyn LookupResolver,
    pub virtual_setup: &'a dyn VirtualSetupResolver,
    pub challenge: &'a dyn ChallengeResolver,
}

// ── Evaluator ─────────────────────────────────────────────────────────────────

/// Evaluate `root` of `layer` at `row`, using `r` for all external references.
///
/// Materialization-only roots (i.e. roots whose `RootId` does not appear in
/// `layer.batching.roots`) are evaluated eagerly in ascending `RootId` order
/// before the target root, so `Prior(id)` can look up their result.
///
/// **Precondition — caches-lead ordering**: all materialization-only (cache)
/// roots MUST occupy leading indices in `layer.roots` (i.e. every cache root
/// has a smaller `RootId` than every claim-bearing root).  The pre-pass only
/// materializes roots with index < the target root's index, so a `Prior`
/// referencing a root with index >= the referencing root's index is never
/// materialized and will panic.  `validate` enforces this invariant; hand-
/// crafted layers must satisfy it too.
///
/// `Prior(id)` is only valid when `id` is a materialization-only root (not in
/// `batching.roots`); evaluating a root that `Prior`-references a batching root
/// will panic.
pub fn eval_layer_root(layer: &DagLayer, root: RootId, row: usize, r: &Resolvers<'_>) -> Ext {
    // Build the set of "claim-bearing" roots (those in batching order).
    let batching_set: std::collections::HashSet<RootId> =
        layer.batching.roots.iter().copied().collect();

    // Map from RootId → materialized Ext value, filled in order.
    let mut materialized: HashMap<RootId, Ext> = HashMap::new();

    // Memoized expr values for this row.
    let mut expr_cache: HashMap<ExprId, Ext> = HashMap::new();

    // Evaluate materialization-only roots (not in batching set) in index order.
    // They must precede the target root index so that Prior(id) references are valid.
    for (idx, dag_root) in layer.roots.iter().enumerate() {
        let rid = RootId(idx as u32);
        if rid == root {
            break; // stop before the requested root; we evaluate it below
        }
        if !batching_set.contains(&rid) {
            // Materialization-only root — evaluate eagerly.
            let val = eval_root_expr(dag_root, layer, row, r, &materialized, &mut expr_cache);
            materialized.insert(rid, val);
        }
    }

    // Now evaluate the requested root.
    let dag_root = &layer.roots[root.0 as usize];
    eval_root_expr(dag_root, layer, row, r, &materialized, &mut expr_cache)
}

// ── Internal helpers ──────────────────────────────────────────────────────────

fn eval_root_expr(
    root: &Root,
    layer: &DagLayer,
    row: usize,
    r: &Resolvers<'_>,
    materialized: &HashMap<RootId, Ext>,
    expr_cache: &mut HashMap<ExprId, Ext>,
) -> Ext {
    let expr_id = match root {
        Root::Output { expr, .. } => *expr,
        Root::Constraint { expr } => *expr,
    };
    eval_expr(expr_id, layer, row, r, materialized, expr_cache)
}

fn eval_expr(
    id: ExprId,
    layer: &DagLayer,
    row: usize,
    r: &Resolvers<'_>,
    materialized: &HashMap<RootId, Ext>,
    cache: &mut HashMap<ExprId, Ext>,
) -> Ext {
    if let Some(&v) = cache.get(&id) {
        return v;
    }
    let val = match &layer.exprs[id.0 as usize] {
        Expr::Source(src_id) => {
            eval_source(&layer.sources[src_id.0 as usize].kind, layer, row, r, materialized, cache)
        }
        Expr::Add(terms) => {
            let mut acc = Ext::ZERO;
            for &t in terms {
                let v = eval_expr(t, layer, row, r, materialized, cache);
                acc.add_assign(&v);
            }
            acc
        }
        Expr::Mul(factors) => {
            let mut acc = Ext::ONE;
            for &f in factors {
                let v = eval_expr(f, layer, row, r, materialized, cache);
                acc.mul_assign(&v);
            }
            acc
        }
    };
    cache.insert(id, val);
    val
}

fn eval_source(
    kind: &SourceKind,
    layer: &DagLayer,
    row: usize,
    r: &Resolvers<'_>,
    materialized: &HashMap<RootId, Ext>,
    cache: &mut HashMap<ExprId, Ext>,
) -> Ext {
    match kind {
        SourceKind::Constant { value } => lift(Bf::from_u32_with_reduction(*value)),
        SourceKind::Challenge { reference } => r.challenge.challenge(reference),
        SourceKind::Read { place } => r.read.read(place, row),
        SourceKind::VirtualSetup { kind: vk } => lift(r.virtual_setup.virtual_setup(vk, row)),
        SourceKind::LookupValue { kind: lk, set_index, query } => {
            let q_val = eval_expr(*query, layer, row, r, materialized, cache);
            lift(r.lookup.lookup(lk, *set_index, q_val, row))
        }
        SourceKind::Prior { id } => {
            // Defense-in-depth: the `Prior` target must have been materialized
            // before this point (caches-lead ordering + pre-pass guarantee).
            // `validate` enforces this at construction time; the assert fires in
            // debug builds if a hand-crafted layer violates the precondition.
            debug_assert!(
                materialized.contains_key(id),
                "Prior({:?}) referenced before materialization — \
                 caches-lead ordering precondition violated",
                id
            );
            *materialized
                .get(id)
                .unwrap_or_else(|| panic!("Prior({:?}) referenced before materialization", id))
        }
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use field::{Field, FieldExtension, PrimeField};

    use super::*;
    use crate::gkr_compiler::dag_ir::{
        ArenaBuilder, BatchingOrder, ChallengeKey, ChallengeRef, ChallengePower, DagLayer, Expr,
        ExprId, FieldKind, LookupValueKind, ReadPlace, Root, RootId, SinkId, SinkKind,
        SourceKind, VirtualSetupKind,
    };

    // ── Stub resolvers ────────────────────────────────────────────────────────

    /// Returns a fixed Ext value for every read.
    struct ConstReadResolver(Ext);
    impl ReadResolver for ConstReadResolver {
        fn read(&self, _place: &ReadPlace, _row: usize) -> Ext {
            self.0
        }
    }

    /// Returns a fixed Bf for every lookup, ignoring all parameters.
    struct ConstLookupResolver(Bf);
    impl LookupResolver for ConstLookupResolver {
        fn lookup(
            &self,
            _kind: &LookupValueKind,
            _set_index: usize,
            _evaluated_query: Ext,
            _row: usize,
        ) -> Bf {
            self.0
        }
    }

    /// Returns a fixed Bf for every virtual-setup call.
    struct ConstVirtualSetupResolver(Bf);
    impl VirtualSetupResolver for ConstVirtualSetupResolver {
        fn virtual_setup(&self, _kind: &VirtualSetupKind, _row: usize) -> Bf {
            self.0
        }
    }

    /// Returns a fixed Ext for every challenge.
    struct ConstChallengeResolver(Ext);
    impl ChallengeResolver for ConstChallengeResolver {
        fn challenge(&self, _r: &ChallengeRef) -> Ext {
            self.0
        }
    }

    // ── Helper to build a minimal DagLayer from an ArenaBuilder ───────────────

    fn layer_from_arena(
        arena: &ArenaBuilder,
        roots: Vec<Root>,
        batching_roots: Vec<RootId>,
    ) -> DagLayer {
        DagLayer {
            sources: arena.sources().to_vec(),
            exprs: arena.exprs().to_vec(),
            roots,
            sinks: Vec::new(),
            batching: BatchingOrder { roots: batching_roots },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        }
    }

    // ── Test: LookupValue fold ────────────────────────────────────────────────

    /// Builds: `lv0 + alpha * lv1`
    ///
    /// where `lv0 = LookupValue{GenericColumn{0}, set_index:3, query}`
    /// and   `lv1 = LookupValue{GenericColumn{1}, set_index:3, query}`
    /// and   `query = Constant(0)` (a trivial query expression).
    ///
    /// Stub resolvers:
    ///   lookup → Bf(7)   for all calls
    ///   challenge (alpha) → Ext from [2, 0, 0, 0]
    ///
    /// Hand-computed expected value:
    ///   lv0_ext = lift(7)
    ///   lv1_ext = lift(7)
    ///   alpha_ext = lift(Bf(2))   (since our stub returns [2,0,0,0])
    ///   result = lv0_ext + alpha_ext * lv1_ext = lift(7) + lift(2)*lift(7) = lift(7+14) = lift(21)
    #[test]
    fn lookup_value_fold() {
        let mut arena = ArenaBuilder::new();

        // query = Constant(0)
        let q_src = arena.intern_source(SourceKind::Constant { value: 0 });
        let q_expr = arena.source_expr(q_src);

        // lv0 = LookupValue{GenericColumn{0}, set_index:3, query=q_expr}
        let lv0_src =
            arena.intern_source(SourceKind::LookupValue {
                kind: LookupValueKind::GenericColumn { column: 0 },
                set_index: 3,
                query: q_expr,
            });
        let lv0 = arena.source_expr(lv0_src);

        // lv1 = LookupValue{GenericColumn{1}, set_index:3, query=q_expr}
        let lv1_src =
            arena.intern_source(SourceKind::LookupValue {
                kind: LookupValueKind::GenericColumn { column: 1 },
                set_index: 3,
                query: q_expr,
            });
        let lv1 = arena.source_expr(lv1_src);

        // alpha = Challenge
        let alpha_ref = ChallengeRef {
            key: ChallengeKey::LookupAdditive,
            power: ChallengePower::One,
        };
        let alpha_src = arena.intern_source(SourceKind::Challenge { reference: alpha_ref });
        let alpha = arena.source_expr(alpha_src);

        // alpha * lv1
        let alpha_lv1 = arena.mul(vec![alpha, lv1]);

        // lv0 + alpha * lv1
        let sum = arena.add(vec![lv0, alpha_lv1]);

        let root_id = RootId(0);
        let roots = vec![Root::Output {
            expr: sum,
            sink: SinkId(0),
        }];
        let layer = layer_from_arena(&arena, roots, vec![root_id]);

        // Stub resolvers
        let bf7 = Bf::from_u32_with_reduction(7);
        let bf2 = Bf::from_u32_with_reduction(2);
        let alpha_val = lift(bf2);

        let r = Resolvers {
            read: &ConstReadResolver(Ext::ZERO),
            lookup: &ConstLookupResolver(bf7),
            virtual_setup: &ConstVirtualSetupResolver(Bf::ZERO),
            challenge: &ConstChallengeResolver(alpha_val),
        };

        let result = eval_layer_root(&layer, root_id, 0, &r);

        // Hand-computed: lift(7) + lift(2)*lift(7) = lift(21)
        let expected = {
            let lv = lift(bf7);
            let alpha_ext = lift(bf2);
            let mut t = alpha_ext;
            t.mul_assign(&lv);
            let mut e = lv;
            e.add_assign(&t);
            e
        };

        assert_eq!(result, expected, "lookup fold mismatch");
    }

    // ── Test: Prior reads materialized root value ─────────────────────────────

    /// Layer with two roots:
    ///   root 0 (materialization-only): Output(Constant(5))
    ///   root 1 (claim-bearing):        Output(Prior(RootId(0)) + Constant(3))
    ///
    /// Expected: eval of root 1 = lift(5) + lift(3) = lift(8)
    #[test]
    fn prior_reads_materialized_root() {
        let mut arena = ArenaBuilder::new();

        // Constant(5)
        let c5_src = arena.intern_source(SourceKind::Constant { value: 5 });
        let c5 = arena.source_expr(c5_src);

        // Prior(RootId(0))
        let prior_src = arena.intern_source(SourceKind::Prior { id: RootId(0) });
        let prior = arena.source_expr(prior_src);

        // Constant(3)
        let c3_src = arena.intern_source(SourceKind::Constant { value: 3 });
        let c3 = arena.source_expr(c3_src);

        // prior + 3
        let sum = arena.add(vec![prior, c3]);

        let roots = vec![
            Root::Output { expr: c5, sink: SinkId(0) },   // RootId(0) — materialization-only
            Root::Output { expr: sum, sink: SinkId(1) },  // RootId(1) — claim-bearing
        ];
        // Only root 1 is in batching; root 0 is materialization-only.
        let layer = layer_from_arena(&arena, roots, vec![RootId(1)]);

        let r = Resolvers {
            read: &ConstReadResolver(Ext::ZERO),
            lookup: &ConstLookupResolver(Bf::ZERO),
            virtual_setup: &ConstVirtualSetupResolver(Bf::ZERO),
            challenge: &ConstChallengeResolver(Ext::ZERO),
        };

        let result = eval_layer_root(&layer, RootId(1), 0, &r);

        let expected = {
            let mut e = lift(Bf::from_u32_with_reduction(5));
            e.add_assign(&lift(Bf::from_u32_with_reduction(3)));
            e
        };

        assert_eq!(result, expected, "Prior resolution mismatch");
    }
}
