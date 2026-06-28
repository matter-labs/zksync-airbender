//! Row-bound reference evaluator for the DAG IR.
//!
//! Evaluates one row of a [`DagLayer`] root, lifting everything into `Ext`.
//! Cache values are ordinary shared sub-exprs: a same-layer cache read is the
//! materialized value's `ExprId`, so it is computed on demand and memoized by
//! `expr_cache` like any other shared node — no sealed-root pre-pass.

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
/// Cache values are ordinary shared sub-exprs: a same-layer cache read is the
/// materialized value's `ExprId`, computed on demand and memoized by
/// `expr_cache`. There is no sealed-root pre-pass and no caches-lead ordering
/// precondition.
pub fn eval_layer_root(layer: &DagLayer, root: RootId, row: usize, r: &Resolvers<'_>) -> Ext {
    let mut expr_cache: HashMap<ExprId, Ext> = HashMap::new();
    let expr_id = match &layer.roots[root.0 as usize] {
        Root::Output { expr, .. } => *expr,
        Root::Constraint { expr } => *expr,
    };
    eval_expr(expr_id, layer, row, r, &mut expr_cache)
}

/// Evaluate an arbitrary `expr` of `layer` at `row`. Cache values reachable from
/// `expr` are ordinary shared sub-exprs computed on demand (memoized by
/// `expr_cache`); there is no pre-pass. Used by the forward-VM CPU interpreter to
/// re-resolve a pruned resolution fold through the authoritative evaluator (SP1).
pub fn eval_layer_expr(layer: &DagLayer, expr: ExprId, row: usize, r: &Resolvers<'_>) -> Ext {
    let mut expr_cache: HashMap<ExprId, Ext> = HashMap::new();
    eval_expr(expr, layer, row, r, &mut expr_cache)
}

// ── Internal helpers ──────────────────────────────────────────────────────────

fn eval_expr(
    id: ExprId,
    layer: &DagLayer,
    row: usize,
    r: &Resolvers<'_>,
    cache: &mut HashMap<ExprId, Ext>,
) -> Ext {
    if let Some(&v) = cache.get(&id) {
        return v;
    }
    let val = match &layer.exprs[id.0 as usize] {
        Expr::Source(src_id) => {
            eval_source(&layer.sources[src_id.0 as usize].kind, layer, row, r, cache)
        }
        Expr::Add(terms) => {
            let mut acc = Ext::ZERO;
            for &t in terms {
                let v = eval_expr(t, layer, row, r, cache);
                acc.add_assign(&v);
            }
            acc
        }
        Expr::Mul(factors) => {
            let mut acc = Ext::ONE;
            for &f in factors {
                let v = eval_expr(f, layer, row, r, cache);
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
    cache: &mut HashMap<ExprId, Ext>,
) -> Ext {
    match kind {
        SourceKind::Constant { value } => lift(Bf::from_u32_with_reduction(*value)),
        SourceKind::Challenge { reference } => r.challenge.challenge(reference),
        SourceKind::Read { place } => r.read.read(place, row),
        SourceKind::VirtualSetup { kind: vk } => lift(r.virtual_setup.virtual_setup(vk, row)),
        SourceKind::LookupValue { kind: lk, set_index, query } => {
            let q_val = eval_expr(*query, layer, row, r, cache);
            lift(r.lookup.lookup(lk, *set_index, q_val, row))
        }
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use field::{Field, PrimeField};

    use super::*;
    use crate::gkr_compiler::dag_ir::{
        ArenaBuilder, BatchingOrder, ChallengeKey, ChallengeRef, ChallengePower, DagLayer, Expr,
        LookupValueKind, ReadPlace, Root, RootId, SinkId, SourceKind, VirtualSetupKind,
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

    // ── Test: a shared cache ExprId is reused by a consumer root ──────────────

    /// Cache reuse is DAG sharing: a cache value (`Constant(5)`) is materialized
    /// by a `Cache`-sink root AND shared as a direct operand of a claim-bearing
    /// consumer root (`cache_expr + Constant(3)`).
    ///
    /// Assert: (a) the consumer's operand IS the cache `ExprId` (sharing, not a
    /// duplicated leaf), and (b) the consumer evaluates to lift(5) + lift(3) =
    /// lift(8) — the cache value flows through on demand, no pre-pass.
    #[test]
    fn shared_cache_expr_is_reused_by_consumer() {
        let mut arena = ArenaBuilder::new();

        // The cache value is an ordinary shared expr: Constant(5).
        let cache_src = arena.intern_source(SourceKind::Constant { value: 5 });
        let cache_expr = arena.source_expr(cache_src);

        // Constant(3)
        let c3_src = arena.intern_source(SourceKind::Constant { value: 3 });
        let c3 = arena.source_expr(c3_src);

        // Consumer = cache_expr + 3 — references the cache value's ExprId directly.
        let sum = arena.add(vec![cache_expr, c3]);

        let roots = vec![
            // RootId(0): Cache-sink Output materializing the value (committed).
            Root::Output { expr: cache_expr, sink: SinkId(0) },
            // RootId(1): claim-bearing consumer sharing the cache ExprId.
            Root::Output { expr: sum, sink: SinkId(1) },
        ];
        // Only root 1 is claim-bearing; root 0 is the materialize-only cache.
        let layer = layer_from_arena(&arena, roots, vec![RootId(1)]);

        // (a) ALIAS IDENTITY: the consumer's Add operand IS the cache ExprId.
        match &layer.exprs[sum.0 as usize] {
            Expr::Add(args) => assert!(
                args.contains(&cache_expr),
                "consumer must SHARE the cache value's ExprId as a direct operand, got {:?}",
                args
            ),
            other => panic!("expected Add, got {:?}", other),
        }

        let r = Resolvers {
            read: &ConstReadResolver(Ext::ZERO),
            lookup: &ConstLookupResolver(Bf::ZERO),
            virtual_setup: &ConstVirtualSetupResolver(Bf::ZERO),
            challenge: &ConstChallengeResolver(Ext::ZERO),
        };

        // (b) VALUE: the cache value flows through on demand → lift(8).
        let result = eval_layer_root(&layer, RootId(1), 0, &r);
        let expected = {
            let mut e = lift(Bf::from_u32_with_reduction(5));
            e.add_assign(&lift(Bf::from_u32_with_reduction(3)));
            e
        };
        assert_eq!(result, expected, "shared cache value mismatch");
    }

    // ── Test: eval_layer_expr evaluates an arbitrary shared sub-expr ──────────

    /// Same layer as `shared_cache_expr_is_reused_by_consumer`, but call
    /// `eval_layer_expr` on arbitrary sub-exprs directly (no pre-pass). The
    /// shared cache `ExprId` evaluates to lift(5); the consumer sum to lift(8).
    #[test]
    fn eval_layer_expr_evaluates_shared_subexpr_on_demand() {
        let mut arena = ArenaBuilder::new();

        let cache_src = arena.intern_source(SourceKind::Constant { value: 5 });
        let cache_expr = arena.source_expr(cache_src);

        let c3_src = arena.intern_source(SourceKind::Constant { value: 3 });
        let c3 = arena.source_expr(c3_src);

        let sum = arena.add(vec![cache_expr, c3]);

        let roots = vec![
            Root::Output { expr: cache_expr, sink: SinkId(0) },
            Root::Output { expr: sum, sink: SinkId(1) },
        ];
        let layer = layer_from_arena(&arena, roots, vec![RootId(1)]);

        let r = Resolvers {
            read: &ConstReadResolver(Ext::ZERO),
            lookup: &ConstLookupResolver(Bf::ZERO),
            virtual_setup: &ConstVirtualSetupResolver(Bf::ZERO),
            challenge: &ConstChallengeResolver(Ext::ZERO),
        };

        // The shared cache sub-expr evaluates to lift(5).
        let result = eval_layer_expr(&layer, cache_expr, 0, &r);
        let expected = lift(Bf::from_u32_with_reduction(5));
        assert_eq!(result, expected, "eval_layer_expr: cache expr mismatch");

        // And the consumer sum evaluates to lift(8).
        let result_sum = eval_layer_expr(&layer, sum, 0, &r);
        let expected_sum = {
            let mut e = lift(Bf::from_u32_with_reduction(5));
            e.add_assign(&lift(Bf::from_u32_with_reduction(3)));
            e
        };
        assert_eq!(result_sum, expected_sum, "eval_layer_expr: sum expr mismatch");
    }
}
