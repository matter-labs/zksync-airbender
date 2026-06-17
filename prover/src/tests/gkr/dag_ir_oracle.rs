//! Task 6 — oracle-hook SPIKE (GATE before broad lowering).
//!
//! Proves that the new DAG-IR reference evaluator
//! (`cs::gkr_compiler::dag_ir::eval::eval_layer_root`) can reproduce the
//! **prover's authoritative per-relation values** on three representative
//! relation shapes, BEFORE any general `lower_dag` is built.
//!
//! The reference (value oracle) is the prover forward-loop relation math:
//!   * `LinearBaseFieldRelation`                 → `evaluate_linear_relation_at_row`
//!     (single base output).
//!   * `LookupPairFromMaterializedBaseInputs`    → the materialized-base lookup
//!     pair math from `lookup_base_pair::pointwise_eval_impl`
//!     (`b = in0 + gamma`, `d = in1 + gamma`; num = b + d, den = b * d).
//!   * `EnforceSingleMaxQuadraticConstraint`     → the constraint kernel math
//!     from `EnforceSingleMaxQuadraticConstraintGKRKernel::evaluate_forward`
//!     (`constant + Σ_quad c·a·b + Σ_lin c·a`, the value that must vanish).
//!
//! `reference_relation_values` is an **exhaustive `match`** over the three
//! shapes (NOT a forward-loop wrapper): the forward loop `todo!()`s
//! `MaxQuadratic` without scratch, `unimplemented!()`s
//! `EnforceConstraintsMaxQuadratic`, and only self-checks
//! `EnforceSingleMaxQuadraticConstraint`, so constraint/quadratic shapes must
//! be evaluated directly. The three shapes here happen to all have direct,
//! self-contained reference math.
//!
//! Binding scheme: one shared `GKRStorage` filled with ONE fixed pseudo-random
//! base-field assignment for every `GKRAddress` the chosen relations read. The
//! prover reference reads that storage; the DAG-IR `Resolvers` read the SAME
//! storage (via a `ReadResolver` that maps `ReadPlace` → `GKRAddress`), and the
//! SAME lookup-additive challenge `gamma` (via the `ChallengeResolver`). Equal
//! inputs ⇒ the two evaluators must agree slot-for-slot.

use std::collections::BTreeSet;

use cs::definitions::gkr::NoFieldLinearRelation;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::dag_ir::{
    eval_layer_root, ArenaBuilder, BatchingOrder, ChallengeKey, ChallengePower, ChallengeRef,
    ChallengeResolver, DagLayer, Expr, ExprId, LookupResolver, LookupValueKind, ReadPlace,
    ReadResolver, Resolvers, Root, RootId, SinkId, SourceKind, VirtualSetupKind, VirtualSetupResolver,
    Bf, Ext,
};
use cs::gkr_compiler::test_support::{build_add_sub_artifact, sample_relations};
use cs::gkr_compiler::{NoFieldGKRRelation, NoFieldMaxQuadraticGKRRelation};
use field::baby_bear::base::BabyBearField;
use field::baby_bear::ext4::BabyBearExt4;
use field::{Field, FieldExtension, PrimeField};

use crate::gkr::prover::forward_loop::utils::evaluate_linear_relation_at_row;
use crate::gkr::sumcheck::access_and_fold::{BaseFieldPoly, GKRStorage};

type F = BabyBearField;
type E = BabyBearExt4;

// ── lift helper (mirrors dag_ir::eval::lift) ───────────────────────────────

#[inline(always)]
fn lift(b: F) -> E {
    <E as FieldExtension<F>>::from_base(b)
}

// ── pseudo-random base value (deterministic, no rng dependency) ────────────

/// Fixed deterministic pseudo-random assignment for a `GKRAddress`. Same seed
/// for both the reference and the IR side, so the binding is identical.
fn assign_base_value(addr: GKRAddress) -> F {
    // splitmix64-style scramble of a stable address key into a small field value.
    let key: u64 = match addr {
        GKRAddress::BaseLayerWitness(o) => 0x1000_0000_0000_0000 ^ (o as u64),
        GKRAddress::BaseLayerMemory(o) => 0x2000_0000_0000_0000 ^ (o as u64),
        GKRAddress::Setup(o) => 0x3000_0000_0000_0000 ^ (o as u64),
        other => panic!("address {:?} not expected as a base input in this spike", other),
    };
    let mut z = key.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^= z >> 31;
    // keep it well under 2^16 so any range-check semantics stay valid, then reduce.
    F::from_u32_with_reduction((z as u32) & 0x0000_FFFF)
}

// ── shared binding context ─────────────────────────────────────────────────

/// Carries the witness/memory sources (as a `GKRStorage`) + the fixed
/// lookup-additive challenge `gamma`. Both the reference and the resolvers read
/// from this single source of truth.
struct RefCtx {
    storage: GKRStorage<F, E>,
    /// `gamma`: the lookup-additive challenge bound for this run.
    lookup_additive: E,
}

impl RefCtx {
    /// Build a storage holding one fixed random base poly (length `trace_len`,
    /// power of two) at layer 0 for every address in `addrs`.
    fn new(addrs: &BTreeSet<GKRAddress>, trace_len: usize) -> Self {
        assert!(trace_len.is_power_of_two());
        let mut storage = GKRStorage::<F, E>::default();
        // ensure layer 0 exists
        storage.layers.push(Default::default());
        for &addr in addrs {
            let v = assign_base_value(addr);
            let values: Box<[F]> = vec![v; trace_len].into_boxed_slice();
            storage.insert_base_field_at_layer(0, addr, BaseFieldPoly::new(values));
        }
        // gamma = a fixed nontrivial extension challenge.
        let lookup_additive = E::from_array_of_base([
            F::from_u32_with_reduction(7),
            F::from_u32_with_reduction(13),
            F::from_u32_with_reduction(1009),
            F::from_u32_with_reduction(40_000),
        ]);
        Self {
            storage,
            lookup_additive,
        }
    }

    fn read_base(&self, addr: GKRAddress, row: usize) -> F {
        self.storage
            .try_get_base_poly(addr)
            .unwrap_or_else(|| panic!("no base poly bound for {:?}", addr))[row]
    }
}

// ── the value oracle: exhaustive match over the spike's three shapes ───────

/// One `Ext` per output slot in `dst`/`ordered_outputs_for_batching` order:
///   * `LinearBaseFieldRelation`              → 1 value.
///   * `LookupPairFromMaterializedBaseInputs` → 2 values [num, den].
///   * `EnforceSingleMaxQuadraticConstraint`  → 1 value (the vanishing value).
fn reference_relation_values(rel: &NoFieldGKRRelation, row: usize, ctx: &RefCtx) -> Vec<Ext> {
    match rel {
        // Single base output: the prover materializes the linear combination
        // and lifts it into the extension field.
        NoFieldGKRRelation::LinearBaseFieldRelation { input, .. } => {
            let v = evaluate_linear_relation_at_row::<F, E>(input, &ctx.storage, row);
            vec![lift(v)]
        }

        // Materialized-base lookup pair: b = in0 + gamma, d = in1 + gamma,
        // num = b + d, den = b * d. (`lookup_base_pair::pointwise_eval_impl`.)
        NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, .. } => {
            let [a0, a1] = *input;
            let in0 = ctx.read_base(a0, row);
            let in1 = ctx.read_base(a1, row);

            let mut b = ctx.lookup_additive;
            b.add_assign(&lift(in0)); // b = gamma + in0
            let mut d = ctx.lookup_additive;
            d.add_assign(&lift(in1)); // d = gamma + in1

            let mut num = b;
            num.add_assign(&d);
            let mut den = b;
            den.mul_assign(&d);

            vec![num, den]
        }

        // Single constraint: the value that the constraint kernel asserts is
        // zero, i.e. constant + Σ_quad c·a·b + Σ_lin c·a, computed in base.
        NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input, .. } => {
            vec![lift(eval_constraint_value(input, ctx, row))]
        }

        other => panic!(
            "reference_relation_values: shape {:?} is out of scope for this spike",
            other
        ),
    }
}

/// `constant + Σ_quad c·a·b + Σ_lin c·a` in the base field. Mirrors
/// `EnforceSingleMaxQuadraticConstraintGKRKernel::evaluate_forward`.
fn eval_constraint_value(rel: &NoFieldMaxQuadraticGKRRelation, ctx: &RefCtx, row: usize) -> F {
    let mut result = F::from_u32_with_reduction(rel.constant);
    for (a, set) in rel.quadratic_terms.iter() {
        let a_val = ctx.read_base(*a, row);
        for (c, b) in set.iter() {
            let mut t = a_val;
            t.mul_assign(&ctx.read_base(*b, row));
            t.mul_assign(&F::from_u32_with_reduction(*c));
            result.add_assign(&t);
        }
    }
    for (c, a) in rel.linear_terms.iter() {
        let mut t = ctx.read_base(*a, row);
        t.mul_assign(&F::from_u32_with_reduction(*c));
        result.add_assign(&t);
    }
    result
}

// ── Resolvers bound to the SAME storage + challenge ────────────────────────

struct StorageReadResolver<'a> {
    ctx: &'a RefCtx,
}
impl<'a> ReadResolver for StorageReadResolver<'a> {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext {
        let addr = read_place_to_address(place);
        lift(self.ctx.read_base(addr, row))
    }
}

/// The spike only reads base witness/memory; map those `ReadPlace`s to the
/// matching `GKRAddress` so the resolver hits the same storage entries.
fn read_place_to_address(place: &ReadPlace) -> GKRAddress {
    match place {
        ReadPlace::BaseLayerWitness { column } => GKRAddress::BaseLayerWitness(*column),
        ReadPlace::BaseLayerMemory { column } => GKRAddress::BaseLayerMemory(*column),
        ReadPlace::Setup { column } => GKRAddress::Setup(*column),
        other => panic!("ReadPlace {:?} is out of scope for this spike", other),
    }
}

struct GammaChallengeResolver {
    gamma: Ext,
}
impl ChallengeResolver for GammaChallengeResolver {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        match (&r.key, &r.power) {
            (ChallengeKey::LookupAdditive, ChallengePower::One) => self.gamma,
            other => panic!("challenge {:?} is out of scope for this spike", other),
        }
    }
}

struct UnusedLookupResolver;
impl LookupResolver for UnusedLookupResolver {
    fn lookup(&self, _: &LookupValueKind, _: usize, _: Ext, _: usize) -> Bf {
        panic!("lookup resolver not used in this spike");
    }
}

struct UnusedVirtualSetupResolver;
impl VirtualSetupResolver for UnusedVirtualSetupResolver {
    fn virtual_setup(&self, _: &VirtualSetupKind, _: usize) -> Bf {
        panic!("virtual-setup resolver not used in this spike");
    }
}

// ── Hand lowering of each relation's expression(s) into DAG roots ──────────

/// `GKRAddress` → `ReadPlace` for the base inputs we support here.
fn address_to_read_place(addr: GKRAddress) -> ReadPlace {
    match addr {
        GKRAddress::BaseLayerWitness(o) => ReadPlace::BaseLayerWitness { column: o },
        GKRAddress::BaseLayerMemory(o) => ReadPlace::BaseLayerMemory { column: o },
        GKRAddress::Setup(o) => ReadPlace::Setup { column: o },
        other => panic!("address {:?} cannot be lowered to a ReadPlace here", other),
    }
}

/// Intern `Expr::Source(Read{place})` for a base address.
fn read_expr(arena: &mut ArenaBuilder, addr: GKRAddress) -> ExprId {
    let src = arena.intern_source(SourceKind::Read {
        place: address_to_read_place(addr),
    });
    arena.source_expr(src)
}

/// Intern a `Constant`.
fn const_expr(arena: &mut ArenaBuilder, value: u32) -> ExprId {
    let src = arena.intern_source(SourceKind::Constant { value });
    arena.source_expr(src)
}

/// Lower `NoFieldLinearRelation` to `constant + Σ c·addr`.
fn lower_linear(arena: &mut ArenaBuilder, lin: &NoFieldLinearRelation) -> ExprId {
    let mut terms = Vec::new();
    if lin.constant != 0 {
        terms.push(const_expr(arena, lin.constant));
    }
    for (c, addr) in lin.linear_terms.iter() {
        let a = read_expr(arena, *addr);
        if *c == 1 {
            terms.push(a);
        } else {
            let cc = const_expr(arena, *c);
            terms.push(arena.mul(vec![cc, a]));
        }
    }
    if terms.is_empty() {
        const_expr(arena, 0)
    } else if terms.len() == 1 {
        terms[0]
    } else {
        arena.add(terms)
    }
}

/// Lower the `MaxQuadratic` relation math: `constant + Σ_quad c·a·b + Σ_lin c·a`.
fn lower_constraint(arena: &mut ArenaBuilder, rel: &NoFieldMaxQuadraticGKRRelation) -> ExprId {
    let mut terms = Vec::new();
    if rel.constant != 0 {
        terms.push(const_expr(arena, rel.constant));
    }
    for (a, set) in rel.quadratic_terms.iter() {
        let a_expr = read_expr(arena, *a);
        for (c, b) in set.iter() {
            let b_expr = read_expr(arena, *b);
            let prod = arena.mul(vec![a_expr, b_expr]);
            if *c == 1 {
                terms.push(prod);
            } else {
                let cc = const_expr(arena, *c);
                terms.push(arena.mul(vec![cc, prod]));
            }
        }
    }
    for (c, a) in rel.linear_terms.iter() {
        let a_expr = read_expr(arena, *a);
        if *c == 1 {
            terms.push(a_expr);
        } else {
            let cc = const_expr(arena, *c);
            terms.push(arena.mul(vec![cc, a_expr]));
        }
    }
    if terms.is_empty() {
        const_expr(arena, 0)
    } else if terms.len() == 1 {
        terms[0]
    } else {
        arena.add(terms)
    }
}

/// Lower the materialized-base lookup pair to its two output expressions
/// `[num = b + d, den = b * d]` where `b = gamma + in0`, `d = gamma + in1`.
fn lower_lookup_pair(arena: &mut ArenaBuilder, input: [GKRAddress; 2]) -> [ExprId; 2] {
    let gamma_src = arena.intern_source(SourceKind::Challenge {
        reference: ChallengeRef {
            key: ChallengeKey::LookupAdditive,
            power: ChallengePower::One,
        },
    });
    let gamma = arena.source_expr(gamma_src);

    let in0 = read_expr(arena, input[0]);
    let in1 = read_expr(arena, input[1]);

    let b = arena.add(vec![gamma, in0]);
    let d = arena.add(vec![gamma, in1]);

    let num = arena.add(vec![b, d]);
    let den = arena.mul(vec![b, d]);
    [num, den]
}

// ── address collection ─────────────────────────────────────────────────────

fn collect_base_addresses(rel: &NoFieldGKRRelation, out: &mut BTreeSet<GKRAddress>) {
    match rel {
        NoFieldGKRRelation::LinearBaseFieldRelation { input, .. } => {
            for (_, a) in input.linear_terms.iter() {
                out.insert(*a);
            }
        }
        NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, .. } => {
            out.insert(input[0]);
            out.insert(input[1]);
        }
        NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input, .. } => {
            for (a, set) in input.quadratic_terms.iter() {
                out.insert(*a);
                for (_, b) in set.iter() {
                    out.insert(*b);
                }
            }
            for (_, a) in input.linear_terms.iter() {
                out.insert(*a);
            }
        }
        other => panic!("collect_base_addresses: shape {:?} out of scope", other),
    }
}

// ── relation selection ──────────────────────────────────────────────────────

/// First `EnforceSingleMaxQuadraticConstraint` in layer 0 of the add_sub
/// artifact, plus the first `LookupPairFromMaterializedBaseInputs`. Returns
/// `(constraint, lookup_pair)`.
fn pick_from_add_sub() -> (NoFieldGKRRelation, NoFieldGKRRelation) {
    let artifact = build_add_sub_artifact();
    let layer = &artifact.layers[0];
    let mut constraint = None;
    let mut pair = None;
    for g in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        match &g.enforced_relation {
            NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { .. }
                if constraint.is_none() =>
            {
                constraint = Some(g.enforced_relation.clone());
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { .. } if pair.is_none() => {
                pair = Some(g.enforced_relation.clone());
            }
            _ => {}
        }
    }
    (
        constraint.expect("add_sub layer 0 must contain an EnforceSingleMaxQuadraticConstraint"),
        pair.expect("add_sub layer 0 must contain a LookupPairFromMaterializedBaseInputs"),
    )
}

/// Canonical `LinearBaseFieldRelation` fixture. (`build_add_sub_artifact` does
/// not emit this variant — it is fully lowered into caches/constraints — so we
/// take the canonical single-output linear relation from the shared fixtures.)
fn pick_linear() -> NoFieldGKRRelation {
    sample_relations()
        .into_iter()
        .find(|(name, _)| *name == "LinearBaseFieldRelation")
        .expect("LinearBaseFieldRelation fixture must exist")
        .1
}

// ── the spike test ──────────────────────────────────────────────────────────

#[test]
fn dag_ir_oracle_matches_prover_reference_on_three_roots() {
    const TRACE_LEN: usize = 2;
    const ROW: usize = 0;

    let linear = pick_linear();
    let (constraint, lookup_pair) = pick_from_add_sub();

    // Collect every base address the three relations read, and bind a single
    // fixed random assignment for each (the shared witness/memory source).
    let mut addrs = BTreeSet::new();
    collect_base_addresses(&linear, &mut addrs);
    collect_base_addresses(&constraint, &mut addrs);
    collect_base_addresses(&lookup_pair, &mut addrs);

    let ctx = RefCtx::new(&addrs, TRACE_LEN);

    // ── Reference (authoritative) values ──
    let ref_linear = reference_relation_values(&linear, ROW, &ctx);
    let ref_pair = reference_relation_values(&lookup_pair, ROW, &ctx);
    let ref_constraint = reference_relation_values(&constraint, ROW, &ctx);
    assert_eq!(ref_linear.len(), 1);
    assert_eq!(ref_pair.len(), 2, "lookup pair must produce (num, den)");
    assert_eq!(ref_constraint.len(), 1);

    // ── Hand-built DAG circuit: one layer, four roots ──
    //   root 0: linear           Output(slot 0)   — claim-bearing
    //   root 1: lookup pair num   Output(slot 0)   — claim-bearing
    //   root 2: lookup pair den   Output(slot 1)   — claim-bearing
    //   root 3: constraint        Constraint
    let mut arena = ArenaBuilder::new();

    let linear_input = match &linear {
        NoFieldGKRRelation::LinearBaseFieldRelation { input, .. } => input,
        _ => unreachable!(),
    };
    let linear_expr = lower_linear(&mut arena, linear_input);

    let pair_inputs = match &lookup_pair {
        NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, .. } => *input,
        _ => unreachable!(),
    };
    let [num_expr, den_expr] = lower_lookup_pair(&mut arena, pair_inputs);

    let constraint_input = match &constraint {
        NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input, .. } => input,
        _ => unreachable!(),
    };
    let constraint_expr = lower_constraint(&mut arena, constraint_input);

    let roots = vec![
        Root::Output {
            expr: linear_expr,
            sink: SinkId(0),
        },
        Root::Output {
            expr: num_expr,
            sink: SinkId(1),
        },
        Root::Output {
            expr: den_expr,
            sink: SinkId(2),
        },
        Root::Constraint {
            expr: constraint_expr,
        },
    ];
    let batching = BatchingOrder {
        roots: vec![RootId(0), RootId(1), RootId(2), RootId(3)],
    };
    let layer = DagLayer {
        sources: arena.sources().to_vec(),
        exprs: arena.exprs().to_vec(),
        roots,
        sinks: Vec::new(),
        batching,
        origins: std::collections::BTreeMap::new(),
    };

    // ── Bind resolvers to the SAME storage + gamma ──
    let read = StorageReadResolver { ctx: &ctx };
    let challenge = GammaChallengeResolver {
        gamma: ctx.lookup_additive,
    };
    let lookup = UnusedLookupResolver;
    let virtual_setup = UnusedVirtualSetupResolver;
    let resolvers = Resolvers {
        read: &read,
        lookup: &lookup,
        virtual_setup: &virtual_setup,
        challenge: &challenge,
    };

    // ── Evaluate each DAG root and compare to the matching reference value ──
    let eval_linear = eval_layer_root(&layer, RootId(0), ROW, &resolvers);
    let eval_num = eval_layer_root(&layer, RootId(1), ROW, &resolvers);
    let eval_den = eval_layer_root(&layer, RootId(2), ROW, &resolvers);
    let eval_constraint = eval_layer_root(&layer, RootId(3), ROW, &resolvers);

    assert_eq!(
        eval_linear, ref_linear[0],
        "LinearBaseFieldRelation: DAG-IR value diverged from prover reference"
    );
    assert_eq!(
        eval_num, ref_pair[0],
        "LookupPair num (slot 0): DAG-IR value diverged from prover reference"
    );
    assert_eq!(
        eval_den, ref_pair[1],
        "LookupPair den (slot 1): DAG-IR value diverged from prover reference"
    );
    assert_eq!(
        eval_constraint, ref_constraint[0],
        "EnforceSingleMaxQuadraticConstraint: DAG-IR value diverged from prover reference"
    );

    println!("DAG-IR oracle spike: all 3 shapes (4 roots) matched the prover reference.");
    println!("  linear      = {:?}", eval_linear);
    println!("  pair num    = {:?}", eval_num);
    println!("  pair den    = {:?}", eval_den);
    println!("  constraint  = {:?} (must equal the kernel's vanishing value)", eval_constraint);
}
