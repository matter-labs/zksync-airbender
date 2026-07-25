//! Task-2 semantic gate: the coefficient IR's `(acc_c0, acc_c2)` equals the
//! `X^0` / `X^2` coefficients of the CANONICAL alpha-combined spine.
//!
//! The oracle is independent of the new lowering: every source is given an affine
//! form `S(X) = s0 + X*ds` (design §4), the canonical claim cones are evaluated
//! with `eval_layer_expr` at `X = 0, 1, 2` and alpha-combined with the real
//! `ClaimBatching` powers, and the resulting quadratic is interpolated. Nothing
//! from `bwd/interp.rs` or `bwd/compile.rs` (the incumbent lineage) participates.
//!
//! The R0 layer's constraint root is built to be ZERO on the hypercube
//! (`w0*w1 - w3` with `w3`'s `Endpoint0` pinned to `w0.s0 * w1.s0`), which is the
//! premise the R0 `acc_c0` shortcut rests on — if that premise were violated the
//! parity assertion below would fail, not paper over it.

use std::collections::{BTreeMap, HashMap};

use cs::gkr_compiler::dag_ir::{
    ArenaBuilder, BatchingOrder, Bf, BwdRegime, ChallengeKey, ChallengePower, ChallengeRef,
    ChallengeResolver, ClaimInfo, DagLayer, ExprId, Ext, FieldKind, LookupResolver,
    LookupValueKind, ReadPlace, ReadResolver, Resolvers, Root, RootGroup, RootId, RootOrigin,
    RootSlot, SinkInfo, SinkKind, SourceKind, VirtualSetupKind, VirtualSetupResolver, bwd_roots,
    eval_layer_expr,
};
use field::{Field, FieldExtension, PrimeField};
use gkr_eval_isa::bwd::coeff::{
    CoeffLayer, CoeffResolver, CoefficientRecipeId, SourceId, interpret_coeff_layer,
    lower_coeff_layer,
};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::source::OriginLeaf;

const NEG_ONE: u32 = 0x78000001 - 1;
const OUT_LAYER: usize = 7;
/// The witness column whose `Endpoint0` is pinned so that `w0*w1 - w3` vanishes
/// on the hypercube.
const CONSTRAINT_COL: usize = 3;
/// Same, for the constant-addend layer: `w0*w1 - w4 + CONST_ADDEND` vanishes on
/// the hypercube.
const CONSTRAINT_COL2: usize = 4;
/// The constant addend both cones in `r0_constant_addend_layer` carry.
const CONST_ADDEND: u32 = 5;

// ── Affine witness model ─────────────────────────────────────────────────────

const FNV_OFFSET: u32 = 0x811c_9dc5;
const FNV_PRIME: u32 = 0x0100_0193;

fn fnv(seed: u32, words: &[u32]) -> u32 {
    let mut h = seed;
    for w in words {
        for b in w.to_le_bytes() {
            h ^= b as u32;
            h = h.wrapping_mul(FNV_PRIME);
        }
    }
    h
}

fn lift(v: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(v)
}

fn bf(v: u32) -> Bf {
    Bf::from_u32_with_reduction(v)
}

/// `(Endpoint0, Delta)` of witness `column` at `row`.
fn witness_pair(seed: u32, column: usize, row: usize) -> (Ext, Ext) {
    let ds = lift(bf(fnv(FNV_OFFSET, &[seed, 0xd1, column as u32, row as u32])));
    if column == CONSTRAINT_COL || column == CONSTRAINT_COL2 {
        let (a0, _) = witness_pair(seed, 0, row);
        let (b0, _) = witness_pair(seed, 1, row);
        let mut e0 = a0;
        e0.mul_assign(&b0);
        if column == CONSTRAINT_COL2 {
            e0.add_assign(&lift(bf(CONST_ADDEND)));
        }
        return (e0, ds);
    }
    (lift(bf(fnv(FNV_OFFSET, &[seed, 0xe0, column as u32, row as u32]))), ds)
}

/// `(Endpoint0, Delta)` of a virtual-setup source at `row`, in the BASE field —
/// `VirtualSetupResolver` serves `Bf`, so the oracle and the coefficient
/// interpreter must agree on a base-field affine form.
fn vs_pair(seed: u32, kind: &VirtualSetupKind, row: usize) -> (Bf, Bf) {
    let tag = match kind {
        VirtualSetupKind::RangeCheck16Bits => 0u32,
        VirtualSetupKind::RangeCheckTimestamp => 1,
        VirtualSetupKind::InitsAndTeardownsLow => 2,
        VirtualSetupKind::InitsAndTeardownsHigh => 3,
    };
    (
        bf(fnv(FNV_OFFSET, &[seed, 0xb0, tag, row as u32])),
        bf(fnv(FNV_OFFSET, &[seed, 0xb1, tag, row as u32])),
    )
}

struct Chal;
impl ChallengeResolver for Chal {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        let key = match &r.key {
            ChallengeKey::LookupAdditive => 0u32,
            ChallengeKey::LookupMultiplicative => 1,
            ChallengeKey::PermutationAdditive => 2,
            ChallengeKey::PermutationLinearization(_) => 3,
            ChallengeKey::ConstraintAggregation => 4,
            ChallengeKey::ClaimBatching => 5,
        };
        let power = match &r.power {
            ChallengePower::One => 1u32,
            ChallengePower::Static(i) => *i,
        };
        lift(bf(fnv(FNV_OFFSET, &[0xc0, key, power])))
    }
}

/// Reads every leaf at the sumcheck point `x` — `S(x) = s0 + x*ds`.
struct Leaves {
    seed: u32,
    x: u32,
}

impl Leaves {
    fn at(&self, e0: Ext, ds: Ext) -> Ext {
        let mut v = ds;
        v.mul_assign(&lift(bf(self.x)));
        v.add_assign(&e0);
        v
    }
}

impl ReadResolver for Leaves {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext {
        match place {
            ReadPlace::BaseLayerWitness { column } => {
                let (e0, ds) = witness_pair(self.seed, *column, row);
                self.at(e0, ds)
            }
            other => panic!("synthetic parity layers read only witness columns, got {other:?}"),
        }
    }
}

impl VirtualSetupResolver for Leaves {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> Bf {
        let (e0, ds) = vs_pair(self.seed, kind, row);
        let mut v = ds;
        v.mul_assign(&bf(self.x));
        v.add_assign(&e0);
        v
    }
}

impl LookupResolver for Leaves {
    fn lookup(&self, k: &LookupValueKind, _: usize, _: Ext, _: usize) -> Bf {
        panic!("synthetic parity layers have no lookup leaves ({k:?})")
    }
}

fn resolvers_at<'a>(leaves: &'a Leaves, ch: &'a Chal) -> Resolvers<'a> {
    Resolvers { read: leaves, lookup: leaves, virtual_setup: leaves, challenge: ch }
}

// ── Layer construction ───────────────────────────────────────────────────────

fn read_leaf(a: &mut ArenaBuilder, column: usize) -> ExprId {
    let s = a.intern_source(SourceKind::Read { place: ReadPlace::BaseLayerWitness { column } });
    a.source_expr(s)
}

fn const_leaf(a: &mut ArenaBuilder, value: u32) -> ExprId {
    let s = a.intern_source(SourceKind::Constant { value });
    a.source_expr(s)
}

fn challenge_leaf(a: &mut ArenaBuilder, key: ChallengeKey) -> ExprId {
    let s = a.intern_source(SourceKind::Challenge {
        reference: ChallengeRef { key, power: ChallengePower::One },
    });
    a.source_expr(s)
}

fn vs_leaf(a: &mut ArenaBuilder, kind: VirtualSetupKind) -> ExprId {
    let s = a.intern_source(SourceKind::VirtualSetup { kind });
    a.source_expr(s)
}

fn output_root(expr: ExprId, offset: usize, relation_index: usize) -> Root {
    Root {
        expr,
        materialize: Some(SinkInfo {
            kind: SinkKind::Inner { layer: OUT_LAYER, offset },
            field: FieldKind::Base,
        }),
        claim: Some(ClaimInfo {
            origin: RootOrigin {
                group: RootGroup::Gates,
                relation_index,
                slot: RootSlot::Output(offset),
            },
        }),
    }
}

fn constraint_root(expr: ExprId, relation_index: usize) -> Root {
    Root {
        expr,
        materialize: None,
        claim: Some(ClaimInfo {
            origin: RootOrigin {
                group: RootGroup::Gates,
                relation_index,
                slot: RootSlot::Constraint(0),
            },
        }),
    }
}

fn assemble(a: &ArenaBuilder, roots: Vec<Root>, batching: Vec<RootId>) -> DagLayer {
    DagLayer {
        sources: a.sources().to_vec(),
        exprs: a.exprs().to_vec(),
        roots,
        batching: BatchingOrder { roots: batching },
        resolutions: BTreeMap::new(),
    }
}

/// One materialized output root (degree 2, with a challenge coefficient, a
/// degree-1 addend and a virtual-setup factor) plus one claim-only constraint
/// root that is zero on the hypercube.
fn r0_parity_layer() -> DagLayer {
    let mut a = ArenaBuilder::new();
    let w0 = read_leaf(&mut a, 0);
    let w1 = read_leaf(&mut a, 1);
    let w2 = read_leaf(&mut a, 2);
    let w3 = read_leaf(&mut a, CONSTRAINT_COL);
    let vs = vs_leaf(&mut a, VirtualSetupKind::RangeCheck16Bits);
    let gamma = challenge_leaf(&mut a, ChallengeKey::LookupAdditive);
    let three = const_leaf(&mut a, 3);
    let neg = const_leaf(&mut a, NEG_ONE);

    let t1 = a.mul(vec![gamma, w0, w1]);
    let t2 = a.mul(vec![three, w2]);
    let t3 = a.mul(vec![w0, vs]);
    let out_cone = a.add(vec![t1, t2, t3]);

    let c1 = a.mul(vec![w0, w1]);
    let c2 = a.mul(vec![neg, w3]);
    let con_cone = a.add(vec![c1, c2]);

    assemble(
        &a,
        vec![output_root(out_cone, 0, 0), constraint_root(con_cone, 1)],
        vec![RootId(0), RootId(1)],
    )
}

/// Two claim-only roots whose batching order is not root-index order, one of them
/// carrying a scalar-only addend (so `c_init` is exercised).
fn ext_parity_layer() -> DagLayer {
    let mut a = ArenaBuilder::new();
    let w0 = read_leaf(&mut a, 0);
    let w1 = read_leaf(&mut a, 1);
    let w2 = read_leaf(&mut a, 2);
    let vs = vs_leaf(&mut a, VirtualSetupKind::RangeCheckTimestamp);
    let gamma = challenge_leaf(&mut a, ChallengeKey::LookupAdditive);
    let three = const_leaf(&mut a, 3);

    let t1 = a.mul(vec![gamma, w0, w1]);
    let t2 = a.mul(vec![three, w2]);
    let scalar = a.mul(vec![gamma, three]);
    let cone_a = a.add(vec![t1, t2, scalar]);

    let t3 = a.mul(vec![w0, vs]);
    let sum = a.add(vec![w1, w2]);
    let t4 = a.mul(vec![sum, w0]);
    let cone_b = a.add(vec![t3, t4]);

    assemble(
        &a,
        vec![constraint_root(cone_a, 0), constraint_root(cone_b, 1)],
        vec![RootId(1), RootId(0)],
    )
}

/// Both claim cones carry a scalar CONSTANT addend, so the spine's `c_init` is
/// structurally non-empty at R0. The materialized output's constant is inside its
/// output column, and the constraint's constant is cancelled by
/// `CONSTRAINT_COL2`'s pinned `Endpoint0` — so R0 must DROP the spine `c_init`
/// rather than add it on top of the output shortcut.
fn r0_constant_addend_layer() -> DagLayer {
    let mut a = ArenaBuilder::new();
    let w0 = read_leaf(&mut a, 0);
    let w1 = read_leaf(&mut a, 1);
    let w4 = read_leaf(&mut a, CONSTRAINT_COL2);
    let gamma = challenge_leaf(&mut a, ChallengeKey::LookupAdditive);
    let five = const_leaf(&mut a, CONST_ADDEND);
    let neg = const_leaf(&mut a, NEG_ONE);

    let t1 = a.mul(vec![gamma, w0, w1]);
    let out_cone = a.add(vec![t1, five]);

    let c1 = a.mul(vec![w0, w1]);
    let c2 = a.mul(vec![neg, w4]);
    let con_cone = a.add(vec![c1, c2, five]);

    assemble(
        &a,
        vec![output_root(out_cone, 0, 0), constraint_root(con_cone, 1)],
        vec![RootId(0), RootId(1)],
    )
}

// ── Oracle ───────────────────────────────────────────────────────────────────

/// The canonical alpha-combined spine at sumcheck point `x`:
/// `root_0 + sum_{i>=1} beta^i * root_i` over `bwd_roots` order.
fn spine_at(canonical: &DagLayer, row: usize, seed: u32, x: u32) -> Ext {
    let leaves = Leaves { seed, x };
    let ch = Chal;
    let r = resolvers_at(&leaves, &ch);
    let mut acc = Ext::ZERO;
    for (i, &rid) in bwd_roots(canonical).iter().enumerate() {
        let mut v = eval_layer_expr(canonical, canonical.roots[rid.0 as usize].expr, row, &r);
        if i > 0 {
            let power = if i == 1 { ChallengePower::One } else { ChallengePower::Static(i as u32) };
            let beta = ch.challenge(&ChallengeRef { key: ChallengeKey::ClaimBatching, power });
            v.mul_assign(&beta);
        }
        acc.add_assign(&v);
    }
    acc
}

/// `(c0, c2)` of the quadratic through `P(0), P(1), P(2)`.
fn interpolate(v0: Ext, v1: Ext, v2: Ext) -> (Ext, Ext) {
    // c2 = (v2 - 2*v1 + v0) / 2
    let mut num = v2;
    num.sub_assign(&v1);
    num.sub_assign(&v1);
    num.add_assign(&v0);
    let two_inv = lift(bf(2)).inverse().expect("2 is invertible");
    let mut c2 = num;
    c2.mul_assign(&two_inv);
    (v0, c2)
}

// ── Coefficient-side resolver ────────────────────────────────────────────────

/// Serves the coefficient interpreter: banked recipes evaluated under `Chal`, and
/// `(Endpoint0, Delta)` pairs from the SAME affine witness model the oracle uses.
/// A materialized-output source resolves to the producing cone's value at `X=0`
/// (witness consistency); its `Delta` is deliberately garbage, so any accidental
/// delta use of an output address breaks parity loudly.
struct Pairs<'a> {
    layer: &'a CoeffLayer,
    canonical: &'a DagLayer,
    outputs: HashMap<(usize, usize), ExprId>,
    seed: u32,
}

impl<'a> Pairs<'a> {
    fn new(layer: &'a CoeffLayer, canonical: &'a DagLayer, seed: u32) -> Self {
        let mut outputs = HashMap::new();
        for root in &canonical.roots {
            if let Some(sink) = &root.materialize {
                if let SinkKind::Inner { layer: l, offset } = sink.kind {
                    outputs.insert((l, offset), root.expr);
                }
            }
        }
        Pairs { layer, canonical, outputs, seed }
    }
}

impl CoeffResolver for Pairs<'_> {
    fn coefficient(&self, id: CoefficientRecipeId) -> Ext {
        self.layer
            .banked_recipe(id)
            .unwrap_or_else(|| panic!("interpreter asked for unbanked {id:?}"))
            .evaluate(&Chal)
    }

    fn source_pair(&self, id: SourceId, row: usize) -> (Ext, Ext) {
        match &self.layer.sources[id.0 as usize].origin {
            OriginLeaf::Read(ReadPlace::BaseLayerWitness { column }) => {
                witness_pair(self.seed, *column, row)
            }
            OriginLeaf::Read(ReadPlace::LayerOutput { layer, offset }) => {
                let expr = self.outputs[&(*layer, *offset)];
                let leaves = Leaves { seed: self.seed, x: 0 };
                let ch = Chal;
                let r = resolvers_at(&leaves, &ch);
                let e0 = eval_layer_expr(self.canonical, expr, row, &r);
                (e0, lift(bf(fnv(FNV_OFFSET, &[0xbad, *offset as u32, row as u32]))))
            }
            OriginLeaf::VirtualSetup { kind } => {
                let (e0, ds) = vs_pair(self.seed, kind, row);
                (lift(e0), lift(ds))
            }
            other => panic!("unexpected parity source origin {other:?}"),
        }
    }
}

// ── The gate ─────────────────────────────────────────────────────────────────

fn assert_parity(canonical: &DagLayer, regime: BwdRegime, ctx: &str) {
    let d = distill(canonical, regime, &HashMap::new(), None);
    let coeff = lower_coeff_layer(canonical, &d).unwrap_or_else(|e| panic!("[{ctx}] lower: {e:?}"));
    for seed in [1u32, 7] {
        let pairs = Pairs::new(&coeff, canonical, seed);
        for row in 0..6usize {
            let (want_c0, want_c2) = interpolate(
                spine_at(canonical, row, seed, 0),
                spine_at(canonical, row, seed, 1),
                spine_at(canonical, row, seed, 2),
            );
            let (got_c0, got_c2) = interpret_coeff_layer(&coeff, row, &pairs)
                .unwrap_or_else(|e| panic!("[{ctx}] interpret row {row}: {e:?}"));
            assert_eq!(got_c0, want_c0, "[{ctx}] seed {seed} row {row}: acc_c0");
            assert_eq!(got_c2, want_c2, "[{ctx}] seed {seed} row {row}: acc_c2");
        }
    }
}

#[test]
fn semantic_coefficients_match_canonical_dag_on_synthetic_rows() {
    let r0_layer = r0_parity_layer();

    // The R0 shortcut's premise: the claim-only constraint root really is zero on
    // the hypercube for this witness model.
    for row in 0..6usize {
        let leaves = Leaves { seed: 1, x: 0 };
        let ch = Chal;
        let r = resolvers_at(&leaves, &ch);
        let con = r0_layer.roots[1].expr;
        assert_eq!(
            eval_layer_expr(&r0_layer, con, row, &r),
            Ext::ZERO,
            "row {row}: the constraint cone must vanish at X=0"
        );
    }

    assert_parity(&r0_layer, BwdRegime::R0, "r0_layer/R0");
    assert_parity(&r0_layer, BwdRegime::Ext, "r0_layer/Ext");

    let ext_layer = ext_parity_layer();
    assert_parity(&ext_layer, BwdRegime::Ext, "ext_layer/Ext");

    // The continuation lowering really did route the scalar addend through
    // `c_init` (otherwise the parity above would have been trivially satisfiable
    // by a per-row constant term).
    let d = distill(&ext_layer, BwdRegime::Ext, &HashMap::new(), None);
    let coeff = lower_coeff_layer(&ext_layer, &d).expect("lower");
    assert!(coeff.c_init.is_some(), "the scalar addend must land in c_init");
}

/// Design §5.3 expected R0's spine `c_init` to be structurally empty and asked for
/// "a documented parity explanation" for any exception. On the pinned corpus the
/// exception is the COMMON case (26 of 57 R0 layers), so this is the explanation,
/// pinned: a scalar cone addend is already inside `cone(0)` — i.e. inside the
/// materialized output column, or inside the constraint's structural zero — so R0
/// must DROP the spine `c_init`. Adding it would double-count.
#[test]
fn r0_constant_addends_are_covered_by_the_output_shortcut() {
    let layer = r0_constant_addend_layer();

    // The premise: the constraint cone (constant addend included) still vanishes.
    for row in 0..6usize {
        let leaves = Leaves { seed: 1, x: 0 };
        let ch = Chal;
        let r = resolvers_at(&leaves, &ch);
        assert_eq!(
            eval_layer_expr(&layer, layer.roots[1].expr, row, &r),
            Ext::ZERO,
            "row {row}: the constraint cone must vanish at X=0"
        );
    }

    // The spine really does carry a scalar-pure addend at R0 ...
    let d = distill(&layer, BwdRegime::R0, &HashMap::new(), None);
    assert!(
        !d.fragments.c_init.terms.is_empty(),
        "this fixture exists to exercise a NON-empty R0 c_init"
    );
    // ... which R0 drops, and dropping is what makes the coefficients correct.
    let coeff = lower_coeff_layer(&layer, &d).expect("R0 lowering must not reject this");
    assert_eq!(coeff.c_init, None, "R0 initializes acc_c0 to zero");
    assert_parity(&layer, BwdRegime::R0, "const_addend/R0");

    // The same scalar addends DO feed the continuation initializer.
    let ext = distill(&layer, BwdRegime::Ext, &HashMap::new(), None);
    let ext_coeff = lower_coeff_layer(&layer, &ext).expect("Ext lowering");
    assert!(ext_coeff.c_init.is_some(), "continuation keeps the scalar contribution");
    assert_parity(&layer, BwdRegime::Ext, "const_addend/Ext");
}
