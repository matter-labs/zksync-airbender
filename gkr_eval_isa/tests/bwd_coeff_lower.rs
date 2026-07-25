//! Task-2 lowering / normalization gates for the backward coefficient IR
//! (design §5 "Shared DAG lowering", §6 "Semantic term set").
//!
//! Every gate here is a STRUCTURAL property of `lower_coeff_layer`, so the layers
//! are built by hand (no fixture load): the assertions are about which terms
//! exist, which projections they read, and which coefficient recipe each one
//! carries. Semantic `(acc_c0, acc_c2)` parity against the canonical DAG lives in
//! the sibling `bwd_coeff_parity.rs`.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};

use cs::gkr_compiler::dag_ir::{
    ArenaBuilder, BatchingOrder, BwdRegime, ChallengeKey, ChallengePower, ChallengeRef,
    ChallengeResolver, ClaimInfo, DagLayer, ExprId, Ext, FieldKind, ReadPlace, Root, RootGroup,
    RootId, RootOrigin, RootSlot, SinkInfo, SinkKind, SourceKind, bwd_roots,
};
use field::{Field, FieldExtension, PrimeField};
use gkr_eval_isa::bwd::coeff::{
    CoeffError, CoeffLayer, CoeffResolver, CoeffTerm, CoefficientRecipeId, Projection, SourceId,
    TermId, interpret_coeff_layer, lower_coeff_layer,
};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::source::OriginLeaf;

type Bf = cs::gkr_compiler::dag_ir::Bf;

/// BabyBear `-1` as a canonical `Constant` payload (same constant `fwd::compile`
/// and `tests/common` use to build a negated additive child).
const NEG_ONE: u32 = 0x78000001 - 1;

/// The inner layer every synthetic materialized output writes to.
const OUT_LAYER: usize = 7;

// ── Layer construction ───────────────────────────────────────────────────────

fn read_leaf(a: &mut ArenaBuilder, column: usize) -> ExprId {
    let s = a.intern_source(SourceKind::Read { place: ReadPlace::BaseLayerWitness { column } });
    a.source_expr(s)
}

fn const_leaf(a: &mut ArenaBuilder, value: u32) -> ExprId {
    let s = a.intern_source(SourceKind::Constant { value });
    a.source_expr(s)
}

fn challenge_leaf_with(a: &mut ArenaBuilder, key: ChallengeKey, power: ChallengePower) -> ExprId {
    let s = a.intern_source(SourceKind::Challenge { reference: ChallengeRef { key, power } });
    a.source_expr(s)
}

fn challenge_leaf(a: &mut ArenaBuilder, key: ChallengeKey) -> ExprId {
    challenge_leaf_with(a, key, ChallengePower::One)
}

/// A claim-bearing root with a materialized `Inner` output at `offset`.
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

/// A claim-ONLY constraint root (`materialize: None`).
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

fn lower(layer: &DagLayer, regime: BwdRegime) -> Result<CoeffLayer, CoeffError> {
    let d = distill(layer, regime, &HashMap::new(), None);
    lower_coeff_layer(layer, &d)
}

fn lower_permuted(layer: &DagLayer, regime: BwdRegime, perm: &[usize]) -> CoeffLayer {
    let d = distill(layer, regime, &HashMap::new(), Some(perm));
    lower_coeff_layer(layer, &d).expect("permuted lowering must succeed")
}

// ── Term inspection helpers ──────────────────────────────────────────────────

/// Every source this term reads at `Endpoint0`. A native `DualProduct` consumes
/// BOTH projections of both factors, so both of its sources count.
fn endpoint0_sources(t: &CoeffTerm) -> Vec<SourceId> {
    match t {
        CoeffTerm::C0Linear { value, .. } => match value.projection {
            Projection::Endpoint0 => vec![value.source],
            Projection::Delta => vec![],
        },
        CoeffTerm::C2Product { lhs, rhs, .. } => [lhs, rhs]
            .iter()
            .filter(|p| p.projection == Projection::Endpoint0)
            .map(|p| p.source)
            .collect(),
        CoeffTerm::DualProduct { lhs, rhs, .. } => vec![*lhs, *rhs],
    }
}

fn origin_of(c: &CoeffLayer, s: SourceId) -> OriginLeaf {
    c.sources[s.0 as usize].origin.clone()
}

/// The witness column a source reads, for tests whose layers use only
/// `BaseLayerWitness` leaves.
fn column_of(c: &CoeffLayer, s: SourceId) -> usize {
    match origin_of(c, s) {
        OriginLeaf::Read(ReadPlace::BaseLayerWitness { column }) => column,
        other => panic!("expected a witness-column source, got {other:?}"),
    }
}

/// The materialized-output offset a source reads.
fn out_offset_of(c: &CoeffLayer, s: SourceId) -> usize {
    match origin_of(c, s) {
        OriginLeaf::Read(ReadPlace::LayerOutput { layer, offset }) => {
            assert_eq!(layer, OUT_LAYER, "output read must target the sink's layer");
            offset
        }
        other => panic!("expected a materialized-output source, got {other:?}"),
    }
}

/// A coefficient recipe that is a plain scalar (no challenge factor), as its
/// canonical reduced BabyBear value. Reserved literals resolve without a bank
/// entry — that is the whole point of reserving them.
fn scalar_coefficient(c: &CoeffLayer, id: CoefficientRecipeId) -> u32 {
    if id == CoefficientRecipeId::ONE {
        return 1;
    }
    if id == CoefficientRecipeId::NEG_ONE {
        return NEG_ONE;
    }
    let r = c.banked_recipe(id).unwrap_or_else(|| panic!("{id:?} has no bank entry"));
    assert_eq!(r.terms.len(), 1, "expected a single-product recipe, got {r:?}");
    assert!(r.terms[0].challenges.is_empty(), "expected a scalar-only recipe, got {r:?}");
    r.terms[0].scalar
}

/// The `ClaimBatching` power a root's `acc_c0` coefficient carries: `None` for
/// root zero (unscaled), `Some(power)` for `beta^i`.
fn batching_power(c: &CoeffLayer, id: CoefficientRecipeId) -> Option<ChallengePower> {
    if id == CoefficientRecipeId::ONE {
        return None;
    }
    let r = c.banked_recipe(id).unwrap_or_else(|| panic!("{id:?} has no bank entry"));
    assert_eq!(r.terms.len(), 1, "a batching factor is one product, got {r:?}");
    let p = &r.terms[0];
    assert_eq!(p.scalar, 1, "a batching factor carries no scalar, got {r:?}");
    assert_eq!(p.challenges.len(), 1, "a batching factor is one challenge, got {r:?}");
    let cr = &p.challenges[0].0;
    assert_eq!(cr.key, ChallengeKey::ClaimBatching, "not a batching challenge: {cr:?}");
    Some(cr.power.clone())
}

/// `offset -> batching power` for every R0 `acc_c0` term.
fn root_coefficient_pairing(c: &CoeffLayer) -> BTreeMap<usize, Option<ChallengePower>> {
    let mut out = BTreeMap::new();
    for t in &c.terms {
        if let CoeffTerm::C0Linear { coefficient, value, .. } = t {
            let prev = out.insert(out_offset_of(c, value.source), batching_power(c, *coefficient));
            assert!(prev.is_none(), "two acc_c0 terms over one output address");
        }
    }
    out
}

fn expected_power(batching_position: usize) -> Option<ChallengePower> {
    match batching_position {
        0 => None,
        1 => Some(ChallengePower::One),
        i => Some(ChallengePower::Static(i as u32)),
    }
}

// ── Resolvers ────────────────────────────────────────────────────────────────

const FNV_OFFSET: u32 = 0x811c_9dc5;
const FNV_PRIME: u32 = 0x0100_0193;

fn hash_dbg<T: std::fmt::Debug>(t: &T, salt: u32) -> u32 {
    let mut h = FNV_OFFSET;
    for b in format!("{t:?}").as_bytes() {
        h ^= *b as u32;
        h = h.wrapping_mul(FNV_PRIME);
    }
    for b in salt.to_le_bytes() {
        h ^= b as u32;
        h = h.wrapping_mul(FNV_PRIME);
    }
    h
}

fn lift(v: u32) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(Bf::from_u32_with_reduction(v))
}

struct Chal;
impl ChallengeResolver for Chal {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        lift(hash_dbg(r, 0))
    }
}

/// Serves banked coefficients (by evaluating the normalized recipe) and a
/// deterministic `(Endpoint0, Delta)` pair per structural source origin, while
/// recording which coefficient ids the interpreter actually asked for.
struct Probe<'a> {
    layer: &'a CoeffLayer,
    /// Overrides the value served for `layer.c_init`.
    c_init_override: Option<Ext>,
    queried: RefCell<Vec<CoefficientRecipeId>>,
}

impl<'a> Probe<'a> {
    fn new(layer: &'a CoeffLayer) -> Self {
        Probe { layer, c_init_override: None, queried: RefCell::new(Vec::new()) }
    }

    fn with_c_init(layer: &'a CoeffLayer, v: Ext) -> Self {
        Probe { layer, c_init_override: Some(v), queried: RefCell::new(Vec::new()) }
    }

    fn pair(&self, origin: &OriginLeaf, row: usize) -> (Ext, Ext) {
        (lift(hash_dbg(origin, row as u32)), lift(hash_dbg(origin, row as u32 ^ 0x5f5f)))
    }

    fn pair_for_column(&self, column: usize, row: usize) -> (Ext, Ext) {
        self.pair(&OriginLeaf::Read(ReadPlace::BaseLayerWitness { column }), row)
    }
}

impl CoeffResolver for Probe<'_> {
    fn coefficient(&self, id: CoefficientRecipeId) -> Ext {
        self.queried.borrow_mut().push(id);
        if self.c_init_override.is_some() && self.layer.c_init == Some(id) {
            return self.c_init_override.unwrap();
        }
        self.layer
            .banked_recipe(id)
            .unwrap_or_else(|| panic!("interpreter asked for unbanked {id:?}"))
            .evaluate(&Chal)
    }

    fn source_pair(&self, id: SourceId, row: usize) -> (Ext, Ext) {
        self.pair(&self.layer.sources[id.0 as usize].origin, row)
    }
}

// ── R0 acc_c0 ────────────────────────────────────────────────────────────────

#[test]
fn r0_materialized_output_uses_one_endpoint0_read() {
    let mut a = ArenaBuilder::new();
    let w0 = read_leaf(&mut a, 0);
    let w1 = read_leaf(&mut a, 1);
    let prod = a.mul(vec![w0, w1]);
    let sum = a.add(vec![w0, w1]);
    let layer = assemble(
        &a,
        vec![output_root(prod, 0, 0), output_root(sum, 1, 1)],
        vec![RootId(0), RootId(1)],
    );

    let c = lower(&layer, BwdRegime::R0).expect("R0 lowering");

    let linear: Vec<&CoeffTerm> =
        c.terms.iter().filter(|t| matches!(t, CoeffTerm::C0Linear { .. })).collect();
    assert_eq!(linear.len(), 2, "one acc_c0 term per materialized claim root: {:?}", c.terms);

    let mut offsets: Vec<usize> = Vec::new();
    for t in &linear {
        let CoeffTerm::C0Linear { value, field, .. } = t else { unreachable!() };
        assert_eq!(value.projection, Projection::Endpoint0, "R0 acc_c0 is an Endpoint0 read");
        assert_eq!(*field, FieldKind::Base, "the sink's field is the read width");
        offsets.push(out_offset_of(&c, value.source));
    }
    offsets.sort();
    assert_eq!(offsets, vec![0, 1], "each root reads its OWN output address");

    // The R0 advantage: no cone leaf is ever resolved at Endpoint0. Only the
    // materialized output addresses are.
    for t in &c.terms {
        for s in endpoint0_sources(t) {
            assert!(
                matches!(origin_of(&c, s), OriginLeaf::Read(ReadPlace::LayerOutput { .. })),
                "R0 re-evaluated a cone leaf at Endpoint0: {:?} in {t:?}",
                origin_of(&c, s)
            );
        }
    }

    // One read per root, not one per (root, cone leaf).
    let e0: usize = c.terms.iter().map(|t| endpoint0_sources(t).len()).sum();
    assert_eq!(e0, 2, "exactly one Endpoint0 read per materialized root");

    assert_eq!(c.c_init, None, "R0 initializes acc_c0 to zero (§5.3)");
}

#[test]
fn r0_constraint_root_contributes_zero_without_reading_its_cone() {
    let mut a = ArenaBuilder::new();
    let w0 = read_leaf(&mut a, 0);
    let w1 = read_leaf(&mut a, 1);
    let prod = a.mul(vec![w0, w1]);
    let layer = assemble(&a, vec![constraint_root(prod, 0)], vec![RootId(0)]);

    let c = lower(&layer, BwdRegime::R0).expect("R0 lowering");

    assert!(
        !c.terms.iter().any(|t| matches!(t, CoeffTerm::C0Linear { .. })),
        "a claim-only constraint root is structurally zero on the hypercube: {:?}",
        c.terms
    );
    assert_eq!(c.c_init, None);
    for t in &c.terms {
        assert!(endpoint0_sources(t).is_empty(), "the constraint cone must not be read at X=0");
    }
    assert_eq!(c.terms.len(), 1, "only the delta product survives: {:?}", c.terms);

    let p = Probe::new(&c);
    let (acc_c0, acc_c2) = interpret_coeff_layer(&c, 3, &p).expect("interpret");
    assert_eq!(acc_c0, Ext::ZERO, "acc_c0 is exactly zero for a constraint-only R0 layer");
    let (_, d0) = p.pair_for_column(0, 3);
    let (_, d1) = p.pair_for_column(1, 3);
    let mut want = d0;
    want.mul_assign(&d1);
    assert_eq!(acc_c2, want, "acc_c2 = dA*dB");
}

#[test]
fn r0_root_coefficients_follow_relation_order() {
    // Batching order is deliberately NOT root-index order: "root zero" (the
    // unscaled claim) is RootId(2), so keying the unscaled slot off RootId(0)
    // fails here.
    let mut a = ArenaBuilder::new();
    let w0 = read_leaf(&mut a, 0);
    let w1 = read_leaf(&mut a, 1);
    let w2 = read_leaf(&mut a, 2);
    let cone_a = a.mul(vec![w0, w1]);
    let cone_b = a.mul(vec![w1, w2]);
    let cone_c = a.mul(vec![w0, w2]);
    let layer = assemble(
        &a,
        vec![output_root(cone_a, 0, 0), output_root(cone_b, 1, 1), output_root(cone_c, 2, 2)],
        vec![RootId(2), RootId(0), RootId(1)],
    );
    assert_eq!(bwd_roots(&layer), &[RootId(2), RootId(0), RootId(1)]);

    // The canonical pairing, read off `bwd_roots`: batching position i carries
    // beta^i, and each root's own materialized address identifies it.
    let mut expect: BTreeMap<usize, Option<ChallengePower>> = BTreeMap::new();
    for (i, &rid) in bwd_roots(&layer).iter().enumerate() {
        let sink = layer.roots[rid.0 as usize].materialize.as_ref().expect("materialized");
        let SinkKind::Inner { offset, .. } = sink.kind else { panic!("{:?}", sink.kind) };
        expect.insert(offset, expected_power(i));
    }
    assert_eq!(
        expect,
        BTreeMap::from([
            (2, None),
            (0, Some(ChallengePower::One)),
            (1, Some(ChallengePower::Static(2))),
        ])
    );

    // The pairing is a property of the canonical batching order, not of the
    // relation-unit construction order.
    for perm in [vec![0, 1, 2], vec![2, 1, 0], vec![1, 2, 0]] {
        let c = lower_permuted(&layer, BwdRegime::R0, &perm);
        assert_eq!(
            root_coefficient_pairing(&c),
            expect,
            "relation-unit permutation {perm:?} moved a root's batching factor"
        );
    }
}

// ── Continuation ─────────────────────────────────────────────────────────────

#[test]
fn continuation_c_init_is_evaluated_once_per_program() {
    let mut a = ArenaBuilder::new();
    let w0 = read_leaf(&mut a, 0);
    let w1 = read_leaf(&mut a, 1);
    let gamma = challenge_leaf(&mut a, ChallengeKey::LookupAdditive);
    let prod = a.mul(vec![w0, w1]);
    let cone = a.add(vec![gamma, prod]);
    let layer = assemble(&a, vec![constraint_root(cone, 0)], vec![RootId(0)]);

    let c = lower(&layer, BwdRegime::Ext).expect("Ext lowering");

    let init = c.c_init.expect("the scalar addend must land in c_init, not in a term");
    assert_eq!(c.terms.len(), 1, "the scalar contribution is not a term: {:?}", c.terms);
    assert!(matches!(c.terms[0], CoeffTerm::DualProduct { .. }), "{:?}", c.terms[0]);

    // The whole scalar contribution is ONE recipe, asked for exactly once per
    // row: it is the per-thread `acc_c0` initializer, not a per-term factor.
    let p = Probe::new(&c);
    for row in [0usize, 1, 5] {
        p.queried.borrow_mut().clear();
        interpret_coeff_layer(&c, row, &p).expect("interpret");
        assert_eq!(
            p.queried.borrow().iter().filter(|&&id| id == init).count(),
            1,
            "c_init must be consumed exactly once per row"
        );
    }

    // Changing only the c_init value shifts acc_c0 by exactly that delta on
    // every row, and never touches acc_c2.
    let k1 = lift(11);
    let k2 = lift(29);
    let p1 = Probe::with_c_init(&c, k1);
    let p2 = Probe::with_c_init(&c, k2);
    for row in 0..4usize {
        let (a0, a2) = interpret_coeff_layer(&c, row, &p1).expect("interpret");
        let (b0, b2) = interpret_coeff_layer(&c, row, &p2).expect("interpret");
        let mut want = k1;
        want.sub_assign(&k2);
        let mut got = a0;
        got.sub_assign(&b0);
        assert_eq!(got, want, "row {row}: c_init is a plain additive initializer");
        assert_eq!(a2, b2, "row {row}: c_init never feeds acc_c2");
    }
}

#[test]
fn continuation_product_is_native_dual() {
    let mut a = ArenaBuilder::new();
    let w0 = read_leaf(&mut a, 0);
    let w1 = read_leaf(&mut a, 1);
    let prod = a.mul(vec![w0, w1]);
    let layer = assemble(&a, vec![constraint_root(prod, 0)], vec![RootId(0)]);

    let ext = lower(&layer, BwdRegime::Ext).expect("Ext lowering");
    assert_eq!(ext.terms.len(), 1, "one product, one native dual: {:?}", ext.terms);
    let CoeffTerm::DualProduct { coefficient, lhs, rhs, .. } = ext.terms[0] else {
        panic!("continuation products must be native duals, got {:?}", ext.terms[0]);
    };
    assert_eq!(scalar_coefficient(&ext, coefficient), 1);
    assert_eq!(
        [column_of(&ext, lhs), column_of(&ext, rhs)],
        [0, 1],
        "dual factors are sorted by stable source identity"
    );
    assert!(
        !ext.terms.iter().any(|t| matches!(t, CoeffTerm::C2Product { .. })),
        "a continuation product is never split into an independent c2 term"
    );

    // R0 is the contrast: acc_c0 there comes from the root output, so the
    // product only needs its delta half.
    let r0 = lower(&layer, BwdRegime::R0).expect("R0 lowering");
    assert_eq!(r0.terms.len(), 1);
    assert!(matches!(r0.terms[0], CoeffTerm::C2Product { .. }), "{:?}", r0.terms[0]);
}

// ── Distribution / degree ────────────────────────────────────────────────────

#[test]
fn multi_atom_add_distribution_preserves_multiplicity() {
    // (A + B) * (A + B): a 2-atom fragment the fragment walk deliberately does
    // NOT distribute, so the coefficient lowering must — into A*A + 2*A*B + B*B.
    let mut a = ArenaBuilder::new();
    let w0 = read_leaf(&mut a, 0);
    let w1 = read_leaf(&mut a, 1);
    let s = a.add(vec![w0, w1]);
    let sq = a.mul(vec![s, s]);
    let layer = assemble(&a, vec![constraint_root(sq, 0)], vec![RootId(0)]);

    let c = lower(&layer, BwdRegime::Ext).expect("Ext lowering");
    assert_eq!(c.terms.len(), 3, "A*A, A*B, B*B: {:?}", c.terms);

    let mut got: BTreeMap<(usize, usize), u32> = BTreeMap::new();
    for t in &c.terms {
        let CoeffTerm::DualProduct { coefficient, lhs, rhs, .. } = t else { panic!("{t:?}") };
        let key = (column_of(&c, *lhs), column_of(&c, *rhs));
        let prev = got.insert(key, scalar_coefficient(&c, *coefficient));
        assert!(prev.is_none(), "A*B and B*A must merge into ONE body, not two");
    }
    assert_eq!(
        got,
        BTreeMap::from([((0, 0), 1), ((0, 1), 2), ((1, 1), 1)]),
        "the cross term's multiplicity must survive as a coefficient of 2"
    );
}

#[test]
fn degree_three_is_a_compiler_error() {
    // (a) three independent factors.
    let mut a = ArenaBuilder::new();
    let w0 = read_leaf(&mut a, 0);
    let w1 = read_leaf(&mut a, 1);
    let w2 = read_leaf(&mut a, 2);
    let cube = a.mul(vec![w0, w1, w2]);
    let layer = assemble(&a, vec![constraint_root(cube, 0)], vec![RootId(0)]);
    for regime in [BwdRegime::R0, BwdRegime::Ext] {
        let err = lower(&layer, regime).expect_err("degree three must not compile");
        assert!(
            matches!(err, CoeffError::DegreeTooHigh { degree: 3, .. }),
            "{regime:?}: wrong error {err:?}"
        );
    }

    // (b) a quadratic ATOM inside a multi-atom product — the fragment walk keeps
    // the Add opaque, so the degree only shows up during linearization.
    let mut b = ArenaBuilder::new();
    let v0 = read_leaf(&mut b, 0);
    let v1 = read_leaf(&mut b, 1);
    let v2 = read_leaf(&mut b, 2);
    let inner = b.mul(vec![v0, v1]);
    let quad_atom = b.add(vec![inner, v2]);
    let deg3 = b.mul(vec![quad_atom, v2]);
    let layer_b = assemble(&b, vec![constraint_root(deg3, 0)], vec![RootId(0)]);
    let err = lower(&layer_b, BwdRegime::Ext).expect_err("degree three must not compile");
    assert!(matches!(err, CoeffError::DegreeTooHigh { degree: 3, .. }), "wrong error {err:?}");
}

/// `Static(1)` and `One` spell the SAME power, so they must intern to one recipe
/// and one id — while a repeated factor and a higher power must NOT be merged,
/// because `ChallengePower` is only an exponent for the keys whose resolver arm
/// reads it (`LookupAdditive` ignores it and returns `gamma` for any power, so
/// rewriting `gamma*gamma` as `gamma^2` would silently lose a factor).
#[test]
fn challenge_power_spellings_of_one_intern_to_a_single_id() {
    let mut a = ArenaBuilder::new();
    let w0 = read_leaf(&mut a, 0);
    let w1 = read_leaf(&mut a, 1);
    let as_one = challenge_leaf_with(&mut a, ChallengeKey::LookupMultiplicative, ChallengePower::One);
    let as_static_1 =
        challenge_leaf_with(&mut a, ChallengeKey::LookupMultiplicative, ChallengePower::Static(1));
    let t0 = a.mul(vec![as_one, w0]);
    let t1 = a.mul(vec![as_static_1, w1]);
    let cone = a.add(vec![t0, t1]);
    let layer = assemble(&a, vec![constraint_root(cone, 0)], vec![RootId(0)]);

    let c = lower(&layer, BwdRegime::Ext).expect("Ext lowering");
    assert_eq!(c.terms.len(), 2, "{:?}", c.terms);
    assert_eq!(c.coefficients.len(), 1, "one power, one bank entry: {:?}", c.coefficients);
    let ids: std::collections::BTreeSet<CoefficientRecipeId> =
        c.terms.iter().map(|t| t.coefficient()).collect();
    assert_eq!(ids.len(), 1, "both spellings must reach the same CoefficientRecipeId");
    assert_eq!(
        c.coefficients[0].terms[0].challenges[0].0.power,
        ChallengePower::One,
        "the canonical spelling of the first power is One"
    );

    // The unsound merge must NOT happen: gamma*gamma and gamma^2 stay distinct.
    let mut b = ArenaBuilder::new();
    let v0 = read_leaf(&mut b, 0);
    let v1 = read_leaf(&mut b, 1);
    let g1 = challenge_leaf_with(&mut b, ChallengeKey::LookupAdditive, ChallengePower::One);
    let g2 = challenge_leaf_with(&mut b, ChallengeKey::LookupAdditive, ChallengePower::Static(2));
    let squared = b.mul(vec![g1, g1, v0]);
    let power = b.mul(vec![g2, v1]);
    let cone_b = b.add(vec![squared, power]);
    let layer_b = assemble(&b, vec![constraint_root(cone_b, 0)], vec![RootId(0)]);

    let cb = lower(&layer_b, BwdRegime::Ext).expect("Ext lowering");
    assert_eq!(
        cb.coefficients.len(),
        2,
        "gamma*gamma must not be rewritten as gamma^2 — LookupAdditive ignores power: {:?}",
        cb.coefficients
    );
    let ids_b: std::collections::BTreeSet<CoefficientRecipeId> =
        cb.terms.iter().map(|t| t.coefficient()).collect();
    assert_eq!(ids_b.len(), 2);
}

// ── Normalization ────────────────────────────────────────────────────────────

#[test]
fn normalization_cancels_signs_and_removes_zero_one_and_copy_alias() {
    let mut a = ArenaBuilder::new();
    let w_a = read_leaf(&mut a, 0);
    let w_b = read_leaf(&mut a, 1);
    let w_c = read_leaf(&mut a, 2);
    let w_d = read_leaf(&mut a, 3);
    let w_e = read_leaf(&mut a, 4);
    let w_f = read_leaf(&mut a, 5);
    let w_g = read_leaf(&mut a, 6);
    let one = const_leaf(&mut a, 1);
    let zero = const_leaf(&mut a, 0);
    let two = const_leaf(&mut a, 2);
    let neg = const_leaf(&mut a, NEG_ONE);

    let mul_one = a.mul(vec![one, w_a]); // ordinary multiplication by one
    let alias_b = a.add(vec![w_b]); // unary alias (CopyAlias shape)
    let mul_zero = a.mul(vec![zero, w_c]); // multiplicative zero
    let neg_d = a.mul(vec![neg, w_d]); // D - D: coefficient cancels
    let two_e = a.mul(vec![two, w_e]);
    let neg_e = a.mul(vec![neg, w_e]); // 2E - E: folds back to one
    let alias_f = a.add(vec![w_f]);
    let dual = a.mul(vec![alias_f, w_g]); // alias inside a product
    let cone = a.add(vec![mul_one, alias_b, mul_zero, w_d, neg_d, two_e, neg_e, dual]);
    let layer = assemble(&a, vec![constraint_root(cone, 0)], vec![RootId(0)]);

    let c = lower(&layer, BwdRegime::Ext).expect("Ext lowering");

    assert!(c.coefficients.is_empty(), "every surviving coefficient is +/-1: {:?}", c.coefficients);
    assert_eq!(c.c_init, None, "no scalar addend here");

    let mut linear: Vec<usize> = Vec::new();
    let mut duals: Vec<(usize, usize)> = Vec::new();
    for t in &c.terms {
        assert_eq!(
            t.coefficient(),
            CoefficientRecipeId::ONE,
            "normalization must fold all-one products into the reserved literal: {t:?}"
        );
        match t {
            CoeffTerm::C0Linear { value, .. } => linear.push(column_of(&c, value.source)),
            CoeffTerm::DualProduct { lhs, rhs, .. } => {
                duals.push((column_of(&c, *lhs), column_of(&c, *rhs)))
            }
            other => panic!("unexpected term {other:?}"),
        }
    }
    linear.sort();
    assert_eq!(linear, vec![0, 1, 4], "A (x1), B (alias), E (2E-E) survive; C (x0), D (D-D) do not");
    assert_eq!(duals, vec![(5, 6)], "the aliased factor is erased, leaving one dual");

    // A pruned body's leaves never reach the source table.
    let columns: Vec<usize> = (0..c.sources.len()).map(|i| column_of(&c, SourceId(i as u32))).collect();
    assert_eq!(columns, vec![0, 1, 4, 5, 6], "sources are the referenced ones, in stable order");

    // TermIds are dense and follow the emitted order.
    for (i, t) in c.terms.iter().enumerate() {
        assert_eq!(t.id(), TermId(i as u32));
    }
}
