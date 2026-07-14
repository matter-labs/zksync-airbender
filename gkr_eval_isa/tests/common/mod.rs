//! Shared fixture/resolver helpers for the Stage-3 integration tests.
//!
//! Each `tests/*.rs` is a separate binary; this module is included via `mod common;`
//! so the Stage-3 schedule-driven tests (and any sibling) reach the same fixture
//! loading + `SyntheticResolvers` used by `fwd_parity.rs`. Lib items are reached via
//! `gkr_eval_isa::`, never `crate::`.

use std::collections::HashMap;
use std::path::PathBuf;

use cs::gkr_compiler::dag_ir::{
    bwd_cache_fences, eval_layer_expr, lower_dag, validate, validate_circuit_schedule, Bf,
    ChallengeRef, ChallengeResolver, CircuitSchedule, DagCircuit, DagLayer, Expr, ExprId, Ext,
    LookupResolver, LookupValueKind, ReadPlace, ReadResolver, Resolvers, SourceKind,
    VirtualSetupKind, VirtualSetupResolver,
};
use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use field::{Field, FieldExtension, PrimeField};

// ── SP1 backward-reduction test surface (added Task 1) ────────────────────────
use std::collections::{BTreeMap, BTreeSet};

use cs::gkr_compiler::dag_ir::{
    bwd_roots, BatchingOrder, BwdRegime, ChallengeKey, ChallengePower, ClaimInfo, FieldKind, Root,
    RootGroup, RootId, RootOrigin, RootSlot, SiteKey, SourceId, SourceInfo,
};
use gkr_eval_isa::bwd::compile::{compile_distilled_legacy_only, BwdCompiledLayer};
use gkr_eval_isa::bwd::distill::{bind, distill, distilled_site_domain, DistilledLayer};
use gkr_eval_isa::bwd::interp::{interpret_bwd_row, role_combine, sumcheck_fold_point, Role};
use gkr_eval_isa::bwd::source::{BwdSpecial, FoldState, MaterializationPolicy, OriginLeaf};
use gkr_eval_isa::fwd::compile::{build_cross_layer_field_map, SiteDecisions};
use gkr_eval_isa::fwd::encode::{decode, encode as encode_result};
use gkr_eval_isa::fwd::error::CompileError;
use gkr_eval_isa::fwd::isa::{Instr, OperandLine, Program};

/// The cross-layer field map threaded into `distill` / `compile` (the width oracle
/// for cross-layer reads). Same shape as `build_cross_layer_field_map`'s output.
pub type CrossFields = HashMap<ReadPlace, FieldKind>;

/// The `-1` field element (BabyBear), matching `fwd::compile`'s internal constant —
/// used to build a NEGATED additive child (`Mul([-1, x])`) in the mixed-field fixture.
const BABYBEAR_NEG_ONE: u32 = 0x78000001 - 1;

/// Column the shared fold leaf reads in `synthetic_wide_add_layer_with_shared_leaf`;
/// `decisions_admitting_a_shared_leaf` / `program_admits_shared_leaf` pivot on it.
const SHARED_COL: usize = 0;

// ── lift ────────────────────────────────────────────────────────────────────

#[inline]
pub fn lift(b: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(b)
}

// ── Stable hash (FNV-1a, 32-bit) — identical to fwd_parity.rs ─────────────────

const FNV_OFFSET: u32 = 0x811c_9dc5;
const FNV_PRIME: u32 = 0x0100_0193;

fn fnv_bytes(seed: u32, bytes: &[u8]) -> u32 {
    let mut h = seed;
    for &b in bytes {
        h ^= b as u32;
        h = h.wrapping_mul(FNV_PRIME);
    }
    h
}

fn fnv_u32(seed: u32, v: u32) -> u32 {
    fnv_bytes(seed, &v.to_le_bytes())
}

fn hash_dbg_row<T: std::fmt::Debug>(t: &T, row: usize) -> u32 {
    let s = format!("{:?}", t);
    let h = fnv_bytes(FNV_OFFSET, s.as_bytes());
    fnv_u32(h, row as u32)
}

// ── SyntheticResolvers (unit struct, matching fwd_parity.rs) ──────────────────

pub struct SyntheticResolvers;

impl cs::gkr_compiler::dag_ir::ReadResolver for SyntheticResolvers {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext {
        lift(Bf::from_u32_with_reduction(hash_dbg_row(place, row)))
    }
}

impl cs::gkr_compiler::dag_ir::LookupResolver for SyntheticResolvers {
    fn lookup(
        &self,
        kind: &LookupValueKind,
        set_index: usize,
        evaluated_query: Ext,
        row: usize,
    ) -> Bf {
        let mut h = hash_dbg_row(kind, row);
        h = fnv_u32(h, set_index as u32);
        let limbs = <Ext as FieldExtension<Bf>>::into_coeffs(evaluated_query);
        for l in limbs {
            h ^= l.as_u32_reduced();
            h = h.wrapping_mul(FNV_PRIME);
        }
        Bf::from_u32_with_reduction(h)
    }
}

impl cs::gkr_compiler::dag_ir::VirtualSetupResolver for SyntheticResolvers {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> Bf {
        Bf::from_u32_with_reduction(hash_dbg_row(kind, row))
    }
}

impl cs::gkr_compiler::dag_ir::ChallengeResolver for SyntheticResolvers {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        lift(Bf::from_u32_with_reduction(hash_dbg_row(r, 0)))
    }
}

pub fn resolvers(s: &SyntheticResolvers) -> Resolvers<'_> {
    Resolvers {
        read: s,
        lookup: s,
        virtual_setup: s,
        challenge: s,
    }
}

// ── Witness-consistent synthetic caches (backward cache fence) ────────────────
//
// After the Task-2 fence, the backward distill replaces each same-layer cache
// cone with a `Read(ReadPlace::CacheOutput{..})` fold leaf (mirroring production,
// which folds `GKRAddress::Cached` columns instead of recomputing the defining
// relation). The G1 oracle keeps recomputing the ORIGINAL cone; the instrument
// reads the fenced cache column. For the two to agree BIT-EXACTLY, the synthetic
// value of a fenced cache column at row `z` must equal the plain per-row value of
// its defining cone at `z` — the WITNESS the forward pass would have written.
//
// `read` for a fenced `CacheOutput` place therefore returns `eval_pointwise` of
// the defining expr over the inner synthetic leaves; every other read (base
// columns, CROSS-layer caches) delegates to the plain synthetic hash. The
// interpreter then applies the shared linear leaf transform (`sumcheck_fold_point`
// then `role_combine`) to this whole column, while the oracle applies it to each
// base leaf of the same cone. Because production cache relations are LINEAR
// (`NoFieldGKRCacheRelation`, all `linear_terms`) and the corpus cache cones are
// lowered from exactly those relations, fold-of-column == column-of-folds and the
// two sides coincide. A nonlinear (or otherwise non-fold-commuting, e.g. a
// VirtualSetup-bearing) cache cone would break this identity and the gate would
// legitimately fail — that is the intended contract, not something to mask.

/// Plain per-row (depth-0, no fold, no role) evaluation of `e` over the inner
/// resolver `r`, with the BACKWARD `LookupValue → query` rewrite. This is the
/// per-row cache-column value the forward pass materializes; unlike the value
/// oracle's leaf path it applies NEITHER the sumcheck fold NOR the T0/T2 role
/// pairing — the interpreter/oracle apply those (linearly) on top. `Constant` /
/// `Challenge` are childless and row/role-invariant, so they delegate to the
/// authoritative `eval_layer_expr` verbatim.
fn eval_pointwise(layer: &DagLayer, e: ExprId, row: usize, r: &Resolvers<'_>) -> Ext {
    match &layer.exprs[e.0 as usize] {
        Expr::Source(sid) => match &layer.sources[sid.0 as usize].kind {
            SourceKind::LookupValue { query, .. } => eval_pointwise(layer, *query, row, r),
            SourceKind::Read { place } => r.read.read(place, row),
            SourceKind::VirtualSetup { kind } => lift(r.virtual_setup.virtual_setup(kind, row)),
            SourceKind::Constant { .. } | SourceKind::Challenge { .. } => {
                eval_layer_expr(layer, e, row, r)
            }
        },
        Expr::Add(children) => {
            let mut acc = Ext::ZERO;
            for &c in children {
                acc.add_assign(&eval_pointwise(layer, c, row, r));
            }
            acc
        }
        Expr::Mul(children) => {
            let mut acc = Ext::ONE;
            for &c in children {
                acc.mul_assign(&eval_pointwise(layer, c, row, r));
            }
            acc
        }
    }
}

/// A `read`-resolver wrapper that makes fenced same-layer cache columns
/// witness-consistent with their defining cones (see the module comment above).
/// Every other resolver method delegates to the inner [`SyntheticResolvers`], so
/// this is a drop-in replacement for the plain read side.
pub struct CacheConsistentResolvers<'a> {
    layer: &'a DagLayer,
    /// `ReadPlace::CacheOutput{..} → defining ExprId`, inverted from
    /// `bwd_cache_fences(layer)` (first defining expr wins on a shared place).
    fences_by_place: HashMap<ReadPlace, ExprId>,
    inner: SyntheticResolvers,
}

impl<'a> CacheConsistentResolvers<'a> {
    pub fn new(layer: &'a DagLayer) -> Self {
        let mut fences_by_place = HashMap::new();
        for (expr, fence) in bwd_cache_fences(layer) {
            fences_by_place.entry(fence.place).or_insert(expr);
        }
        Self { layer, fences_by_place, inner: SyntheticResolvers }
    }

    /// Number of distinct fenced cache columns exercised by this layer.
    pub fn n_fences(&self) -> usize {
        self.fences_by_place.len()
    }
}

impl ReadResolver for CacheConsistentResolvers<'_> {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext {
        match self.fences_by_place.get(place) {
            Some(&expr) => eval_pointwise(self.layer, expr, row, &resolvers(&self.inner)),
            None => self.inner.read(place, row),
        }
    }
}

impl LookupResolver for CacheConsistentResolvers<'_> {
    fn lookup(
        &self,
        kind: &LookupValueKind,
        set_index: usize,
        evaluated_query: Ext,
        row: usize,
    ) -> Bf {
        self.inner.lookup(kind, set_index, evaluated_query, row)
    }
}

impl VirtualSetupResolver for CacheConsistentResolvers<'_> {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> Bf {
        self.inner.virtual_setup(kind, row)
    }
}

impl ChallengeResolver for CacheConsistentResolvers<'_> {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        self.inner.challenge(r)
    }
}

/// Bundle a `CacheConsistentResolvers` into a `Resolvers` (all four sides).
pub fn cache_consistent_resolvers<'a>(
    c: &'a CacheConsistentResolvers<'a>,
) -> Resolvers<'a> {
    Resolvers { read: c, lookup: c, virtual_setup: c, challenge: c }
}

// ── Fixture / schedule loading ────────────────────────────────────────────────

pub fn compiled_circuit_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../cs/compiled_circuits")
}

/// Deserialize one layout fixture JSON (`<name>` includes the `.json` suffix).
pub fn load_fixture(name: &str) -> GKRCircuitArtifact<BabyBearField> {
    let path = compiled_circuit_dir().join(name);
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {path:?}: {e}"));
    serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("parse {path:?}: {e}"))
}

/// `cs/compiled_circuits/{stem}_schedule_b16_gkr.json`.
pub fn schedule_path(stem: &str) -> PathBuf {
    compiled_circuit_dir().join(format!("{stem}_schedule_b16_gkr.json"))
}

/// Map a layout fixture file name → its committed-schedule stem.
///
/// The `_preprocessed` variants (only `inits_and_teardowns_preprocessed_layout_gkr.json`)
/// commit their schedule under the bare `inits_and_teardowns` stem, so those suffixes
/// must be tried FIRST — they also end with `_layout_gkr.json`, and a broad trim would
/// otherwise leave a dangling `_preprocessed` that no schedule file matches (see the
/// same reverse-trim note in `schedule_search_gates.rs`).
pub fn schedule_stem(name: &str) -> &str {
    name.trim_end_matches("_preprocessed_layout_no_caches_gkr.json")
        .trim_end_matches("_preprocessed_layout_gkr.json")
        .trim_end_matches("_layout_no_caches_gkr.json")
        .trim_end_matches("_layout_gkr.json")
}

/// Lower the DAG from the named fixture, load + validate the committed b16 schedule,
/// and return `(dag, schedule, artifact)`.
pub fn load_dag_sched(
    name: &str,
) -> (DagCircuit, CircuitSchedule, GKRCircuitArtifact<BabyBearField>) {
    let artifact = load_fixture(name);
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate(dag): {e}"));
    let stem = schedule_stem(name);
    let sp = schedule_path(stem);
    let sched: CircuitSchedule = serde_json::from_reader(
        std::fs::File::open(&sp).unwrap_or_else(|e| panic!("open {sp:?}: {e}")),
    )
    .unwrap_or_else(|e| panic!("parse {sp:?}: {e}"));
    validate_circuit_schedule(&dag, &sched)
        .unwrap_or_else(|e| panic!("[{name}] validate_circuit_schedule: {e}"));
    (dag, sched, artifact)
}

/// Sample rows `[0, 1, n/2, n-1]`, deduped.
pub fn sample_rows(n: usize) -> Vec<usize> {
    if n == 0 {
        return vec![];
    }
    let mut rows = vec![0usize, 1, n / 2, n - 1];
    rows.retain(|&r| r < n);
    rows.sort_unstable();
    rows.dedup();
    rows
}

// ═════════════════════════════════════════════════════════════════════════════
// SP1 backward-reduction shared test surface (Task 1)
//
// A single implementation of the backward value-parity sweep (`assert_bwd_value_
// parity`), lifted here so `bwd_value_parity.rs` and the SP1 `bwd_stream_reduction.
// rs` synthetic tests share ONE oracle. Plus small classifiers (`is_budget_below_
// floor`, `program_has_fma`) and the synthetic DistilledLayer builders that route a
// wide reduction through `compile_reduction_virtual` (the streamed engine's entry).
// ═════════════════════════════════════════════════════════════════════════════

/// `beta^i` as the distilled spine resolves it (i >= 1): power `One` at i == 1,
/// `Static(i)` beyond — mirrors `distill`'s alpha-spine construction.
fn beta_i(r: &Resolvers<'_>, i: usize) -> Ext {
    let power = if i == 1 { ChallengePower::One } else { ChallengePower::Static(i as u32) };
    r.challenge.challenge(&ChallengeRef { key: ChallengeKey::ClaimBatching, power })
}

// A resolver whose reads ARE the depth-`round` fold of the ORIGINALS (`orig`),
// folded with `ch` via the shared `sumcheck_fold_point`. Feeding this to a
// `Materialized` binding reproduces exactly what a `LazyFromOriginals { depth:
// round }` binding computes from `orig` — so all policies agree bit-for-bit.
struct BufferAt<'a> {
    orig: &'a CacheConsistentResolvers<'a>,
    round: u8,
    ch: &'a [Ext],
}
impl ReadResolver for BufferAt<'_> {
    fn read(&self, place: &ReadPlace, y: usize) -> Ext {
        sumcheck_fold_point(&|z| self.orig.read(place, z), y, self.round, self.ch)
            .expect("buffer read fold within round_challenges depth")
    }
}
impl VirtualSetupResolver for BufferAt<'_> {
    fn virtual_setup(&self, kind: &VirtualSetupKind, y: usize) -> Bf {
        // VS-origin FoldSources are ALWAYS bound `LazyFromOriginals` by `bind()`, so
        // even in a materialized run the interpreter reads VS ORIGINALS and folds them
        // itself. Pass the original through unfolded (pre-folding would double-fold).
        self.orig.virtual_setup(kind, y)
    }
}
impl LookupResolver for BufferAt<'_> {
    fn lookup(&self, kind: &LookupValueKind, set_index: usize, evaluated_query: Ext, row: usize) -> Bf {
        self.orig.lookup(kind, set_index, evaluated_query, row)
    }
}
impl ChallengeResolver for BufferAt<'_> {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        self.orig.challenge(r)
    }
}
fn buffer_resolvers<'a>(b: &'a BufferAt<'a>) -> Resolvers<'a> {
    Resolvers { read: b, lookup: b, virtual_setup: b, challenge: b }
}

/// Evaluate canonical expr `e` at (`regime`, `role`, `row`, `round`), applying the
/// SHARED role+fold transform at every `Read`/`VirtualSetup` leaf. The independent
/// expression-tree reference the compiled backward program is checked against.
#[allow(clippy::too_many_arguments)]
fn eval_oracle(
    layer: &DagLayer,
    e: ExprId,
    regime: BwdRegime,
    role: Role,
    row: usize,
    round: u8,
    ch: &[Ext],
    orig: &SyntheticResolvers,
    plain: &Resolvers<'_>,
    memo: &mut HashMap<ExprId, Ext>,
) -> Ext {
    if let Some(&v) = memo.get(&e) {
        return v;
    }
    let v = match &layer.exprs[e.0 as usize] {
        Expr::Source(sid) => match &layer.sources[sid.0 as usize].kind {
            SourceKind::LookupValue { query, .. } => {
                eval_oracle(layer, *query, regime, role, row, round, ch, orig, plain, memo)
            }
            SourceKind::Read { place } => {
                let depth = if regime == BwdRegime::Ext { round } else { 0 };
                let base = |z: usize| orig.read(place, z);
                let a = sumcheck_fold_point(&base, 2 * row, depth, ch).unwrap();
                let b = sumcheck_fold_point(&base, 2 * row + 1, depth, ch).unwrap();
                role_combine(role, a, b)
            }
            SourceKind::VirtualSetup { kind } => {
                let base = |z: usize| lift(orig.virtual_setup(kind, z));
                let a = sumcheck_fold_point(&base, 2 * row, round, ch).unwrap();
                let b = sumcheck_fold_point(&base, 2 * row + 1, round, ch).unwrap();
                role_combine(role, a, b)
            }
            SourceKind::Constant { .. } | SourceKind::Challenge { .. } => {
                eval_layer_expr(layer, e, row, plain)
            }
        },
        Expr::Add(children) => {
            let ch_ids = children.clone();
            let mut acc = Ext::ZERO;
            for c in ch_ids {
                acc.add_assign(&eval_oracle(layer, c, regime, role, row, round, ch, orig, plain, memo));
            }
            acc
        }
        Expr::Mul(children) => {
            let ch_ids = children.clone();
            let mut acc = Ext::ONE;
            for c in ch_ids {
                acc.mul_assign(&eval_oracle(layer, c, regime, role, row, round, ch, orig, plain, memo));
            }
            acc
        }
    };
    memo.insert(e, v);
    v
}

/// The alpha-combined oracle value: `Σ_i beta^i · eval(root_i)`, root 0 unscaled,
/// over the canonical `bwd_roots` batching order.
#[allow(clippy::too_many_arguments)]
fn oracle_root(
    layer: &DagLayer,
    regime: BwdRegime,
    role: Role,
    row: usize,
    round: u8,
    ch: &[Ext],
    orig: &SyntheticResolvers,
    plain: &Resolvers<'_>,
) -> Ext {
    let mut memo: HashMap<ExprId, Ext> = HashMap::new();
    let mut acc = Ext::ZERO;
    for (i, &rid) in bwd_roots(layer).iter().enumerate() {
        let expr = layer.roots[rid.0 as usize].expr;
        let mut t = eval_oracle(layer, expr, regime, role, row, round, ch, orig, plain, &mut memo);
        if i >= 1 {
            t.mul_assign(&beta_i(plain, i));
        }
        acc.add_assign(&t);
    }
    acc
}

fn for_each_operand(p: &Program, mut f: impl FnMut(&OperandLine)) {
    for instr in &p.instrs {
        match instr {
            Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                operands.iter().for_each(&mut f)
            }
            Instr::Fma { pairs, .. } => pairs.iter().for_each(|(l, r)| {
                f(l);
                f(r);
            }),
            Instr::Mov { src: Some(op), .. } => f(op),
            Instr::Mov { src: None, .. } => {}
        }
    }
}

fn count_desc_uses(p: &Program, desc: u16) -> usize {
    let mut n = 0;
    for_each_operand(p, |op| {
        if matches!(op, OperandLine::Special { desc: d } if *d == desc) {
            n += 1;
        }
    });
    n
}


/// Load fixture `name` → lower/validate the DAG → return layer `li` and the circuit's
/// cross-layer field map (for `distill`). The reusable per-fixture entry for later SP1
/// tasks (4–6); `bwd_value_parity.rs` keeps its own multi-layer loop.
pub fn load_layer(name: &str, li: usize) -> (DagLayer, CrossFields) {
    let artifact = load_fixture(name);
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
    let cross = build_cross_layer_field_map(&dag);
    (dag.layers[li].clone(), cross)
}

/// True iff `e` is the streaming-fallback trigger `BudgetBelowFloor`.
pub fn is_budget_below_floor(e: &CompileError) -> bool {
    matches!(e, CompileError::BudgetBelowFloor { .. })
}

/// True iff the program contains any fused multiply-add (Task-2 surface).
pub fn program_has_fma(p: &Program) -> bool {
    p.instrs.iter().any(|i| matches!(i, Instr::Fma { .. }))
}

/// The full per-(compiled, distilled) backward parity check against the independent
/// expression oracle over `oracle_layer` (the RAW canonical layer for fixtures — its
/// cache cones are recomputed against the witness-consistent read side; the distilled
/// layer itself for cache-free synthetic fixtures). Regime is read from `d.regime`.
/// Asserts (i) encode/decode roundtrip, (ii) no orphan/out-of-range Special descs, and
/// (iii) interp(program) == oracle across round × role × row, all policies bit-identical.
pub fn assert_bwd_value_parity(c: &BwdCompiledLayer, d: &DistilledLayer, oracle_layer: &DagLayer) {
    const ROUNDS: &[u8] = &[0, 1, 2];
    const ROLES: &[Role] = &[Role::T0, Role::T2];
    const ROWS: &[usize] = &[0, 1];
    const POLICIES: &[MaterializationPolicy] = &[
        MaterializationPolicy::AlwaysMaterialize,
        MaterializationPolicy::LazyUpTo(1),
        MaterializationPolicy::LazyUpTo(2),
    ];
    let round_challenges: Vec<Ext> =
        [3u32, 5, 7].into_iter().map(|k| lift(Bf::from_u32_with_reduction(k))).collect();
    let syn = SyntheticResolvers;
    let plain = resolvers(&syn);
    let cc = CacheConsistentResolvers::new(oracle_layer);
    let cc_r = cache_consistent_resolvers(&cc);

    // (i) encode/decode roundtrip reproduces the program exactly.
    let lanes = encode_result(&c.program).expect("encode");
    let decoded = decode(&lanes).expect("decode");
    assert_eq!(decoded, c.program, "encode/decode roundtrip mismatch");

    // (ii) every Special desc is in range, and every table entry is referenced.
    let n_specials = c.specials.len();
    let mut used: BTreeSet<u16> = BTreeSet::new();
    for_each_operand(&c.program, |op| {
        if let OperandLine::Special { desc } = op {
            assert!((*desc as usize) < n_specials, "Special desc {desc} >= specials.len() {n_specials}");
            used.insert(*desc);
        }
    });
    for i in 0..n_specials as u16 {
        assert!(used.contains(&i), "orphan descriptor {i} of {n_specials} is never referenced");
    }

    // (iii) value parity: interp == oracle for every round/role/row, all policies identical.
    for &round in ROUNDS {
        for &role in ROLES {
            for &row in ROWS {
                let expected =
                    oracle_root(oracle_layer, d.regime, role, row, round, &round_challenges, &syn, &plain);
                let mut first: Option<Ext> = None;
                for &policy in POLICIES {
                    let bindings = bind(d, policy, round);
                    let materialized =
                        bindings.states.iter().any(|s| matches!(s, FoldState::Materialized));
                    let buf = BufferAt { orig: &cc, round, ch: &round_challenges };
                    let buf_r = buffer_resolvers(&buf);
                    let run_r = if materialized { &buf_r } else { &cc_r };
                    let got = interpret_bwd_row(c, d, &bindings, run_r, role, row, &round_challenges)
                        .unwrap_or_else(|e| {
                            panic!("interp round {round} {role:?} row {row} {policy:?}: {e:?}")
                        });
                    assert_eq!(
                        got, expected,
                        "value mismatch: round {round} {role:?} row {row} {policy:?} interp != oracle"
                    );
                    match first {
                        None => first = Some(got),
                        Some(f) => assert_eq!(
                            got, f,
                            "policy {policy:?} disagrees (round {round} {role:?} row {row})"
                        ),
                    }
                }
            }
        }
    }
}

// ── synthetic DistilledLayer builders ─────────────────────────────────────────

fn read_src(column: usize) -> SourceInfo {
    SourceInfo { kind: SourceKind::Read { place: ReadPlace::BaseLayerWitness { column } } }
}

fn const_src(value: u32) -> SourceInfo {
    SourceInfo { kind: SourceKind::Constant { value } }
}

/// Append a fresh `Read` leaf (its own unique column == its source index) and return
/// its `ExprId`. Column 0 is the first read appended, hence `SHARED_COL`.
fn add_read(sources: &mut Vec<SourceInfo>, exprs: &mut Vec<Expr>) -> ExprId {
    let col = sources.len();
    sources.push(read_src(col));
    let e = ExprId(exprs.len() as u32);
    exprs.push(Expr::Source(SourceId(col as u32)));
    e
}

fn add_const(sources: &mut Vec<SourceInfo>, exprs: &mut Vec<Expr>, value: u32) -> ExprId {
    let sid = sources.len();
    sources.push(const_src(value));
    let e = ExprId(exprs.len() as u32);
    exprs.push(Expr::Source(SourceId(sid as u32)));
    e
}

fn add_expr(exprs: &mut Vec<Expr>, ex: Expr) -> ExprId {
    let e = ExprId(exprs.len() as u32);
    exprs.push(ex);
    e
}

fn claim_only_root(expr: ExprId, relation_index: usize) -> Root {
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

fn raw_layer(sources: Vec<SourceInfo>, exprs: Vec<Expr>, roots: Vec<Root>) -> DagLayer {
    let batching = BatchingOrder {
        roots: roots
            .iter()
            .enumerate()
            .filter(|(_, r)| r.claim.is_some())
            .map(|(i, _)| RootId(i as u32))
            .collect(),
    };
    DagLayer { sources, exprs, roots, batching, resolutions: BTreeMap::new() }
}

/// A wide pure-ADD reduction of `n` compound children (each `Add(read, read)`), nested
/// one level below a 2-term alpha spine so it is lowered as ONE spine term through
/// `compile_reduction_virtual` (not the driver's term loop, and never FMA — no products).
/// Legacy pre-materialization needs `4·n` Ext cells (floor ≫ 16); streaming needs one.
/// Distilled in the Ext regime (fold leaves), so the fold engages at round > 0.
pub fn synthetic_wide_add_layer(n: usize) -> DistilledLayer {
    assert!(n >= 2, "need at least two children");
    let mut sources = Vec::new();
    let mut exprs = Vec::new();
    let mut gis = Vec::with_capacity(n);
    for _ in 0..n {
        let a = add_read(&mut sources, &mut exprs);
        let b = add_read(&mut sources, &mut exprs);
        gis.push(add_expr(&mut exprs, Expr::Add(vec![a, b])));
    }
    let root0 = add_expr(&mut exprs, Expr::Add(gis));
    // A small second claim root: forces `distill` to wrap the roots in a spine `Add`,
    // so the wide `Add` above survives as a single nested spine TERM.
    let root1 = add_read(&mut sources, &mut exprs);
    let roots = vec![claim_only_root(root0, 0), claim_only_root(root1, 1)];
    distill(&raw_layer(sources, exprs, roots), BwdRegime::Ext, &CrossFields::new(), None)
}

/// The MUL sibling of [`synthetic_wide_add_layer`]: a wide product of `n` compound
/// children. A single claim root suffices — the root is a `Mul` (not an `Add`), so
/// `spine_terms` yields the whole product as one term and it lowers through
/// `compile_reduction_virtual` with `is_add = false`.
pub fn synthetic_wide_mul_layer(n: usize) -> DistilledLayer {
    assert!(n >= 2, "need at least two factors");
    let mut sources = Vec::new();
    let mut exprs = Vec::new();
    let mut gis = Vec::with_capacity(n);
    for _ in 0..n {
        let a = add_read(&mut sources, &mut exprs);
        let b = add_read(&mut sources, &mut exprs);
        gis.push(add_expr(&mut exprs, Expr::Add(vec![a, b])));
    }
    let root = add_expr(&mut exprs, Expr::Mul(gis));
    distill(&raw_layer(sources, exprs, vec![claim_only_root(root, 0)]), BwdRegime::Ext, &CrossFields::new(), None)
}

/// A small mixed-field reduction reaching `compile_reduction_virtual` (nested under a
/// 2-term spine). `ext_seed` selects which cross-field stash the streamed fold exercises:
///   * `false` — a Base leaf seeds (Base acc): a Base compound stashes onto the Base acc
///     and an Ext compound stashes onto the still-Base acc (Ext-stash-onto-Base-acc).
///   * `true` — an Ext leaf seeds (Ext acc; the only Base child is NEGATED so no
///     Base-Plus child steals the seed): the Base compound stashes onto the Ext acc
///     (Base-stash-onto-Ext-acc) and an Ext compound stashes onto the Ext acc.
/// Both variants FIT the legacy path, so the SP1 test forces `stream_reductions` on.
pub fn synthetic_mixed_field_micro_layer(ext_seed: bool) -> DistilledLayer {
    let mut sources = Vec::new();
    let mut exprs = Vec::new();
    // Ext compound C = Add(read, read) (both variants).
    let c0 = add_read(&mut sources, &mut exprs);
    let c1 = add_read(&mut sources, &mut exprs);
    let c_ext_compound = add_expr(&mut exprs, Expr::Add(vec![c0, c1]));
    // Base compound = Add(const2, const3).
    let k2 = add_const(&mut sources, &mut exprs, 2);
    let k3 = add_const(&mut sources, &mut exprs, 3);
    let base_compound = add_expr(&mut exprs, Expr::Add(vec![k2, k3]));

    let root0_children = if ext_seed {
        let b_ext_leaf = add_read(&mut sources, &mut exprs);
        let neg1 = add_const(&mut sources, &mut exprs, BABYBEAR_NEG_ONE);
        // Mul([-1, base_compound]) → classifies as a Base-MINUS addend (its lowering id
        // is `base_compound`), so no Base-Plus child exists and the seed is the Ext leaf.
        let neg_base = add_expr(&mut exprs, Expr::Mul(vec![neg1, base_compound]));
        vec![b_ext_leaf, neg_base, c_ext_compound]
    } else {
        let d_base_leaf = add_const(&mut sources, &mut exprs, 5);
        vec![d_base_leaf, base_compound, c_ext_compound]
    };
    let root0 = add_expr(&mut exprs, Expr::Add(root0_children));
    let root1 = add_read(&mut sources, &mut exprs);
    let roots = vec![claim_only_root(root0, 0), claim_only_root(root1, 1)];
    distill(&raw_layer(sources, exprs, roots), BwdRegime::Ext, &CrossFields::new(), None)
}

/// A wide-Add reduction whose DIRECT children include a shared fold leaf `S`
/// (`Read(SHARED_COL)`, fan-out 2 — also the second claim root), plus a Base leaf seed
/// and `k` Ext compounds (floor ≫ 16). Under decisions that prioritize `S`
/// ([`decisions_admitting_a_shared_leaf`]) the streamed fold classifies `S` as
/// may-admit and takes the admission branch mid-reduction.
pub fn synthetic_wide_add_layer_with_shared_leaf() -> DistilledLayer {
    const K: usize = 40;
    let mut sources = Vec::new();
    let mut exprs = Vec::new();
    // S = Read(SHARED_COL) — the first read appended, so its column is `SHARED_COL`.
    let s = add_read(&mut sources, &mut exprs);
    // A Base leaf seed (Base-Plus → preferred seed), so S is a NON-seed direct child and
    // therefore takes the `fold_compound_child_into_partial` admission branch.
    let seed = add_const(&mut sources, &mut exprs, 7);
    let mut children = vec![seed, s];
    for _ in 0..K {
        let a = add_read(&mut sources, &mut exprs);
        let b = add_read(&mut sources, &mut exprs);
        children.push(add_expr(&mut exprs, Expr::Add(vec![a, b])));
    }
    let root0 = add_expr(&mut exprs, Expr::Add(children));
    // root1 == S gives S fan-out 2 (so it enters the genome-scored site domain).
    let roots = vec![claim_only_root(root0, 0), claim_only_root(s, 1)];
    distill(&raw_layer(sources, exprs, roots), BwdRegime::Ext, &CrossFields::new(), None)
}

/// A wide FMA cone (Task 2) whose product children mix LEAF products (`Mul([read, read])`
/// — both operands direct, stay fused through `emit_fma_products`) and COMPOUND×COMPOUND
/// products (`Mul([Add(read,read), Add(read,read)])` — BOTH operands must stash, the nested
/// per-operand `lower_operand_virtual` path). Nested one level below a 2-term alpha spine so
/// the whole Add-of-products survives as ONE spine TERM routed through
/// `try_compile_fma_virtual` (a binary `Mul` classifies as a `Product`; distill does NOT
/// distribute Mul over Add). Legacy pre-materializes EVERY product operand concurrently
/// (`2·n_cxc` Ext cells, floor ≫ 16); streaming holds only one product's operands + the
/// running partial (`acc + P + lhs_cell + rhs_cell = 16` lanes at the cxc peak). Ext regime.
pub fn synthetic_fma_compound_products_layer(n_cxc: usize, n_leaf: usize) -> DistilledLayer {
    assert!(n_leaf >= 2, "need >=2 leaf products so a non-seed leaf product stays FMA-fused");
    let mut sources = Vec::new();
    let mut exprs = Vec::new();
    let mut children: Vec<ExprId> = Vec::new();
    // Leaf products: read * read (both operands direct → fused FMA).
    for _ in 0..n_leaf {
        let a = add_read(&mut sources, &mut exprs);
        let b = add_read(&mut sources, &mut exprs);
        children.push(add_expr(&mut exprs, Expr::Mul(vec![a, b])));
    }
    // Compound×compound products: (read+read) * (read+read) (both operands must stash).
    for _ in 0..n_cxc {
        let a = add_read(&mut sources, &mut exprs);
        let b = add_read(&mut sources, &mut exprs);
        let c = add_read(&mut sources, &mut exprs);
        let e = add_read(&mut sources, &mut exprs);
        let lhs = add_expr(&mut exprs, Expr::Add(vec![a, b]));
        let rhs = add_expr(&mut exprs, Expr::Add(vec![c, e]));
        children.push(add_expr(&mut exprs, Expr::Mul(vec![lhs, rhs])));
    }
    let root0 = add_expr(&mut exprs, Expr::Add(children));
    // A small second claim root forces `distill` to wrap the roots in a spine `Add`.
    let root1 = add_read(&mut sources, &mut exprs);
    let roots = vec![claim_only_root(root0, 0), claim_only_root(root1, 1)];
    distill(&raw_layer(sources, exprs, roots), BwdRegime::Ext, &CrossFields::new(), None)
}

/// A shared-compound cone with genuine fan-out-2 nesting, for Task-8 removal-set
/// pricing tests. Three nested shared compounds:
///   * `U = Add(rU0, rU1)`   — used inside `W` and directly (Mul(U, rd)) → fan-out 2
///   * `W = Mul(U, rW)`      — used inside `V` and directly (Mul(W, rc)) → fan-out 2
///   * `V = Mul(W, rV)`      — used in Mul(V, ra) and Mul(V, rb)        → fan-out 2
/// `root0 = Add(Mul(V,ra), Mul(V,rb), Mul(W,rc), Mul(U,rd))` (single claim root, so
/// its four products become the spine terms). Every read leaf is fan-out 1
/// (non-domain), so the site domain is exactly `{U, W, V}` and there are NO domain
/// leaves — the pricing exercises pure COMPOUND cone suppression. Distilled Ext.
/// No non-domain compound is ever wedged between two of these on a path (each is a
/// direct operand of the next), so the pre-order stream reconstruction is exact.
pub fn synthetic_shared_compound_layer() -> DistilledLayer {
    let mut sources = Vec::new();
    let mut exprs = Vec::new();
    let ru0 = add_read(&mut sources, &mut exprs);
    let ru1 = add_read(&mut sources, &mut exprs);
    let rw = add_read(&mut sources, &mut exprs);
    let rv = add_read(&mut sources, &mut exprs);
    let ra = add_read(&mut sources, &mut exprs);
    let rb = add_read(&mut sources, &mut exprs);
    let rc = add_read(&mut sources, &mut exprs);
    let rd = add_read(&mut sources, &mut exprs);
    let u = add_expr(&mut exprs, Expr::Add(vec![ru0, ru1]));
    let w = add_expr(&mut exprs, Expr::Mul(vec![u, rw]));
    let v = add_expr(&mut exprs, Expr::Mul(vec![w, rv]));
    let m_va = add_expr(&mut exprs, Expr::Mul(vec![v, ra]));
    let m_vb = add_expr(&mut exprs, Expr::Mul(vec![v, rb]));
    let m_wc = add_expr(&mut exprs, Expr::Mul(vec![w, rc]));
    let m_ud = add_expr(&mut exprs, Expr::Mul(vec![u, rd]));
    let root0 = add_expr(&mut exprs, Expr::Add(vec![m_va, m_vb, m_wc, m_ud]));
    distill(
        &raw_layer(sources, exprs, vec![claim_only_root(root0, 0)]),
        BwdRegime::Ext,
        &CrossFields::new(),
        None,
    )
}

/// Locate the three shared compounds `(U, W, V)` of
/// [`synthetic_shared_compound_layer`] in the DISTILLED arena by structure: `U` is
/// the site-domain `Add`; `W` is the site-domain `Mul` whose children include `U`;
/// `V` is the site-domain `Mul` whose children include `W`.
pub fn find_shared_compounds(d: &DistilledLayer) -> (ExprId, ExprId, ExprId) {
    let domain: BTreeSet<ExprId> =
        distilled_site_domain(d).into_iter().map(|s| s.value).collect();
    let is_mul_with = |parent: ExprId, child: ExprId| -> bool {
        matches!(&d.layer.exprs[parent.0 as usize], Expr::Mul(ch) if ch.contains(&child))
    };
    let u = domain
        .iter()
        .copied()
        .find(|&e| matches!(d.layer.exprs[e.0 as usize], Expr::Add(_)))
        .expect("shared U = domain Add");
    let w = domain
        .iter()
        .copied()
        .find(|&e| is_mul_with(e, u))
        .expect("shared W = domain Mul containing U");
    let v = domain
        .iter()
        .copied()
        .find(|&e| is_mul_with(e, w))
        .expect("shared V = domain Mul containing W");
    (u, w, v)
}

// ── admission fixtures / probes ───────────────────────────────────────────────

/// Locate the distilled `ExprId` of the `Read(column)` fold leaf, if present.
fn find_read_leaf(layer: &DagLayer, column: usize) -> Option<ExprId> {
    layer.exprs.iter().enumerate().find_map(|(i, e)| match e {
        Expr::Source(sid) => match &layer.sources[sid.0 as usize].kind {
            SourceKind::Read { place: ReadPlace::BaseLayerWitness { column: c } } if *c == column => {
                Some(ExprId(i as u32))
            }
            _ => None,
        },
        _ => None,
    })
}

/// All-sites decisions over the DISTILLED domain, with the shared leaf `Read(SHARED_COL)`
/// pinned to a dominating priority so `try_admit` keeps it resident mid-reduction (the
/// searched-path admission the Global Constraint requires to be value-safe in Task 1).
pub fn decisions_admitting_a_shared_leaf(d: &DistilledLayer) -> SiteDecisions {
    let shared = find_read_leaf(&d.layer, SHARED_COL).expect("shared leaf present in distilled layer");
    SiteDecisions::new(distilled_site_domain(d).into_iter().map(|k| {
        let p = if k.value == shared { 1_000.0 } else { 1.0 };
        (k, p)
    }))
}

/// The `BwdSpecialTable` descriptor of the shared `Read(SHARED_COL)` fold leaf, if any.
fn shared_leaf_desc(c: &BwdCompiledLayer) -> Option<u16> {
    (0..c.specials.len() as u16).find(|&i| match c.specials.get(i) {
        Some(BwdSpecial::FoldSource {
            origin: OriginLeaf::Read(ReadPlace::BaseLayerWitness { column }),
        }) => *column == SHARED_COL,
        _ => false,
    })
}

/// Fold-source operand uses of the shared leaf in `c`'s program: 2 under pure recompute
/// (one gather per occurrence), collapsing to 1 once admission caches it to a cell.
pub fn shared_leaf_fold_uses(c: &BwdCompiledLayer) -> usize {
    shared_leaf_desc(c).map_or(0, |desc| count_desc_uses(&c.program, desc))
}

/// Non-vacuous proof the admission branch fired: the shared leaf's fold-source gather
/// count dropped to exactly ONE. This metric is SHARED-LEAF-SCOPED (`count_desc_uses` on
/// the leaf's own `Special` descriptor). For the SYNTHETIC fixture the leaf has fan-out 2,
/// so the no-decisions baseline is 2 gathers; `== 1` means exactly one occurrence was
/// served from a resident cell instead of re-gathered — i.e. that one is a Smem read of the
/// leaf's own admitted cell. (An earlier form also `&&`'d a WHOLE-PROGRAM `count_smem_reads
/// > 0`, but that was loose corroboration: the shared-leaf-scoped gather drop already
/// witnesses the resident read of exactly this leaf.)
pub fn program_admits_shared_leaf(c: &BwdCompiledLayer) -> bool {
    shared_leaf_fold_uses(c) == 1
}

/// Non-vacuous proof the admission branch fired on a REAL wide fixture. There the shared
/// leaf has many uses and b16 budget pressure keeps only SOME of them resident, so the
/// exact-1 collapse above does not apply. Instead: pinning the leaf's priority must
/// STRICTLY reduce its fold-source gathers versus the no-decisions baseline `c_none`. Each
/// dropped gather is exactly one occurrence now served from the leaf's resident cell (a Smem
/// read of ITS cell), so the strict drop IS the shared-leaf-scoped resident-read count — no
/// whole-program Smem tally needed. The drop is specific to the shared leaf (its priority
/// alone is pinned), so it directly witnesses its admission.
pub fn program_admits_shared_leaf_vs_baseline(c: &BwdCompiledLayer, c_none: &BwdCompiledLayer) -> bool {
    shared_leaf_fold_uses(c) < shared_leaf_fold_uses(c_none)
}

// ── synthetic value checks (independent recompute vs compiled program) ─────────

/// Independently recompute the synthetic root's value (the expression oracle) and assert
/// the compiled backward program evaluates to it across the full round/role/row/policy
/// sweep. The synthetic layers are cache-free, so the distilled layer's own expression
/// tree is a valid oracle target (no fenced cone to recompute from originals).
pub fn assert_synthetic_value_exact(c: &BwdCompiledLayer, d: &DistilledLayer) {
    assert_bwd_value_parity(c, d, &d.layer);
}

/// As [`assert_synthetic_value_exact`], for a program compiled UNDER decisions. Value is
/// residency-invariant (decisions only move cells, never values), so the same oracle
/// applies; `_decisions` is accepted to document the searched-path intent at the call site.
pub fn assert_synthetic_value_exact_with_decisions(
    c: &BwdCompiledLayer,
    d: &DistilledLayer,
    _decisions: &SiteDecisions,
) {
    assert_bwd_value_parity(c, d, &d.layer);
}

/// As [`assert_synthetic_value_exact`], for a program compiled UNDER a plan
/// (`compile_distilled_planned`, Task 4). Value is residency-invariant (Retain/Bypass
/// only move cells, never values — same as the decisions channel), so the distilled
/// layer's own expression tree is still a valid oracle across the full sweep.
pub fn assert_synthetic_value_exact_planned(c: &BwdCompiledLayer, d: &DistilledLayer) {
    assert_bwd_value_parity(c, d, &d.layer);
}

// ═════════════════════════════════════════════════════════════════════════════
// SP1 Task 4 — A3 read-side traffic-invariance surface (streamed == legacy)
//
// The "free-fix" certificate: for every fixture/layer/regime on the UNCACHED path
// (`decisions: None`), the streamed program's read-side stats must be bit-identical
// to legacy's at a commonly-feasible budget. These helpers back
// `tests/bwd_stream_traffic_parity.rs`.
// ═════════════════════════════════════════════════════════════════════════════

/// The 12 pinned Global-Constraints fixtures — same list (and order) as
/// `bwd_value_parity.rs` / `bwd_distill_fixtures.rs` / `fwd_vm_desc_census.rs`.
pub const FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_preprocessed_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

/// Every layer of fixture `name` that has backward roots, as `(layer_index, layer,
/// cross_field_map)`. The cross-layer field map is a whole-circuit property, so the
/// same clone rides each tuple (matching `distill(&layer, regime, &cross, None)`).
/// Returns an OWNED iterator (the DAG is dropped) so callers hold no borrow.
pub fn layers_with_bwd_roots(name: &str) -> impl Iterator<Item = (usize, DagLayer, CrossFields)> {
    let artifact = load_fixture(name);
    let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
    validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
    let cross = build_cross_layer_field_map(&dag);
    let mut out = Vec::new();
    for (li, layer) in dag.layers.iter().enumerate() {
        if bwd_roots(layer).is_empty() {
            continue; // nothing to prove backward
        }
        out.push((li, layer.clone(), cross.clone()));
    }
    out.into_iter()
}

/// Legacy's smallest feasible budget for `d`, with the legacy program compiled there.
///
/// Scans the candidate budgets `[16, 24, 32, 48, 64, floor]` (spec A3) and returns the
/// smallest at which the pure legacy pre-materialize lowering
/// (`compile_distilled_legacy_only`) is `Ok`. Feasibility is monotone (feasible iff
/// `b >= floor`), so:
///   * the first fixed probe that compiles is the answer, UNLESS an earlier probe already
///     revealed a `floor` strictly below it — then the floor itself is the smaller feasible
///     budget (e.g. `mem_*` floor 20: b16 fails → floor=20, b24 Ok, but 20 < 24 wins);
///   * if every fixed probe overflows (floor > 64: the wide L0s), compile at the reported
///     floor (bigint Ext=320, keccak=172, ...).
/// Budgets below 16 are never probed — 16 is the scan floor. Streaming's feasibility ⊇
/// legacy's, so streamed is always feasible at the returned budget too.
pub fn smallest_legacy_feasible(d: &DistilledLayer) -> (usize, BwdCompiledLayer) {
    const FIXED: [usize; 5] = [16, 24, 32, 48, 64];
    let mut floor: Option<usize> = None;
    for &b in &FIXED {
        match compile_distilled_legacy_only(d, b, None) {
            Ok(c) => {
                // A floor learned from a smaller failed probe is the true smallest feasible
                // budget in the candidate set (`floor` is exactly the feasibility threshold).
                if let Some(f) = floor {
                    if f < b {
                        let cf = compile_distilled_legacy_only(d, f, None)
                            .expect("legacy is feasible at its own reported floor");
                        return (f, cf);
                    }
                }
                return (b, c);
            }
            Err(CompileError::BudgetBelowFloor { floor: fl, .. }) => floor = Some(fl),
            Err(e) => panic!("unexpected legacy compile error at b{b}: {e:?}"),
        }
    }
    // No fixed probe fit → floor > 64; compile legacy at the reported floor.
    let f = floor.expect("all fixed probes overflowed, so a BudgetBelowFloor floor was observed");
    let cf = compile_distilled_legacy_only(d, f, None).expect("legacy is feasible at its floor");
    (f, cf)
}

/// Per-`FoldSource`-descriptor use histogram: `origin → number of `Special{desc}`
/// operand occurrences whose desc resolves to a `FoldSource{origin}` in `c.specials`.
///
/// Keying by the ORIGIN (its `Debug` form — `Read(place-with-column)` vs
/// `VirtualSetup{kind}`) makes the comparison width/origin-sensitive: a VS-origin fold
/// (zero DRAM, closed form) and a Read-origin fold (4 cells) land in different buckets,
/// so a same-count substitution that would net out in the scalar `fold_uses`/`special_
/// reads`/`fold_traffic` sums still shows up as a histogram drift. `VirtualSetup`
/// descriptors are not `FoldSource`s and are excluded (they carry no fold traffic).
pub fn foldsource_use_histogram(c: &BwdCompiledLayer) -> BTreeMap<String, usize> {
    let mut hist: BTreeMap<String, usize> = BTreeMap::new();
    for_each_operand(&c.program, |op| {
        if let OperandLine::Special { desc } = op {
            if let Some(BwdSpecial::FoldSource { origin }) = c.specials.get(*desc) {
                *hist.entry(format!("{origin:?}")).or_insert(0) += 1;
            }
        }
    });
    hist
}

/// Deterministic byte serialization of a program (the encoded lane stream) for the
/// legacy-program byte-identity check. Panics if the program is not encodable (it always
/// is for a well-formed compiled layer — the roundtrip is exercised in every value gate).
pub fn encode(p: &Program) -> Vec<u16> {
    encode_result(p).expect("program encodes")
}
