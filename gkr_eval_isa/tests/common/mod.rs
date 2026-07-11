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
