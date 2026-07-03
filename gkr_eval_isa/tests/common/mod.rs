//! Shared fixture/resolver helpers for the Stage-3 integration tests.
//!
//! Each `tests/*.rs` is a separate binary; this module is included via `mod common;`
//! so the Stage-3 schedule-driven tests (and any sibling) reach the same fixture
//! loading + `SyntheticResolvers` used by `fwd_parity.rs`. Lib items are reached via
//! `gkr_eval_isa::`, never `crate::`.

use std::path::PathBuf;

use cs::gkr_compiler::dag_ir::{
    lower_dag, validate, validate_circuit_schedule, Bf, ChallengeRef, CircuitSchedule, DagCircuit,
    Ext, LookupValueKind, ReadPlace, Resolvers, VirtualSetupKind,
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
pub fn schedule_stem(name: &str) -> &str {
    name.trim_end_matches("_layout_gkr.json")
        .trim_end_matches("_layout_no_caches_gkr.json")
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
