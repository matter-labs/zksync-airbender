//! CS-M5a Task 6.1: the BYTE-LEVEL neutrality pin for the backward TERM compile
//! path. Task 6 re-parameterizes the freeze + pricing stack over a
//! `BwdCompileBackend` trait (TermBackend / FragmentBackend). The single binding
//! property of that refactor is that the TERM path stays BYTE-IDENTICAL: the shipped
//! backward program, its descriptor table, its traffic/lane stats, its certificate,
//! and the priced plan's `entries_fnv` must not move by a single byte.
//!
//! This test pins all of those, per fixture, for the CURRENT production term entry
//! `cs_schedule_bwd_layer` (L0, Ext regime, b16 — the same corpus/slice the engine
//! gates in `bwd_cs_engine.rs` run). The pinned constants in `PINS` below were
//! generated at HEAD `e2ae8173` with the crate source CLEAN (before any Task-6 src
//! change); the refactor is byte-neutral iff this test stays green afterward.
//!
//! Per fixture it pins:
//!   * `traffic`         — `stats_ext.global + stats_ext.fold_traffic` (the objective);
//!   * `lanes`           — `stats.program_lanes` (the shipped instruction count);
//!   * certificate counts — `counted_traffic` / `reported_traffic` / `refusals` /
//!                          `evictions` (and `diverged` must be `None`);
//!   * `entries_fnv`     — the shipped priced plan's `entries_fnv` (`None` on a
//!                          canonical-baseline fallback, where `plan` is `None`);
//!   * `digest`          — an FNV-1a over an EXPLICIT byte serialization of the
//!                          encoded backward program: the wire `u16` lanes
//!                          (little-endian, in order) followed by the CLONED
//!                          `BwdSpecialTable` content, each descriptor hand-serialized
//!                          field-by-field (mirrors `tests/fwd_digest.rs`). The lanes
//!                          carry only `u16` indices into the descriptor table, so the
//!                          table CONTENT must be pinned too or a descriptor could drift
//!                          while every lane stays byte-identical.
//!
//! Regeneration: run with `--nocapture` and copy the printed `PIN …` lines into
//! `PINS`. A missing pin fails the test (never a vacuous pass).
//!   RUST_MIN_STACK=1073741824 RUSTFLAGS="-Awarnings" \
//!     cargo test -p gkr_eval_isa --release --test bwd_backend_neutrality -- --nocapture

mod common;
use common::*;

use gkr_eval_isa::bwd::engine::cs_schedule_bwd_layer;
use gkr_eval_isa::bwd::source::{BwdSpecial, BwdSpecialTable, OriginLeaf};
use gkr_eval_isa::fwd::isa::Program;
use gkr_eval_isa::fwd::source::virtual_setup_kind_code;

use cs::gkr_compiler::dag_ir::{bwd_roots, BwdRegime, ReadPlace};

// ── explicit byte serialization (mirrors tests/fwd_digest.rs) ───────────────────

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

fn fnv1a(bytes: &[u8]) -> u64 {
    let mut h = FNV_OFFSET;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(FNV_PRIME);
    }
    h
}

fn push_tag(buf: &mut Vec<u8>, t: u8) {
    buf.push(t);
}
fn push_u32(buf: &mut Vec<u8>, v: u32) {
    buf.extend_from_slice(&v.to_le_bytes());
}
fn push_u64(buf: &mut Vec<u8>, v: u64) {
    buf.extend_from_slice(&v.to_le_bytes());
}

/// Explicit byte serialization of one `ReadPlace` — variant tag (declaration order)
/// then fields, `usize` widened to `u64` LE. Same layout as `fwd_digest.rs`.
fn serialize_read_place(buf: &mut Vec<u8>, p: &ReadPlace) {
    match p {
        ReadPlace::BaseLayerMemory { column } => {
            push_tag(buf, 0);
            push_u64(buf, *column as u64);
        }
        ReadPlace::BaseLayerWitness { column } => {
            push_tag(buf, 1);
            push_u64(buf, *column as u64);
        }
        ReadPlace::Setup { column } => {
            push_tag(buf, 2);
            push_u64(buf, *column as u64);
        }
        ReadPlace::Scratch { slot } => {
            push_tag(buf, 3);
            push_u64(buf, *slot as u64);
        }
        ReadPlace::LayerOutput { layer, offset } => {
            push_tag(buf, 4);
            push_u64(buf, *layer as u64);
            push_u64(buf, *offset as u64);
        }
        ReadPlace::CacheOutput { layer, offset } => {
            push_tag(buf, 5);
            push_u64(buf, *layer as u64);
            push_u64(buf, *offset as u64);
        }
    }
}

/// Explicit byte serialization of one `BwdSpecial` descriptor payload — variant tag
/// first (declaration order in `bwd::source`), then fields. `VirtualSetupKind` reuses
/// the crate's own kind ↔ device-code mapping (`virtual_setup_kind_code`).
fn serialize_bwd_special(buf: &mut Vec<u8>, s: &BwdSpecial) {
    match s {
        BwdSpecial::FoldSource { origin } => {
            push_tag(buf, 0);
            match origin {
                OriginLeaf::Read(place) => {
                    push_tag(buf, 0);
                    serialize_read_place(buf, place);
                }
                OriginLeaf::VirtualSetup { kind } => {
                    push_tag(buf, 1);
                    push_u32(buf, virtual_setup_kind_code(kind));
                }
            }
        }
        BwdSpecial::VirtualSetup { kind } => {
            push_tag(buf, 1);
            push_u32(buf, virtual_setup_kind_code(kind));
        }
        BwdSpecial::Coefficient { fragment } => {
            push_tag(buf, 2);
            push_u32(buf, *fragment);
        }
        BwdSpecial::AccInit => {
            push_tag(buf, 3);
        }
    }
}

/// FNV-1a over the encoded backward program: the wire `u16` lanes (LE, in order),
/// then the descriptor table (length-prefixed `u64` count, then each `BwdSpecial` in
/// descriptor-index order). The lane stream carries only descriptor INDICES, so the
/// table content is required to pin the program's full semantics.
fn program_digest(program: &Program, specials: &BwdSpecialTable) -> u64 {
    let lanes = encode(program);
    let mut buf = Vec::with_capacity(lanes.len() * 2 + specials.len() * 12);
    for &lane in &lanes {
        buf.extend_from_slice(&lane.to_le_bytes());
    }
    push_u64(&mut buf, specials.len() as u64);
    for i in 0..specials.len() {
        let s = specials.get(i as u16).expect("i < len must resolve");
        serialize_bwd_special(&mut buf, s);
    }
    fnv1a(&buf)
}

// ── the pin ─────────────────────────────────────────────────────────────────────

struct Pin {
    name: &'static str,
    traffic: usize,
    lanes: usize,
    counted: usize,
    reported: usize,
    refusals: usize,
    evictions: usize,
    entries_fnv: Option<u64>,
    digest: u64,
}

/// Generated at HEAD `e2ae8173` (rr/gkr_bwd_full_decomp), crate source CLEAN, via the
/// `--nocapture` regeneration run in the module doc. Each row is `cs_schedule_bwd_layer`
/// on the fixture's L0, Ext regime, b16. `inits_and_teardowns` fell back to the canonical
/// baseline (no priced plan shipped → `entries_fnv = None`).
const PINS: &[Pin] = &[
    Pin { name: "add_sub_lui_auipc_mop_layout_gkr.json", traffic: 892, lanes: 936, counted: 892, reported: 892, refusals: 0, evictions: 56, entries_fnv: Some(18244912854743436632), digest: 0xc8613db6f5de6f5b },
    Pin { name: "bigint_with_extended_control_layout_gkr.json", traffic: 18056, lanes: 15275, counted: 18056, reported: 18056, refusals: 0, evictions: 453, entries_fnv: Some(591413752844331828), digest: 0x5e7849d2e570ebcc },
    Pin { name: "blake2_g_function_layout_gkr.json", traffic: 532, lanes: 572, counted: 532, reported: 532, refusals: 0, evictions: 63, entries_fnv: Some(8490909918706597748), digest: 0xc1624970e3525590 },
    Pin { name: "blake2_with_extended_control_layout_gkr.json", traffic: 8348, lanes: 5285, counted: 8348, reported: 8348, refusals: 0, evictions: 431, entries_fnv: Some(6829404962789468074), digest: 0x023f752de4898555 },
    Pin { name: "inits_and_teardowns_preprocessed_layout_gkr.json", traffic: 256, lanes: 263, counted: 256, reported: 256, refusals: 0, evictions: 0, entries_fnv: None, digest: 0xc841107d89b2b2fb },
    Pin { name: "jump_branch_slt_layout_gkr.json", traffic: 748, lanes: 827, counted: 748, reported: 748, refusals: 0, evictions: 58, entries_fnv: Some(2416640550128445911), digest: 0x010b397f7df46863 },
    Pin { name: "keccak_special5_layout_gkr.json", traffic: 14580, lanes: 12678, counted: 14580, reported: 14580, refusals: 0, evictions: 388, entries_fnv: Some(14727149004627702300), digest: 0x7d4e5db517975672 },
    Pin { name: "mem_subword_only_layout_gkr.json", traffic: 572, lanes: 691, counted: 572, reported: 572, refusals: 0, evictions: 41, entries_fnv: Some(8561008963937760174), digest: 0x950a6aed8af67c8f },
    Pin { name: "mem_word_only_layout_gkr.json", traffic: 380, lanes: 484, counted: 380, reported: 380, refusals: 0, evictions: 30, entries_fnv: Some(1451386828103137462), digest: 0xcc2b22e63c5159cc },
    Pin { name: "shift_binop_layout_gkr.json", traffic: 656, lanes: 686, counted: 656, reported: 656, refusals: 0, evictions: 35, entries_fnv: Some(6077704548435557912), digest: 0x8af344bf63ab8944 },
    Pin { name: "unsigned_mul_div_layout_gkr.json", traffic: 412, lanes: 443, counted: 412, reported: 412, refusals: 0, evictions: 51, entries_fnv: Some(1850612376543111069), digest: 0xcce25912ff528e5b },
    Pin { name: "unified_reduced_machine_layout_gkr.json", traffic: 3668, lanes: 3687, counted: 3668, reported: 3668, refusals: 0, evictions: 186, entries_fnv: Some(8553123700608381970), digest: 0x83b136caba3c1b46 },
];

#[test]
fn bwd_backend_neutrality() {
    let mut checked = 0usize;
    let mut missing: Vec<String> = Vec::new();
    for &name in FIXTURES {
        let (layer, cross) = load_layer(name, 0);
        if bwd_roots(&layer).is_empty() {
            continue; // L0 has no backward roots for this fixture
        }
        let outcome = cs_schedule_bwd_layer(&layer, BwdRegime::Ext, &cross, 16);
        let traffic = outcome.stats.global + outcome.stats.fold_traffic;
        let lanes = outcome.instrs;
        let cert = outcome.certificate;
        let entries_fnv = outcome.plan.as_ref().map(|p| p.entries_fnv);
        let digest = program_digest(&outcome.compiled.program, &outcome.compiled.specials);

        // Regeneration line — copy into `PINS`.
        println!(
            "PIN name={name:?} traffic={traffic} lanes={lanes} counted={} reported={} \
             refusals={} evictions={} entries_fnv={:?} digest={:#018x}",
            cert.counted_traffic,
            cert.reported_traffic,
            cert.refusals,
            cert.evictions,
            entries_fnv,
            digest,
        );

        assert!(cert.diverged.is_none(), "{name}: shipped program diverged");

        match PINS.iter().find(|p| p.name == name) {
            Some(p) => {
                assert_eq!(traffic, p.traffic, "{name}: traffic drift (TERM path not neutral)");
                assert_eq!(lanes, p.lanes, "{name}: program_lanes drift");
                assert_eq!(cert.counted_traffic, p.counted, "{name}: certificate counted_traffic drift");
                assert_eq!(cert.reported_traffic, p.reported, "{name}: certificate reported_traffic drift");
                assert_eq!(cert.refusals, p.refusals, "{name}: certificate refusals drift");
                assert_eq!(cert.evictions, p.evictions, "{name}: certificate evictions drift");
                assert_eq!(entries_fnv, p.entries_fnv, "{name}: plan entries_fnv drift");
                assert_eq!(
                    digest, p.digest,
                    "{name}: encoded backward program digest drift — TERM path is NOT byte-neutral"
                );
                checked += 1;
            }
            None => missing.push(name.to_string()),
        }
    }
    assert!(
        missing.is_empty(),
        "no pin constants for: {missing:?} — regenerate PINS from the printed `PIN …` table"
    );
    assert!(checked > 0, "no fixture L0 had bwd roots — enumeration broke");
}
