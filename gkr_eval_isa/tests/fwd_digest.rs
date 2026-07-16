//! CS-M5a Task 0: pin a digest of every encoded FORWARD program at the pre-change
//! base commit (`rr/gkr_bwd_fc` tip `6b72026e`), BEFORE any source change, so a
//! later task in the backward full-decomposition rewrite can prove the forward
//! path stayed byte-identical.
//!
//! Corpus: the same 11 `_layout_gkr.json` fixtures `fwd_parity.rs`'s `CORPUS`
//! compiles — the fwd-compilable set with a committed b16 schedule. The
//! `_no_caches` fixtures and `unified_reduced_machine` (no committed schedule) are
//! out of scope here, same as the forward parity gate.
//!
//! Per (fixture, layer) this test:
//!   1. compiles the fwd program exactly as `fwd_parity.rs` does: `load_dag_sched`
//!      (lower_dag + validate + load/validate the committed b16 schedule) then
//!      `compile_circuit`;
//!   2. `encode`s the compiled program to its wire `u16` lanes;
//!   3. hashes an EXPLICIT byte serialization — NEVER `Debug` formatting:
//!        (a) every encoded `u16` lane, little-endian, in order, then
//!        (b) all FOUR `DagForwardContext` tables (`context.rs`'s field order):
//!            the descriptor table (`ctx.specials`), the const bank
//!            (`ctx.consts`), the challenge banks (`ctx.challenges`), and the
//!            backing table (`ctx.backings`) — each hand-serialized
//!            field-by-field (see `serialize_*` below), in table order.
//!      The encoded lanes carry only INDICES into these four tables —
//!      `OperandLine::Special { desc }`, `Ldc { sub, idx }`, `Global { slot, col }`
//!      (see `gkr_eval_isa::fwd::encode::pack_operand`) — table CONTENT is never
//!      inlined into the lane stream, so all four parts are required to pin the
//!      program's full semantics: content drift in any one of them (e.g. a
//!      `ConstBank` value or a `BackingTable` slot's meaning changing) would
//!      leave every lane byte-identical while silently changing what the
//!      program computes.
//!
//! FNV-1a (64-bit) is the hash throughout. Output: one canonical line per program,
//! `DIGEST <fixture> <layer> <hex>`, then a final `DIGEST-ALL <hex>`.
//!
//! DIGEST-ALL is FNV-1a over the concatenation of all per-program digests (each as
//! 8 little-endian bytes), in this test's own iteration order — fixture order as
//! listed in `FIXTURES` below, then ascending layer index within each fixture —
//! NOT the lexicographic order the pin command's shell `sort` applies to the
//! `DIGEST` lines it captures. This keeps DIGEST-ALL reproducible from this file
//! alone, independent of how the output is post-processed.
//!
//! `#[ignore]`: a pinning harness, not part of the default test gate. Run
//! explicitly (release; the bigint fixture needs a larger stack):
//!   RUST_MIN_STACK=1073741824 RUSTFLAGS="-Awarnings" \
//!     cargo test -p gkr_eval_isa --release --test fwd_digest -- --ignored --nocapture

mod common;
use common::load_dag_sched;

use gkr_eval_isa::fwd::binding::{BackingKey, BackingTable};
use gkr_eval_isa::fwd::compile::compile_circuit;
use gkr_eval_isa::fwd::context::DagForwardContext;
use gkr_eval_isa::fwd::encode::encode;
use gkr_eval_isa::fwd::isa::{LdcSub, OperandField};
use gkr_eval_isa::fwd::source::{
    virtual_setup_kind_code, ChallengeBanks, ConstBank, SpecialDescriptor, SpecialStrategy, SpecialTable,
};

use cs::gkr_compiler::dag_ir::{
    ChallengeKey, ChallengePower, ChallengeRef, FillSource, PermutationSlot, RangeWidth, ReadPlace,
};

/// The fwd-compilable corpus (matches `fwd_parity.rs`'s `CORPUS` fixture list —
/// `load_dag_sched` derives each committed-schedule stem itself via
/// `common::schedule_stem`, so only the fixture names are needed here).
const FIXTURES: &[&str] = &[
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
];

/// FNV-1a, 64-bit, byte at a time.
fn fnv1a(bytes: &[u8]) -> u64 {
    const OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut h = OFFSET_BASIS;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(PRIME);
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

/// Explicit byte serialization of one `ReadPlace` — hand-rolled (no `Debug`, no
/// serde) so the digest is stable independent of any derive/formatting change.
/// Variant tag first (declaration order), then fields in declaration order,
/// `usize` fields widened to a fixed `u64` LE so the digest does not depend on
/// the host pointer width.
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

fn serialize_range_width(buf: &mut Vec<u8>, w: &RangeWidth) {
    push_tag(
        buf,
        match w {
            RangeWidth::Bits16 => 0,
            RangeWidth::Timestamp => 1,
        },
    );
}

fn serialize_fill_source(buf: &mut Vec<u8>, f: &FillSource) {
    push_tag(
        buf,
        match f {
            FillSource::DecoderLookupFill => 0,
        },
    );
}

/// Explicit byte serialization of one `SpecialStrategy`. Variant tag first
/// (declaration order in `gkr_eval_isa::fwd::source`), then fields in
/// declaration order. `VirtualSetup` reuses the crate's own established
/// kind ↔ device-code mapping (`virtual_setup_kind_code`) rather than inventing
/// a second one here.
fn serialize_strategy(buf: &mut Vec<u8>, s: &SpecialStrategy) {
    match s {
        SpecialStrategy::PeekSingleColumn { set_index, width } => {
            push_tag(buf, 0);
            push_u64(buf, *set_index as u64);
            serialize_range_width(buf, width);
        }
        SpecialStrategy::PeekAggregate { set_index } => {
            push_tag(buf, 1);
            push_u64(buf, *set_index as u64);
        }
        SpecialStrategy::PeekSetup => {
            push_tag(buf, 2);
        }
        SpecialStrategy::PeekDecoder { predicate, fill } => {
            push_tag(buf, 3);
            serialize_read_place(buf, predicate);
            serialize_fill_source(buf, fill);
        }
        SpecialStrategy::VirtualSetup { kind } => {
            push_tag(buf, 4);
            push_u32(buf, virtual_setup_kind_code(kind));
        }
    }
}

fn serialize_descriptor(buf: &mut Vec<u8>, d: &SpecialDescriptor) {
    serialize_strategy(buf, &d.strategy);
    push_u32(buf, d.origin_expr.0);
}

/// Explicit byte serialization of one `OperandField` — variant tag matches its
/// own explicit discriminant (`Base = 0`, `Ext = 1`, `isa.rs`), spelled out here
/// rather than relied on via `as u8` so a future repr change fails to compile
/// here instead of silently reordering the digest.
fn serialize_operand_field(buf: &mut Vec<u8>, f: OperandField) {
    push_tag(
        buf,
        match f {
            OperandField::Base => 0,
            OperandField::Ext => 1,
        },
    );
}

/// Explicit byte serialization of one `BackingKey` — variant tag first
/// (declaration order in `gkr_eval_isa::fwd::binding`), then fields in
/// declaration order, `usize` widened to `u64` LE.
fn serialize_backing_key(buf: &mut Vec<u8>, k: &BackingKey) {
    match k {
        BackingKey::BaseLayerMemory => push_tag(buf, 0),
        BackingKey::BaseLayerWitness => push_tag(buf, 1),
        BackingKey::Setup => push_tag(buf, 2),
        BackingKey::Scratch => push_tag(buf, 3),
        BackingKey::LayerOutput { layer, field } => {
            push_tag(buf, 4);
            push_u64(buf, *layer as u64);
            serialize_operand_field(buf, *field);
        }
        BackingKey::CacheOutput { layer, field } => {
            push_tag(buf, 5);
            push_u64(buf, *layer as u64);
            serialize_operand_field(buf, *field);
        }
    }
}

/// Explicit byte serialization of the backing table's CONTENT. A `Global {
/// slot, col }` operand lane (`gkr_eval_isa::fwd::isa::OperandLine::Global`)
/// carries only a `(slot, col)` INDEX pair into this table
/// (`BackingTable::read_slot_col`/`slot_col`) — the digest must therefore pin
/// what each slot actually names (its `BackingKey`) and its dense column →
/// original-offset mapping (`slot_columns`), not just the slot count, or slot
/// content could drift while every lane stays byte-identical.
///
/// Length-prefixed (`u64` LE slot count), then per slot in slot-index order:
/// the `BackingKey`, then its dense-ordered original offsets (`u64` LE
/// length-prefix, then each offset widened to `u64` LE). Reads only the
/// table's public accessors (`n_slots`/`backing`/`slot_columns`) — the private
/// `dense_of` reverse index is fully determined by `slot_columns`'s order, so
/// it carries no additional content to pin.
fn serialize_backing_table(buf: &mut Vec<u8>, t: &BackingTable) {
    let n = t.n_slots();
    push_u64(buf, n as u64);
    for slot in 0..n {
        let slot = slot as u8;
        let key = t
            .backing(slot)
            .unwrap_or_else(|| panic!("slot {slot} < n_slots({n}) must resolve"));
        serialize_backing_key(buf, key);
        let cols = t.slot_columns(slot);
        push_u64(buf, cols.len() as u64);
        for &offset in cols {
            push_u64(buf, offset as u64);
        }
    }
}

/// Explicit byte serialization of the const bank's CONTENT. An `Ldc { sub:
/// Const, idx }` lane carries only an index into this bank
/// (`ConstBank::intern`/`get`), so the digest must pin the interned values
/// themselves, not just their count.
///
/// Length-prefixed (`u64` LE), then each value as its raw `u32` LE limb.
/// `ConstBank` stores BabyBear field elements as plain canonical `u32`s (see
/// its own doc / the `BABYBEAR_NEG_ONE` invariant assert in `source.rs`) — no
/// Montgomery form or other wrapper to unwrap, so the stored `u32` IS the raw
/// representation.
fn serialize_const_bank(buf: &mut Vec<u8>, c: &ConstBank) {
    let values = c.values();
    push_u64(buf, values.len() as u64);
    for &v in values {
        push_u32(buf, v);
    }
}

fn serialize_permutation_slot(buf: &mut Vec<u8>, s: &PermutationSlot) {
    push_tag(
        buf,
        match s {
            PermutationSlot::AddressLow => 0,
            PermutationSlot::AddressHigh => 1,
            PermutationSlot::TimestampLow => 2,
            PermutationSlot::TimestampHigh => 3,
            PermutationSlot::ValueLow => 4,
            PermutationSlot::ValueHigh => 5,
        },
    );
}

/// Variant tag first (declaration order in `cs::gkr_compiler::dag_ir::model`),
/// then fields in declaration order.
fn serialize_challenge_key(buf: &mut Vec<u8>, k: &ChallengeKey) {
    match k {
        ChallengeKey::LookupAdditive => push_tag(buf, 0),
        ChallengeKey::LookupMultiplicative => push_tag(buf, 1),
        ChallengeKey::PermutationAdditive => push_tag(buf, 2),
        ChallengeKey::PermutationLinearization(slot) => {
            push_tag(buf, 3);
            serialize_permutation_slot(buf, slot);
        }
        ChallengeKey::ConstraintAggregation => push_tag(buf, 4),
        ChallengeKey::ClaimBatching => push_tag(buf, 5),
    }
}

fn serialize_challenge_power(buf: &mut Vec<u8>, p: &ChallengePower) {
    match p {
        ChallengePower::One => push_tag(buf, 0),
        ChallengePower::Static(n) => {
            push_tag(buf, 1);
            push_u32(buf, *n);
        }
    }
}

/// Struct field order: `key` then `power` (`ChallengeRef`, `model.rs`).
fn serialize_challenge_ref(buf: &mut Vec<u8>, r: &ChallengeRef) {
    serialize_challenge_key(buf, &r.key);
    serialize_challenge_power(buf, &r.power);
}

/// Explicit byte serialization of the challenge banks' CONTENT. An `Ldc { sub:
/// ConstChallenge | ArgChallenge, idx }` lane carries only an index into the
/// matching channel (`ChallengeBanks::intern`/`get`), so the digest must pin
/// the interned `ChallengeRef`s themselves, not just their counts.
///
/// Both fields of `ChallengeBanks` are private, so this walks the public `get`
/// accessor from `idx = 0` until it returns `None` rather than reaching into
/// the struct — the internal `index: HashMap` is a pure lookup cache over
/// the same two channels, so it carries no content the channels don't already
/// pin. Per channel, `ConstChallenge` then `ArgChallenge` (declaration order —
/// `const_refs`/`arg_refs` in `source.rs`), length-prefixed (`u64` LE) then
/// each ref serialized field-by-field.
fn serialize_challenge_banks(buf: &mut Vec<u8>, banks: &ChallengeBanks) {
    for sub in [LdcSub::ConstChallenge, LdcSub::ArgChallenge] {
        let mut n: u16 = 0;
        while banks.get(sub, n).is_some() {
            n += 1;
        }
        push_u64(buf, n as u64);
        for idx in 0..n {
            let r = banks.get(sub, idx).expect("idx < n by construction above");
            serialize_challenge_ref(buf, r);
        }
    }
}

/// The full explicit byte serialization for one compiled layer's program:
/// encoded `u16` lanes (little-endian, in order), then all four
/// `DagForwardContext` tables in the struct's own field declaration order —
/// `specials`, `consts`, `challenges`, `backings` (`context.rs`). Each table is
/// length-prefixed (`u64` LE count) then its entries serialized field-by-field
/// in table order (`specials`: `SpecialTable::iter()`'s natural `Vec` order).
fn serialize_program_bytes(lanes: &[u16], ctx: &DagForwardContext) -> Vec<u8> {
    let specials = &ctx.specials;
    let mut buf = Vec::with_capacity(lanes.len() * 2 + specials.len() * 12);
    for &lane in lanes {
        buf.extend_from_slice(&lane.to_le_bytes());
    }
    push_u64(&mut buf, specials.len() as u64);
    for d in specials.iter() {
        serialize_descriptor(&mut buf, d);
    }
    serialize_const_bank(&mut buf, &ctx.consts);
    serialize_challenge_banks(&mut buf, &ctx.challenges);
    serialize_backing_table(&mut buf, &ctx.backings);
    buf
}

#[test]
#[ignore] // pinning harness — see module doc for the exact run command
fn fwd_digest_pin() {
    let mut per_program_digests: Vec<u64> = Vec::new();

    for &name in FIXTURES {
        let (dag, sched, artifact) = load_dag_sched(name);
        let compiled = compile_circuit(&dag, &sched, &artifact)
            .unwrap_or_else(|e| panic!("[{name}] compile_circuit: {e:?}"));
        assert_eq!(
            compiled.layers.len(),
            dag.layers.len(),
            "[{name}] compiled/dag layer count mismatch"
        );

        for (li, cl) in compiled.layers.iter().enumerate() {
            let lanes = encode(&cl.program).unwrap_or_else(|e| panic!("[{name}] layer {li}: encode: {e:?}"));
            let bytes = serialize_program_bytes(&lanes, &cl.ctx);
            let d = fnv1a(&bytes);
            per_program_digests.push(d);
            println!("DIGEST {name} {li} {d:016x}");
        }
    }

    assert!(!per_program_digests.is_empty(), "digest pin compared 0 programs — vacuous");

    // See module doc: DIGEST-ALL folds over this test's own iteration order, not
    // the pin command's post-hoc `sort`.
    let mut all_bytes = Vec::with_capacity(per_program_digests.len() * 8);
    for d in &per_program_digests {
        all_bytes.extend_from_slice(&d.to_le_bytes());
    }
    let all = fnv1a(&all_bytes);
    println!("DIGEST-ALL {all:016x}");
}
