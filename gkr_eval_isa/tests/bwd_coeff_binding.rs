//! Task 6 gates: final source binding (design §9.4, §10, §12.3).
//!
//! Two claims are gated here, and they pull in opposite directions:
//!
//!   * the FORWARD program's binding is byte-identical after the sequence core was
//!     lifted out of `fwd::binding::bind_final_sources` — pinned locally by
//!     `forward_binding_and_digest_are_unchanged` over the whole forward corpus,
//!     and by `tests/fwd_digest.rs` (release, `--ignored`) over the encoded
//!     programs and all five indexed context tables; and
//!   * the BACKWARD coefficient schedule binds ONE source coordinate per PHYSICAL
//!     source resolution, with `first_access` assigned dead last.
//!
//! Nothing here encodes a u16 (Task 7) or builds an artifact (Task 8).

mod common;

use std::collections::{BTreeMap, BTreeSet};

use common::{FIXTURES, layers_with_bwd_roots, load_dag_sched};
use cs::gkr_compiler::dag_ir::BwdRegime;
use gkr_eval_isa::fwd::binding::BackingKey;
use gkr_eval_isa::fwd::compile::compile_circuit;
use gkr_eval_isa::fwd::isa::{Instr, OperandField, OperandLine, Program};

/// The forward-compilable corpus: the same 11 committed `b16` layouts
/// `fwd_digest.rs` and `source_window_census.rs` compile.
const FORWARD_FIXTURES: &[&str] = &[
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

// ── Forward equivalence ──────────────────────────────────────────────────────

/// FNV-1a, 64-bit — the same hash `fwd_digest.rs` pins with.
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

fn push_u64(buf: &mut Vec<u8>, v: u64) {
    buf.extend_from_slice(&v.to_le_bytes());
}

/// Explicit, hand-rolled serialization (never `Debug`): variant tag in declaration
/// order, then fields, `usize` widened to `u64` LE.
fn serialize_backing(buf: &mut Vec<u8>, key: &BackingKey) {
    let field_tag = |f: OperandField| match f {
        OperandField::Base => 0u8,
        OperandField::Ext => 1,
    };
    match key {
        BackingKey::BaseLayerMemory => buf.push(0),
        BackingKey::BaseLayerWitness => buf.push(1),
        BackingKey::Setup => buf.push(2),
        BackingKey::Scratch => buf.push(3),
        BackingKey::LayerOutput { layer, field } => {
            buf.push(4);
            push_u64(buf, *layer as u64);
            buf.push(field_tag(*field));
        }
        BackingKey::CacheOutput { layer, field } => {
            buf.push(5);
            push_u64(buf, *layer as u64);
            buf.push(field_tag(*field));
        }
    }
}

fn visit_operands(program: &Program, mut visit: impl FnMut(&OperandLine)) {
    for instr in &program.instrs {
        match instr {
            Instr::Mov { src: Some(operand), .. } => visit(operand),
            Instr::Mov { src: None, .. } => {}
            Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                operands.iter().for_each(&mut visit);
            }
            Instr::Fma { pairs, .. } => {
                for (lhs, rhs) in pairs {
                    visit(lhs);
                    visit(rhs);
                }
            }
        }
    }
}

/// Everything final binding decides for one forward program: the window layout
/// (backing, free base, referenced columns, fold descriptors) and every bound
/// operand coordinate in program order.
fn forward_binding_bytes(name: &str) -> Vec<u8> {
    let (dag, schedule, artifact) = load_dag_sched(name);
    let compiled = compile_circuit(&dag, &schedule, &artifact)
        .unwrap_or_else(|e| panic!("[{name}] forward compile: {e:?}"));
    assert_eq!(compiled.budget, 16, "[{name}] expected the committed four-cell budget");
    let mut buf = Vec::new();
    for (li, layer) in compiled.layers.iter().enumerate() {
        push_u64(&mut buf, li as u64);
        let table = &layer.ctx.source_windows;
        push_u64(&mut buf, table.len() as u64);
        for window in table.windows() {
            serialize_backing(&mut buf, &window.backing);
            push_u64(&mut buf, window.first_column as u64);
            for column in window.referenced_columns() {
                push_u64(&mut buf, column as u64);
            }
            buf.push(0xff);
            for (column, desc) in window.fold_descriptors() {
                push_u64(&mut buf, column as u64);
                push_u64(&mut buf, u64::from(desc));
            }
            buf.push(0xfe);
        }
        visit_operands(&layer.program, |operand| match *operand {
            OperandLine::LogicalGlobal { .. } | OperandLine::LogicalFold { .. } => {
                panic!("[{name} L{li}] final forward program kept an unbound logical source")
            }
            OperandLine::Source { window, column, first_access } => {
                assert!(
                    !first_access,
                    "[{name} L{li}] the forward VM has no first-access semantics"
                );
                buf.push(window);
                buf.push(column);
                buf.push(u8::from(first_access));
            }
            _ => {}
        });
    }
    buf
}

/// The forward binding of every committed layout, digested.
///
/// The value was captured on the pre-extraction code and is NOT regenerated: it is
/// the whole point of the test. A drift here is a forward regression, not a stale
/// pin — the same rule `fwd_digest.rs` states for its own aggregate.
#[test]
fn forward_binding_and_digest_are_unchanged() {
    let mut all = Vec::new();
    for name in FORWARD_FIXTURES {
        let bytes = forward_binding_bytes(name);
        let digest = fnv1a(&bytes);
        println!("BINDING {name} {digest:016x}");
        push_u64(&mut all, digest);
    }
    let aggregate = fnv1a(&all);
    println!("BINDING-ALL {aggregate:016x}");
    assert_eq!(aggregate, 0x2cc4_eb9b_7757_69a7, "forward source binding drift");
}
