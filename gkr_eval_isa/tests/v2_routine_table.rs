//! Phase-1 gate (spec §9): decoder + oracle + report + CUDA must agree on
//! routine IDs/shapes BEFORE phase 2. Two distinct gates (finding 3 + 4):
//!  (A) every forward gate/cache is CLASSIFIED into a lowering kind, and only
//!      `LoweringKind::Macro` requires a routine — arithmetic/alias/scratch
//!      gates must NOT be forced into bogus routines;
//!  (B) the routine table is decode-sound: dense, `id == index`, one schema
//!      per `RoutineId`, fixed-shape counts match the round-trip test vectors.

use gkr_eval_isa::isa_v2::routines::{
    lowering_kind, routine_for_cache, routine_for_gate, routine_table, LoweringKind, Shape,
};
// RoutineId lives in isa_v2 (mod.rs), NOT routines.rs (which only reads it via
// `super::RoutineId` and does not re-export it) — import it from its owner.
use gkr_eval_isa::isa_v2::RoutineId;
use gkr_eval_isa::test_support::all_fixtures;
use gkr_design_space::import::load_circuit;

/// Every id a mapper returns MUST index a schema row whose own id matches —
/// else encode2/decode2 (`routine_table()[routine]`, Task 1.5) panic OOB or
/// read the wrong schema. This is the load-bearing coverage check (RR2-F1):
/// `routine_table_is_decode_sound` only validates rows that ALREADY exist, so
/// a mapper returning an unrowed id would otherwise pass the gate and panic
/// later. `schema.id` is `u8`, `RoutineId` is `#[repr(u8)]`.
fn assert_resolvable(id: RoutineId, ctx: &str, bad: &mut Vec<String>) {
    let t = routine_table();
    let i = id as usize;
    if i >= t.len() {
        bad.push(format!("{ctx}: routine id {i} ({id:?}) has no schema row (table len {})", t.len()));
    } else if t[i].id != id as u8 {
        bad.push(format!("{ctx}: routine id {i} ({id:?}) indexes schema with id {}", t[i].id));
    }
}

/// (A) Coverage by lowering kind. A Macro-classified gate/cache MUST resolve to
/// a routine whose id is backed by a schema row; Arith/Alias/ScratchSkip must
/// NOT have a routine (that would corrupt the ISA boundary). Unsupported is a
/// hard failure — a kind the corpus contains that no lowering handles.
#[test]
fn every_forward_kind_is_classified_and_macros_have_routines() {
    let mut bad: Vec<String> = Vec::new();
    for p in all_fixtures() {
        let c = load_circuit(&p).unwrap();
        let name = p.file_name().unwrap().to_str().unwrap();
        for layer in &c.circuit.layers {
            for gate in layer.gates.iter().chain(&layer.gates_external) {
                match lowering_kind(&gate.kind) {
                    LoweringKind::Macro => match routine_for_gate(&gate.kind) {
                        Some(id) => assert_resolvable(id, &format!("{name}: gate {:?}", gate.kind), &mut bad),
                        None => bad.push(format!("{name}: Macro gate without routine: {:?}", gate.kind)),
                    },
                    LoweringKind::Arith | LoweringKind::Alias | LoweringKind::ScratchSkip => {
                        if routine_for_gate(&gate.kind).is_some() {
                            bad.push(format!("{name}: non-Macro gate has a routine (boundary leak): {:?}", gate.kind));
                        }
                    }
                    LoweringKind::Unsupported => {
                        bad.push(format!("{name}: UNSUPPORTED gate kind: {:?}", gate.kind));
                    }
                }
            }
            for cache in &layer.caches {
                // every cache lowers through a macro (gather / memory-tuple)
                match routine_for_cache(&cache.kind) {
                    Some(id) => assert_resolvable(id, &format!("{name}: cache {:?}", cache.kind), &mut bad),
                    None => bad.push(format!("{name}: cache without routine: {:?}", cache.kind)),
                }
            }
        }
    }
    assert!(bad.is_empty(), "classification/coverage failures:\n{}", bad.join("\n"));
}

/// (B) Decode soundness of the routine table.
#[test]
fn routine_table_is_decode_sound() {
    let t = routine_table();
    for (idx, schema) in t.iter().enumerate() {
        assert_eq!(schema.id as usize, idx, "routine table not densely id-indexed at {idx}");
        assert!(schema.id <= 127, "routine-id {} exceeds 7-bit space", schema.id);
        assert!(!schema.reference.is_empty(), "routine {idx} has no reference anchor");
        // Fixed-shape routines must declare a concrete operand count so decode
        // knows the lane boundary without a count lane; Variable/MemTuple carry
        // a count lane instead (Task 1.5).
        match schema.shape {
            Shape::Fixed(n) => assert!(n <= 8, "Fixed routine {idx} arity {n} unreasonable"),
            Shape::Variable | Shape::MemTuple => {}
        }
        assert!(schema.output_count >= 1, "routine {idx} has no output");
    }
}
