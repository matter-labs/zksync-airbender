//! Phase-1 pre-build gates for ISA-v2 (spec §1a, §8, §9).

use cs::gkr_compiler::codegen_ir::{CodegenGate, CodegenLayer, ForwardSource, GateKind};
use gkr_design_space::import::load_circuit;
use gkr_eval_isa::test_support::{all_fixtures, collect_v2_addresses, column_offset};

/// R3 gate: the largest column offset any source OR destination references must
/// fit the declared 1024-column ISA cap (10-bit `col`). Measured max is 645.
pub const COL_CAP: u32 = 1024;

#[test]
fn r3_col_within_cap() {
    let mut global_max = 0u32;
    for p in all_fixtures() {
        let c = load_circuit(&p).unwrap();
        let name = p.file_name().unwrap().to_str().unwrap();
        for (li, layer) in c.circuit.layers.iter().enumerate() {
            for addr in collect_v2_addresses(layer) {
                let col = column_offset(&addr);
                global_max = global_max.max(col);
                assert!(
                    col < COL_CAP,
                    "{name} L{li}: column offset {col} >= cap {COL_CAP} \
                     — R3 option (c) invalid, escalate (source-id table or wider lane)"
                );
            }
        }
    }
    eprintln!("[R3] global max column offset = {global_max} (cap {COL_CAP})");
    assert!(global_max <= 645 + 64, "max column drifted far above the measured 645");
}

/// §9 MaxQuadratic gate: production has no general forward impl for non-scratch
/// MaxQuadratic; the corpus is all-scratch. v2 must NOT compute it. Assert every
/// forward MaxQuadratic output is scratch-prefilled; if this fires, a non-scratch
/// circuit appeared and that becomes its own design item.
#[test]
fn maxquadratic_all_scratch_prefilled() {
    let mut counts: Vec<(String, usize, usize)> = Vec::new();
    for p in all_fixtures() {
        let c = load_circuit(&p).unwrap();
        let name = p.file_name().unwrap().to_str().unwrap().to_string();
        let mut total = 0usize;
        let mut scratch = 0usize;
        for layer in &c.circuit.layers {
            for gate in layer.gates.iter().chain(&layer.gates_external) {
                if matches!(gate.kind, GateKind::MaxQuadratic { .. }) {
                    total += 1;
                    if gate_output_is_scratch_prefilled(layer, gate) {
                        scratch += 1;
                    }
                }
            }
        }
        assert_eq!(
            scratch, total,
            "{name}: {}/{} forward MaxQuadratic NOT scratch-prefilled — \
             non-scratch forward MaxQuadratic is a new design item (spec §9)",
            total - scratch, total
        );
        counts.push((name, total, scratch));
    }
    for (n, t, s) in &counts {
        eprintln!("[MaxQuad] {n}: {s}/{t} scratch-prefilled");
    }
}

/// True if the gate's output is produced by ForwardSource::ScratchPrefill /
/// backed by ScratchSpace. Ports the v1 scratch-prefill predicate from
/// `gkr_eval_isa/src/compiler/fwd.rs:102-105` (`gate_is_scratch_prefilled`):
///   `!g.dst.is_empty() && g.dst.iter().all(|s| matches!(s.forward_source, ForwardSource::ScratchPrefill))`
fn gate_output_is_scratch_prefilled(
    _layer: &CodegenLayer,
    gate: &CodegenGate,
) -> bool {
    !gate.dst.is_empty()
        && gate.dst.iter().all(|s| matches!(s.forward_source, ForwardSource::ScratchPrefill))
}
