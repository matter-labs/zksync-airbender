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

// ===========================================================================
// Task 3.6 — COMPILE-TIME GUARDS over ALL 22 fixtures × EVERY (layer, graph).
//
// These are PER-LAYER / CROSS-LAYER ISA-encodability invariants, so the sweep
// must cover EVERY layer (not just L0): an L0-only check misses upper-layer
// violations (inner-layer reads, deeper caches). For each (fixture, layer) the
// test compiles `compile_forward_v2(layer, g, FwdParams2::default())` and
// asserts six guards on the fused program (each tied to an ISA wire-field bit
// width or a soundness invariant). The const cap is the 12-bit `LDC_IDX_BITS`
// (= 4096), NOT a stale 256 — confirmed in `isa_v2/mod.rs` (`LDC_IDX_BITS = 12`)
// and matched by `challenges::build_const_table_v2`'s own `<= 4096` assert.
// ===========================================================================

use gkr_eval_isa::compiler_v2::{compile_forward_v2, FwdParams2};
use gkr_eval_isa::isa_v2::{Dst, Header, MAX_ARITY, MATRIX_SLOT_BITS, Operand, SLOT_CELL_BITS};

/// The 12-bit `Ldc{Const}` index bound (`LDC_IDX_BITS = 12` in `isa_v2/mod.rs`).
/// R2 raised the const cap from a stale u8 (256) to this real bound; the const
/// table is indexed by a 12-bit field, so `consts.len()` must fit `2^12 = 4096`.
const LDC_IDX_CAP: usize = 1 << 12; // 4096

#[test]
fn compiled_programs_satisfy_guards_all_layers() {
    let fixtures = all_fixtures();
    assert_eq!(fixtures.len(), 22, "expected the 22-fixture codegen_ir corpus");

    // The 4-bit MatrixSlot cap (16 backings) and 7-bit SLOT_CELL_BITS (< 128).
    let matrix_slot_cap: usize = 1 << MATRIX_SLOT_BITS; // 16
    let slot_cell_cap: usize = 1 << SLOT_CELL_BITS; // 128

    // Non-vacuity / coverage accumulators.
    let mut pairs_exercised = 0usize; // (fixture, layer) pairs compiled
    let mut affine_cols_walked = 0usize; // guard 2: Operand::Affine cols seen
    let mut materialize_cols_walked = 0usize; // guard 2: Dst::Materialize cols seen
    let mut arith_arities_walked = 0usize; // guard 3: Header::Arith arities seen
    let mut macro_arities_walked = 0usize; // guard 3: Header::Macro n_operands seen
    let mut isolation_ok_layers = 0usize; // guard 4: isolation_ok == true count

    for p in &fixtures {
        let name = p.file_name().unwrap().to_str().unwrap().to_string();
        let c = load_circuit(p).unwrap_or_else(|e| panic!("load {name}: {e:?}"));
        for (li, layer) in c.circuit.layers.iter().enumerate() {
            let Some(g) = c.graphs.get(li) else { continue };
            let cf = compile_forward_v2(layer, g, FwdParams2::default());
            pairs_exercised += 1;

            // GUARD 1: matrix table <= 16 backings (4-bit MatrixSlot cap).
            // Assert BOTH the table itself and the recorded stat (they must agree).
            assert!(
                cf.matrix_table.len() <= matrix_slot_cap,
                "{name} L{li}: matrix table has {} backings > {matrix_slot_cap} (4-bit MatrixSlot cap)",
                cf.matrix_table.len()
            );
            assert!(
                cf.stats.n_matrix_slots <= matrix_slot_cap,
                "{name} L{li}: stats.n_matrix_slots {} > {matrix_slot_cap}",
                cf.stats.n_matrix_slots
            );
            assert_eq!(
                cf.matrix_table.len(),
                cf.stats.n_matrix_slots,
                "{name} L{li}: matrix_table.len() and stats.n_matrix_slots disagree"
            );

            // Walk EVERY instruction's lanes for guards 2/3/6.
            for (ii, ins) in cf.program.instrs.iter().enumerate() {
                // GUARD 3: arith arity / macro n_operands <= 127 (7-bit fields).
                match ins.header {
                    Header::Arith { arity, .. } => {
                        assert!(
                            (arity as u32) <= MAX_ARITY,
                            "{name} L{li} i{ii}: arith arity {arity} > MAX_ARITY {MAX_ARITY}"
                        );
                        arith_arities_walked += 1;
                    }
                    Header::Macro { n_operands, .. } => {
                        assert!(
                            (n_operands as u32) <= MAX_ARITY,
                            "{name} L{li} i{ii}: macro n_operands {n_operands} > MAX_ARITY {MAX_ARITY}"
                        );
                        macro_arities_walked += 1;
                    }
                }

                // Closures to walk operand/dst cols for guard 2. An Affine col and
                // a Materialize col both ride the 10-bit `col` field, so both must
                // be < COL_CAP (1024). Walk operands, dsts, AND the memtup lanes
                // (its role/payload/const operands carry Affine cols too).
                let mut check_operand_col = |op: &Operand| {
                    if let Operand::Affine { col, .. } = op {
                        assert!(
                            (*col as u32) < COL_CAP,
                            "{name} L{li} i{ii}: Affine col {col} >= COL_CAP {COL_CAP} (10-bit col)"
                        );
                        affine_cols_walked += 1;
                    }
                };
                for op in &ins.operands {
                    check_operand_col(op);
                }
                if let Some(mt) = &ins.memtup {
                    for (_r, op) in &mt.roles {
                        check_operand_col(op);
                    }
                    if let Some(p) = &mt.as_payload {
                        check_operand_col(p);
                    }
                    for (_r, op) in &mt.consts {
                        check_operand_col(op);
                    }
                }
                for d in &ins.dsts {
                    match d {
                        Dst::Materialize { col, .. } => {
                            assert!(
                                (*col as u32) < COL_CAP,
                                "{name} L{li} i{ii}: Materialize col {col} >= COL_CAP {COL_CAP} (10-bit col)"
                            );
                            materialize_cols_walked += 1;
                        }
                        // GUARD 6 (part b): a macro/cache instr must NEVER carry a
                        // Dst::Slot. Caches/macros Materialize into matrix backings
                        // (`lower_cache`/`lower_gate` footers are all
                        // `Dst::Materialize`); only base-arith uses persistent slot
                        // CELLS. So a Dst::Slot on a Macro header would mean a cache
                        // occupies a persistent slot — the thing guard 6 forbids.
                        Dst::Slot { .. } => {
                            assert!(
                                matches!(ins.header, Header::Arith { .. }),
                                "{name} L{li} i{ii}: a Macro instr carries a Dst::Slot — a cache \
                                 must Materialize into a backing, never occupy a persistent slot cell"
                            );
                        }
                    }
                }
            }

            // GUARD 4: isolation_ok == true for every in-tree layer (the fused
            // program is sound — no cross-strand Slot dep). The forced-false
            // FALLBACK path is proven separately by Task 2.7's
            // `isolation_detector_finds_real_cross_strand_dep_then_falls_back`; we
            // do NOT try to trip it from the corpus.
            assert!(
                cf.isolation_ok,
                "{name} L{li}: isolation_ok == false for an in-tree layer (fused program unsound)"
            );
            isolation_ok_layers += 1;

            // GUARD 5: const table <= 4096 (the real 12-bit LDC_IDX_BITS bound,
            // NOT a stale 256 — R2 raised it; see `build_const_table_v2`). The
            // program's `consts` are indexed by the 12-bit `Ldc{Const}` field.
            assert!(
                cf.program.consts.len() <= LDC_IDX_CAP,
                "{name} L{li}: const table {} > LDC_IDX_CAP {LDC_IDX_CAP} (12-bit LDC_IDX_BITS)",
                cf.program.consts.len()
            );

            // GUARD 6 (part a): the persistent slot-cell working set is base-arith
            // ONLY and fits the 7-bit SLOT_CELL_BITS field (< 128). `max_live_cells`
            // is the high-water count of simultaneously-live slot cells (== the
            // program's `n_slot_cells`); caches/macros do not allocate slot cells
            // (they Materialize), so this counts base-arith transients only. A
            // value < 128 is exactly "no cache occupies a [persistent] slot cell
            // beyond the 7-bit working set". (FwdParams2::default budget_cells=120,
            // itself < 128, bounds this; the assert pins the wire-field invariant.)
            assert!(
                cf.stats.max_live_cells < slot_cell_cap,
                "{name} L{li}: max_live_cells {} >= {slot_cell_cap} (7-bit SLOT_CELL_BITS)",
                cf.stats.max_live_cells
            );
            assert_eq!(
                cf.stats.max_live_cells, cf.program.n_slot_cells as usize,
                "{name} L{li}: max_live_cells and program.n_slot_cells disagree"
            );
        }
    }

    // Non-vacuity: the sweep actually exercised layers and walked the things the
    // guards check (a guard that walked nothing would pass vacuously).
    assert!(pairs_exercised >= 1, "no (fixture, layer) pair exercised");
    // The corpus is multi-layer across 22 fixtures, so this is well above 1.
    assert!(
        pairs_exercised > 22,
        "expected many (fixture, layer) pairs (>22), got {pairs_exercised}"
    );
    assert!(affine_cols_walked > 0, "guard 2 walked no Affine cols (vacuous)");
    assert!(
        materialize_cols_walked > 0,
        "guard 2 walked no Materialize cols (vacuous)"
    );
    assert!(arith_arities_walked > 0, "guard 3 walked no arith arities (vacuous)");
    assert!(macro_arities_walked > 0, "guard 3 walked no macro arities (vacuous)");
    assert!(isolation_ok_layers > 0, "guard 4 checked no layers (vacuous)");

    eprintln!(
        "[3.6 guards] pairs={pairs_exercised} affine_cols={affine_cols_walked} \
         mat_cols={materialize_cols_walked} arith={arith_arities_walked} \
         macros={macro_arities_walked} isolation_ok_layers={isolation_ok_layers}"
    );
}
