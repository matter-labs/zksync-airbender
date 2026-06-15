//! ISA-v2 compiler (spec §5). New sibling module to the v1 `compiler`; reuses
//! v1 infrastructure but does not change v1 behaviour. Sub-passes are added by
//! later tasks; Task 2.1 seeds the joint matrix-slot table.

pub mod matrix_table;
pub mod challenges;
pub mod gather;
pub mod macros;

use crate::compiler::slots::SlotAlloc;
use crate::compiler::view::{self, ProgramView};
use crate::compiler::{is_computed, node_domain};
use crate::compiler_v2::matrix_table::MatrixTable;
use crate::isa::NEG_ONE_U32;
use crate::isa_v2::{
    ArithOp, Dst, Header, Instr2, LdcSub, Operand, Program2, SPECIAL_NEG_ONE, SPECIAL_ONE,
    SPECIAL_ZERO,
};
use crate::compiler_v2::challenges::build_const_table;
use cs::gkr_compiler::codegen_ir::{CodegenLayer, Domain, ExprNode};
use gkr_design_space::graph::AnalysisGraph;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug)]
pub struct FwdParams2 {
    pub budget_cells: usize,
    pub leaf_cache: bool,
    pub order: crate::compiler::OrderKind,
    /// Also emit the per-strand decomposition (Task 3.6 fallback assertion +
    /// Task 4.2 fused-vs-strand R2 proxy). Default false (fused-only). (F6)
    pub emit_per_strand: bool,
}
impl Default for FwdParams2 {
    fn default() -> Self {
        Self {
            budget_cells: 4096,
            leaf_cache: false,
            order: crate::compiler::OrderKind::Arena,
            emit_per_strand: false,
        }
    }
}

/// The three computation-isolated forward strands (spec §6, §2). Defined here
/// in Task 2.4; the partitioning logic lands in Task 2.7. (F6)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strand {
    BaseArith, // base Sum/Prod/Dot arena (CSE-rich)
    LookupGp,  // Lookup* leaves -> AggregateLookupRationalPair (AGG) cascade
    MemoryGp,  // MemoryTuple caches -> grand-product (PROD) cascade
}

/// Per-strand compiled programs (the §6/§7 fallback path).
pub struct PerStrand2 {
    pub programs: Vec<(Strand, Program2)>,
}

#[derive(Debug, Default)]
pub struct CompileStats2 {
    pub instrs: usize,
    pub lanes: usize,
    pub bytes: usize,
    pub arith: usize,
    pub macros: usize,
    pub gathers: usize,
    pub materializes: usize,
    pub max_live_cells: usize,
    pub n_matrix_slots: usize,
}

pub struct CompiledForward2 {
    /// The fused single-pass program over all three strands (the BW-win path).
    pub program: Program2,
    pub matrix_table: MatrixTable,
    pub stats: CompileStats2,
    /// `true` iff the §2 AGG/PROD isolation invariant held (fused is sound).
    /// `false` => callers MUST use `per_strand` (spec §6/§7: fall back, never
    /// abort). Task 2.4 sets it `true`; Task 2.7 computes it. (F6)
    pub isolation_ok: bool,
    /// Per-strand decomposition. `Some` when `emit_per_strand` was requested
    /// (Task 4.2 proxy) OR when `isolation_ok == false` (Task 3.6 fallback);
    /// `None` otherwise. Filled by Task 2.7. (F6)
    pub per_strand: Option<PerStrand2>,
    /// Debug/test hook (F7): arena node id behind each `program.instrs[k]` that
    /// came from base-arith lowering (None for macro/gather/materialize),
    /// instr-aligned (`instr_node.len() == program.instrs.len()`). Lets the
    /// Task 2.4 binding test map instr -> arena node.
    pub instr_node: Vec<Option<u32>>,
    /// Strand owning each fused `program.instrs[k]`, instr-aligned
    /// (`instr_strand.len() == program.instrs.len()`). Filled by Task 2.7; lets
    /// the strand test prove EXACT one-strand-per-instr coverage (RR2-F3).
    pub instr_strand: Vec<Strand>,
}

/// bf-cell width of a node's result.
fn width_cells(arena: &[ExprNode], node: usize) -> usize {
    match node_domain(&arena[node]) {
        Domain::Base => 1,
        Domain::Ext => 4,
    }
}

/// Where a computed node's result currently lives (a slot cell), so consumers
/// can read it back as `Operand::Slot`.
#[derive(Clone, Copy)]
struct SlotResidence {
    e4: bool,
    cell: u8,
}

pub fn compile_forward_v2(
    layer: &CodegenLayer,
    g: &AnalysisGraph,
    params: FwdParams2,
) -> CompiledForward2 {
    // (1) Joint matrix-slot table — shared by Affine reads and Materialize stores.
    let matrix_table = MatrixTable::build(layer);
    // (2) Program-DAG view (CSE fan-out per arena node).
    let pv: ProgramView = view::build(layer, g);
    let arena: &[ExprNode] = &layer.arena.nodes;

    // Deduped bf-const table (0/1/-1 are Special, not entries) — same dedup v1
    // uses, so the LdcSub::Const indices line up with the launcher's const bank.
    let consts = build_const_table(arena);
    let const_idx: HashMap<u32, u16> = consts
        .iter()
        .enumerate()
        .map(|(i, c)| (*c, i as u16))
        .collect();

    // Computed nodes that are layer outputs the PROGRAM owns (node is NOT a
    // native GateOutput): these materialize to their backing column. add_sub L0
    // has none, but the path is exercised by later fixtures (Task 2.6 hardens
    // alias/scratch handling on top of this simple correct policy).
    let mut output_addr: HashMap<usize, cs::definitions::GKRAddress> = HashMap::new();
    for out in &g.outputs {
        if !matches!(arena[out.node], ExprNode::GateOutput { .. }) {
            // First-seen wins (a node maps to one backing address).
            output_addr.entry(out.node).or_insert(out.addr);
        }
    }

    // Slot allocator for transient multi-use base intermediates AND single-use
    // results that must survive to their (single) consumer. Allocate on the
    // node's def; release operand cells after their last use (refcount via
    // ProgramView fan-out). A straightforward correct policy — Belady/leaf-cache
    // parity with v1 is a Phase-4 report concern, not a 2.4 correctness gate.
    let mut alloc = SlotAlloc::new(params.budget_cells);
    let mut residence: HashMap<usize, SlotResidence> = HashMap::new();
    // Remaining uses, decremented as we consume operands (drives cell release).
    let mut remaining: Vec<u32> = pv.uses.clone();

    let mut program = Program2 {
        instrs: Vec::new(),
        consts: consts.clone(),
        n_slot_cells: 0,
        n_matrix_slots: matrix_table.len() as u8,
    };
    let mut instr_node: Vec<Option<u32>> = Vec::new();
    let mut instr_strand: Vec<Strand> = Vec::new();
    let mut arith_count = 0usize;
    let mut materialize_count = 0usize;

    // Emission order: arena order is the IR's topological CSE encounter order
    // (children strictly precede parents), which is the Task 2.4 default. The
    // alternative orders (Pressure/Reuse) are validated in the report; honoring
    // them here is a no-op for correctness, so stick to arena order.
    let order: Vec<usize> = arena
        .iter()
        .enumerate()
        .filter(|(i, n)| is_computed(n) && pv.uses[*i] > 0)
        .map(|(i, _)| i)
        .collect();

    // Resolve a child node to its typed operand lane.
    let mut operand_for = |child: usize, residence: &HashMap<usize, SlotResidence>| -> Operand {
        match &arena[child] {
            ExprNode::Constant(c) => {
                let c = *c;
                if c == 0 {
                    Operand::Ldc { sub: LdcSub::Special, idx: SPECIAL_ZERO }
                } else if c == 1 {
                    Operand::Ldc { sub: LdcSub::Special, idx: SPECIAL_ONE }
                } else if c == NEG_ONE_U32 {
                    Operand::Ldc { sub: LdcSub::Special, idx: SPECIAL_NEG_ONE }
                } else {
                    let idx = *const_idx
                        .get(&c)
                        .expect("non-special const must be in the const table");
                    Operand::Ldc { sub: LdcSub::Const, idx }
                }
            }
            ExprNode::Place { addr, .. } => {
                // Staged source column: LDG via the joint matrix table. Field is
                // implied by the slot's logical key, so the lane carries none.
                let slot = matrix_table
                    .slot_for(addr)
                    .expect("Place source must have a backing slot");
                Operand::Affine { slot, col: matrix_table.column_of(addr) }
            }
            ExprNode::Sum { .. } | ExprNode::Product { .. } => {
                // CSE-resident computed result: read it back from its slot cell.
                let r = residence
                    .get(&child)
                    .expect("computed operand must be resident before its use");
                Operand::Slot { e4: r.e4, cell: r.cell }
            }
            ExprNode::GateOutput { .. } => {
                // No GateOutput child appears at L0 (gates of prior layers do not
                // feed L0 base arithmetic). Macro/gather lowering for these lands
                // in Task 2.5; reaching here in a later fixture is a real gap.
                unreachable!("GateOutput operand in base-arith lowering (Task 2.5 scope)")
            }
        }
    };

    for &node in &order {
        let (op, children): (ArithOp, Vec<usize>) = match &arena[node] {
            ExprNode::Sum { terms, .. } => {
                (ArithOp::Sum, terms.iter().map(|t| t.0 as usize).collect())
            }
            ExprNode::Product { factors, .. } => {
                (ArithOp::Prod, factors.iter().map(|f| f.0 as usize).collect())
            }
            // Only computed Sum/Product reach here (order filtered by is_computed).
            _ => unreachable!("non-computed node in emission order"),
        };

        // Operand lanes — one per term/factor, in IR order (operand[k] reads the
        // source for child[k]; VALUE binding is checked by the execute2 oracle).
        let operands: Vec<Operand> =
            children.iter().map(|&c| operand_for(c, &residence)).collect();

        // Footer dst: a layer-output computed node materializes to its backing
        // column; otherwise the result is a transient (multi- or single-use)
        // base intermediate living in a slot cell.
        let e4 = node_domain(&arena[node]) == Domain::Ext;
        let dst = if let Some(addr) = output_addr.get(&node) {
            let slot = matrix_table
                .slot_for(addr)
                .expect("computed layer output must have a backing slot");
            materialize_count += 1;
            Dst::Materialize { slot, col: matrix_table.column_of(addr) }
        } else {
            let w = width_cells(arena, node);
            let cell = alloc
                .alloc(w)
                .expect("slot budget exhausted (raise FwdParams2::budget_cells)")
                as u8;
            residence.insert(node, SlotResidence { e4, cell });
            Dst::Slot { e4, cell }
        };

        program.instrs.push(Instr2 {
            header: Header::Arith { op, arity: children.len() as u8 },
            operands,
            dsts: vec![dst],
            memtup: None,
        });
        instr_node.push(Some(node as u32));
        instr_strand.push(Strand::BaseArith);
        arith_count += 1;

        // Release operand cells whose last use was this instruction (computed
        // children only — Place/Const reads do not occupy a slot cell).
        for &c in &children {
            if is_computed(&arena[c]) {
                let r = remaining[c];
                debug_assert!(r > 0, "operand consumed past its use count");
                remaining[c] = r - 1;
                if remaining[c] == 0 {
                    if let Some(res) = residence.remove(&c) {
                        alloc.release(res.cell as u16, width_cells(arena, c));
                    }
                }
            }
        }
    }

    // Macro / gather / materialize lowering (Task 2.5). After the base-arith
    // instrs, emit one macro Instr2 per Macro gate and per cache. Macro instrs
    // are not single arena nodes (instr_node = None); strand classification is
    // Task 2.7's job, so tag all non-arith as BaseArith for now (instr-aligned).
    let cache_kinds = macros::cache_kind_by_addr(layer);
    let mut mctx = macros::MacroCtx::new(&matrix_table, &const_idx, &cache_kinds);
    let mut macro_count = 0usize;
    let mut gather_lane_count = 0usize;

    // Caches first (they produce values gates/outputs may read), then gates.
    for cache in &layer.caches {
        let instr = macros::lower_cache(cache, arena, &mut mctx);
        macro_count += 1;
        gather_lane_count += instr
            .operands
            .iter()
            .filter(|o| matches!(o, Operand::Indirect { .. }))
            .count();
        materialize_count += instr
            .dsts
            .iter()
            .filter(|d| matches!(d, Dst::Materialize { .. }))
            .count();
        program.instrs.push(instr);
        instr_node.push(None);
        instr_strand.push(Strand::BaseArith);
    }
    for gate in layer.gates.iter().chain(&layer.gates_external) {
        if let Some(instr) = macros::lower_gate(gate, arena, &mut mctx) {
            macro_count += 1;
            gather_lane_count += instr
                .operands
                .iter()
                .filter(|o| matches!(o, Operand::Indirect { .. }))
                .count();
            materialize_count += instr
                .dsts
                .iter()
                .filter(|d| matches!(d, Dst::Materialize { .. }))
                .count();
            program.instrs.push(instr);
            instr_node.push(None);
            instr_strand.push(Strand::BaseArith);
        }
    }

    program.n_slot_cells = alloc.high_water_cells as u16;

    // Non-packing lane count for stats: a base-arith layer can have >127 live
    // slot cells (a real 7-bit SLOT_CELL_BITS finding, orthogonal to macro
    // lowering), which would trip `encode2`'s width debug-assert. `lane_count`
    // mirrors the same lane layout without packing, so the compiler stays
    // panic-free across the whole corpus.
    let lanes = crate::isa_v2::encode::lane_count(&program);
    let stats = CompileStats2 {
        instrs: program.instrs.len(),
        lanes,
        // 16-bit lanes -> 2 bytes each.
        bytes: lanes * 2,
        arith: arith_count,
        macros: macro_count,
        gathers: gather_lane_count,
        materializes: materialize_count,
        max_live_cells: alloc.high_water_cells,
        n_matrix_slots: matrix_table.len(),
    };

    debug_assert_eq!(instr_node.len(), program.instrs.len());
    debug_assert_eq!(instr_strand.len(), program.instrs.len());

    CompiledForward2 {
        program,
        matrix_table,
        stats,
        // Task 2.7 computes the §2 AGG/PROD isolation check + per-strand split.
        isolation_ok: true,
        per_strand: None,
        instr_node,
        instr_strand,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::{is_computed, view};
    use crate::isa_v2::{ArithOp, Dst, Header};
    use crate::test_support::fixture_path;
    use cs::gkr_compiler::codegen_ir::ExprNode;
    use gkr_design_space::import::load_circuit;

    #[test]
    fn add_sub_base_arith_emits_every_live_computed_node() {
        let c = load_circuit(&fixture_path("add_sub_lui_auipc_mop_codegen_ir_gkr.json")).unwrap();
        let layer = &c.circuit.layers[0];
        let arena = &layer.arena.nodes;
        let pv = view::build(layer, &c.graphs[0]);

        // Reference census: every live computed base node must be emitted as one
        // Arith instruction, UNLESS it is an intentional pass-through alias
        // (Task 2.6 handles aliasing; add_sub L0 is pure base arithmetic with
        // no macro/alias, so the counts match exactly here).
        let live_computed: usize = arena
            .iter()
            .enumerate()
            .filter(|(i, n)| is_computed(n) && pv.uses[*i] > 0)
            .count();

        let cf = compile_forward_v2(layer, &c.graphs[0], FwdParams2::default());
        let arith: Vec<_> = cf
            .program
            .instrs
            .iter()
            .filter(|i| matches!(i.header, Header::Arith { .. }))
            .collect();
        assert_eq!(
            arith.len(),
            live_computed,
            "every live computed base node must lower to exactly one Arith instr"
        );

        // Per-instruction BINDING (F7): map each arith instr back to its arena
        // node via `instr_node` and assert the op matches the node KIND, the
        // operand count matches the node's terms/factors (not just the instr's
        // own self-written arity), and the dst FIELD matches the node domain.
        // This is a STRUCTURAL guard; operand-VALUE binding (operand[k] reads
        // the source for terms[k]) is checked by the execute2 oracle, Task 3.3.
        use crate::compiler::node_domain;
        use cs::gkr_compiler::codegen_ir::Domain;
        // instr_node must be instr-aligned, else `zip` silently drops trailing
        // instructions and the binding check passes vacuously (RR2-F4).
        assert_eq!(
            cf.instr_node.len(),
            cf.program.instrs.len(),
            "instr_node must be instr-aligned"
        );
        for (ins, node) in cf.program.instrs.iter().zip(&cf.instr_node) {
            let Header::Arith { op, arity } = ins.header else { continue };
            let nid = node.expect("arith instr must carry its arena node id") as usize;
            match (&arena[nid], op) {
                (ExprNode::Sum { terms, .. }, ArithOp::Sum) => {
                    assert_eq!(arity as usize, terms.len());
                    assert_eq!(ins.operands.len(), terms.len());
                }
                (ExprNode::Product { factors, .. }, ArithOp::Prod) => {
                    assert_eq!(arity as usize, factors.len());
                    assert_eq!(ins.operands.len(), factors.len());
                }
                // Dot = strength-reduced sum-of-products; only on a Sum node.
                (ExprNode::Sum { .. }, ArithOp::Dot) => {
                    assert_eq!(ins.operands.len(), 2 * arity as usize)
                }
                (n, o) => panic!("arith op {o:?} bound to wrong node kind {n:?}"),
            }
            // Domain: Affine operands carry no field tag (implied by slot), but
            // the dst does — assert it matches the node's domain.
            match ins.dsts.as_slice() {
                [Dst::Slot { e4, .. }] => {
                    assert_eq!(*e4, node_domain(&arena[nid]) == Domain::Ext)
                }
                [Dst::Materialize { slot, .. }] => {
                    assert_eq!(
                        cf.matrix_table.field_is_ext(*slot),
                        node_domain(&arena[nid]) == Domain::Ext
                    );
                }
                _ => panic!("arith has exactly one footer dst"),
            }
        }
        assert!(cf.program.consts.len() <= 256, "const table within u8 index space");
    }
}
