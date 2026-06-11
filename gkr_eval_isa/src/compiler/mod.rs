//! IR -> ISA program compiler (forward pass). Pipeline over the ProgramView
//! DAG (GateOutput = staged leaf; gate-input cones = roots).

mod emit;
mod fixed_regs;
mod slots;
pub mod view;

use crate::isa::{NEG_ONE_U32, Program};
use cs::gkr_compiler::codegen_ir::{CodegenLayer, Domain, ExprNode};
use gkr_design_space::graph::AnalysisGraph;
use serde::Serialize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum OrderKind {
    /// Arena index order (topological by IR invariant). Default HYPOTHESIS —
    /// validated against Pressure by the report.
    Arena,
    /// Greedy pressure-aware order over ProgramView (view::pressure_order).
    Pressure,
}

#[derive(Clone, Copy, Debug)]
pub struct CompileParams {
    /// bf cells available in the slot file (e4 = 4 cells).
    pub slot_budget_cells: usize,
    /// bf cells in the decode-selected fixed-register file (0 = disabled).
    pub fixed_reg_cells: usize,
    pub order: OrderKind,
}

impl Default for CompileParams {
    fn default() -> Self {
        // Validation default: effectively unbounded slots, no fixed regs.
        CompileParams {
            slot_budget_cells: 4096,
            fixed_reg_cells: 0,
            order: OrderKind::Arena,
        }
    }
}

/// id -> arena node, one namespace per domain.
#[derive(Debug, Default, Serialize)]
pub struct SourceMap {
    pub bf: Vec<usize>,
    pub e4: Vec<usize>,
}

#[derive(Debug, Default, Serialize)]
pub struct CompileStats {
    pub instrs: usize,
    pub lanes: usize,
    pub bytes: usize,
    /// [SumK, ProdK, DotK]
    pub op_hist: [usize; 3],
    /// Indexed by operand-kind code 0..7.
    pub operand_kind_hist: [usize; 7],
    pub gate_in_roots: usize,
    pub max_live_cells: usize,
    pub spill_evictions: usize,
    pub remat_instrs: usize,
    /// Operand references served by the fixed-register file.
    pub fixed_reg_hits: usize,
}

pub struct CompiledLayer {
    pub program: Program,
    pub source_map: SourceMap,
    /// staging idx -> arena node (for the oracle to check gate-in values).
    pub gate_in_roots: Vec<usize>,
    pub stats: CompileStats,
}

/// A leaf is anything the program cannot compute: Place or GateOutput.
pub(crate) fn is_leaf(n: &ExprNode) -> bool {
    matches!(n, ExprNode::Place { .. } | ExprNode::GateOutput { .. })
}

/// Computed nodes are what the program emits instructions for.
pub(crate) fn is_computed(n: &ExprNode) -> bool {
    matches!(n, ExprNode::Sum { .. } | ExprNode::Product { .. })
}

pub(crate) fn node_domain(n: &ExprNode) -> Domain {
    match n {
        ExprNode::Constant(_) => Domain::Base,
        ExprNode::Place { domain, .. }
        | ExprNode::GateOutput { domain, .. }
        | ExprNode::Sum { domain, .. }
        | ExprNode::Product { domain, .. } => *domain,
    }
}

/// Enumerate staged sources in arena order (deterministic), per domain.
pub(crate) fn enumerate_sources(arena: &[ExprNode]) -> SourceMap {
    let mut m = SourceMap::default();
    for (i, n) in arena.iter().enumerate() {
        if is_leaf(n) {
            match node_domain(n) {
                Domain::Base => m.bf.push(i),
                Domain::Ext => m.e4.push(i),
            }
        }
    }
    m
}

/// Deduplicated constant table; 0/1/-1 are special operand kinds, not entries.
pub(crate) fn build_const_table(arena: &[ExprNode]) -> Vec<u32> {
    let mut consts: Vec<u32> = arena
        .iter()
        .filter_map(|n| match n {
            ExprNode::Constant(c) if *c != 0 && *c != 1 && *c != NEG_ONE_U32 => Some(*c),
            _ => None,
        })
        .collect();
    consts.sort_unstable();
    consts.dedup();
    assert!(consts.len() <= 256, "constant table exceeds u8 index space");
    consts
}

pub fn compile_layer(
    layer: &CodegenLayer,
    g: &AnalysisGraph,
    params: CompileParams,
) -> CompiledLayer {
    emit::emit_layer(layer, g, params)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval_ref::tests::fixture;
    use gkr_design_space::import::load_circuit;

    #[test]
    fn add_sub_l0_view_sources_consts() {
        let c = load_circuit(&fixture("add_sub_lui_auipc_mop_codegen_ir_gkr.json")).unwrap();
        let layer = &c.circuit.layers[0];
        let arena = &layer.arena.nodes;

        let m = enumerate_sources(arena);
        assert!(!m.bf.is_empty());

        let consts = build_const_table(arena);
        assert!(consts.len() <= 9); // measured circuit-wide arena count is 9
        for cv in &consts {
            assert!(*cv != 0 && *cv != 1 && *cv != NEG_ONE_U32);
        }

        let pv = view::build(layer, &c.graphs[0]);

        // Report counts for the controller.
        eprintln!(
            "[task4] gate_in_roots={} program_outputs={}",
            pv.gate_in_roots.len(),
            pv.program_outputs.len()
        );

        // 45 gates + 16 caches must surface at least one computed input root.
        assert!(!pv.gate_in_roots.is_empty());
        // Every root has at least its root use.
        for &r in &pv.gate_in_roots {
            assert!(pv.uses[r] >= 1);
        }
        // GateOutput-node output slots must be excluded from program outputs.
        for &(_, n) in &pv.program_outputs {
            assert!(!matches!(
                arena[n],
                cs::gkr_compiler::codegen_ir::ExprNode::GateOutput { .. }
            ));
        }
        // pressure_order emits exactly the live computed nodes, topologically.
        let po = view::pressure_order(arena, &pv);
        let expected: usize = arena
            .iter()
            .enumerate()
            .filter(|(i, n)| is_computed(n) && pv.uses[*i] > 0)
            .count();
        assert_eq!(po.len(), expected);
        let mut pos = vec![usize::MAX; arena.len()];
        for (k, &i) in po.iter().enumerate() {
            pos[i] = k;
        }
        for &i in &po {
            match &arena[i] {
                ExprNode::Sum { terms, .. } => {
                    for t in terms {
                        let c = t.0 as usize;
                        if is_computed(&arena[c]) {
                            assert!(pos[c] < pos[i]);
                        }
                    }
                }
                ExprNode::Product { factors, .. } => {
                    for f in factors {
                        let c = f.0 as usize;
                        if is_computed(&arena[c]) {
                            assert!(pos[c] < pos[i]);
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
    }
}
