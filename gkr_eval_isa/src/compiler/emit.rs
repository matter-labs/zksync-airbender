//! Arena-order instruction emission over the ProgramView DAG (forward pass).

use super::slots::SlotAlloc;
use super::view::{self, ProgramView};
use super::{CompileParams, CompileStats, CompiledLayer, OrderKind, SourceMap, build_const_table, enumerate_sources, is_computed, node_domain};
use crate::isa::{Dst, Instr, MAX_ARITY, Op, Operand, Program, encode};
use cs::gkr_compiler::codegen_ir::{CodegenLayer, Domain, ExprNode};
use gkr_design_space::graph::AnalysisGraph;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug)]
pub(crate) enum Placement {
    Slot { cell: u16, e4: bool },
    FixedReg { cell: u16, e4: bool },
}

struct EmitCtx<'a> {
    arena: &'a [ExprNode],
    /// node -> (source id per-domain, e4 flag)
    source_id: HashMap<usize, (u16, bool)>,
    /// raw u32 value -> index in const table
    const_id: HashMap<u32, u8>,
    placements: HashMap<usize, Placement>,
    remaining_uses: Vec<u32>,
    instrs: Vec<Instr>,
    stats: CompileStats,
    slot_alloc: SlotAlloc,
}

impl<'a> EmitCtx<'a> {
    fn operand_for(&self, node: usize) -> Operand {
        use crate::isa::NEG_ONE_U32;
        match &self.arena[node] {
            ExprNode::Constant(c) => match *c {
                0 => Operand::Zero,
                1 => Operand::One,
                v if v == NEG_ONE_U32 => Operand::NegOne,
                v => Operand::Const { idx: *self.const_id.get(&v).expect("constant not in table") },
            },
            ExprNode::Place { .. } | ExprNode::GateOutput { .. } => {
                let (id, e4) = *self.source_id.get(&node).expect("source not mapped");
                Operand::Source { id, e4 }
            }
            ExprNode::Sum { .. } | ExprNode::Product { .. } => {
                match *self.placements.get(&node).expect("computed node has no placement") {
                    Placement::Slot { cell, e4 } => Operand::Slot { cell, e4 },
                    Placement::FixedReg { cell, e4 } => {
                        Operand::FixedReg { cell, e4 }
                        // Note: fixed_reg_hits counted at emit time
                    }
                }
            }
        }
    }

    fn release_if_dead(&mut self, node: usize) {
        if self.remaining_uses[node] == 0 {
            return;
        }
        self.remaining_uses[node] -= 1;
        if self.remaining_uses[node] == 0 {
            if let Some(placement) = self.placements.remove(&node) {
                match placement {
                    Placement::Slot { cell, e4 } => {
                        let w = if e4 { 4 } else { 1 };
                        self.slot_alloc.release(cell, w);
                    }
                    Placement::FixedReg { .. } => {
                        // FixedReg cells are not freed (they persist for the program).
                    }
                }
            }
        }
    }

    fn place_result(&mut self, node: usize, e4: bool) -> Placement {
        let w = if e4 { 4 } else { 1 };
        let cell = self.slot_alloc.alloc(w)
            .expect("slot budget exhausted (Task 7 will add Belady eviction)");
        let p = Placement::Slot { cell, e4 };
        self.placements.insert(node, p);
        p
    }

    fn dst_from_placement(p: Placement) -> Dst {
        match p {
            Placement::Slot { cell, .. } => Dst::Slot(cell),
            Placement::FixedReg { cell, .. } => Dst::FixedReg(cell),
        }
    }

    /// Returns the per-instruction operand counts that `emit_with_split` would
    /// produce for a list of `total_operands` operands with the given `unit`.
    /// Used by tests to verify the split stays within MAX_ARITY.
    #[cfg(test)]
    pub(crate) fn split_chunks(total_operands: usize, unit: usize) -> Vec<usize> {
        let max_per_instr = MAX_ARITY * unit;
        if total_operands <= max_per_instr {
            return vec![total_operands];
        }
        let mut counts = vec![max_per_instr]; // first chunk
        let mut remaining = total_operands - max_per_instr;
        let cont_chunk_size = max_per_instr - unit;
        while remaining > 0 {
            let chunk = remaining.min(cont_chunk_size);
            // Continuation instruction: chunk payload + unit prepend
            counts.push(chunk + unit);
            remaining -= chunk;
        }
        counts
    }

    /// Emit one or more instructions for `op` with `operands` to `dst`.
    /// If operands exceed MAX_ARITY (or MAX_ARITY pairs for DotK), split into
    /// a chain. `unit` = 1 for SumK/ProdK, 2 for DotK (pairs).
    /// `e4_result` is the domain of the result.
    fn emit_with_split(
        &mut self,
        op: Op,
        e4_result: bool,
        dst: Dst,
        operands: Vec<Operand>,
    ) {
        let unit = if op == Op::DotK { 2 } else { 1 };
        let max_per_instr = MAX_ARITY * unit;

        if operands.len() <= max_per_instr {
            self.record_instr(op, e4_result, dst, operands);
        } else {
            // Must have a re-readable dst (Slot or FixedReg).
            debug_assert!(
                matches!(dst, Dst::Slot(_) | Dst::FixedReg(_)),
                "wide node must use slot dst"
            );
            // First chunk may fill MAX_ARITY fully.
            let first_chunk = operands[..max_per_instr].to_vec();
            let remainder = &operands[max_per_instr..];
            self.record_instr(op, e4_result, dst, first_chunk);

            // Subsequent chunks prepend dst as continuation operand (1 operand for
            // SumK/ProdK, 2 for DotK = exactly `unit`), so each continuation
            // instruction uses at most max_per_instr operands total.
            // Cap per-chunk at max_per_instr - unit to leave room for the prepend.
            let cont_chunk_size = max_per_instr - unit;
            let dst_operand = match dst {
                Dst::Slot(cell) => Operand::Slot { cell, e4: e4_result },
                Dst::FixedReg(cell) => Operand::FixedReg { cell, e4: e4_result },
                _ => unreachable!("wide node must have slot/fixed-reg dst"),
            };
            for chunk in remainder.chunks(cont_chunk_size) {
                let mut cont_ops = Vec::with_capacity(chunk.len() + unit);
                if op == Op::DotK {
                    // Continuation pair: (dst, One)
                    cont_ops.push(dst_operand);
                    cont_ops.push(Operand::One);
                } else {
                    cont_ops.push(dst_operand);
                }
                cont_ops.extend_from_slice(chunk);
                self.record_instr(op, e4_result, dst, cont_ops);
            }
        }
    }

    fn record_instr(&mut self, op: Op, e4_result: bool, dst: Dst, operands: Vec<Operand>) {
        let op_idx = op as usize;
        self.stats.op_hist[op_idx] += 1;
        for o in &operands {
            let kind_idx = match o {
                Operand::Source { .. } => 0,
                Operand::Slot { .. } => 1,
                Operand::FixedReg { .. } => {
                    self.stats.fixed_reg_hits += 1;
                    2
                }
                Operand::Const { .. } => 3,
                Operand::Zero => 4,
                Operand::One => 5,
                Operand::NegOne => 6,
            };
            self.stats.operand_kind_hist[kind_idx] += 1;
        }
        self.instrs.push(Instr { op, e4_result, dst, operands });
    }
}

pub(crate) fn emit_layer(
    layer: &CodegenLayer,
    g: &AnalysisGraph,
    params: CompileParams,
) -> CompiledLayer {
    let arena: &[ExprNode] = &layer.arena.nodes;
    let pv = view::build(layer, g);

    // Build source map and source_id lookup.
    let source_map = enumerate_sources(arena);
    let mut source_id: HashMap<usize, (u16, bool)> = HashMap::new();
    for (id, &node) in source_map.bf.iter().enumerate() {
        source_id.insert(node, (id as u16, false));
    }
    for (id, &node) in source_map.e4.iter().enumerate() {
        source_id.insert(node, (id as u16, true));
    }

    // Build constant table and const_id lookup.
    let consts = build_const_table(arena);
    let mut const_id: HashMap<u32, u8> = HashMap::new();
    for (i, &c) in consts.iter().enumerate() {
        const_id.insert(c, i as u8);
    }

    // Build gate_in_idx: node -> staging index.
    let mut gate_in_idx: HashMap<usize, u16> = HashMap::new();
    for (idx, &node) in pv.gate_in_roots.iter().enumerate() {
        gate_in_idx.insert(node, idx as u16);
    }

    // Build output_idx: node -> list of output j indices.
    let mut output_idx: HashMap<usize, Vec<u16>> = HashMap::new();
    for &(j, node) in &pv.program_outputs {
        output_idx.entry(node).or_default().push(j);
    }

    let slot_alloc = SlotAlloc::new(params.slot_budget_cells);

    let mut ctx = EmitCtx {
        arena,
        source_id,
        const_id,
        placements: HashMap::new(),
        remaining_uses: pv.uses.clone(),
        instrs: Vec::new(),
        stats: CompileStats::default(),
        slot_alloc,
    };

    // Determine emission order.
    let order: Vec<usize> = match params.order {
        OrderKind::Arena => (0..arena.len())
            .filter(|&n| is_computed(&arena[n]) && pv.uses[n] > 0)
            .collect(),
        OrderKind::Pressure => view::pressure_order(arena, &pv),
    };

    // Identify fused product nodes: product nodes that are children of a Sum node
    // where they will be fused into DotK.
    // A Sum node fuses into DotK if ≥ 2 of its children are 2-factor Product nodes with uses == 1.
    let mut fused: Vec<bool> = vec![false; arena.len()];

    // Pre-scan to find which product nodes will be fused.
    for &n in &order {
        if let ExprNode::Sum { terms, .. } = &arena[n] {
            let fuse_count = terms.iter().filter(|t| {
                let c = t.0 as usize;
                matches!(&arena[c], ExprNode::Product { factors, .. } if factors.len() == 2)
                    && pv.uses[c] == 1
            }).count();
            if fuse_count >= 2 {
                for t in terms {
                    let c = t.0 as usize;
                    if matches!(&arena[c], ExprNode::Product { factors, .. } if factors.len() == 2)
                        && pv.uses[c] == 1
                    {
                        fused[c] = true;
                    }
                }
            }
        }
    }

    // Main emission walk.
    for &n in &order {
        if fused[n] || pv.uses[n] == 0 {
            continue;
        }

        let e4_result = node_domain(&arena[n]) == Domain::Ext;

        let (op, operands, consumed): (Op, Vec<Operand>, Vec<usize>) = match &arena[n] {
            ExprNode::Sum { terms, .. } => {
                // Check if this sum should become DotK.
                let fuse_count = terms.iter().filter(|t| {
                    let c = t.0 as usize;
                    fused[c]
                }).count();

                if fuse_count >= 2 {
                    // DotK: build pairs.
                    let mut pairs: Vec<Operand> = Vec::new();
                    let mut consumed_nodes: Vec<usize> = Vec::new();

                    for t in terms {
                        let c = t.0 as usize;
                        if fused[c] {
                            // Fused product: emit pair (f0, f1).
                            let factors = match &arena[c] {
                                ExprNode::Product { factors, .. } => factors,
                                _ => unreachable!(),
                            };
                            let f0 = factors[0].0 as usize;
                            let f1 = factors[1].0 as usize;
                            pairs.push(ctx.operand_for(f0));
                            pairs.push(ctx.operand_for(f1));
                            // Consume the product node's factors and the product itself.
                            consumed_nodes.push(f0);
                            consumed_nodes.push(f1);
                            consumed_nodes.push(c); // the product node dies here
                        } else {
                            // Plain term: (term, One).
                            pairs.push(ctx.operand_for(c));
                            pairs.push(Operand::One);
                            consumed_nodes.push(c);
                        }
                    }
                    (Op::DotK, pairs, consumed_nodes)
                } else {
                    // SumK.
                    let mut ops = Vec::new();
                    let mut consumed_nodes = Vec::new();
                    for t in terms {
                        let c = t.0 as usize;
                        ops.push(ctx.operand_for(c));
                        consumed_nodes.push(c);
                    }
                    (Op::SumK, ops, consumed_nodes)
                }
            }
            ExprNode::Product { factors, .. } => {
                let mut ops = Vec::new();
                let mut consumed_nodes = Vec::new();
                for f in factors {
                    let c = f.0 as usize;
                    ops.push(ctx.operand_for(c));
                    consumed_nodes.push(c);
                }
                (Op::ProdK, ops, consumed_nodes)
            }
            _ => continue,
        };

        // Determine if we need to split (wide node).
        let unit = if op == Op::DotK { 2 } else { 1 };
        let needs_split = operands.len() > MAX_ARITY * unit;

        let gi = gate_in_idx.get(&n).copied();
        let outs = output_idx.get(&n).cloned().unwrap_or_default();
        let total_uses = pv.uses[n];
        let root_uses = gi.is_some() as u32 + outs.len() as u32;

        if total_uses == 1 && root_uses == 1 && !needs_split {
            // Emit directly to the root destination (no slot needed).
            let dst = if let Some(idx) = gi {
                Dst::GateIn(idx)
            } else {
                Dst::Output(outs[0])
            };
            ctx.emit_with_split(op, e4_result, dst, operands);
            // Release consumed operands.
            for c in consumed {
                ctx.release_if_dead(c);
            }
            // No placement for n; it was written directly.
        } else {
            // Need a slot placement (or FixedReg, but FixedReg allocation is Task 6).
            let placement = ctx.place_result(n, e4_result);
            let dst = EmitCtx::dst_from_placement(placement);
            ctx.emit_with_split(op, e4_result, dst, operands);
            // Release consumed operands.
            for c in consumed {
                ctx.release_if_dead(c);
            }
            // Emit copies to each root destination.
            if let Some(idx) = gi {
                let src_op = ctx.operand_for(n);
                ctx.release_if_dead(n);
                ctx.record_instr(
                    Op::SumK,
                    e4_result,
                    Dst::GateIn(idx),
                    vec![src_op],
                );
            }
            for j in outs {
                let src_op = ctx.operand_for(n);
                ctx.release_if_dead(n);
                ctx.record_instr(
                    Op::SumK,
                    e4_result,
                    Dst::Output(j),
                    vec![src_op],
                );
            }
        }
    }

    // Trailing: program outputs where the node is a leaf or constant.
    for &(j, node) in &pv.program_outputs {
        if !is_computed(&arena[node]) {
            let e4_result = node_domain(&arena[node]) == Domain::Ext;
            let op = ctx.operand_for(node);
            ctx.record_instr(
                Op::SumK,
                e4_result,
                Dst::Output(j),
                vec![op],
            );
        }
    }

    // Finalize stats.
    let max_live_cells = ctx.slot_alloc.high_water_cells;
    ctx.stats.instrs = ctx.instrs.len();
    ctx.stats.max_live_cells = max_live_cells;
    ctx.stats.gate_in_roots = pv.gate_in_roots.len();

    // Build program.
    let n_consts = consts.len();
    let program = Program {
        instrs: ctx.instrs,
        consts,
        n_slot_cells: max_live_cells as u16,
        n_fixed_cells: params.fixed_reg_cells as u16,
        n_sources_bf: source_map.bf.len() as u16,
        n_sources_e4: source_map.e4.len() as u16,
        n_outputs: g.outputs.len() as u16,
        n_gate_ins: pv.gate_in_roots.len() as u16,
    };

    // Run encode to trigger asserts.
    let lanes = encode(&program);
    ctx.stats.lanes = lanes.len();
    ctx.stats.bytes = lanes.len() * 2 + n_consts * 4 + 16;

    CompiledLayer {
        program,
        source_map,
        gate_in_roots: pv.gate_in_roots.clone(),
        stats: ctx.stats,
    }
}

#[cfg(test)]
mod tests {
    use super::EmitCtx;
    use crate::compiler::{CompileParams, compile_layer};
    use crate::eval_ref::tests::fixture;
    use crate::isa::{Dst, MAX_ARITY};
    use gkr_design_space::import::load_circuit;

    /// Regression test: continuation chunks must not exceed MAX_ARITY after
    /// prepending the accumulator operand.
    #[test]
    fn split_chunks_stay_within_max_arity() {
        // SumK/ProdK: unit = 1.  70 operands -> first=31, cont=1+30=31. All ≤ 31.
        let counts = EmitCtx::split_chunks(70, 1);
        for &c in &counts {
            assert!(
                c <= MAX_ARITY,
                "SumK chunk size {c} exceeds MAX_ARITY={MAX_ARITY} (counts={counts:?})"
            );
        }
        // Sum of counts must equal total (first chunk) + continuation payloads + prepends.
        // Simpler: the first count is the first chunk payload; continuations include
        // the prepend. Total payload = first + sum(cont - unit).
        let payload: usize = counts[0] + counts[1..].iter().map(|&c| c - 1).sum::<usize>();
        assert_eq!(payload, 70, "SumK: payload mismatch {payload}");

        // DotK: unit = 2.  70 pairs (140 operands) -> first=62, cont=2+60=62. All ≤ 62 = 31*2.
        let counts = EmitCtx::split_chunks(140, 2);
        for &c in &counts {
            assert!(
                c <= MAX_ARITY * 2,
                "DotK chunk size {c} exceeds MAX_ARITY*2={} (counts={counts:?})",
                MAX_ARITY * 2
            );
        }
        let payload: usize = counts[0] + counts[1..].iter().map(|&c| c - 2).sum::<usize>();
        assert_eq!(payload, 140, "DotK: payload mismatch {payload}");

        // Edge: exactly MAX_ARITY operands -> single instruction, no split.
        let counts = EmitCtx::split_chunks(MAX_ARITY, 1);
        assert_eq!(counts, vec![MAX_ARITY]);

        // Edge: MAX_ARITY + 1 -> two instructions; continuation has 1 payload + 1 prepend = 2.
        let counts = EmitCtx::split_chunks(MAX_ARITY + 1, 1);
        assert_eq!(counts.len(), 2);
        assert!(counts.iter().all(|&c| c <= MAX_ARITY));
    }

    #[test]
    fn emits_add_sub_l0() {
        let c = load_circuit(&fixture("add_sub_lui_auipc_mop_codegen_ir_gkr.json")).unwrap();
        let cl = compile_layer(&c.circuit.layers[0], &c.graphs[0], CompileParams::default());
        assert!(cl.stats.instrs > 0);
        // Every gate-in staging index is written exactly once.
        let mut gate_in_writes = vec![0u32; cl.program.n_gate_ins as usize];
        for i in &cl.program.instrs {
            if let Dst::GateIn(idx) = i.dst {
                gate_in_writes[idx as usize] += 1;
            }
        }
        assert!(gate_in_writes.iter().all(|&w| w == 1), "{gate_in_writes:?}");
        // Encoding roundtrip on a real program.
        let lanes = crate::isa::encode(&cl.program);
        assert_eq!(crate::isa::decode(&lanes, cl.program.instrs.len()), cl.program.instrs);
        // DotK fusion fires on a real circuit.
        assert!(cl.stats.op_hist[2] > 0, "expected DotK instructions");

        // Report stats for the controller.
        eprintln!(
            "[task5] instrs={} lanes={} bytes={} op_hist={:?} max_live_cells={}",
            cl.stats.instrs,
            cl.stats.lanes,
            cl.stats.bytes,
            cl.stats.op_hist,
            cl.stats.max_live_cells,
        );
    }
}
