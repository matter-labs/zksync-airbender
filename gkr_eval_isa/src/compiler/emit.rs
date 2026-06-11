//! Arena-order instruction emission over the ProgramView DAG (forward pass).

use super::slots::SlotAlloc;
use super::view::{self, ProgramView};
use super::{CompileParams, CompileStats, CompiledLayer, OrderKind, SourceMap, build_const_table, enumerate_sources, is_computed, node_domain};
use crate::isa::{Dst, Instr, MAX_ARITY, Op, Operand, Program, encode};
use cs::gkr_compiler::codegen_ir::{CodegenLayer, Domain, ExprNode};
use gkr_design_space::graph::AnalysisGraph;
use std::collections::HashMap;

/// A live placement eviction candidate, used by Belady victim selection.
struct LiveReg {
    node: usize,
    cell: u16,
    width: usize,
}

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
    /// Current walk position (index into the emission order vec).
    /// Updated once per main-walk iteration. Used by Belady eviction.
    pos: usize,
    /// For each arena node: sorted ascending list of order-positions where it
    /// is consumed as an arithmetic operand (Sum/Product consumer edges and
    /// DotK-fused factor edges). Root uses (gate_in, output copies) are NOT
    /// included because those are satisfied immediately at the producer's own
    /// position, so the value never stays live waiting for them.
    use_positions: Vec<Vec<usize>>,
}

impl<'a> EmitCtx<'a> {
    /// Return the next use position of `node` at or after walk position `after`.
    /// Returns `usize::MAX` if there is no future use (should never be called on
    /// such a node — the caller's debug_assert guards this).
    fn next_use(&self, node: usize, after: usize) -> usize {
        let uses = &self.use_positions[node];
        // Binary search for first position > after (strictly after, since `after`
        // is the current position where we're about to produce, not consume).
        match uses.binary_search(&after) {
            Ok(i) => {
                // Exact match: there's a use AT `after`. Walk forward to find the
                // first entry strictly greater (the real "next" future use from
                // the current position's perspective during eviction is any use
                // that hasn't happened yet, including the current one).
                uses.get(i).copied().unwrap_or(usize::MAX)
            }
            Err(i) => uses.get(i).copied().unwrap_or(usize::MAX),
        }
    }

    /// Build the victim list from all current Slot placements, excluding any
    /// node whose cells overlap `protect_cells`.
    fn build_victims(&self, protect: &[usize]) -> Vec<LiveReg> {
        self.placements
            .iter()
            .filter_map(|(&n, &p)| {
                if protect.contains(&n) {
                    return None;
                }
                match p {
                    Placement::Slot { cell, e4 } => Some(LiveReg {
                        node: n,
                        cell,
                        width: if e4 { 4 } else { 1 },
                    }),
                    Placement::FixedReg { .. } => None, // FixedReg never evicted
                }
            })
            .collect()
    }

    /// Allocate `width` cells for `node`, evicting Belady-optimal victims as
    /// needed.  `protect` lists node ids that must not be evicted (they are
    /// operands that will be read immediately after this allocation).
    fn alloc_with_eviction(&mut self, node: usize, width: usize, protect: &[usize]) -> u16 {
        loop {
            if let Some(cell) = self.slot_alloc.alloc(width) {
                return cell;
            }
            // Evict the victim with the furthest next use (Belady optimal).
            // We must not hold a borrow on self when calling slot_alloc.release,
            // so we find the victim node first (immutable phase), then mutate.
            let pos = self.pos;
            let victims = self.build_victims(protect);
            // Pick the victim with the furthest next use, tie-break by width.
            let budget = self.slot_alloc.budget();
            let protected = protect.len();
            let victim = victims
                .iter()
                .max_by_key(|r| (self.next_use(r.node, pos), r.width))
                .unwrap_or_else(|| panic!(
                    "slot budget infeasible for instruction footprint: \
                     need {width} more cells, budget {budget}, \
                     {protected} cells protected by the current instruction"
                ));
            let evicted_node = victim.node;
            let evicted_cell = victim.cell;
            let evicted_width = victim.width;
            // Safety: evicted node must have a future use — otherwise it would
            // have been dead and released by release_if_dead. If remaining_uses > 0
            // then use_positions must be non-empty (they were populated from the
            // same consumer edges).
            // Safe ONLY because root-use copies are emitted in the producer's own
            // iteration: a root-use-only placement never survives into an eviction
            // window. If root copies are ever deferred, this assert will fire spuriously.
            debug_assert!(
                self.next_use(evicted_node, pos) != usize::MAX || self.remaining_uses[evicted_node] == 0,
                "evicted node {evicted_node} has remaining_uses={} but no future use position \
                 (use_positions={:?})",
                self.remaining_uses[evicted_node],
                self.use_positions[evicted_node],
            );
            self.slot_alloc.release(evicted_cell, evicted_width);
            self.placements.remove(&evicted_node);
            self.stats.spill_evictions += 1;
        }
    }

    /// Rematerialize `node` (which has been evicted) by re-emitting its
    /// computation. `depth` is a recursion guard (DAG depth is shallow, ~10).
    /// Returns the new Placement.
    ///
    /// IMPORTANT: remat-emitted instructions do NOT decrement remaining_uses
    /// of their operands. The original refcounts already account for the original
    /// edges; remat is extra reads beyond those. Calling release_if_dead here
    /// would over-decrement and prematurely free live values.
    ///
    /// A remat'd child that has a placement will be read directly. A remat'd
    /// child WITHOUT a placement is itself rematerialized recursively. Leaf
    /// children (Place, GateOutput, Constant) are direct operands — they never
    /// have placements.
    ///
    /// Safety of the "victim has a future use" debug_assert during remat:
    /// when remat reads a child that has a placement, that child must have
    /// remaining_uses > 0 (otherwise release_if_dead would have already freed
    /// it and removed its placement). If remaining_uses > 0, then use_positions
    /// is non-empty for that child, so next_use returns a valid position and the
    /// assert holds.
    fn remat(&mut self, node: usize, depth: usize, protect: &[usize]) -> Placement {
        debug_assert!(depth < 32, "remat recursion depth {depth} too deep (cycle?)");

        let e4 = node_domain(&self.arena[node]) == Domain::Ext;
        let w = if e4 { 4 } else { 1 };

        // Determine the op and child nodes — must NOT borrow self.arena beyond
        // this block (we need &mut self for alloc/remat below).
        let (op, children): (Op, Vec<usize>) = match &self.arena[node] {
            ExprNode::Sum { terms, .. } => {
                (Op::SumK, terms.iter().map(|t| t.0 as usize).collect())
            }
            ExprNode::Product { factors, .. } => {
                (Op::ProdK, factors.iter().map(|f| f.0 as usize).collect())
            }
            _ => panic!("remat called on non-computed node {node}"),
        };

        // Gather child operands. For each child:
        //   - leaf/constant: direct operand (no placement)
        //   - computed with placement: use placement directly
        //   - computed without placement: recurse into remat
        // Build a protect list for the dst allocation: all children whose slots
        // we need readable must not be evicted when we allocate the dst.
        // We collect child nodes that have slot placements first, then allocate dst.
        let mut child_operands: Vec<Operand> = Vec::with_capacity(children.len());
        let mut protect_for_dst: Vec<usize> = protect.to_vec();

        for &c in &children {
            let is_computed_child = is_computed(&self.arena[c]);
            if is_computed_child {
                if self.placements.contains_key(&c) {
                    protect_for_dst.push(c);
                } else {
                    // Recurse: remat the child first, then protect its new placement.
                    // No borrow on self.arena during this call.
                    self.remat(c, depth + 1, &protect_for_dst);
                    protect_for_dst.push(c);
                }
            }
            // leaf / constant: no slot to protect
        }

        // Now resolve operands (all computed children should have placements by now).
        for &c in &children {
            child_operands.push(self.operand_for_no_remat(c));
        }

        // Allocate dst, protecting all child slots.
        let cell = self.alloc_with_eviction(node, w, &protect_for_dst);
        let p = Placement::Slot { cell, e4 };
        self.placements.insert(node, p);

        // Emit the instruction (plain SumK/ProdK — never re-fuse DotK in remat).
        let dst = Dst::Slot(cell);
        self.emit_with_split(op, e4, dst, child_operands);
        self.stats.remat_instrs += 1;

        p
    }

    /// Like `operand_for` but panics if a computed node is missing its placement
    /// instead of rematerializing. Used inside `remat` after ensuring all children
    /// have been placed.
    fn operand_for_no_remat(&self, node: usize) -> Operand {
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
                match *self.placements.get(&node).expect("computed node has no placement (operand_for_no_remat)") {
                    Placement::Slot { cell, e4 } => Operand::Slot { cell, e4 },
                    Placement::FixedReg { cell, e4 } => Operand::FixedReg { cell, e4 },
                }
            }
        }
    }

    fn operand_for(&mut self, node: usize) -> Operand {
        use crate::isa::NEG_ONE_U32;
        // Classify the node kind without keeping a borrow on self.arena, so that
        // we can call self.remat() (which needs &mut self) in the computed branch.
        enum Kind { Zero, One, NegOne, Const(u8), Source { id: u16, e4: bool }, Computed }
        let kind = match &self.arena[node] {
            ExprNode::Constant(c) => match *c {
                0 => Kind::Zero,
                1 => Kind::One,
                v if v == NEG_ONE_U32 => Kind::NegOne,
                v => Kind::Const(*self.const_id.get(&v).expect("constant not in table")),
            },
            ExprNode::Place { .. } | ExprNode::GateOutput { .. } => {
                let (id, e4) = *self.source_id.get(&node).expect("source not mapped");
                Kind::Source { id, e4 }
            }
            ExprNode::Sum { .. } | ExprNode::Product { .. } => Kind::Computed,
        };
        match kind {
            Kind::Zero => Operand::Zero,
            Kind::One => Operand::One,
            Kind::NegOne => Operand::NegOne,
            Kind::Const(idx) => Operand::Const { idx },
            Kind::Source { id, e4 } => Operand::Source { id, e4 },
            Kind::Computed => {
                // If the placement was evicted, rematerialize it now.
                // Empty protect is sound today: build_operands pre-remats operands
                // before operand_for sees them, and root copies trigger no interleaved
                // allocation. Pass real protect if that changes.
                if !self.placements.contains_key(&node) {
                    self.remat(node, 0, &[]);
                }
                match *self.placements.get(&node).expect("computed node has no placement after remat") {
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

    /// Allocate a slot for `node` with Belady eviction if the budget is full.
    /// `protect` = node ids whose slots must not be evicted (they are operands
    /// that have already been resolved and must remain readable until the
    /// instruction is pushed).
    fn place_result(&mut self, node: usize, e4: bool, protect: &[usize]) -> Placement {
        let w = if e4 { 4 } else { 1 };
        let cell = self.alloc_with_eviction(node, w, protect);
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

/// Given a resolved operand list, collect the node ids of Slot-placed nodes
/// (those whose cell addresses are encoded in the operand list and must remain
/// valid until the instruction executes). These are determined by cross-referencing
/// Slot operands with the placements map.
fn collect_protect_from_operands(
    operands: &[Operand],
    placements: &HashMap<usize, Placement>,
) -> Vec<usize> {
    // Build a cell->node reverse map from current Slot placements, then look up
    // each Slot operand's cell to find which node owns it.
    let mut cell_to_node: HashMap<u16, usize> = HashMap::new();
    for (&n, &p) in placements {
        if let Placement::Slot { cell, .. } = p {
            cell_to_node.insert(cell, n);
        }
    }
    let mut protect = Vec::new();
    for op in operands {
        if let Operand::Slot { cell, .. } = op {
            if let Some(&n) = cell_to_node.get(cell) {
                if !protect.contains(&n) {
                    protect.push(n);
                }
            }
        }
    }
    protect
}

/// Build the operand list for node `n` with the given `op`, using the current
/// ctx state (which may trigger rematerialization for evicted nodes).
/// This mirrors the operand structure used in use_positions computation — the
/// two must stay in sync.
///
/// `initial_protect` lists node ids whose slots must not be evicted during
/// operand resolution (e.g., the just-allocated dst slot for `n`, or other
/// previously-resolved operands from the same instruction).
///
/// As each computed operand is resolved, its node is added to the running
/// protect list so that subsequent remat operations cannot evict it.
fn build_operands(
    ctx: &mut EmitCtx<'_>,
    n: usize,
    op: Op,
    fused: &[bool],
    arena: &[ExprNode],
    initial_protect: &[usize],
) -> Vec<Operand> {
    // Collect the node ids to resolve, in operand order.
    // For DotK: interleaved (f0, f1) pairs or (c, sentinel) for plain terms.
    // Sentinels are represented as usize::MAX (One).
    let node_seq: Vec<Option<usize>> = match op {
        Op::DotK => {
            let terms = match &arena[n] {
                ExprNode::Sum { terms, .. } => terms.clone(),
                _ => unreachable!("DotK must come from Sum"),
            };
            let mut seq = Vec::new();
            for t in &terms {
                let c = t.0 as usize;
                if fused[c] {
                    let factors = match &arena[c] {
                        ExprNode::Product { factors, .. } => factors.clone(),
                        _ => unreachable!(),
                    };
                    seq.push(Some(factors[0].0 as usize));
                    seq.push(Some(factors[1].0 as usize));
                } else {
                    seq.push(Some(c));
                    seq.push(None); // will become Operand::One
                }
            }
            seq
        }
        Op::SumK => {
            let terms = match &arena[n] {
                ExprNode::Sum { terms, .. } => terms.clone(),
                _ => unreachable!("SumK must come from Sum"),
            };
            terms.iter().map(|t| Some(t.0 as usize)).collect()
        }
        Op::ProdK => {
            let factors = match &arena[n] {
                ExprNode::Product { factors, .. } => factors.clone(),
                _ => unreachable!("ProdK must come from Product"),
            };
            factors.iter().map(|f| Some(f.0 as usize)).collect()
        }
    };

    // Resolve operands sequentially, growing the protect list so that
    // rematerialization of one operand cannot evict another.
    let mut protect: Vec<usize> = initial_protect.to_vec();
    let mut operands = Vec::with_capacity(node_seq.len());

    for node_opt in node_seq {
        match node_opt {
            None => operands.push(Operand::One),
            Some(c) => {
                // Ensure the node has a placement (remat if needed), protecting
                // everything we've already resolved.
                if is_computed(&arena[c]) && !ctx.placements.contains_key(&c) {
                    ctx.remat(c, 0, &protect);
                }
                let op = ctx.operand_for(c);
                // Track computed nodes with slots in the protect list.
                if is_computed(&arena[c]) {
                    if !protect.contains(&c) {
                        protect.push(c);
                    }
                }
                operands.push(op);
            }
        }
    }

    operands
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

    // Build use_positions: for each arena node, the sorted list of order-positions
    // at which it is consumed as an arithmetic operand.
    //
    // Walk order with its index p. For each non-skipped node at order[p], determine
    // the EXACT operand list the emitter will use (mirroring the main walk below,
    // including fusion expansion: fused products' factors contribute their use at
    // the consuming Sum's position p; the fused product node itself is also
    // consumed at position p).
    //
    // Root uses (gate_in / output copies) are NOT included: the emitter satisfies
    // them immediately at the producer's own position via release_if_dead, so the
    // value never stays live waiting for a separate root-use position.
    let mut use_positions: Vec<Vec<usize>> = vec![Vec::new(); arena.len()];

    for (p, &n) in order.iter().enumerate() {
        if fused[n] || pv.uses[n] == 0 {
            continue;
        }
        // Collect the arithmetic consumers for this node at position p.
        let consumed: Vec<usize> = match &arena[n] {
            ExprNode::Sum { terms, .. } => {
                let fuse_count = terms.iter().filter(|t| fused[t.0 as usize]).count();
                if fuse_count >= 2 {
                    // DotK path: fused products expand to factors + the product node.
                    let mut v = Vec::new();
                    for t in terms {
                        let c = t.0 as usize;
                        if fused[c] {
                            if let ExprNode::Product { factors, .. } = &arena[c] {
                                v.push(factors[0].0 as usize);
                                v.push(factors[1].0 as usize);
                            }
                            v.push(c); // the fused product node itself is consumed here
                        } else {
                            v.push(c);
                        }
                    }
                    v
                } else {
                    // SumK path: all terms.
                    terms.iter().map(|t| t.0 as usize).collect()
                }
            }
            ExprNode::Product { factors, .. } => {
                factors.iter().map(|f| f.0 as usize).collect()
            }
            _ => continue,
        };
        for c in consumed {
            if is_computed(&arena[c]) {
                use_positions[c].push(p);
            }
        }
    }
    // use_positions[n] is already sorted ascending because we iterate p in order.

    let mut ctx = EmitCtx {
        arena,
        source_id,
        const_id,
        placements: HashMap::new(),
        remaining_uses: pv.uses.clone(),
        instrs: Vec::new(),
        stats: CompileStats::default(),
        slot_alloc,
        pos: 0,
        use_positions,
    };

    // Main emission walk.
    for (walk_idx, &n) in order.iter().enumerate() {
        if fused[n] || pv.uses[n] == 0 {
            continue;
        }

        // Update the current walk position for Belady eviction decisions.
        ctx.pos = walk_idx;

        let e4_result = node_domain(&arena[n]) == Domain::Ext;

        // Step 1: Determine which nodes are consumed and which op is used.
        // We need the consumed-node list BEFORE resolving operands so we can
        // pass it as `protect` to place_result (preventing Belady from evicting
        // a node whose slot we're about to read).
        let (op, consumed): (Op, Vec<usize>) = match &arena[n] {
            ExprNode::Sum { terms, .. } => {
                let fuse_count = terms.iter().filter(|t| fused[t.0 as usize]).count();
                if fuse_count >= 2 {
                    // DotK: expand fused products.
                    let mut consumed_nodes: Vec<usize> = Vec::new();
                    for t in terms {
                        let c = t.0 as usize;
                        if fused[c] {
                            if let ExprNode::Product { factors, .. } = &arena[c] {
                                consumed_nodes.push(factors[0].0 as usize);
                                consumed_nodes.push(factors[1].0 as usize);
                            }
                            consumed_nodes.push(c);
                        } else {
                            consumed_nodes.push(c);
                        }
                    }
                    (Op::DotK, consumed_nodes)
                } else {
                    (Op::SumK, terms.iter().map(|t| t.0 as usize).collect())
                }
            }
            ExprNode::Product { factors, .. } => {
                (Op::ProdK, factors.iter().map(|f| f.0 as usize).collect())
            }
            _ => continue,
        };

        // Determine if we need to split (need to know operand count first).
        // For DotK the operand count = consumed.len() (pairs, but we count
        // elements not pairs here since unit handles it below).
        let unit = if op == Op::DotK { 2 } else { 1 };
        // For DotK consumed list: fused child contributes 2 (factors) + 1 (product node) = 3 entries,
        // but only 2 operands in the pairs (the product node entry is for refcount purposes).
        // We need the actual operand count for the split check.
        // Compute it directly from op structure.
        let operand_count = match &arena[n] {
            ExprNode::Sum { terms, .. } => {
                let fuse_count = terms.iter().filter(|t| fused[t.0 as usize]).count();
                if fuse_count >= 2 {
                    terms.len() * 2 // each term (fused or plain) produces exactly 2 operand slots
                } else {
                    terms.len()
                }
            }
            ExprNode::Product { factors, .. } => factors.len(),
            _ => 0,
        };
        let needs_split = operand_count > MAX_ARITY * unit;

        let gi = gate_in_idx.get(&n).copied();
        let outs = output_idx.get(&n).cloned().unwrap_or_default();
        let total_uses = pv.uses[n];
        let root_uses = gi.is_some() as u32 + outs.len() as u32;

        if total_uses == 1 && root_uses == 1 && !needs_split {
            // Emit directly to the root destination (no slot needed).
            // No place_result needed, so no eviction risk here.
            let dst = if let Some(idx) = gi {
                Dst::GateIn(idx)
            } else {
                Dst::Output(outs[0])
            };
            // Resolve operands (may trigger remat for evicted nodes).
            // No dst slot to protect; initial_protect is empty.
            let operands = build_operands(&mut ctx, n, op, &fused, arena, &[]);
            ctx.emit_with_split(op, e4_result, dst, operands);
            // Release consumed operands.
            for c in consumed {
                ctx.release_if_dead(c);
            }
            // No placement for n; it was written directly.
        } else {
            // Need a slot placement.
            // Step A: Resolve all operands FIRST (with growing protect list).
            //   This ensures each computed operand has a valid placement, and we
            //   accumulate the set of node ids whose cells are encoded in the
            //   operand list.
            // Step B: Allocate dst slot, protecting the encoded operand cells so
            //   eviction cannot steal a cell that an operand is pointing to.
            // Step C: Push instruction.
            //
            // This order (operands then dst) avoids the deadlock of allocating dst
            // first and then having to protect it PLUS all operands simultaneously.
            let operands = build_operands(&mut ctx, n, op, &fused, arena, &[]);
            // Collect which computed nodes were encoded as slot operands.
            let protect_for_dst = collect_protect_from_operands(&operands, &ctx.placements);
            let placement = ctx.place_result(n, e4_result, &protect_for_dst);
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
