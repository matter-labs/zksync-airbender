//! Arena-order instruction emission over the ProgramView DAG (forward pass).

use super::pinning;
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
    /// A cell in the pinned prefix: written once (leaf preload or first
    /// computation), never evicted, never released.
    PinnedSlot { cell: u16, e4: bool },
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
    /// Pinned prefix assignment: node -> absolute cell address. Leaves are
    /// preloaded into their cell; computed nodes write it at emission and
    /// stay resident for the whole program.
    pinned: HashMap<usize, u16>,
    /// Reads + writes per cell address (e4 touches 4 cells) — the data for
    /// the later per-address smem-vs-register placement.
    cell_accesses: Vec<u32>,
}

/// One logical operand group of an instruction: `unit` operand lanes that must
/// stay in the same chunk (a DotK pair, or a single SumK/ProdK operand), plus
/// the refcount decrements owed once the chunk containing it has been emitted.
struct OperandGroup {
    /// `None` lanes become `Operand::One` (DotK plain-term filler).
    nodes: Vec<Option<usize>>,
    release: Vec<usize>,
}

/// Transient slot headroom kept free per chunk so rematerialization of an
/// evicted operand has somewhere to land (one e4 value). Heuristic — the
/// infeasible-budget panic in alloc_with_eviction remains the backstop.
const REMAT_SLACK: usize = 4;

impl<'a> EmitCtx<'a> {
    /// Return the next use position of `node` at or after walk position `after`.
    /// Returns `usize::MAX` if there is no future use (should never be called on
    /// such a node — the caller's debug_assert guards this).
    fn next_use(&self, node: usize, after: usize) -> usize {
        let uses = &self.use_positions[node];
        // First use at or after the current position (a use AT `after` is one
        // that has not been satisfied yet during this iteration).
        let i = uses.partition_point(|&p| p < after);
        uses.get(i).copied().unwrap_or(usize::MAX)
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
                    // The pinned prefix is never evicted.
                    Placement::PinnedSlot { .. } => None,
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
            // Pick the victim with the furthest next use, tie-break by width
            // then node id. The node id makes the key TOTAL: victims come
            // from a HashMap walk, and without it ties resolve by hash
            // iteration order, making compilation nondeterministic across
            // runs (caught as run-to-run jitter in the static report).
            let budget = self.slot_alloc.budget();
            let protected = protect.len();
            let victim = victims
                .iter()
                .max_by_key(|r| (self.next_use(r.node, pos), r.width, r.node))
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
    /// computation through the same footprint-aware chunked path as the main
    /// walk (plain SumK/ProdK — never re-fuse DotK in remat). `depth` is a
    /// recursion guard (DAG depth is shallow, ~10). Returns the new Placement.
    ///
    /// IMPORTANT: remat-emitted instructions do NOT decrement remaining_uses
    /// of their operands (release-less groups). The original refcounts already
    /// account for the original edges; remat is extra reads beyond those.
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
        let (op, children): (Op, Vec<usize>) = match &self.arena[node] {
            ExprNode::Sum { terms, .. } => {
                (Op::SumK, terms.iter().map(|t| t.0 as usize).collect())
            }
            ExprNode::Product { factors, .. } => {
                (Op::ProdK, factors.iter().map(|f| f.0 as usize).collect())
            }
            _ => panic!("remat called on non-computed node {node}"),
        };
        let groups: Vec<OperandGroup> = children
            .into_iter()
            .map(|c| OperandGroup { nodes: vec![Some(c)], release: Vec::new() })
            .collect();
        let p = self.emit_grouped_slotted(node, op, e4, &groups, protect, depth + 1, false);
        self.stats.remat_instrs += 1;
        p
    }

    /// Slot cells this operand's protection will occupy: 0 when it is (or will
    /// be) served outside the evictable slot file, its width otherwise (a
    /// missing placement means an upcoming remat into a fresh slot).
    fn protect_footprint(&self, node: usize) -> usize {
        match self.placements.get(&node) {
            Some(Placement::PinnedSlot { .. }) => 0,
            Some(Placement::Slot { e4, .. }) => {
                if *e4 { 4 } else { 1 }
            }
            None => {
                if node_domain(&self.arena[node]) == Domain::Ext { 4 } else { 1 }
            }
        }
    }

    /// Resolve one operand group into `ops`, rematerializing evicted computed
    /// operands (protected by the growing `protect` list) and tracking the
    /// protected slot footprint in `protect_cells`.
    fn resolve_group(
        &mut self,
        g: &OperandGroup,
        depth: usize,
        protect: &mut Vec<usize>,
        protect_cells: &mut usize,
        ops: &mut Vec<Operand>,
    ) {
        for node_opt in &g.nodes {
            match *node_opt {
                None => ops.push(Operand::One),
                Some(c) => {
                    let computed = is_computed(&self.arena[c]);
                    if computed && !self.placements.contains_key(&c) {
                        self.remat(c, depth, protect);
                    }
                    let o = self.operand_for(c);
                    if computed && !protect.contains(&c) {
                        *protect_cells += self.protect_footprint(c);
                        protect.push(c);
                    }
                    ops.push(o);
                }
            }
        }
    }

    /// Emit `op` over `groups` into a re-readable destination for `n`,
    /// splitting into continuation chunks whenever the lane cap (MAX_ARITY)
    /// or the protected-slot footprint cap would be exceeded. The footprint
    /// cap is what keeps a single wide instruction from demanding more
    /// simultaneously-protected cells than the budget holds.
    ///
    /// `base_protect` carries the caller's protect list (remat nesting).
    /// `do_release` applies each group's refcount decrements as soon as its
    /// chunk is emitted (false during remat).
    fn emit_grouped_slotted(
        &mut self,
        n: usize,
        op: Op,
        e4_result: bool,
        groups: &[OperandGroup],
        base_protect: &[usize],
        depth: usize,
        do_release: bool,
    ) -> Placement {
        debug_assert!(!groups.is_empty());
        let unit = if op == Op::DotK { 2 } else { 1 };
        let dst_w = if e4_result { 4 } else { 1 };
        let budget = self.slot_alloc.budget();
        let dst_in_slots = !self.pinned.contains_key(&n);

        let mut placement: Option<Placement> = None;
        let mut gi = 0usize;
        while gi < groups.len() {
            let first = placement.is_none();
            let mut protect: Vec<usize> = base_protect.to_vec();
            let mut protect_cells: usize = base_protect
                .iter()
                .map(|&c| match self.placements.get(&c) {
                    Some(Placement::Slot { e4, .. }) => {
                        if *e4 { 4 } else { 1 }
                    }
                    _ => 0,
                })
                .sum();
            let mut ops: Vec<Operand> = Vec::new();
            let max_groups = if first {
                MAX_ARITY
            } else {
                // The accumulator prepend takes one group's lanes.
                protect.push(n);
                if dst_in_slots {
                    protect_cells += dst_w;
                }
                let acc = self.operand_for(n);
                ops.push(acc);
                if unit == 2 {
                    ops.push(Operand::One);
                }
                MAX_ARITY - 1
            };
            // Keep headroom for the dst (first chunk only — afterwards it is
            // counted via the protect list) and for remat transients.
            let cap = budget
                .saturating_sub(REMAT_SLACK + if first && dst_in_slots { dst_w } else { 0 });

            let mut chunk_release: Vec<usize> = Vec::new();
            let mut taken = 0usize;
            while gi < groups.len() && taken < max_groups {
                let g = &groups[gi];
                let mut add = 0usize;
                for c in g.nodes.iter().flatten() {
                    if is_computed(&self.arena[*c]) && !protect.contains(c) {
                        add += self.protect_footprint(*c);
                    }
                }
                // Close the chunk rather than exceed the footprint cap; every
                // chunk takes at least one group (the alloc panic backstops a
                // group that alone cannot fit).
                if taken > 0 && protect_cells + add > cap {
                    break;
                }
                self.resolve_group(g, depth, &mut protect, &mut protect_cells, &mut ops);
                if do_release {
                    chunk_release.extend_from_slice(&g.release);
                }
                taken += 1;
                gi += 1;
            }

            if first {
                placement = Some(self.place_result(n, e4_result, &protect));
            }
            self.record_instr(op, e4_result, Self::dst_from_placement(placement.unwrap()), ops);
            for c in chunk_release {
                self.release_if_dead(c);
            }
        }
        placement.unwrap()
    }

    fn operand_for(&mut self, node: usize) -> Operand {
        use crate::isa::NEG_ONE_U32;
        // Classify the node kind without keeping a borrow on self.arena, so that
        // we can call self.remat() (which needs &mut self) in the computed branch.
        enum Kind { Zero, One, NegOne, Const(u8), Source { id: u16, e4: bool }, Placed(Placement), Computed }
        let kind = match &self.arena[node] {
            ExprNode::Constant(c) => match *c {
                0 => Kind::Zero,
                1 => Kind::One,
                v if v == NEG_ONE_U32 => Kind::NegOne,
                v => Kind::Const(*self.const_id.get(&v).expect("constant not in table")),
            },
            ExprNode::Place { .. } | ExprNode::GateOutput { .. } => {
                // A leaf preloaded into the pinned prefix is read from
                // there. Check placement FIRST.
                match self.placements.get(&node).copied() {
                    Some(p @ Placement::PinnedSlot { .. }) => Kind::Placed(p),
                    _ => {
                        let (id, e4) = *self.source_id.get(&node).expect("source not mapped");
                        Kind::Source { id, e4 }
                    }
                }
            }
            ExprNode::Sum { .. } | ExprNode::Product { .. } => Kind::Computed,
        };
        match kind {
            Kind::Zero => Operand::Zero,
            Kind::One => Operand::One,
            Kind::NegOne => Operand::NegOne,
            Kind::Const(idx) => Operand::Const { idx },
            Kind::Source { id, e4 } => Operand::Source { id, e4 },
            Kind::Placed(p) => self.placement_operand(p),
            Kind::Computed => {
                // If the placement was evicted, rematerialize it now.
                // Empty protect is sound today: resolve_group pre-remats operands
                // before operand_for sees them, and root copies trigger no interleaved
                // allocation. Pass real protect if that changes.
                if !self.placements.contains_key(&node) {
                    self.remat(node, 0, &[]);
                }
                let p = *self.placements.get(&node).expect("computed node has no placement after remat");
                self.placement_operand(p)
            }
        }
    }

    /// Operand for an existing placement; attributes pinned-prefix reads
    /// (indistinguishable from ordinary Slot operands at record_instr time).
    fn placement_operand(&mut self, p: Placement) -> Operand {
        match p {
            Placement::Slot { cell, e4 } => Operand::Slot { cell, e4 },
            Placement::PinnedSlot { cell, e4 } => {
                self.stats.pinned_hits += 1;
                Operand::Slot { cell, e4 }
            }
        }
    }

    fn release_if_dead(&mut self, node: usize) {
        if self.remaining_uses[node] == 0 {
            return;
        }
        self.remaining_uses[node] -= 1;
        if self.remaining_uses[node] == 0 {
            // Check placement type before removing. Pinned placements stay in
            // the map permanently so that subsequent operand_for calls still
            // find the value.
            match self.placements.get(&node) {
                Some(Placement::Slot { cell, e4 }) => {
                    let w = if *e4 { 4 } else { 1 };
                    let c = *cell;
                    self.placements.remove(&node);
                    self.slot_alloc.release(c, w);
                }
                Some(Placement::PinnedSlot { .. }) => {
                    // Pinned cells stay resident for the whole program — do
                    // NOT remove the placement entry; future operand_for
                    // calls must still resolve to it even after
                    // remaining_uses hits 0.
                }
                None => {}
            }
        }
    }

    /// Allocate a slot for `node` with Belady eviction if the budget is full.
    /// `protect` = node ids whose slots must not be evicted (they are operands
    /// that have already been resolved and must remain readable until the
    /// instruction is pushed).
    ///
    /// If `node` appears in the pinned map, it writes its reserved prefix
    /// cell instead (no allocation).
    fn place_result(&mut self, node: usize, e4: bool, protect: &[usize]) -> Placement {
        // Pinned computed candidates write their reserved prefix cell and stay
        // resident for the whole program (no allocation, no eviction).
        if let Some(&cell) = self.pinned.get(&node) {
            let p = Placement::PinnedSlot { cell, e4 };
            self.placements.insert(node, p);
            return p;
        }
        let w = if e4 { 4 } else { 1 };
        let cell = self.alloc_with_eviction(node, w, protect);
        let p = Placement::Slot { cell, e4 };
        self.placements.insert(node, p);
        p
    }

    fn dst_from_placement(p: Placement) -> Dst {
        match p {
            Placement::Slot { cell, .. } | Placement::PinnedSlot { cell, .. } => Dst::Slot(cell),
        }
    }

    fn touch_cells(&mut self, cell: u16, e4: bool) {
        let w = if e4 { 4 } else { 1 };
        for c in cell as usize..cell as usize + w {
            self.cell_accesses[c] += 1;
        }
    }

    fn record_instr(&mut self, op: Op, e4_result: bool, dst: Dst, operands: Vec<Operand>) {
        let op_idx = op as usize;
        self.stats.op_hist[op_idx] += 1;
        for o in &operands {
            let kind_idx = match o {
                Operand::Source { .. } => 0,
                Operand::Slot { cell, e4 } => {
                    self.touch_cells(*cell, *e4);
                    1
                }
                Operand::FixedReg { .. } => 2, // reserved for the backend remap; never emitted
                Operand::Const { .. } => 3,
                Operand::Zero => 4,
                Operand::One => 5,
                Operand::NegOne => 6,
            };
            self.stats.operand_kind_hist[kind_idx] += 1;
        }
        if let Dst::Slot(cell) = dst {
            self.touch_cells(cell, e4_result);
        }
        self.instrs.push(Instr { op, e4_result, dst, operands });
    }
}

/// Build the logical operand groups for node `n` with the given `op`. One
/// group = the operand lanes that must share a chunk (a DotK pair or a single
/// SumK/ProdK operand) plus the refcount decrements owed for it. This mirrors
/// the operand structure used in use_positions computation — the two must
/// stay in sync.
fn build_groups(arena: &[ExprNode], n: usize, op: Op, fused: &[bool]) -> Vec<OperandGroup> {
    match op {
        Op::DotK => {
            let terms = match &arena[n] {
                ExprNode::Sum { terms, .. } => terms,
                _ => unreachable!("DotK must come from Sum"),
            };
            terms
                .iter()
                .map(|t| {
                    let c = t.0 as usize;
                    if fused[c] {
                        let factors = match &arena[c] {
                            ExprNode::Product { factors, .. } => factors,
                            _ => unreachable!(),
                        };
                        let (f0, f1) = (factors[0].0 as usize, factors[1].0 as usize);
                        // The fused product node itself is also consumed here.
                        OperandGroup { nodes: vec![Some(f0), Some(f1)], release: vec![f0, f1, c] }
                    } else {
                        OperandGroup { nodes: vec![Some(c), None], release: vec![c] }
                    }
                })
                .collect()
        }
        Op::SumK => {
            let terms = match &arena[n] {
                ExprNode::Sum { terms, .. } => terms,
                _ => unreachable!("SumK must come from Sum"),
            };
            terms
                .iter()
                .map(|t| {
                    let c = t.0 as usize;
                    OperandGroup { nodes: vec![Some(c)], release: vec![c] }
                })
                .collect()
        }
        Op::ProdK => {
            let factors = match &arena[n] {
                ExprNode::Product { factors, .. } => factors,
                _ => unreachable!("ProdK must come from Product"),
            };
            factors
                .iter()
                .map(|f| {
                    let c = f.0 as usize;
                    OperandGroup { nodes: vec![Some(c)], release: vec![c] }
                })
                .collect()
        }
    }
}

pub(crate) fn emit_layer(
    layer: &CodegenLayer,
    g: &AnalysisGraph,
    params: CompileParams,
) -> CompiledLayer {
    let arena: &[ExprNode] = &layer.arena.nodes;
    let pv = view::build(layer, g);

    // Assign the pinned prefix (hub leaves and intermediates alike). The
    // prefix-relative cells double as absolute cell addresses (prefix at 0).
    let pinned = pinning::assign(arena, &pv, params.pinned_cells.min(params.budget_cells));
    let pinned_prefix = pinned
        .iter()
        .map(|(&n, &c)| c as usize + if node_domain(&arena[n]) == Domain::Ext { 4 } else { 1 })
        .max()
        .unwrap_or(0);

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

    let mut slot_alloc = SlotAlloc::new(params.budget_cells);
    slot_alloc.reserve_prefix(pinned_prefix);

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
        pinned: pinned.clone(),
        cell_accesses: vec![0; params.budget_cells],
    };
    ctx.stats.pinned_cells = pinned_prefix;

    // Preload leaves assigned to the pinned prefix (an explicit SumK arity-1
    // copy of the staged source; ascending node-id order for determinism);
    // computed pinned nodes get their PinnedSlot placement at emission
    // (place_result).
    if pinned_prefix > 0 {
        let mut leaf_pinned: Vec<(usize, u16)> = pinned
            .iter()
            .filter(|&(&node, _)| !is_computed(&arena[node]))
            .map(|(&node, &cell)| (node, cell))
            .collect();
        leaf_pinned.sort_by_key(|&(node, _)| node);
        for (node, cell) in leaf_pinned {
            let e4 = node_domain(&arena[node]) == Domain::Ext;
            let (id, _) = *ctx.source_id.get(&node).expect("leaf pinned node not in source_id");
            let src_op = Operand::Source { id, e4 };
            ctx.placements.insert(node, Placement::PinnedSlot { cell, e4 });
            ctx.record_instr(Op::SumK, e4, Dst::Slot(cell), vec![src_op]);
        }
    }

    // Main emission walk.
    for (walk_idx, &n) in order.iter().enumerate() {
        if fused[n] || pv.uses[n] == 0 {
            continue;
        }

        // Update the current walk position for Belady eviction decisions.
        ctx.pos = walk_idx;

        let e4_result = node_domain(&arena[n]) == Domain::Ext;

        let op = match &arena[n] {
            ExprNode::Sum { terms, .. } => {
                let fuse_count = terms.iter().filter(|t| fused[t.0 as usize]).count();
                if fuse_count >= 2 { Op::DotK } else { Op::SumK }
            }
            ExprNode::Product { .. } => Op::ProdK,
            _ => continue,
        };
        let groups = build_groups(arena, n, op, &fused);

        // A single chunk works only when BOTH caps hold: the lane cap, and the
        // protected-slot footprint cap (distinct computed operands' cells +
        // remat headroom must fit the budget). Wide-footprint nodes go through
        // the chunked slotted path even when single-use.
        let mut est_cells = 0usize;
        let mut est_seen: Vec<usize> = Vec::new();
        for c in groups.iter().flat_map(|g| g.nodes.iter().flatten()) {
            if is_computed(&arena[*c]) && !est_seen.contains(c) {
                est_seen.push(*c);
                est_cells += ctx.protect_footprint(*c);
            }
        }
        let single_chunk_ok = groups.len() <= MAX_ARITY
            && est_cells + REMAT_SLACK <= ctx.slot_alloc.budget();

        let gi = gate_in_idx.get(&n).copied();
        let outs = output_idx.get(&n).cloned().unwrap_or_default();
        let total_uses = pv.uses[n];
        let root_uses = gi.is_some() as u32 + outs.len() as u32;

        if total_uses == 1 && root_uses == 1 && single_chunk_ok {
            // Emit directly to the root destination (no slot needed).
            // No place_result needed, so no eviction risk here.
            let dst = if let Some(idx) = gi {
                Dst::GateIn(idx)
            } else {
                Dst::Output(outs[0])
            };
            let mut protect: Vec<usize> = Vec::new();
            let mut protect_cells = 0usize;
            let mut operands: Vec<Operand> = Vec::new();
            for g in &groups {
                ctx.resolve_group(g, 0, &mut protect, &mut protect_cells, &mut operands);
            }
            ctx.record_instr(op, e4_result, dst, operands);
            for g in &groups {
                for &c in &g.release {
                    ctx.release_if_dead(c);
                }
            }
            // No placement for n; it was written directly.
        } else {
            // Slot placement via the footprint-aware chunked path (resolves,
            // emits, and releases per chunk).
            ctx.emit_grouped_slotted(n, op, e4_result, &groups, &[], 0, true);
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

    // Access concentration over cell addresses, for the later per-address
    // smem-vs-register decision (hot -> indexable smem, cold -> selector-tree
    // registers).
    let mut acc = ctx.cell_accesses.clone();
    acc.sort_unstable_by(|a, b| b.cmp(a));
    ctx.stats.cell_accesses_total = acc.iter().map(|&a| a as usize).sum();
    for (i, k) in [8usize, 16, 24, 32].into_iter().enumerate() {
        ctx.stats.cell_accesses_top[i] =
            acc.iter().take(k).map(|&a| a as usize).sum();
    }

    // Build program.
    let n_consts = consts.len();
    let program = Program {
        instrs: ctx.instrs,
        consts,
        n_slot_cells: max_live_cells as u16,
        n_fixed_cells: 0,
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
    use crate::compiler::{CompileParams, compile_layer};
    use crate::eval_ref::tests::fixture;
    use crate::isa::{Dst, MAX_ARITY};
    use gkr_design_space::import::load_circuit;

    /// Regression test for footprint-aware splitting: every emitted
    /// instruction stays within the lane cap, on the circuit with the widest
    /// Sums (bigint, arity 65), at a budget where the old arity-only splitter
    /// was infeasible (its single wide instruction protected ~50 cells).
    #[test]
    fn chunked_emission_respects_lane_cap_at_tight_budget() {
        let c = load_circuit(&fixture("bigint_with_extended_control_codegen_ir_gkr.json")).unwrap();
        let cl = compile_layer(
            &c.circuit.layers[0],
            &c.graphs[0],
            CompileParams { budget_cells: 24, ..Default::default() },
        );
        for i in &cl.program.instrs {
            let unit = if i.op == crate::isa::Op::DotK { 2 } else { 1 };
            assert!(
                i.operands.len() <= MAX_ARITY * unit,
                "instr exceeds lane cap: {} operands (unit {unit})",
                i.operands.len()
            );
        }
        assert!(cl.stats.spill_evictions > 0, "expected spills at 24 cells");
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
