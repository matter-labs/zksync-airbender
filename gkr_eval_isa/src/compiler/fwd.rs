//! Forward witness program compiler (spec rev-3): the per-layer witness
//! kernel as a native-op (CacheK/GateK) program. Lives BESIDE the cone
//! compiler (emit.rs) — different kernel, different uses, different view.
//!
//! Forward programs are ARITHMETIC-FREE at every layer: NativeK + arity-1
//! leaf loads + arity-1 output copies, nothing else. The one gate class
//! with a computed operand (MaxQuadratic) is served via its factored flat
//! form inside the routine (spec §2a) — `fwd_operand_nodes` drops the
//! trailing expr lane. Guarded by tests/native_guards.rs.

use super::slots::SlotAlloc;
use super::{SourceMap, build_const_table, is_computed, node_domain};
use crate::isa::{Dst, Instr, MAX_ARITY, NEG_ONE_U32, Op, Operand, PayloadMeta, Program, encode};
use cs::definitions::GKRAddress;
use cs::gkr_compiler::codegen_ir::{
    CacheKind, CodegenCache, CodegenGate, CodegenLayer, Domain, ExprNode, GateKind, LinearComb,
    gate_kind_input_nodes,
};
use gkr_design_space::graph::AnalysisGraph;
use serde::Serialize;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug)]
pub struct FwdParams {
    /// Unified bf-cell budget (e4 = 4 aligned cells).
    pub budget_cells: usize,
    /// Dynamic leaf residency over native operand reads. Loads are OPTIONAL:
    /// skipped when they would evict a cache resident or not fit.
    pub leaf_cache: bool,
}

impl Default for FwdParams {
    fn default() -> Self {
        FwdParams { budget_cells: 4096, leaf_cache: true }
    }
}

/// Payload table entry: the FULL IR record (oracle compares structural
/// equality against the layer's own record — payload binding).
#[derive(Clone, Debug, PartialEq)]
pub enum PayloadRecord {
    Gate(CodegenGate),
    Cache(CodegenCache),
}

#[derive(Debug, Default, Serialize)]
pub struct FwdStats {
    pub instrs: usize,
    pub native_gates: usize,
    /// First fires (== cache count); re-fires after eviction count separately.
    pub native_caches: usize,
    pub cache_refires: usize,
    pub leaf_loads: usize,
    pub output_copies: usize,
    /// Operand::Source lanes — the read-traffic metric.
    pub src_reads: usize,
    /// Operand::Slot lanes (cells doing their job).
    pub cell_reads: usize,
    /// Distinct plain-leaf columns referenced — the generated kernel's
    /// load-once floor. Invariant: dyn@unbounded src_reads == this.
    pub distinct_sources: usize,
    pub evictions: usize,
    pub max_live_cells: usize,
    pub payload_bytes: usize,
    /// lanes*2 + consts*4 + payload_bytes + 16 (header).
    pub bytes: usize,
    pub max_native_arity: usize,
    pub native_arity_over_31: usize,
}

pub struct CompiledForward {
    pub program: Program,
    /// Indexed by the instruction payload lane: caches first (payload idx ==
    /// cache idx), then eligible gates in `gates` -> `gates_external` order.
    pub payloads: Vec<PayloadRecord>,
    /// Canonical operand nodes per payload (the oracle re-derives and checks).
    pub payload_operands: Vec<Vec<usize>>,
    pub source_map: SourceMap,
    /// Same-layer Cached Place node -> producing cache payload idx.
    pub cached_alias: HashMap<usize, u16>,
    /// (original output index j, arena node) the program copies out.
    pub outputs: Vec<(u16, usize)>,
    pub stats: FwdStats,
}

/// Forward-eligible: output-bearing and not a host-side copy alias.
pub fn fwd_eligible(g: &CodegenGate) -> bool {
    !g.dst.is_empty()
        && !matches!(
            g.kind,
            GateKind::CopyInBaseField { .. } | GateKind::CopyInExtensionField { .. }
        )
}

/// Canonical FORWARD operand nodes for a gate: `gate_kind_input_nodes`, with
/// the trailing MaxQuadratic `expr` lane dropped (native-flat contract,
/// spec §2a — the routine evaluates the factored flat form from leaf
/// operands; coefficients ride the payload).
pub fn fwd_operand_nodes(gate: &CodegenGate) -> Vec<usize> {
    let mut v: Vec<usize> =
        gate_kind_input_nodes(&gate.kind).iter().map(|id| id.0 as usize).collect();
    if let GateKind::MaxQuadratic { expr, .. } = &gate.kind {
        let popped = v.pop().expect("MaxQuadratic with empty operand list");
        debug_assert_eq!(popped, expr.0 as usize, "expr must be enumerated last");
    }
    v
}

// ---------------------------------------------------------------------------
// Payload byte model (documented estimates; feeds the residency tier only).
// Operand VALUES ride instruction lanes; payload bytes cover static config:
// routine id (2) + native dst slots (2 each) + batch-challenge powers
// (4 each) + num_challenges (1) + per-kind scalars below.
// ---------------------------------------------------------------------------

fn lincomb_bytes(lc: &LinearComb) -> usize {
    4 * lc.terms.len() + 4
}

fn gate_kind_bytes(k: &GateKind) -> usize {
    use GateKind::*;
    match k {
        LinearBaseField { input } => lincomb_bytes(input),
        // Native-flat MaxQuadratic: one u32 coeff per quadratic/linear term
        // plus the constant.
        MaxQuadratic { flat, .. } => {
            4 * (flat.quadratic.iter().map(|(_, v)| v.len()).sum::<usize>()
                + flat.linear.len())
                + 4
        }
        MaterializeSingleLookupInput { input, .. } => lincomb_bytes(&input.column) + 4,
        MaterializedVectorLookupInput { input } => {
            input.columns.iter().map(lincomb_bytes).sum::<usize>() + 2
        }
        LookupWithDensAndSetupExpressions { input_vec, .. }
        | LookupWithDensAndCachedSetup { input_vec, .. } => {
            input_vec.columns.iter().map(lincomb_bytes).sum::<usize>() + 2
        }
        LookupPairFromBaseInputs { input, .. } => {
            input.iter().map(|s| lincomb_bytes(&s.column) + 4).sum()
        }
        LookupPairFromVectorInputs { input } => input
            .iter()
            .map(|v| v.columns.iter().map(lincomb_bytes).sum::<usize>() + 2)
            .sum(),
        LookupFromVectorInputWithSetup { input, .. } => {
            input.columns.iter().map(lincomb_bytes).sum::<usize>() + 2
        }
        LookupUnbalancedPairWithVectorInputs { remainder, .. } => {
            remainder.columns.iter().map(lincomb_bytes).sum::<usize>() + 2
        }
        // Descriptor-shaped payloads: small fixed recipe tags (estimate).
        InitialGrandProductWithoutCaches { .. }
        | MaterializeGrandProductTermExpression { .. }
        | InitsOrTeardownsInitialPair { .. } => 16,
        // Pure operand-ref kinds: no static scalars beyond the common part.
        CopyInBaseField { .. }
        | CopyInExtensionField { .. }
        | InitialGrandProductFromCaches { .. }
        | UnbalancedGrandProductWithCache { .. }
        | TrivialProduct { .. }
        | MaskIntoIdentityProduct { .. }
        | LookupWithCachedDensAndSetup { .. }
        | LookupPairFromMaterializedBaseInputs { .. }
        | LookupFromMaterializedBaseInputWithSetup { .. }
        | LookupUnbalancedPairWithMaterializedBaseInputs { .. }
        | LookupPairFromMaterializedVectorInputs { .. }
        | LookupFromMaterializedVectorInputWithSetup { .. }
        | LookupUnbalancedPairWithMaterializedVectorInputs { .. }
        | LookupPairFromCachedVectorInputs { .. }
        | AggregateLookupRationalPair { .. } => 0,
        EnforceSingleMaxQuadraticConstraint { .. } | EnforceConstraintsMaxQuadratic { .. } => {
            unreachable!("constraint gates are not forward-eligible")
        }
    }
}

fn payload_record_bytes(r: &PayloadRecord) -> usize {
    match r {
        PayloadRecord::Gate(g) => {
            2 + 2 * g.dst.len() + 4 * g.batch_terms.len() + 1 + gate_kind_bytes(&g.kind)
        }
        PayloadRecord::Cache(c) => {
            2 + 2 + match &c.kind {
                CacheKind::SingleColumnLookup { column, .. } => lincomb_bytes(column) + 4,
                CacheKind::VectorizedLookup { columns, .. } => {
                    columns.iter().map(lincomb_bytes).sum::<usize>() + 2
                }
                CacheKind::MemoryTuple { .. } => 16,
                CacheKind::VectorizedLookupSetup => 0,
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Forward view
// ---------------------------------------------------------------------------

struct FwdView {
    payloads: Vec<PayloadRecord>,
    /// payload idx -> canonical operand nodes (caches: inputs; gates:
    /// fwd_operand_nodes — flat contract applied).
    operands: Vec<Vec<usize>>,
    /// Cached Place node -> producing cache payload idx.
    alias: HashMap<usize, u16>,
    /// cache payload idx -> its alias Place node (None = consumer-less).
    cache_cell_node: Vec<Option<usize>>,
    /// Reads per arena node in THIS kernel: native operand lanes + output
    /// copies. Leaves and Cached places only (no computed deps — guarded).
    uses: Vec<u32>,
    outputs: Vec<(u16, usize)>,
    n_caches: usize,
}

fn build_fwd_view(layer: &CodegenLayer, g: &AnalysisGraph) -> FwdView {
    let arena: &[ExprNode] = &layer.arena.nodes;

    // Alias: cache out-address -> the (unique, guarded) Cached Place node.
    let mut addr_to_place: HashMap<GKRAddress, usize> = HashMap::new();
    for (i, n) in arena.iter().enumerate() {
        if let ExprNode::Place { addr, .. } = n {
            if matches!(addr, GKRAddress::Cached { .. }) {
                addr_to_place.insert(*addr, i);
            }
        }
    }

    let mut payloads = Vec::new();
    let mut operands = Vec::new();
    let mut alias = HashMap::new();
    let mut cache_cell_node = Vec::new();
    for (ci, cache) in layer.caches.iter().enumerate() {
        payloads.push(PayloadRecord::Cache(cache.clone()));
        operands.push(cache.inputs.iter().map(|id| id.0 as usize).collect::<Vec<_>>());
        let place = addr_to_place.get(&cache.out.1).copied();
        if let Some(p) = place {
            alias.insert(p, ci as u16);
        }
        cache_cell_node.push(place);
    }
    for gate in layer.gates.iter().chain(&layer.gates_external) {
        if !fwd_eligible(gate) {
            continue;
        }
        payloads.push(PayloadRecord::Gate(gate.clone()));
        operands.push(fwd_operand_nodes(gate));
    }

    let mut uses = vec![0u32; arena.len()];
    for ops in &operands {
        for &n in ops {
            assert!(
                !is_computed(&arena[n]),
                "computed forward operand {n} — flat contract violated (guarded)"
            );
            if !matches!(arena[n], ExprNode::Constant(_)) {
                uses[n] += 1;
            }
        }
    }
    let mut outputs = Vec::new();
    for (j, out) in g.outputs.iter().enumerate() {
        if !matches!(arena[out.node], ExprNode::GateOutput { .. }) {
            assert!(!is_computed(&arena[out.node]), "computed program output (guarded)");
            outputs.push((j as u16, out.node));
            uses[out.node] += 1;
        }
    }

    let n_caches = layer.caches.len();
    FwdView { payloads, operands, alias, cache_cell_node, uses, outputs, n_caches }
}

// ---------------------------------------------------------------------------
// Canonical schedule (spec rev-3 §3): CacheK immediately before its first
// consumer; gates in `gates` -> `gates_external` order; outputs after gates;
// consumer-less caches last. No cones exist.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
enum FwdItem {
    Cache(u16), // payload idx (== cache idx)
    Gate(u16),  // payload idx
}

fn build_schedule(v: &FwdView) -> Vec<FwdItem> {
    let mut fired = vec![false; v.n_caches];
    let mut in_progress = vec![false; v.n_caches];
    let mut items = Vec::new();

    fn ensure_cache(
        c: usize,
        v: &FwdView,
        fired: &mut [bool],
        in_progress: &mut [bool],
        items: &mut Vec<FwdItem>,
    ) {
        if fired[c] {
            return;
        }
        assert!(!in_progress[c], "cyclic cache dependency (guarded impossible)");
        in_progress[c] = true;
        for &op in &v.operands[c] {
            if let Some(&dep) = v.alias.get(&op) {
                ensure_cache(dep as usize, v, fired, in_progress, items);
            }
        }
        in_progress[c] = false;
        fired[c] = true;
        items.push(FwdItem::Cache(c as u16));
    }

    for p in v.n_caches..v.payloads.len() {
        for &op in &v.operands[p] {
            if let Some(&dep) = v.alias.get(&op) {
                ensure_cache(dep as usize, v, &mut fired, &mut in_progress, &mut items);
            }
        }
        items.push(FwdItem::Gate(p as u16));
    }
    for &(_, node) in &v.outputs {
        if let Some(&dep) = v.alias.get(&node) {
            ensure_cache(dep as usize, v, &mut fired, &mut in_progress, &mut items);
        }
    }
    for c in 0..v.n_caches {
        ensure_cache(c, v, &mut fired, &mut in_progress, &mut items);
    }
    items
}

// ---------------------------------------------------------------------------
// Emission
// ---------------------------------------------------------------------------

struct FwdCtx<'a> {
    arena: &'a [ExprNode],
    v: &'a FwdView,
    source_id: HashMap<usize, (u16, bool)>,
    const_id: HashMap<u32, u8>,
    /// node -> (cell, e4). Keys: loaded leaves and cache results (keyed by
    /// their alias Place node).
    placements: HashMap<usize, (u16, bool)>,
    remaining_uses: Vec<u32>,
    use_positions: Vec<Vec<usize>>,
    pos: usize,
    alloc: SlotAlloc,
    leaf_cache: bool,
    instrs: Vec<Instr>,
    stats: FwdStats,
}

impl<'a> FwdCtx<'a> {
    fn width(&self, node: usize) -> usize {
        if node_domain(&self.arena[node]) == Domain::Ext { 4 } else { 1 }
    }

    fn next_use(&self, node: usize, after: usize) -> usize {
        let uses = &self.use_positions[node];
        let i = uses.partition_point(|&p| p < after);
        uses.get(i).copied().unwrap_or(usize::MAX)
    }

    /// Belady-evicting allocation. Returns None when every resident is
    /// protected (caller decides: optional loads fall back to Source reads;
    /// mandatory allocations panic = infeasible budget).
    fn try_alloc_evicting(&mut self, width: usize, protect: &[usize]) -> Option<u16> {
        loop {
            if let Some(cell) = self.alloc.alloc(width) {
                return Some(cell);
            }
            let pos = self.pos;
            let victim = self
                .placements
                .iter()
                .filter(|(n, _)| !protect.contains(n))
                .max_by_key(|&(&n, _)| (self.next_use(n, pos), n))
                .map(|(&n, &(cell, e4))| (n, cell, e4));
            let (n, cell, e4) = victim?;
            self.alloc.release(cell, if e4 { 4 } else { 1 });
            self.placements.remove(&n);
            self.stats.evictions += 1;
        }
    }

    fn must_alloc(&mut self, node: usize, width: usize, protect: &[usize]) -> u16 {
        self.try_alloc_evicting(width, protect).unwrap_or_else(|| {
            panic!(
                "forward budget infeasible: need {width} cells for node {node}, \
                 {} protected, budget {}",
                protect.len(),
                self.alloc.budget()
            )
        })
    }

    /// Resolve one operand lane. All operands are constants, plain leaves,
    /// or Cached places (the flat contract guarantees no computed operands).
    fn resolve_operand(&mut self, node: usize, protect: &mut Vec<usize>) -> Operand {
        if let ExprNode::Constant(c) = &self.arena[node] {
            return match *c {
                0 => Operand::Zero,
                1 => Operand::One,
                v if v == NEG_ONE_U32 => Operand::NegOne,
                v => Operand::Const { idx: *self.const_id.get(&v).expect("const not in table") },
            };
        }
        if let Some(&ci) = self.v.alias.get(&node) {
            // Cache-produced value: must live in its cell; re-fire on
            // eviction (remat = run the routine again, idempotent native store).
            if !self.placements.contains_key(&node) {
                self.fire_cache(ci as usize, protect, true);
            }
        } else if self.leaf_cache
            && !self.placements.contains_key(&node)
            && self.remaining_uses[node] >= 2
        {
            // OPTIONAL load: leaf-vs-leaf Belady only — never evict a cache
            // resident for a leaf (a re-fire costs more than a re-load).
            let w = self.width(node);
            let mut opt_protect = protect.clone();
            for &n in self.placements.keys() {
                if self.v.alias.contains_key(&n) && !opt_protect.contains(&n) {
                    opt_protect.push(n);
                }
            }
            if let Some(cell) = self.try_alloc_evicting(w, &opt_protect) {
                let e4 = w == 4;
                self.placements.insert(node, (cell, e4));
                let (id, src_e4) = *self.source_id.get(&node).expect("leaf not in source map");
                self.push_instr(
                    Op::SumK,
                    e4,
                    Dst::Slot(cell),
                    vec![Operand::Source { id, e4: src_e4 }],
                    None,
                );
                self.stats.leaf_loads += 1;
            }
        }
        match self.placements.get(&node) {
            Some(&(cell, e4)) => {
                if !protect.contains(&node) {
                    protect.push(node);
                }
                Operand::Slot { cell, e4 }
            }
            None => {
                let (id, e4) = *self.source_id.get(&node).expect("leaf not in source map");
                Operand::Source { id, e4 }
            }
        }
    }

    fn release_lane(&mut self, node: usize) {
        if matches!(self.arena[node], ExprNode::Constant(_)) || self.remaining_uses[node] == 0 {
            return;
        }
        self.remaining_uses[node] -= 1;
        if self.remaining_uses[node] == 0 {
            if let Some((cell, e4)) = self.placements.remove(&node) {
                self.alloc.release(cell, if e4 { 4 } else { 1 });
            }
        }
    }

    fn fire_cache(&mut self, c: usize, base_protect: &[usize], refire: bool) {
        let mut protect = base_protect.to_vec();
        let operand_nodes = self.v.operands[c].clone();
        let ops: Vec<Operand> =
            operand_nodes.iter().map(|&n| self.resolve_operand(n, &mut protect)).collect();
        let (dst, e4) = match self.v.cache_cell_node[c] {
            Some(place) => {
                let w = self.width(place);
                let cell = self.must_alloc(place, w, &protect);
                let e4 = w == 4;
                self.placements.insert(place, (cell, e4));
                (Dst::Slot(cell), e4)
            }
            // Consumer-less cache: native store only.
            None => (Dst::Native, false),
        };
        self.note_native_arity(ops.len());
        self.push_instr(Op::NativeK, e4, dst, ops, Some(c as u16));
        if refire {
            self.stats.cache_refires += 1;
        } else {
            self.stats.native_caches += 1;
            for &n in &operand_nodes {
                self.release_lane(n);
            }
        }
    }

    fn fire_gate(&mut self, p: usize) {
        let mut protect = Vec::new();
        let operand_nodes = self.v.operands[p].clone();
        let ops: Vec<Operand> =
            operand_nodes.iter().map(|&n| self.resolve_operand(n, &mut protect)).collect();
        self.note_native_arity(ops.len());
        self.push_instr(Op::NativeK, false, Dst::Native, ops, Some(p as u16));
        self.stats.native_gates += 1;
        for &n in &operand_nodes {
            self.release_lane(n);
        }
    }

    fn note_native_arity(&mut self, arity: usize) {
        self.stats.max_native_arity = self.stats.max_native_arity.max(arity);
        if arity > MAX_ARITY {
            self.stats.native_arity_over_31 += 1;
        }
    }

    fn push_instr(
        &mut self,
        op: Op,
        e4_result: bool,
        dst: Dst,
        operands: Vec<Operand>,
        payload: Option<u16>,
    ) {
        for o in &operands {
            match o {
                Operand::Source { .. } => self.stats.src_reads += 1,
                Operand::Slot { .. } => self.stats.cell_reads += 1,
                _ => {}
            }
        }
        self.instrs.push(Instr { op, e4_result, dst, operands, payload });
    }
}

/// Sources for the FORWARD kernel: plain leaves only — same-layer Cached
/// places are cache cells, not staged sources.
fn enumerate_fwd_sources(arena: &[ExprNode], alias: &HashMap<usize, u16>) -> SourceMap {
    let mut m = SourceMap::default();
    for (i, n) in arena.iter().enumerate() {
        if matches!(n, ExprNode::Place { .. } | ExprNode::GateOutput { .. })
            && !alias.contains_key(&i)
        {
            match node_domain(n) {
                Domain::Base => m.bf.push(i),
                Domain::Ext => m.e4.push(i),
            }
        }
    }
    m
}

pub fn compile_forward(
    layer: &CodegenLayer,
    g: &AnalysisGraph,
    params: FwdParams,
) -> CompiledForward {
    let arena: &[ExprNode] = &layer.arena.nodes;
    let v = build_fwd_view(layer, g);
    let schedule = build_schedule(&v);

    let source_map = enumerate_fwd_sources(arena, &v.alias);
    let mut source_id: HashMap<usize, (u16, bool)> = HashMap::new();
    for (id, &node) in source_map.bf.iter().enumerate() {
        source_id.insert(node, (id as u16, false));
    }
    for (id, &node) in source_map.e4.iter().enumerate() {
        source_id.insert(node, (id as u16, true));
    }
    let consts = build_const_table(arena);
    let mut const_id: HashMap<u32, u8> = HashMap::new();
    for (i, &c) in consts.iter().enumerate() {
        const_id.insert(c, i as u8);
    }

    // use_positions over schedule positions; output copies get tail positions.
    let mut use_positions: Vec<Vec<usize>> = vec![Vec::new(); arena.len()];
    for (p, item) in schedule.iter().enumerate() {
        let idx = match item {
            FwdItem::Cache(c) => *c as usize,
            FwdItem::Gate(g) => *g as usize,
        };
        for &n in &v.operands[idx] {
            if !matches!(arena[n], ExprNode::Constant(_)) {
                use_positions[n].push(p);
            }
        }
    }
    for (k, &(_, node)) in v.outputs.iter().enumerate() {
        use_positions[node].push(schedule.len() + k);
    }

    let mut ctx = FwdCtx {
        arena,
        v: &v,
        source_id,
        const_id,
        placements: HashMap::new(),
        remaining_uses: v.uses.clone(),
        use_positions,
        pos: 0,
        alloc: SlotAlloc::new(params.budget_cells),
        leaf_cache: params.leaf_cache,
        instrs: Vec::new(),
        stats: FwdStats::default(),
    };
    ctx.stats.distinct_sources = arena
        .iter()
        .enumerate()
        .filter(|(i, n)| {
            matches!(n, ExprNode::Place { .. } | ExprNode::GateOutput { .. })
                && !v.alias.contains_key(i)
                && v.uses[*i] > 0
        })
        .count();

    for (pos, item) in schedule.iter().enumerate() {
        ctx.pos = pos;
        match *item {
            FwdItem::Cache(c) => ctx.fire_cache(c as usize, &[], false),
            FwdItem::Gate(p) => ctx.fire_gate(p as usize),
        }
    }
    // Output copies (tail positions).
    for (k, &(j, node)) in v.outputs.iter().enumerate() {
        ctx.pos = schedule.len() + k;
        let e4 = node_domain(&arena[node]) == Domain::Ext;
        let mut protect = Vec::new();
        let op = ctx.resolve_operand(node, &mut protect);
        ctx.push_instr(Op::SumK, e4, Dst::Output(j), vec![op], None);
        ctx.stats.output_copies += 1;
        ctx.release_lane(node);
    }

    let payload_metas: Vec<PayloadMeta> = v
        .payloads
        .iter()
        .enumerate()
        .map(|(i, r)| match r {
            PayloadRecord::Cache(_) => PayloadMeta {
                cache: Some(i as u16),
                e4: v.cache_cell_node[i]
                    .map(|n| node_domain(&arena[n]) == Domain::Ext)
                    .unwrap_or(false),
            },
            PayloadRecord::Gate(_) => PayloadMeta { cache: None, e4: false },
        })
        .collect();

    ctx.stats.instrs = ctx.instrs.len();
    ctx.stats.max_live_cells = ctx.alloc.high_water_cells;
    ctx.stats.payload_bytes = v.payloads.iter().map(payload_record_bytes).sum();

    let program = Program {
        instrs: ctx.instrs,
        consts: consts.clone(),
        n_slot_cells: ctx.stats.max_live_cells as u16,
        n_fixed_cells: 0,
        n_sources_bf: source_map.bf.len() as u16,
        n_sources_e4: source_map.e4.len() as u16,
        n_outputs: g.outputs.len() as u16,
        n_gate_ins: 0,
        payloads: payload_metas,
    };
    let lanes = encode(&program);
    let mut stats = ctx.stats;
    stats.bytes = lanes.len() * 2 + consts.len() * 4 + stats.payload_bytes + 16;

    CompiledForward {
        program,
        payloads: v.payloads,
        payload_operands: v.operands,
        source_map,
        cached_alias: v.alias,
        outputs: v.outputs,
        stats,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval_ref::tests::fixture;
    use gkr_design_space::import::load_circuit;

    #[test]
    fn add_sub_l0_forward_program_shape() {
        let c = load_circuit(&fixture("add_sub_lui_auipc_mop_codegen_ir_gkr.json")).unwrap();
        let layer = &c.circuit.layers[0];
        let cf = compile_forward(layer, &c.graphs[0], FwdParams::default());
        let eligible =
            layer.gates.iter().chain(&layer.gates_external).filter(|g| fwd_eligible(g)).count();
        assert_eq!(cf.stats.native_caches, layer.caches.len());
        assert_eq!(cf.stats.native_gates, eligible);
        assert!(cf.stats.native_gates > 0);
        // No GateIn anywhere, every NativeK carries a payload.
        for i in &cf.program.instrs {
            assert!(!matches!(i.dst, Dst::GateIn(_)));
            assert_eq!(i.op == Op::NativeK, i.payload.is_some());
        }
        // Encode/decode roundtrip on a real forward program.
        let lanes = crate::isa::encode(&cf.program);
        assert_eq!(crate::isa::decode(&lanes, cf.program.instrs.len()), cf.program.instrs);
    }

    #[test]
    fn forward_programs_are_arithmetic_free() {
        // shift_binop has 40 MaxQuadratic gates at L0 (the flat-contract
        // stress); blake2 is the cache-heavy case.
        for f in [
            "shift_binop_codegen_ir_gkr.json",
            "blake2_with_extended_control_codegen_ir_gkr.json",
        ] {
            let c = load_circuit(&fixture(f)).unwrap();
            for (layer, g) in c.circuit.layers.iter().zip(&c.graphs) {
                let cf = compile_forward(layer, g, FwdParams::default());
                for i in &cf.program.instrs {
                    assert!(
                        i.op == Op::NativeK || (i.op == Op::SumK && i.operands.len() == 1),
                        "{f}: unexpected arithmetic instruction {:?}",
                        i.op
                    );
                }
            }
        }
    }

    #[test]
    fn blake2_l0_cache_aliasing_and_floor() {
        let c =
            load_circuit(&fixture("blake2_with_extended_control_codegen_ir_gkr.json")).unwrap();
        let cf = compile_forward(&c.circuit.layers[0], &c.graphs[0], FwdParams::default());
        assert_eq!(cf.stats.native_caches, 382); // measured fixture fact
        assert_eq!(cf.cached_alias.len(), 382);
        // dyn@unbounded: every multi-use leaf loads once -> reads == floor.
        assert_eq!(cf.stats.src_reads, cf.stats.distinct_sources);
        assert_eq!(cf.stats.evictions, 0);
        assert_eq!(cf.stats.cache_refires, 0);
    }
}
