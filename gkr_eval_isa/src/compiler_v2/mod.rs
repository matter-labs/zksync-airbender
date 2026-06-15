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
use crate::compiler_v2::challenges::build_const_table_v2;
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
            // A HARD cap on simultaneously-live slot cells. 120 (<=127) fits the
            // 7-bit `Dst::Slot`/`Operand::Slot` cell field (SLOT_CELL_BITS) and
            // the `u8` cell type, with headroom. The base-arith working set is
            // bounded to this via order + Belady eviction + rematerialization
            // (mirroring v1's `compile_layer`). Kept a parameter so the Phase-4
            // report can still sweep it (incl. a huge value for the unbounded
            // max_live measurement).
            budget_cells: 120,
            leaf_cache: false,
            order: crate::compiler::OrderKind::Arena,
            emit_per_strand: false,
        }
    }
}

/// The three computation-isolated forward strands (spec §6, §2). Defined here
/// in Task 2.4; the partitioning logic lands in Task 2.7. (F6)
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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

/// Bounded base-arith emitter: ports v1 `emit.rs`'s order + Belady eviction +
/// rematerialization to the `Instr2` model so the simultaneously-live slot-cell
/// working set stays under `FwdParams2::budget_cells`.
///
/// Differences vs v1's `EmitCtx`:
/// - No DotK fusion, no footprint-aware chunking: every computed node lowers to
///   exactly ONE `Header::Arith` instr with all its operands inline (plus remat
///   duplicates). The only slot-pressure event is the dst allocation.
/// - Leaves are NEVER resident: `ExprNode::Place` always lowers to a re-readable
///   `Operand::Affine` (LDG), and `ExprNode::Constant` to `Operand::Ldc`. So the
///   slot working set is computed Sum/Product results ONLY — the v1 "leaf cache"
///   idea collapses to "leaf re-read is always free", and remat applies solely
///   to evicted COMPUTED values (recompute by re-emitting their arith instr).
struct FwdEmit<'a> {
    arena: &'a [ExprNode],
    matrix_table: &'a MatrixTable,
    const_idx: &'a HashMap<u32, u16>,
    output_addr: &'a HashMap<usize, cs::definitions::GKRAddress>,
    /// Current slot residence of each live computed node (evicted => absent).
    residence: HashMap<usize, SlotResidence>,
    /// Remaining ARITH-OPERAND uses per node (== `use_positions[n].len()` at
    /// start), decremented as operands are consumed; drives cell release. This
    /// counts ONLY resident-cell reads in this walk — NOT gate-in/output root
    /// references, which are served by Materialize/macro lowering off a backing
    /// column (macros never read a base-arith slot: see `macros::operand_for`),
    /// so a root ref must not pin a slot cell. Keeping this consistent with
    /// `use_positions` is what makes the eviction invariant (line ~241) hold:
    /// `remaining[n] == 0` exactly when `next_use(n, _) == MAX`. Remat does NOT
    /// decrement these (remat reads are extra, beyond the accounted edges).
    remaining: Vec<u32>,
    /// For each arena node: sorted-ascending order-positions where it is consumed
    /// as an arith operand. Belady victim selection ranks by furthest next use.
    use_positions: Vec<Vec<usize>>,
    /// Current main-walk position (index into the emission order vec).
    pos: usize,
    alloc: SlotAlloc,
    instrs: Vec<Instr2>,
    instr_node: Vec<Option<u32>>,
    instr_strand: Vec<Strand>,
    arith_count: usize,
    materialize_count: usize,
    /// Count of remat instrs (recomputes) emitted — a duplicate beyond the
    /// node's single primary emission.
    remat_instrs: usize,
}

impl<'a> FwdEmit<'a> {
    /// Next use position of `node` at or after walk position `after`, or
    /// `usize::MAX` if none.
    fn next_use(&self, node: usize, after: usize) -> usize {
        let uses = &self.use_positions[node];
        let i = uses.partition_point(|&p| p < after);
        uses.get(i).copied().unwrap_or(usize::MAX)
    }

    /// Resolve a child node to its typed operand lane. Computed children MUST be
    /// resident at this point (the caller pre-remats evicted ones); leaves and
    /// constants resolve to always-available LDG/LDC lanes.
    fn operand_for(&self, child: usize) -> Operand {
        match &self.arena[child] {
            ExprNode::Constant(c) => {
                let c = *c;
                if c == 0 {
                    Operand::Ldc { sub: LdcSub::Special, idx: SPECIAL_ZERO }
                } else if c == 1 {
                    Operand::Ldc { sub: LdcSub::Special, idx: SPECIAL_ONE }
                } else if c == NEG_ONE_U32 {
                    Operand::Ldc { sub: LdcSub::Special, idx: SPECIAL_NEG_ONE }
                } else {
                    let idx = *self
                        .const_idx
                        .get(&c)
                        .expect("non-special const must be in the const table");
                    Operand::Ldc { sub: LdcSub::Const, idx }
                }
            }
            ExprNode::Place { addr, .. } => {
                // Staged source column: LDG via the joint matrix table. Always
                // re-readable, so leaves never occupy a slot cell.
                let slot = self
                    .matrix_table
                    .slot_for(addr)
                    .expect("Place source must have a backing slot");
                Operand::Affine { slot, col: self.matrix_table.column_of(addr) }
            }
            ExprNode::Sum { .. } | ExprNode::Product { .. } => {
                let r = self
                    .residence
                    .get(&child)
                    .expect("computed operand must be resident before its use (remat failed?)");
                Operand::Slot { e4: r.e4, cell: r.cell }
            }
            ExprNode::GateOutput { .. } => {
                unreachable!("GateOutput operand in base-arith lowering (Task 2.5 scope)")
            }
        }
    }

    /// Allocate `width` cells, Belady-evicting live computed values as needed.
    /// `protect` lists computed node ids whose cells must NOT be evicted (they
    /// are operands already resolved for the current/parent instruction and must
    /// stay readable until it is emitted).
    fn alloc_with_eviction(&mut self, width: usize, protect: &[usize]) -> u8 {
        loop {
            if let Some(cell) = self.alloc.alloc(width) {
                return cell as u8;
            }
            // Evict the resident computed value whose next use is furthest in the
            // future (Belady optimal). Tie-break by width then node id to keep the
            // key TOTAL (HashMap iteration order is otherwise nondeterministic).
            let pos = self.pos;
            let budget = self.alloc.budget();
            let victim = self
                .residence
                .iter()
                .filter(|(n, _)| !protect.contains(n))
                .map(|(&n, r)| (n, r.cell, if r.e4 { 4usize } else { 1 }))
                .max_by_key(|&(n, _, w)| (self.next_use(n, pos), w, n))
                .map(|(n, cell, w)| (n, cell, w))
                .unwrap_or_else(|| {
                    panic!(
                        "slot budget infeasible: need {width} more cells, budget \
                         {budget}, {} cells protected by the current instruction",
                        protect.len()
                    )
                });
            let (vn, vcell, vwidth) = victim;
            // A computed victim must have a future use — else release_if_dead
            // would have freed it already.
            debug_assert!(
                self.next_use(vn, pos) != usize::MAX || self.remaining[vn] == 0,
                "evicted computed node {vn} has remaining={} but no future use \
                 (use_positions={:?})",
                self.remaining[vn],
                self.use_positions[vn],
            );
            self.alloc.release(vcell as u16, vwidth);
            self.residence.remove(&vn);
        }
    }

    /// Rematerialize an evicted computed `node` by re-emitting its arith instr
    /// into a freshly allocated slot. Recurses through evicted operands (DAG
    /// depth is shallow). `protect` guards the consumer's already-resolved
    /// operands so eviction during remat cannot free them. Returns the new
    /// residence. Does NOT touch `remaining` — remat reads are extra.
    fn remat(&mut self, node: usize, depth: usize, protect: &[usize]) -> SlotResidence {
        debug_assert!(depth < 64, "remat recursion depth {depth} too deep (cycle?)");
        let (op, children): (ArithOp, Vec<usize>) = match &self.arena[node] {
            ExprNode::Sum { terms, .. } => {
                (ArithOp::Sum, terms.iter().map(|t| t.0 as usize).collect())
            }
            ExprNode::Product { factors, .. } => {
                (ArithOp::Prod, factors.iter().map(|f| f.0 as usize).collect())
            }
            _ => panic!("remat called on non-computed node {node}"),
        };
        // Resolve operands, rematerializing evicted computed children first and
        // protecting them (plus the caller's protect set) so the dst allocation
        // below cannot evict them. Operands are resolved in order, each freshly
        // remat'd one protected as we go.
        let mut protect: Vec<usize> = protect.to_vec();
        let mut operands: Vec<Operand> = Vec::with_capacity(children.len());
        for &c in &children {
            if is_computed(&self.arena[c]) && !self.residence.contains_key(&c) {
                let r = self.remat(c, depth + 1, &protect);
                self.residence.insert(c, r);
            }
            operands.push(self.operand_for(c));
            if is_computed(&self.arena[c]) && !protect.contains(&c) {
                protect.push(c);
            }
        }
        let e4 = node_domain(&self.arena[node]) == Domain::Ext;
        let w = width_cells(self.arena, node);
        let cell = self.alloc_with_eviction(w, &protect);
        let res = SlotResidence { e4, cell };
        self.instrs.push(Instr2 {
            header: Header::Arith { op, arity: children.len() as u8 },
            operands,
            dsts: vec![Dst::Slot { e4, cell }],
            memtup: None,
        });
        self.instr_node.push(Some(node as u32));
        self.instr_strand.push(Strand::BaseArith);
        self.arith_count += 1;
        self.remat_instrs += 1;
        res
    }

    /// Decrement an operand's accounted use count; free its cell once dead.
    fn release_if_dead(&mut self, child: usize) {
        if !is_computed(&self.arena[child]) {
            return;
        }
        let r = self.remaining[child];
        debug_assert!(r > 0, "operand {child} consumed past its use count");
        self.remaining[child] = r - 1;
        if self.remaining[child] == 0 {
            if let Some(res) = self.residence.remove(&child) {
                self.alloc.release(res.cell as u16, width_cells(self.arena, child));
            }
        }
    }

    /// Emit one primary arith instr for `node`: resolve operands (rematerializing
    /// evicted computed ones), allocate the dst (Slot, with eviction, OR a
    /// Materialize for layer-output nodes), record it, then release dead operands.
    fn emit_node(&mut self, node: usize) {
        let (op, children): (ArithOp, Vec<usize>) = match &self.arena[node] {
            ExprNode::Sum { terms, .. } => {
                (ArithOp::Sum, terms.iter().map(|t| t.0 as usize).collect())
            }
            ExprNode::Product { factors, .. } => {
                (ArithOp::Prod, factors.iter().map(|f| f.0 as usize).collect())
            }
            _ => unreachable!("non-computed node in emission order"),
        };

        // Resolve operands in IR order. Rematerialize any evicted computed child
        // into a fresh slot before reading it, and protect every resolved
        // computed operand so the subsequent dst allocation (and later operands'
        // remats) cannot evict it out from under this instruction.
        let mut protect: Vec<usize> = Vec::new();
        let mut operands: Vec<Operand> = Vec::with_capacity(children.len());
        for &c in &children {
            if is_computed(&self.arena[c]) && !self.residence.contains_key(&c) {
                let r = self.remat(c, 0, &protect);
                self.residence.insert(c, r);
            }
            operands.push(self.operand_for(c));
            if is_computed(&self.arena[c]) && !protect.contains(&c) {
                protect.push(c);
            }
        }

        let e4 = node_domain(&self.arena[node]) == Domain::Ext;
        let dst = if let Some(addr) = self.output_addr.get(&node) {
            // Layer-output computed node materializes to its backing column; it
            // takes no slot cell (matching the original v2 policy — such a node
            // is not re-consumed as an arith operand in this corpus).
            let slot = self
                .matrix_table
                .slot_for(addr)
                .expect("computed layer output must have a backing slot");
            self.materialize_count += 1;
            Dst::Materialize { slot, col: self.matrix_table.column_of(addr) }
        } else {
            let w = width_cells(self.arena, node);
            let cell = self.alloc_with_eviction(w, &protect);
            self.residence.insert(node, SlotResidence { e4, cell });
            Dst::Slot { e4, cell }
        };

        self.instrs.push(Instr2 {
            header: Header::Arith { op, arity: children.len() as u8 },
            operands,
            dsts: vec![dst],
            memtup: None,
        });
        self.instr_node.push(Some(node as u32));
        self.instr_strand.push(Strand::BaseArith);
        self.arith_count += 1;

        // Release operand cells whose last accounted use was this instruction.
        for &c in &children {
            self.release_if_dead(c);
        }
    }
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

    // Deduped bf-const table (0/1/-1 are Special, not entries). R2: the v2 table
    // is a SUPERSET of the arena-only v1 table — it also collects the cache
    // `LinearComb` coeffs/constants and the memory-tuple folded constants that
    // `macros::lower_cache` now emits as recoverable `Ldc{Const}` lanes (so a
    // coefficient is never a placeholder). Arena consts keep their entries, so
    // base-arith `Ldc{Const}` lookups still resolve.
    let consts = build_const_table_v2(layer);
    let const_idx: HashMap<u32, u16> = consts
        .iter()
        .enumerate()
        .map(|(i, c)| (*c, i as u16))
        .collect();

    // Dst selection + pass-through aliasing + scratch-prefill skip (Task 2.6).
    //
    // (a) Dst::Materialize vs Dst::Slot. A computed node that is a PROGRAM-owned
    //     layer output (the output node is NOT a native GateOutput) materializes
    //     to its backing column (`Dst::Materialize`, below in `emit_node`); every
    //     OTHER computed node — including every multi-use CSE intermediate — gets
    //     a bounded `Dst::Slot`. (In the in-tree corpus EVERY program output node
    //     is a native GateOutput, so `output_addr` is empty and the Materialize
    //     arm is correct-but-unexercised here; macros/caches are the only sources
    //     of `Dst::Materialize` in practice. The arm stays for circuits that copy
    //     a computed value out directly.)
    //
    // (b) Pass-through aliasing (no-emit). The genuine alias in this corpus is a
    //     Cached `Place` node — a leaf column whose address is produced by a
    //     SAME-layer cache (v1's `cached_alias`, fwd.rs:251-258). It is the
    //     consumer-side read of a cache cell, NOT a staged source. Two facts make
    //     it a true pass-through with no instruction of its own:
    //       - It is a `Place` (never `is_computed`), so it never enters the
    //         base-arith emission `order` and emits no `Header::Arith` instr.
    //       - When a macro/cache consumes it, `macros::operand_for` maps the
    //         `GKRAddress::Cached` Place to an inline gather (`Operand::Indirect`),
    //         never an `Operand::Affine` staged-source read — so no copy/load
    //         instruction backs the alias either. Consumers resolve to the cache's
    //         own `Dst::Materialize` backing, produced once by `lower_cache`.
    //     `CopyInBaseField`/`CopyInExtensionField` gates are the other alias class
    //     (`LoweringKind::Alias`): `lower_gate` returns `None` for them, so they
    //     emit nothing and the consumer reads the copied-in backing directly.
    //
    // (c) Scratch-prefill skip. A scratch-prefilled `MaxQuadratic` is a
    //     witness-stage value read from scratch by address, never computed
    //     forward. It is classified `LoweringKind::ScratchSkip`
    //     (routines.rs:172), for which `macros::lower_gate` returns `None` — so it
    //     emits no instruction. We keep the KIND-based skip rather than the v1
    //     per-gate predicate (`gate_is_scratch_prefilled`) because the corpus
    //     invariant "every forward `MaxQuadratic` is scratch-prefilled" is pinned
    //     by `tests/v2_gates.rs::maxquadratic_all_scratch_prefilled`; if a
    //     non-scratch `MaxQuadratic` ever appears it is a new design item (spec
    //     §9), not a silent mis-lowering. The Task-2.6 test asserts BOTH that no
    //     `MaxQuadratic` gate produces an `Instr2` AND that the invariant still
    //     holds, so the kind-based skip stays sound.
    let mut output_addr: HashMap<usize, cs::definitions::GKRAddress> = HashMap::new();
    for out in &g.outputs {
        if !matches!(arena[out.node], ExprNode::GateOutput { .. }) {
            // First-seen wins (a node maps to one backing address).
            output_addr.entry(out.node).or_insert(out.addr);
        }
    }

    // Emission order: locality-aware over the ProgramView DAG to shrink the
    // natural live set (mirroring v1's `emit_layer`). Arena order is the IR's
    // topological CSE encounter order (children strictly precede parents); the
    // greedy Pressure/Reuse orders are the alternatives the Phase-4 report
    // sweeps. All three are topological, so operands are always emitted before
    // their consumer regardless of choice.
    let order: Vec<usize> = match params.order {
        crate::compiler::OrderKind::Arena => arena
            .iter()
            .enumerate()
            .filter(|(i, n)| is_computed(n) && pv.uses[*i] > 0)
            .map(|(i, _)| i)
            .collect(),
        crate::compiler::OrderKind::Pressure => view::pressure_order(arena, &pv),
        crate::compiler::OrderKind::Reuse => view::reuse_order(arena, &pv, params.budget_cells),
    };

    // Build use_positions: for each arena node, the sorted-ascending list of
    // emission-order positions at which it is consumed as an arith operand.
    // Belady victim selection ranks resident computed values by their furthest
    // next use. Root references (gate-in / output copies) are NOT positions in
    // this walk — they are satisfied by Materialize/macro lowering, never by a
    // resident-cell read in this loop — so they do not extend liveness here.
    let mut use_positions: Vec<Vec<usize>> = vec![Vec::new(); arena.len()];
    for (p, &n) in order.iter().enumerate() {
        let children: Vec<usize> = match &arena[n] {
            ExprNode::Sum { terms, .. } => terms.iter().map(|t| t.0 as usize).collect(),
            ExprNode::Product { factors, .. } => factors.iter().map(|f| f.0 as usize).collect(),
            _ => continue,
        };
        for c in children {
            if is_computed(&arena[c]) {
                use_positions[c].push(p);
            }
        }
    }
    // use_positions[n] is sorted ascending because p increases monotonically.

    // Bounded base-arith emission: order + Belady eviction + rematerialization
    // keeps the simultaneously-live cell count under params.budget_cells.
    //
    // `remaining` is the per-node arith-operand use count — exactly
    // `use_positions[n].len()`, NOT `pv.uses[n]`. `pv.uses` additionally counts
    // gate-in/output root references (view.rs), but those are served by
    // Materialize/macro lowering off a backing column, never by reading this
    // node's slot cell (macros are arithmetic-free: `macros::operand_for`). So a
    // root-only node (use_positions empty) must release immediately and never
    // pin a cell — and the two liveness views stay consistent, which is what
    // makes `alloc_with_eviction`'s `remaining==0 <=> next_use==MAX` invariant
    // hold instead of panicking on a root-pinned victim.
    let remaining: Vec<u32> = use_positions.iter().map(|v| v.len() as u32).collect();
    let mut emit = FwdEmit {
        arena,
        matrix_table: &matrix_table,
        const_idx: &const_idx,
        output_addr: &output_addr,
        residence: HashMap::new(),
        remaining,
        use_positions,
        pos: 0,
        alloc: SlotAlloc::new(params.budget_cells),
        instrs: Vec::new(),
        instr_node: Vec::new(),
        instr_strand: Vec::new(),
        arith_count: 0,
        materialize_count: 0,
        remat_instrs: 0,
    };
    for (p, &node) in order.iter().enumerate() {
        emit.pos = p;
        emit.emit_node(node);
    }

    let mut program = Program2 {
        instrs: emit.instrs,
        consts: consts.clone(),
        n_slot_cells: 0,
        n_matrix_slots: matrix_table.len() as u8,
    };
    let mut instr_node = emit.instr_node;
    let mut instr_strand = emit.instr_strand;
    let arith_count = emit.arith_count;
    let mut materialize_count = emit.materialize_count;
    let _remat_instrs = emit.remat_instrs;
    let alloc = emit.alloc;

    // Macro / gather / materialize lowering (Task 2.5). After the base-arith
    // instrs, emit one macro Instr2 per Macro gate and per cache. Macro instrs
    // are not single arena nodes (instr_node = None). Strand classification
    // (Task 2.7) tags each emitted macro from its `Header::Macro { routine }`
    // via `routine_strand` (the spec §2 routine→strand map).
    let cache_kinds = macros::cache_kind_by_addr(layer);
    let mut mctx = macros::MacroCtx::new(&matrix_table, &const_idx, &cache_kinds);
    let mut macro_count = 0usize;
    let mut gather_lane_count = 0usize;

    // Strand of an emitted macro instr from its header routine.
    let macro_strand = |instr: &Instr2| -> Strand {
        match instr.header {
            Header::Macro { routine, .. } => {
                let rid = routine_from_u8(routine);
                routine_strand(rid)
            }
            // base-arith never reaches this loop.
            Header::Arith { .. } => Strand::BaseArith,
        }
    };

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
        let strand = macro_strand(&instr);
        program.instrs.push(instr);
        instr_node.push(None);
        instr_strand.push(strand);
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
            let strand = macro_strand(&instr);
            program.instrs.push(instr);
            instr_node.push(None);
            instr_strand.push(strand);
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

    // (Task 2.7) §2 AGG/PROD isolation check + per-strand split. `isolation_ok`
    // is `false` iff some instr reads a COMPUTED `Operand::Slot` whose writer is
    // in a different strand. The per-strand decomposition is materialized when
    // requested (Task 4.2 proxy) OR when isolation fails (Task 3.6 fallback);
    // `split_into_strands` rematerializes any genuine cross-strand Slot dep so
    // each per-strand program is independently valid.
    let isolation_ok = isolation_holds(&program, &instr_strand);
    let per_strand = if params.emit_per_strand || !isolation_ok {
        Some(split_into_strands(&program, &instr_strand))
    } else {
        None
    };

    CompiledForward2 {
        program,
        matrix_table,
        stats,
        isolation_ok,
        per_strand,
        instr_node,
        instr_strand,
    }
}

/// §2 routine→strand map, by FAMILY. `LookupGp` = the whole lookup-argument
/// family (the num/den pair routines, the aggregate, the single/vectorized
/// lookup gathers + their gate forms); `MemoryGp` = the memory-tuple caches AND
/// the grand-product (PROD) cascade that consumes them (product, mask-identity,
/// tuple grand-products, memory init/teardown); `BaseArith` = the gate-output
/// fold.
///
/// The PROD cascade routines (`Product`/`MaskIdentity`/`GrandProductWithoutCaches`/
/// `MaterializeGrandProductTerm`/`MemoryInitTeardownPair`) carry no
/// lookup-vs-memory tag in the gate kind (see `routine_for_gate`), and in the
/// in-tree corpus they read only materialized backings (`Affine`) / inline
/// gathers (`Indirect`) — NEVER a base-arith `Operand::Slot` — so the bucket
/// choice creates no cross-strand `Slot` dependency either way (the isolation
/// oracle only sees Slot-to-Slot crossings, and macros emit no Slot reads:
/// `macros::operand_for`). We assign the PROD cascade to `MemoryGp`, matching
/// the spec §2/§6 phrasing "MemoryGp — memory-tuple caches → grand-product
/// (PROD) cascade", and the LOOKUP rational/gather family to `LookupGp`.
pub(crate) fn routine_strand(routine: crate::isa_v2::RoutineId) -> Strand {
    use crate::isa_v2::RoutineId::*;
    match routine {
        GateOutputFold => Strand::BaseArith,
        // Lookup-argument family.
        AggregateLookupPair
        | LookupBasePair
        | LookupExtPair
        | LookupBaseMinusMult
        | LookupExtMinusMult
        | LookupCachedDens
        | LookupUnbalancedBase
        | LookupUnbalancedExt
        | LookupDecoderDensSetup
        | VectorLookupGate
        | MaterializeSingleLookup
        | SingleColumnLookup
        | VectorizedLookup
        | VectorizedLookupSetup => Strand::LookupGp,
        // Memory permutation / grand-product (PROD) cascade.
        Product
        | MaskIdentity
        | GrandProductWithoutCaches
        | MaterializeGrandProductTerm
        | MemoryTuple
        | MemoryInitTeardownPair => Strand::MemoryGp,
    }
}

/// Recover a `RoutineId` from the 7-bit header `routine` byte. The compiler only
/// emits the dense 0..=20 ids; an out-of-range byte is a corrupt program.
fn routine_from_u8(routine: u8) -> crate::isa_v2::RoutineId {
    use crate::isa_v2::RoutineId::*;
    match routine {
        0 => GateOutputFold,
        1 => Product,
        2 => MaskIdentity,
        3 => AggregateLookupPair,
        4 => LookupBasePair,
        5 => LookupExtPair,
        6 => LookupBaseMinusMult,
        7 => LookupExtMinusMult,
        8 => LookupCachedDens,
        9 => LookupUnbalancedBase,
        10 => LookupUnbalancedExt,
        11 => VectorLookupGate,
        12 => MaterializeSingleLookup,
        13 => LookupDecoderDensSetup,
        14 => GrandProductWithoutCaches,
        15 => MaterializeGrandProductTerm,
        16 => SingleColumnLookup,
        17 => VectorizedLookup,
        18 => VectorizedLookupSetup,
        19 => MemoryTuple,
        20 => MemoryInitTeardownPair,
        other => panic!("unknown routine id {other} in fused program header"),
    }
}

/// Every COMPUTED `Operand::Slot { cell }` an instr reads — in its `operands`
/// AND inside its `memtup` (roles + as-payload). Shared `Affine`/`Ldc`/
/// `Indirect` INPUT reads are NOT computed transients, so they are excluded.
fn slot_reads(instr: &Instr2) -> Vec<u8> {
    let mut cells = Vec::new();
    let mut scan = |op: &Operand| {
        if let Operand::Slot { cell, .. } = op {
            cells.push(*cell);
        }
    };
    for op in &instr.operands {
        scan(op);
    }
    if let Some(mt) = &instr.memtup {
        for (_role, op) in &mt.roles {
            scan(op);
        }
        if let Some(op) = &mt.as_payload {
            scan(op);
        }
    }
    cells
}

/// Every `Dst::Slot { cell }` an instr writes (a computed transient backing).
fn slot_writes(instr: &Instr2) -> Vec<u8> {
    instr
        .dsts
        .iter()
        .filter_map(|d| match d {
            Dst::Slot { cell, .. } => Some(*cell),
            Dst::Materialize { .. } => None,
        })
        .collect()
}

/// §2 isolation check. Returns `false` iff some instruction reads an
/// `Operand::Slot { cell }` (a COMPUTED transient) whose `Dst::Slot { cell }`
/// writer (the LAST writer at or before this instr) lives in a DIFFERENT strand.
/// Shared `Affine`/`Ldc`/`Indirect` input reads do not count — only computed
/// Slot values cross. Slot reads inside `memtup` are accounted for too.
///
/// `instr_strand` must be instr-aligned (`== program.instrs.len()`).
pub(crate) fn isolation_holds(program: &Program2, instr_strand: &[Strand]) -> bool {
    debug_assert_eq!(instr_strand.len(), program.instrs.len());
    // cell -> (strand of its current/last writer). Updated as we walk forward,
    // so a reader sees the most-recent writer of that cell.
    let mut writer_strand: HashMap<u8, Strand> = HashMap::new();
    for (i, instr) in program.instrs.iter().enumerate() {
        let strand = instr_strand[i];
        for cell in slot_reads(instr) {
            if let Some(&ws) = writer_strand.get(&cell) {
                if ws != strand {
                    return false;
                }
            }
            // A Slot read with no prior writer is a forward-ordering bug, not a
            // cross-strand dep; the emitter never produces one, so leave it to
            // the per-strand dangling-read assertion to surface.
        }
        for cell in slot_writes(instr) {
            writer_strand.insert(cell, strand);
        }
    }
    true
}

/// Produce one INDEPENDENTLY-VALID `Program2` per strand (the §6/§7 fallback
/// decomposition). Not a blind partition: a blind split leaves a consumer strand
/// reading a `Slot` only the producer strand wrote (rereview-5). For every
/// cross-strand `Slot` dependency (a `Dst::Slot { cell }` in strand A read by an
/// `Operand::Slot { cell }` in strand B) we MATERIALIZE the bridge: the producer
/// instr (kept in A's program) ALSO gets a `Dst::Materialize { slot, col }` into
/// a fresh scratch matrix backing, and the consumer's `Operand::Slot { cell }`
/// (in `operands` AND `memtup`) is rewritten to `Operand::Affine { slot, col }`
/// of that backing. Fresh slot ids start at `program.n_matrix_slots`, one per
/// materialized (writer-strand, cell) pair; col is 0.
///
/// When isolation holds (the §2 norm — all 22 in-tree fixtures) there are NO
/// cross-strand Slot deps, so this reduces to a plain instr partition.
pub(crate) fn split_into_strands(program: &Program2, instr_strand: &[Strand]) -> PerStrand2 {
    debug_assert_eq!(instr_strand.len(), program.instrs.len());

    // (1) Identify cross-strand Slot bridges. Walk forward tracking, per cell,
    // the (instr index, strand) of its last Slot writer. A read from a different
    // strand marks both the writer instr (must also Materialize) and the
    // consumer operand (must be rewritten) against an allocated backing slot.
    let mut last_writer: HashMap<u8, (usize, Strand)> = HashMap::new();
    // (writer_instr_idx, cell) -> backing slot id (so the producer materializes
    // each bridged cell exactly once, and every consumer of that same write
    // rewrites to the SAME backing).
    let mut bridge_slot: HashMap<(usize, u8), u8> = HashMap::new();
    let mut next_slot: u8 = program.n_matrix_slots;

    for (i, instr) in program.instrs.iter().enumerate() {
        let strand = instr_strand[i];
        for cell in slot_reads(instr) {
            if let Some(&(wi, ws)) = last_writer.get(&cell) {
                if ws != strand {
                    bridge_slot.entry((wi, cell)).or_insert_with(|| {
                        let s = next_slot;
                        next_slot = next_slot.checked_add(1).expect("scratch slot overflow");
                        s
                    });
                }
            }
        }
        for cell in slot_writes(instr) {
            last_writer.insert(cell, (i, strand));
        }
    }

    // (2) Re-walk and emit per-strand programs. For each instr, in its OWN
    // strand's program: a producer of a bridged cell gets an extra
    // `Dst::Materialize`; a consumer reading a foreign-strand cell has that
    // `Operand::Slot` (operands + memtup) rewritten to the bridge `Affine`.
    let strands = [Strand::BaseArith, Strand::LookupGp, Strand::MemoryGp];
    let mut programs: Vec<(Strand, Program2)> = Vec::new();

    // We need, for each instr, the per-cell writer at the time of its reads, to
    // know which reads are cross-strand. Recompute the same forward state.
    let mut last_writer2: HashMap<u8, (usize, Strand)> = HashMap::new();

    // Per-instr precomputed: the rewrite map (cell -> Affine backing) for reads,
    // and the set of bridged cells this instr WRITES (-> add Materialize).
    let mut read_rewrite: Vec<HashMap<u8, (u8, u16)>> = Vec::with_capacity(program.instrs.len());
    let mut write_bridges: Vec<Vec<(u8, u16)>> = Vec::with_capacity(program.instrs.len());

    for (i, instr) in program.instrs.iter().enumerate() {
        let strand = instr_strand[i];
        let mut rewrite: HashMap<u8, (u8, u16)> = HashMap::new();
        for cell in slot_reads(instr) {
            if let Some(&(wi, ws)) = last_writer2.get(&cell) {
                if ws != strand {
                    if let Some(&slot) = bridge_slot.get(&(wi, cell)) {
                        rewrite.insert(cell, (slot, 0));
                    }
                }
            }
        }
        read_rewrite.push(rewrite);

        let mut writes: Vec<(u8, u16)> = Vec::new();
        for cell in slot_writes(instr) {
            if let Some(&slot) = bridge_slot.get(&(i, cell)) {
                writes.push((slot, 0));
            }
            last_writer2.insert(cell, (i, strand));
        }
        write_bridges.push(writes);
    }

    let rewrite_operand = |op: &Operand, rewrite: &HashMap<u8, (u8, u16)>| -> Operand {
        if let Operand::Slot { cell, .. } = op {
            if let Some(&(slot, col)) = rewrite.get(cell) {
                return Operand::Affine { slot, col };
            }
        }
        *op
    };

    for &s in &strands {
        let mut instrs: Vec<Instr2> = Vec::new();
        for (i, instr) in program.instrs.iter().enumerate() {
            if instr_strand[i] != s {
                continue;
            }
            let rewrite = &read_rewrite[i];
            // Rewrite cross-strand Slot reads to their bridge Affine backing.
            let operands: Vec<Operand> =
                instr.operands.iter().map(|o| rewrite_operand(o, rewrite)).collect();
            let memtup = instr.memtup.as_ref().map(|mt| crate::isa_v2::MemTup {
                roles: mt
                    .roles
                    .iter()
                    .map(|(role, op)| (*role, rewrite_operand(op, rewrite)))
                    .collect(),
                as_arm: mt.as_arm,
                as_payload: mt.as_payload.as_ref().map(|op| rewrite_operand(op, rewrite)),
                // R2 folded-constant lanes are all `Ldc` (never a cross-strand
                // Slot), so the rewrite is identity; carry them through verbatim.
                consts: mt.consts.clone(),
            });
            // Producers of bridged cells also Materialize into the backing.
            let mut dsts = instr.dsts.clone();
            for &(slot, col) in &write_bridges[i] {
                dsts.push(Dst::Materialize { slot, col });
            }
            instrs.push(Instr2 { header: instr.header, operands, dsts, memtup });
        }
        if instrs.is_empty() {
            continue;
        }
        let prog = Program2 {
            instrs,
            consts: program.consts.clone(),
            n_slot_cells: program.n_slot_cells,
            n_matrix_slots: next_slot,
        };
        programs.push((s, prog));
    }

    PerStrand2 { programs }
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

    /// Task 2.6: corpus-wide dst-selection + pass-through aliasing + scratch
    /// skip. Over all 22 fixtures × every layer:
    ///  (a) every multi-use (`pv.uses >= 2`) computed intermediate that is NOT a
    ///      program-owned output gets a `Dst::Slot`; a computed program output
    ///      gets a `Dst::Materialize`.
    ///  (b) a pass-through alias — a Cached `Place` node whose address is produced
    ///      by a same-layer cache — emits NO `Instr2` of its own; consumers read
    ///      it via an inline gather (`Operand::Indirect`), never a staged-source
    ///      Affine, and the only writer of its backing is the producing cache's
    ///      `Dst::Materialize`. Proven non-vacuous (>= 1 alias consumed).
    ///  (c) no `MaxQuadratic` gate produces an `Instr2` (kind-based ScratchSkip),
    ///      and the corpus invariant that every such gate IS scratch-prefilled
    ///      still holds (so the kind-based skip is sound — see the comment in
    ///      `compile_forward_v2`).
    #[test]
    fn dst_selection_alias_and_scratch_skip_22_fixtures() {
        use crate::compiler::fwd::gate_is_scratch_prefilled;
        use crate::isa_v2::Operand;
        use crate::test_support::all_fixtures;
        use cs::definitions::GKRAddress;
        use cs::gkr_compiler::codegen_ir::GateKind;
        use std::collections::{HashMap, HashSet};

        let fixtures = all_fixtures();
        assert_eq!(fixtures.len(), 22, "expected the 22-fixture codegen_ir corpus");

        // Non-vacuity accumulators across the whole corpus.
        let mut total_multiuse_slot = 0usize; // (a) multi-use computed -> Slot
        let mut total_materialize_outputs = 0usize; // (a) computed output -> Materialize
        let mut total_alias_nodes = 0usize; // (b) Cached-Place aliases seen
        let mut total_alias_backed = 0usize; // (b) alias (slot,col) backings keyed
        let mut total_indirect_for_alias = 0usize; // (b) aliases read via gather
        let mut total_maxq_gates = 0usize; // (c) MaxQuadratic gates
        let mut total_maxq_scratch = 0usize; // (c) of which scratch-prefilled

        for p in &fixtures {
            let name = p.file_name().unwrap().to_str().unwrap().to_string();
            let c = load_circuit(p).unwrap_or_else(|e| panic!("load {name}: {e:?}"));
            for (li, layer) in c.circuit.layers.iter().enumerate() {
                let Some(g) = c.graphs.get(li) else { continue };
                let arena = &layer.arena.nodes;
                let pv = view::build(layer, g);
                let cf = compile_forward_v2(layer, g, FwdParams2::default());

                // Program-owned output nodes (node is NOT a native GateOutput):
                // the only nodes allowed a base-arith `Dst::Materialize`.
                let output_nodes: HashSet<usize> = g
                    .outputs
                    .iter()
                    .filter(|o| !matches!(arena[o.node], ExprNode::GateOutput { .. }))
                    .map(|o| o.node)
                    .collect();

                // (a) Bind each base-arith instr back to its arena node and check
                //     the dst KIND against the node's role. instr_node must be
                //     instr-aligned, else the zip silently drops instrs.
                assert_eq!(
                    cf.instr_node.len(),
                    cf.program.instrs.len(),
                    "{name} L{li}: instr_node not instr-aligned"
                );
                // A computed node may be emitted (as Slot) MORE THAN ONCE via
                // rematerialization; track which nodes we have seen materialized.
                for (ins, node) in cf.program.instrs.iter().zip(&cf.instr_node) {
                    let Header::Arith { .. } = ins.header else { continue };
                    let nid = node.expect("arith instr carries its arena node id") as usize;
                    assert!(is_computed(&arena[nid]), "{name} L{li}: arith node not computed");
                    match ins.dsts.as_slice() {
                        [Dst::Slot { .. }] => {
                            // A Slot dst must NOT be a program-owned output node
                            // (those must Materialize).
                            assert!(
                                !output_nodes.contains(&nid),
                                "{name} L{li}: computed output node {nid} written to a Slot, \
                                 must Materialize"
                            );
                        }
                        [Dst::Materialize { .. }] => {
                            total_materialize_outputs += 1;
                            assert!(
                                output_nodes.contains(&nid),
                                "{name} L{li}: non-output computed node {nid} Materialized; \
                                 only program-owned outputs may Materialize from base-arith"
                            );
                        }
                        _ => panic!("{name} L{li}: arith must have exactly one footer dst"),
                    }
                }

                // (a) Every multi-use computed intermediate that is NOT a program
                //     output must be emitted with a Slot dst (at least its primary
                //     emission). Build node -> set of dst kinds it received.
                let mut node_has_slot: HashMap<usize, bool> = HashMap::new();
                for (ins, node) in cf.program.instrs.iter().zip(&cf.instr_node) {
                    let Header::Arith { .. } = ins.header else { continue };
                    let nid = node.unwrap() as usize;
                    if matches!(ins.dsts.as_slice(), [Dst::Slot { .. }]) {
                        node_has_slot.insert(nid, true);
                    }
                }
                for (i, n) in arena.iter().enumerate() {
                    if is_computed(n) && pv.uses[i] >= 2 && !output_nodes.contains(&i) {
                        assert!(
                            *node_has_slot.get(&i).unwrap_or(&false),
                            "{name} L{li}: multi-use computed node {i} (uses={}) \
                             never received a Dst::Slot",
                            pv.uses[i]
                        );
                        total_multiuse_slot += 1;
                    }
                }

                // (b) Pass-through aliasing. Cached-Place alias set = Place nodes
                //     whose addr is produced by a same-layer cache (v1 cached_alias).
                let mut cache_out_addr: HashMap<GKRAddress, usize> = HashMap::new();
                for (ci, cache) in layer.caches.iter().enumerate() {
                    cache_out_addr.insert(cache.out.1, ci);
                }
                let mut alias_addrs: HashSet<GKRAddress> = HashSet::new();
                for n in arena.iter() {
                    if let ExprNode::Place { addr, .. } = n {
                        if cache_out_addr.contains_key(addr) {
                            alias_addrs.insert(*addr);
                            total_alias_nodes += 1;
                        }
                    }
                }
                // The matrix-table slot of each alias address == the slot the
                // producing cache materializes into. The ONLY instruction writing
                // that (slot,col) backing must be a `Dst::Materialize` (the cache),
                // never a base-arith Slot/Materialize keyed to the alias and never
                // a duplicate copy. base-arith writes Slots (cells), not matrix
                // backings, so there is structurally no base-arith write of an
                // alias backing — assert that holds.
                let alias_slots: HashSet<u8> = alias_addrs
                    .iter()
                    .filter_map(|a| cf.matrix_table.slot_for(a))
                    .collect();
                for (ins, node) in cf.program.instrs.iter().zip(&cf.instr_node) {
                    if !matches!(ins.header, Header::Arith { .. }) {
                        continue;
                    }
                    // No base-arith instr may Materialize into an alias backing.
                    for d in &ins.dsts {
                        if let Dst::Materialize { slot, .. } = d {
                            assert!(
                                !alias_slots.contains(slot),
                                "{name} L{li}: base-arith instr (node {:?}) materialized into \
                                 an alias cache backing slot {slot}",
                                node
                            );
                        }
                    }
                }
                // Alias-SPECIFIC pass-through proof: an alias (Cached Place) is
                // gathered inline (`Operand::Indirect`), so its exact backing
                // must NEVER appear as a staged-source `Operand::Affine` read.
                // Keyed on (slot, col) — not slot alone — because the joint
                // matrix table can coalesce several addresses onto one backing
                // slot, so a slot-only check would false-positive a legitimate
                // read of a non-alias address sharing that slot. An Affine read
                // of an alias backing would be a stale read (the producing cache
                // materializes AFTER the base-arith block), so this also guards
                // the forward ordering: base-arith must not consume a cache
                // output via a staged column.
                let alias_slot_cols: HashSet<(u8, u16)> = alias_addrs
                    .iter()
                    .filter_map(|a| {
                        cf.matrix_table.slot_for(a).map(|s| (s, cf.matrix_table.column_of(a)))
                    })
                    .collect();
                total_alias_backed += alias_slot_cols.len();
                for ins in &cf.program.instrs {
                    for op in &ins.operands {
                        match op {
                            Operand::Affine { slot, col } => assert!(
                                !alias_slot_cols.contains(&(*slot, *col)),
                                "{name} L{li}: alias backing (slot {slot}, col {col}) read via a \
                                 staged-source Affine — an alias must be a gather pass-through, \
                                 and base-arith must not read a not-yet-materialized cache output"
                            ),
                            // Gather path exercised (corpus-wide corroboration).
                            Operand::Indirect { .. } => total_indirect_for_alias += 1,
                            _ => {}
                        }
                    }
                }

                // (c) Scratch-prefill skip. No Instr2 may exist for a MaxQuadratic
                //     gate. Base-arith never lowers a gate (instr_node bound nodes
                //     are Sum/Product, asserted above), and `lower_gate` returns
                //     None for ScratchSkip — so the corpus must emit zero macro
                //     instrs attributable to MaxQuadratic. We assert the stronger,
                //     directly-checkable fact: every MaxQuadratic gate IS
                //     scratch-prefilled (so the kind-based skip is sound), and the
                //     macro lowering of each returns None.
                for gate in layer.gates.iter().chain(&layer.gates_external) {
                    if !matches!(gate.kind, GateKind::MaxQuadratic { .. }) {
                        continue;
                    }
                    total_maxq_gates += 1;
                    assert!(
                        gate_is_scratch_prefilled(gate),
                        "{name} L{li}: a non-scratch forward MaxQuadratic appeared — \
                         the kind-based ScratchSkip is no longer sound (spec §9 design item)"
                    );
                    total_maxq_scratch += 1;
                    // The macro lowering must not emit an instruction for it.
                    let cache_kinds = macros::cache_kind_by_addr(layer);
                    let consts = challenges::build_const_table_v2(layer);
                    let const_idx: HashMap<u32, u16> =
                        consts.iter().enumerate().map(|(i, c)| (*c, i as u16)).collect();
                    let mut mctx =
                        macros::MacroCtx::new(&cf.matrix_table, &const_idx, &cache_kinds);
                    assert!(
                        macros::lower_gate(gate, arena, &mut mctx).is_none(),
                        "{name} L{li}: scratch MaxQuadratic lowered to an Instr2 (must skip)"
                    );
                }
            }
        }

        // Non-vacuity: each phenomenon must actually occur in the corpus.
        assert!(
            total_multiuse_slot > 0,
            "(a) no multi-use computed intermediate landed in a Slot (vacuous)"
        );
        assert!(
            total_alias_nodes > 0,
            "(b) no Cached-Place pass-through alias in the corpus (vacuous)"
        );
        assert!(
            total_alias_backed > 0,
            "(b) no alias resolved to a matrix (slot,col) backing — the staged-Affine \
             pass-through guard never ran (vacuous)"
        );
        assert!(
            total_indirect_for_alias > 0,
            "(b) no alias consumed via gather (Indirect); pass-through path unexercised"
        );
        assert!(
            total_maxq_gates > 0,
            "(c) no MaxQuadratic gate in the corpus (scratch-skip test vacuous)"
        );
        assert_eq!(
            total_maxq_scratch, total_maxq_gates,
            "(c) some MaxQuadratic gate was not scratch-prefilled"
        );
        // `total_materialize_outputs` is 0 in the in-tree corpus (every program
        // output node is a native GateOutput); the Materialize arm is still
        // dst-kind-checked above whenever it fires, so a future computed-output
        // circuit is covered without making this assertion brittle today.
        let _ = total_materialize_outputs;
    }
}

/// Task 2.7: strand classification + isolation detection + per-strand split.
#[cfg(test)]
mod strand_tests {
    use super::*;
    use crate::isa_v2::{ArithOp, Dst, Header, Instr2, MemTup, Operand, Program2, RoutineId};
    use crate::test_support::all_fixtures;
    use cs::gkr_compiler::codegen_ir::CacheKind;
    use gkr_design_space::import::load_circuit;
    use std::collections::HashSet;

    /// Test-only structural validity: every `Operand::Slot { cell }` read by an
    /// instr in `prog` (in `operands` AND inside `memtup` roles/payload) has a
    /// `Dst::Slot { cell }` writer EARLIER in the SAME program. A per-strand
    /// program that fails this is reading a transient nobody in its own strand
    /// produced (the rereview-5 dangling-read failure mode).
    fn assert_no_dangling_slot_reads(prog: &Program2, s: Strand) {
        let mut written: HashSet<u8> = HashSet::new();
        for (i, instr) in prog.instrs.iter().enumerate() {
            for cell in slot_reads(instr) {
                assert!(
                    written.contains(&cell),
                    "{s:?} program instr {i} reads Slot cell {cell} with no earlier \
                     same-strand Dst::Slot writer (dangling cross-strand read)"
                );
            }
            for cell in slot_writes(instr) {
                written.insert(cell);
            }
        }
    }

    /// TEST 1. A rich cached fixture (L0 has BOTH a lookup cache AND a
    /// MemoryTuple cache) fuses into all THREE strands, the per-strand split is
    /// an exact partition by count, AND `isolation_ok` holds for every fixture ×
    /// layer (validating the routine→strand map fabricates no false dep).
    #[test]
    fn fused_partitions_into_three_strands() {
        // Resolve a rich fixture dynamically: scan the corpus, pick the first
        // whose L0 carries BOTH a lookup-family cache and a MemoryTuple cache.
        let fixtures = all_fixtures();
        let rich_path = fixtures
            .iter()
            .find(|p| {
                let name = match p.file_name().and_then(|n| n.to_str()) {
                    Some(n) => n,
                    None => return false,
                };
                if name.contains("no_caches") {
                    return false;
                }
                let c = match load_circuit(p) {
                    Ok(c) => c,
                    Err(_) => return false,
                };
                let Some(layer) = c.circuit.layers.first() else { return false };
                let mut has_lookup = false;
                let mut has_memory = false;
                for cache in &layer.caches {
                    match cache.kind {
                        CacheKind::MemoryTuple { .. } => has_memory = true,
                        CacheKind::SingleColumnLookup { .. }
                        | CacheKind::VectorizedLookup { .. }
                        | CacheKind::VectorizedLookupSetup => has_lookup = true,
                    }
                }
                has_lookup && has_memory
            })
            .expect("a fixture whose L0 has BOTH a lookup cache AND a MemoryTuple cache");
        let name = rich_path.file_name().unwrap().to_str().unwrap().to_string();
        let c = load_circuit(rich_path).unwrap_or_else(|e| panic!("load {name}: {e:?}"));
        let layer = &c.circuit.layers[0];
        let g = &c.graphs[0];

        let cf = compile_forward_v2(
            layer,
            g,
            FwdParams2 { emit_per_strand: true, ..FwdParams2::default() },
        );

        assert!(cf.isolation_ok, "{name} L0: fused isolation must hold");
        assert_eq!(
            cf.instr_strand.len(),
            cf.program.instrs.len(),
            "{name} L0: instr_strand must be instr-aligned"
        );

        // All three strands must appear in the fused tagging.
        let seen: HashSet<Strand> = cf.instr_strand.iter().copied().collect();
        for s in [Strand::BaseArith, Strand::LookupGp, Strand::MemoryGp] {
            assert!(seen.contains(&s), "{name} L0: strand {s:?} absent from fused program");
        }

        // Per-strand split is an EXACT partition by count.
        let per = cf.per_strand.as_ref().expect("emit_per_strand => per_strand Some");
        for (strand, prog) in &per.programs {
            let count = cf.instr_strand.iter().filter(|&&s| s == *strand).count();
            assert_eq!(
                prog.instrs.len(),
                count,
                "{name} L0: strand {strand:?} program length {} != fused count {count}",
                prog.instrs.len()
            );
            // Each per-strand program is independently valid (no dangling reads).
            assert_no_dangling_slot_reads(prog, *strand);
        }
        // The split covers every fused instr exactly once (sum of per-strand
        // lengths == fused length), since every instr is tagged with one strand.
        let split_total: usize = per.programs.iter().map(|(_, p)| p.instrs.len()).sum();
        assert_eq!(
            split_total,
            cf.program.instrs.len(),
            "{name} L0: per-strand split is not a partition of the fused program"
        );

        // Corpus-wide: isolation_ok must hold for ALL 22 fixtures × every layer.
        // A wrong routine→strand map would fabricate a false cross-strand Slot
        // dep and flip this to false somewhere.
        assert_eq!(fixtures.len(), 22, "expected the 22-fixture corpus");
        for p in &fixtures {
            let fname = p.file_name().unwrap().to_str().unwrap().to_string();
            let c = load_circuit(p).unwrap_or_else(|e| panic!("load {fname}: {e:?}"));
            for (li, layer) in c.circuit.layers.iter().enumerate() {
                let Some(g) = c.graphs.get(li) else { continue };
                let cf = compile_forward_v2(layer, g, FwdParams2::default());
                assert!(
                    cf.isolation_ok,
                    "{fname} L{li}: isolation_ok must hold (routine→strand map \
                     fabricated a false cross-strand dep?)"
                );
            }
        }
    }

    /// TEST 2. A SYNTHETIC 3-instr program with a REAL cross-strand Slot dep is
    /// detected (`isolation_holds == false`), `split_into_strands` materializes
    /// the bridge so every per-strand program is dangling-read-free, and an
    /// all-`BaseArith` tagging of the same instrs IS isolated (proving the
    /// detector is not hardwired to false).
    #[test]
    fn isolation_detector_finds_real_cross_strand_dep_then_falls_back() {
        // instr0 (BaseArith): writes Slot cell 0.
        let instr0 = Instr2 {
            header: Header::Arith { op: ArithOp::Sum, arity: 2 },
            operands: vec![
                Operand::Affine { slot: 0, col: 1 },
                Operand::Affine { slot: 0, col: 2 },
            ],
            dsts: vec![Dst::Slot { e4: false, cell: 0 }],
            memtup: None,
        };
        // instr1 (LookupGp): reads Slot cell 0 (the cross-strand read) plus a
        // shared committed input; materializes its output.
        let instr1 = Instr2 {
            header: Header::Macro { routine: RoutineId::LookupExtPair as u8, n_operands: 2 },
            operands: vec![
                Operand::Slot { e4: false, cell: 0 },
                Operand::Affine { slot: 1, col: 0 },
            ],
            dsts: vec![Dst::Materialize { slot: 2, col: 0 }],
            memtup: None,
        };
        // instr2 (MemoryGp): a memory-tuple macro reading only committed columns.
        let instr2 = Instr2 {
            header: Header::Macro { routine: RoutineId::MemoryTuple as u8, n_operands: 1 },
            operands: vec![],
            dsts: vec![Dst::Materialize { slot: 3, col: 0 }],
            memtup: Some(MemTup {
                roles: vec![(0u8, Operand::Affine { slot: 4, col: 0 })],
                as_arm: 0,
                as_payload: None,
                consts: Vec::new(),
            }),
        };

        let program = Program2 {
            instrs: vec![instr0, instr1, instr2],
            consts: Vec::new(),
            n_slot_cells: 1,
            n_matrix_slots: 5,
        };

        // Real strand tags: instr1 (LookupGp) reads a Slot instr0 (BaseArith)
        // wrote => NOT isolated.
        let tags = vec![Strand::BaseArith, Strand::LookupGp, Strand::MemoryGp];
        assert!(
            !isolation_holds(&program, &tags),
            "LookupGp instr reading a BaseArith-written Slot must break isolation"
        );

        // The split must yield a program per strand, each independently valid:
        // the bridge cell is materialized by the producer and the consumer reads
        // it as an Affine backing (no dangling Slot read survives).
        let per = split_into_strands(&program, &tags);
        let strands_present: HashSet<Strand> = per.programs.iter().map(|(s, _)| *s).collect();
        for s in [Strand::BaseArith, Strand::LookupGp, Strand::MemoryGp] {
            assert!(strands_present.contains(&s), "split must emit a {s:?} program");
        }
        for (s, prog) in &per.programs {
            assert_no_dangling_slot_reads(prog, *s);
        }
        // The bridge actually fired: the LookupGp consumer no longer reads any
        // Slot (its cross-strand Slot read was rewritten to an Affine backing),
        // and a fresh scratch backing slot (>= original n_matrix_slots) was used.
        let lookup_prog = &per
            .programs
            .iter()
            .find(|(s, _)| *s == Strand::LookupGp)
            .expect("LookupGp program")
            .1;
        assert!(
            lookup_prog.instrs.iter().all(|i| slot_reads(i).is_empty()),
            "LookupGp consumer's cross-strand Slot read must be rewritten to Affine"
        );
        assert!(
            lookup_prog.instrs[0]
                .operands
                .iter()
                .any(|o| matches!(o, Operand::Affine { slot, .. } if *slot >= program.n_matrix_slots)),
            "consumer must read the bridge via a fresh scratch Affine backing"
        );
        // The BaseArith producer must have gained the bridge Materialize.
        let base_prog = &per
            .programs
            .iter()
            .find(|(s, _)| *s == Strand::BaseArith)
            .expect("BaseArith program")
            .1;
        assert!(
            base_prog.instrs[0].dsts.iter().any(
                |d| matches!(d, Dst::Materialize { slot, .. } if *slot >= program.n_matrix_slots)
            ),
            "producer must Materialize the bridged cell into the fresh backing"
        );

        // Detector is NOT hardwired to false: tagging ALL instrs BaseArith makes
        // the same program isolated (no cross-strand crossing).
        let all_base = vec![Strand::BaseArith; program.instrs.len()];
        assert!(
            isolation_holds(&program, &all_base),
            "an all-BaseArith tagging has no cross-strand Slot dep => isolated"
        );
    }

    /// Lock the routine→strand bucketing. The `isolation_holds` Slot-crossing
    /// oracle is BLIND to how macros are bucketed across LookupGp/MemoryGp,
    /// because production macro lowering never emits an `Operand::Slot` (it reads
    /// committed columns via `Affine`/`Indirect`/`Ldc`) — so the corpus-wide
    /// `isolation_ok == true` assertion cannot catch a Lookup↔Memory misbucket.
    /// This exhaustive table is that missing guard: any future edit to
    /// `routine_strand` that flips a routine forces a conscious update here.
    ///
    /// The bucketing is grounded in the cs/ GKR data-flow: the lookup argument
    /// accumulates via its OWN tree (the lookup pair/aggregate/gather family),
    /// while the grand-product cascade (`Product`/`MaskIdentity`/
    /// `GrandProductWithoutCaches`/`MaterializeGrandProductTerm` from
    /// `InitialGrandProduct*`/`TrivialProduct`/`MaskIntoIdentityProduct`, plus
    /// `MemoryTuple`/`MemoryInitTeardownPair`) serves the MEMORY permutation
    /// argument only — the two trees never cross-feed
    /// (cs/src/gkr_compiler/family_circuit.rs hands them as separate output
    /// lists). Hence the whole PROD cascade is `MemoryGp`.
    #[test]
    fn routine_strand_mapping_is_locked() {
        use crate::isa_v2::RoutineId::*;
        let expected = [
            (GateOutputFold, Strand::BaseArith),
            (Product, Strand::MemoryGp),
            (MaskIdentity, Strand::MemoryGp),
            (AggregateLookupPair, Strand::LookupGp),
            (LookupBasePair, Strand::LookupGp),
            (LookupExtPair, Strand::LookupGp),
            (LookupBaseMinusMult, Strand::LookupGp),
            (LookupExtMinusMult, Strand::LookupGp),
            (LookupCachedDens, Strand::LookupGp),
            (LookupUnbalancedBase, Strand::LookupGp),
            (LookupUnbalancedExt, Strand::LookupGp),
            (VectorLookupGate, Strand::LookupGp),
            (MaterializeSingleLookup, Strand::LookupGp),
            (LookupDecoderDensSetup, Strand::LookupGp),
            (GrandProductWithoutCaches, Strand::MemoryGp),
            (MaterializeGrandProductTerm, Strand::MemoryGp),
            (SingleColumnLookup, Strand::LookupGp),
            (VectorizedLookup, Strand::LookupGp),
            (VectorizedLookupSetup, Strand::LookupGp),
            (MemoryTuple, Strand::MemoryGp),
            (MemoryInitTeardownPair, Strand::MemoryGp),
        ];
        for (routine, strand) in expected {
            assert_eq!(
                routine_strand(routine),
                strand,
                "routine {routine:?} must map to {strand:?} (see cs/ data-flow note)"
            );
        }
        // Non-vacuity: the table must cover every dense RoutineId 0..=20 (a new
        // variant added to the enum without a row here is a coverage hole — the
        // `routine_strand` match is exhaustive so it compiles, but its strand
        // would be untested). Asserting the count pins the corpus of ids.
        assert_eq!(expected.len(), 21, "RoutineId has 21 dense variants (0..=20)");
    }
}
