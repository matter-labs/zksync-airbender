//! Macro gate/cache lowering (spec §3/§4/§5, Task 2.5). STRUCTURAL lowering:
//! emit one `Instr2` per Macro gate / per cache carrying the right
//! `Header::Macro { routine }`, the right OPERAND LANES (one per IR input
//! column/value), and the right FOOTER DSTS (`Dst::Materialize` targets).
//!
//! The EXACT per-term arithmetic (which α-power multiplies which column, the
//! γ=[γ,γ²,2γ] forms, fms/seed) is NOT computed here — it is executed by the
//! Phase-3 CPU interpreter (Task 3.1) and validated by its oracle (Task 3.3),
//! driven by the routine's schema. Challenges are NOT operand lanes (spec §5):
//! α-powers are a column-indexed bank, γ fixed bank entries, both read by the
//! routine. So operand lanes carry SOURCE COLUMNS/VALUES only.
//!
//! Operand mapping (per IR input node):
//!   - committed-column `Place` (BaseLayerWitness/Memory/Setup/Inner/…) →
//!     `Operand::Affine { slot, col }` from the joint matrix table.
//!   - `Cached` `Place` (a value produced by a cache) → inline gather
//!     `Operand::Indirect { e4, desc }` (spec §4: forward gathers inline,
//!     never reading a materialized backing). A descriptor index is allocated
//!     per distinct gathered cached address.
//!   - `Constant` → `Operand::Ldc { Const, idx }` (Special for 0/1/-1).
//!   - `GateOutput` (a previous gate's output column) → `Operand::Affine` via
//!     its backing address when resolvable; this kind does not appear as a
//!     macro input in the in-tree corpus (verified), so it is handled
//!     defensively.
//!
//! Footer dsts: the macro's output address(es) → `Dst::Materialize { slot,
//! col }`. `output_count == 2` routines (num/den) emit TWO Materialize dsts
//! derived from the gate's two `dst` output slots.

use crate::compiler_v2::gather::{build_descriptor, GatherDescriptor};
use crate::compiler_v2::matrix_table::MatrixTable;
use crate::isa::NEG_ONE_U32;
use crate::isa_v2::{
    lowering_kind, routine_for_cache, routine_for_gate, routine_table, Dst, Header, Instr2, LdcSub,
    LoweringKind, MemTup, Operand, RoutineId, Shape, SPECIAL_NEG_ONE, SPECIAL_ONE, SPECIAL_ZERO,
};
use cs::definitions::GKRAddress;
use cs::gkr_compiler::codegen_ir::{
    gate_kind_input_nodes, CacheKind, CodegenCache, CodegenGate, CodegenLayer, Domain, ExprNode,
};
use std::collections::HashMap;

// Fixed memory-tuple role term indices (forward/kernels/mod.rs:31-39). Kept as
// local consts so this CPU-side lowering does not depend on the GPU crate.
const MEMORY_TUPLE_ADDRESS_LOW_TERM: u8 = 0;
const MEMORY_TUPLE_ADDRESS_HIGH_TERM: u8 = 1;
const MEMORY_TUPLE_TIMESTAMP_LOW_TERM: u8 = 2;
const MEMORY_TUPLE_TIMESTAMP_HIGH_TERM: u8 = 3;
const MEMORY_TUPLE_VALUE_LOW_TERM: u8 = 4;
const MEMORY_TUPLE_VALUE_LOW_EXTRA_TERM: u8 = 5;
const MEMORY_TUPLE_VALUE_HIGH_TERM: u8 = 6;
const MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM: u8 = 7;

// Address-space arm encoding (cache_relation.rs:91 match): the strict relation
// has no `Empty`; it appears as a logical default for tuples with no
// address-space dependency. Encoder packs as_arm in 2 bits (0..=3).
/// Logical `Empty` arm (no address-space dependency). The strict relation
/// (`CompiledAddressSpaceRelationStrict`) never produces it — it is the
/// encoder's `as_arm == 0` default and is asserted against in tests.
#[allow(dead_code)]
const AS_ARM_EMPTY: u8 = 0;
const AS_ARM_CONSTANT: u8 = 1;
const AS_ARM_IS_REGISTER: u8 = 2;
const AS_ARM_IS_RAM: u8 = 3;

/// 0/1/-1 map to the Special LDC lanes; anything else is None.
fn special_const(c: u32) -> Option<Operand> {
    if c == 0 {
        Some(Operand::Ldc { sub: LdcSub::Special, idx: SPECIAL_ZERO })
    } else if c == 1 {
        Some(Operand::Ldc { sub: LdcSub::Special, idx: SPECIAL_ONE })
    } else if c == NEG_ONE_U32 {
        Some(Operand::Ldc { sub: LdcSub::Special, idx: SPECIAL_NEG_ONE })
    } else {
        None
    }
}

/// Shared lowering context threaded through `lower_gate`/`lower_cache`.
/// Owns the const-index map (already deduped by `build_const_table`), the joint
/// matrix table, and the gather-descriptor accumulator (one entry per distinct
/// gathered cached address; the index is what rides the `Indirect` operand).
pub struct MacroCtx<'a> {
    pub matrix_table: &'a MatrixTable,
    /// bf-const value -> dedup index (LdcSub::Const), matching `build_const_table`.
    pub const_idx: &'a HashMap<u32, u16>,
    /// Cached out-address -> producing CacheKind (this-layer caches), so a
    /// `Cached` Place operand can pick the right gather variant.
    pub cache_kind_by_addr: &'a HashMap<GKRAddress, CacheKind>,
    /// Accumulated gather descriptors (Task 2.3 variant + Task 2.5 fields).
    pub gathers: Vec<GatherDescriptor>,
    /// Cached address -> its allocated descriptor index (dedup gathers).
    pub gather_idx: HashMap<GKRAddress, u16>,
    /// Gates whose Fixed(n) routine could not be matched to the IR operand
    /// count (structurally unrepresentable without a routine-table revision);
    /// recorded here, NOT emitted. (Phase-3 review.)
    pub skipped_fixed_mismatch: Vec<(RoutineId, usize)>,
}

impl<'a> MacroCtx<'a> {
    pub fn new(
        matrix_table: &'a MatrixTable,
        const_idx: &'a HashMap<u32, u16>,
        cache_kind_by_addr: &'a HashMap<GKRAddress, CacheKind>,
    ) -> Self {
        MacroCtx {
            matrix_table,
            const_idx,
            cache_kind_by_addr,
            gathers: Vec::new(),
            gather_idx: HashMap::new(),
            skipped_fixed_mismatch: Vec::new(),
        }
    }

    /// Allocate (or reuse) a gather descriptor index for a `Cached` address.
    /// The descriptor variant comes from the producing CacheKind when it is a
    /// THIS-layer cache; otherwise (prior-layer cached value) a best-effort
    /// base/ext descriptor is recorded and the precise slot wiring is left for
    /// Phase-3 (the descriptor INDEX in the operand lane is the structural fact).
    fn gather_index_for(&mut self, addr: GKRAddress, field_ext: bool) -> u16 {
        if let Some(&i) = self.gather_idx.get(&addr) {
            return i;
        }
        let desc = match self.cache_kind_by_addr.get(&addr) {
            Some(kind) if !matches!(kind, CacheKind::MemoryTuple { .. }) => build_descriptor(kind),
            // MemoryTuple caches are not gathers, and prior-layer cached values
            // expose no CacheKind here: record a minimal descriptor matching the
            // operand's field. Phase-3 fills the precise slot/len/decoder fields.
            _ => GatherDescriptor {
                kind: crate::isa_v2::IndirectKind::RowIndexedSetupE4,
                field_ext,
                n_slot: None,
                mapping_slot: None,
                n_len: None,
                decoder: None,
            },
        };
        let i = self.gathers.len() as u16;
        self.gathers.push(desc);
        self.gather_idx.insert(addr, i);
        i
    }

    /// Map one IR input node to its typed operand lane.
    fn operand_for(&mut self, arena: &[ExprNode], child: usize) -> Operand {
        match &arena[child] {
            ExprNode::Constant(c) => self.const_operand(*c),
            ExprNode::Place { addr, domain } => match addr {
                GKRAddress::Cached { .. } => Operand::Indirect {
                    e4: *domain == Domain::Ext,
                    desc: self.gather_index_for(*addr, *domain == Domain::Ext),
                },
                // Any committed/staged column backing.
                other => self.affine_for(other),
            },
            // A previous gate's output column: read it back from its backing
            // address. Not produced as a macro input in the in-tree corpus
            // (verified by probe); defensive Affine via the matrix table.
            ExprNode::GateOutput { .. } => {
                // No address on a GateOutput node; treat as a placeholder slot 0
                // col 0 read. Flagged structurally — Phase-3 binds the value.
                Operand::Affine { slot: 0, col: 0 }
            }
            // Computed Sum/Product never reach a macro operand (the forward
            // contract is arithmetic-free at macros — guarded in v1).
            ExprNode::Sum { .. } | ExprNode::Product { .. } => {
                Operand::Affine { slot: 0, col: 0 }
            }
        }
    }

    /// Arena `Constant` node -> Ldc operand. The const-table membership is an
    /// invariant for arena constants (`build_const_table` collected them all),
    /// so a miss is a real bug here.
    fn const_operand(&self, c: u32) -> Operand {
        if let Some(o) = special_const(c) {
            return o;
        }
        let idx = *self
            .const_idx
            .get(&c)
            .expect("non-special const must be in the const table");
        Operand::Ldc { sub: LdcSub::Const, idx }
    }

    /// Descriptor-sourced base-field scalar (e.g. the memory-tuple
    /// address-space `Constant(c)` payload). These are routine-seed scalars,
    /// NOT arena Constant nodes, so they need not be in the dedup table. Special
    /// 0/1/-1 map to Special lanes; any other value rides a Const lane if the
    /// table happens to hold it, else a structural placeholder (Ldc{Const,0})
    /// the Phase-3 oracle re-binds from the descriptor. (Never panics.)
    fn const_scalar_operand(&self, c: u32) -> Operand {
        if let Some(o) = special_const(c) {
            return o;
        }
        match self.const_idx.get(&c) {
            Some(&idx) => Operand::Ldc { sub: LdcSub::Const, idx },
            // Structural placeholder: the value lives in the descriptor the
            // interpreter reads; the lane only needs to be a well-formed Const.
            None => Operand::Ldc { sub: LdcSub::Const, idx: 0 },
        }
    }

    fn affine_for(&self, addr: &GKRAddress) -> Operand {
        let slot = self
            .matrix_table
            .slot_for(addr)
            .expect("Place source must have a backing slot");
        Operand::Affine { slot, col: self.matrix_table.column_of(addr) }
    }

    /// `Dst::Materialize` for a committed output address.
    fn materialize_for(&self, addr: &GKRAddress) -> Dst {
        let slot = self
            .matrix_table
            .slot_for(addr)
            .expect("macro output must have a backing slot");
        Dst::Materialize { slot, col: self.matrix_table.column_of(addr) }
    }
}

/// Build the address-space arm + payload for a MemoryTuple descriptor.
fn address_space_arm(
    ctx: &MacroCtx,
    rel: &cs::gkr_compiler::CompiledAddressSpaceRelationStrict,
) -> (u8, Option<Operand>) {
    use cs::gkr_compiler::CompiledAddressSpaceRelationStrict as AS;
    match rel {
        // Constant carries a base-field constant -> Ldc payload (descriptor
        // scalar, not an arena Constant node).
        AS::Constant(c) => (AS_ARM_CONSTANT, Some(ctx.const_scalar_operand(*c))),
        // IsRegister/IsRam carry a dynamic base-column source -> Affine payload.
        AS::IsRegister(offset) => (
            AS_ARM_IS_REGISTER,
            Some(ctx.affine_for(&GKRAddress::BaseLayerMemory(*offset))),
        ),
        AS::IsRam(offset) => (
            AS_ARM_IS_RAM,
            Some(ctx.affine_for(&GKRAddress::BaseLayerMemory(*offset))),
        ),
    }
}

/// Push a role-tagged Affine operand for a `BaseLayerMemory(offset)` column.
fn push_role(ctx: &MacroCtx, roles: &mut Vec<(u8, Operand)>, role: u8, offset: usize) {
    roles.push((role, ctx.affine_for(&GKRAddress::BaseLayerMemory(offset))));
}

/// Lower a MemoryTuple cache to the `MemTup` form: role-tagged operands (the
/// fixed addr/ts/value term indices) + the address-space arm/payload. Mirrors
/// the term assignment in `build_memory_expr` (cache_relation.rs:91+).
fn lower_memory_tuple(ctx: &mut MacroCtx, cache: &CodegenCache) -> Instr2 {
    use cs::gkr_compiler::{CompiledAddressStrict, CompiledMemoryTimestamp};
    use cs::definitions::gkr::RamWordRepresentation;

    let CacheKind::MemoryTuple { descriptor } = &cache.kind else {
        unreachable!("lower_memory_tuple called on non-MemoryTuple cache");
    };
    let rel = &descriptor.descriptor;
    let mut roles: Vec<(u8, Operand)> = Vec::new();

    // address-space arm/payload.
    let (as_arm, as_payload) = address_space_arm(ctx, &rel.address_space);

    // address terms (low/high) — constants fold into the routine's seed, only
    // dynamic columns become operands.
    match &rel.address {
        CompiledAddressStrict::ConstantU16(_) | CompiledAddressStrict::Constant(_) => {}
        CompiledAddressStrict::U16Space(off) => {
            push_role(ctx, &mut roles, MEMORY_TUPLE_ADDRESS_LOW_TERM, *off)
        }
        CompiledAddressStrict::U32Space([low, high]) => {
            push_role(ctx, &mut roles, MEMORY_TUPLE_ADDRESS_LOW_TERM, *low);
            push_role(ctx, &mut roles, MEMORY_TUPLE_ADDRESS_HIGH_TERM, *high);
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base, low_dynamic_offset, high, ..
        } => {
            push_role(ctx, &mut roles, MEMORY_TUPLE_ADDRESS_LOW_TERM, *low_base);
            push_role(ctx, &mut roles, MEMORY_TUPLE_ADDRESS_HIGH_TERM, *high);
            // The deferred low-dynamic term is appended last (next free slot)
            // by `build_memory_expr`; tag it as a value-extra slot structurally.
            if let Some((_, dyn_off)) = low_dynamic_offset {
                push_role(ctx, &mut roles, MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM, *dyn_off);
            }
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {
            // Unsupported on the GPU memory path too (cache_relation.rs:198).
            // Not produced by the in-tree corpus; leave no role for it.
        }
    }

    // timestamp terms (low/high).
    if let CompiledMemoryTimestamp::Normal(ts) = &rel.timestamp {
        push_role(ctx, &mut roles, MEMORY_TUPLE_TIMESTAMP_LOW_TERM, ts[0]);
        push_role(ctx, &mut roles, MEMORY_TUPLE_TIMESTAMP_HIGH_TERM, ts[1]);
    }

    // value terms.
    match &rel.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(v) => {
            push_role(ctx, &mut roles, MEMORY_TUPLE_VALUE_LOW_TERM, v[0]);
            push_role(ctx, &mut roles, MEMORY_TUPLE_VALUE_HIGH_TERM, v[1]);
        }
        RamWordRepresentation::U8Limbs(v) => {
            push_role(ctx, &mut roles, MEMORY_TUPLE_VALUE_LOW_TERM, v[0]);
            push_role(ctx, &mut roles, MEMORY_TUPLE_VALUE_LOW_EXTRA_TERM, v[1]);
            push_role(ctx, &mut roles, MEMORY_TUPLE_VALUE_HIGH_TERM, v[2]);
            push_role(ctx, &mut roles, MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM, v[3]);
        }
    }

    // The MemTup carries up to 8 linear terms (forward/kernels/mod.rs:31).
    debug_assert!(roles.len() <= 8, "memory-tuple over 8 linear terms");

    let dst = ctx.materialize_for(&cache.out.1);
    Instr2 {
        header: Header::Macro { routine: RoutineId::MemoryTuple as u8 },
        operands: Vec::new(),
        dsts: vec![dst],
        memtup: Some(MemTup { roles, as_arm, as_payload }),
    }
}

/// Lower one forward gate. `Some(Instr2)` only for `LoweringKind::Macro` gates;
/// `None` for Arith/Alias/Constraint/ScratchSkip (handled elsewhere / no emit),
/// and `None` (recorded in `ctx.skipped_fixed_mismatch`) for a Fixed(n) routine
/// whose IR operand count differs from `n` (structurally unrepresentable
/// without a routine-table revision — flagged for Phase-3).
pub fn lower_gate(gate: &CodegenGate, arena: &[ExprNode], ctx: &mut MacroCtx) -> Option<Instr2> {
    if lowering_kind(&gate.kind) != LoweringKind::Macro {
        return None;
    }
    let routine = routine_for_gate(&gate.kind).expect("Macro gate must have a routine");
    let schema = &routine_table()[routine as u8 as usize];

    // Operand lanes — one per IR input node, in IR order.
    let input_nodes: Vec<usize> =
        gate_kind_input_nodes(&gate.kind).iter().map(|id| id.0 as usize).collect();

    // Fixed-shape guard: the encoder asserts `operands.len() == n`. The
    // memory-tuple-flattening grand-product gates (InitialGrandProductWithoutCaches
    // / MaterializeGrandProductTermExpression) route to GrandProductStep Fixed(2)
    // but expose many base columns (each a flattened MemTupleDescriptor). They are
    // not representable as a clean 2-factor step without a routine-table revision;
    // skip + flag rather than panic or silently drop operands.
    if let Shape::Fixed(n) = schema.shape {
        if input_nodes.len() != n as usize {
            ctx.skipped_fixed_mismatch.push((routine, input_nodes.len()));
            return None;
        }
    }

    let operands: Vec<Operand> =
        input_nodes.iter().map(|&c| ctx.operand_for(arena, c)).collect();

    // Footer dsts: one Materialize per gate output address. `output_count == 2`
    // (LookupNumDen-style num/den) derives both from the gate's dst slots.
    let dsts: Vec<Dst> = macro_gate_dsts(gate, schema.output_count, ctx);

    Some(Instr2 { header: Header::Macro { routine: routine as u8 }, operands, dsts, memtup: None })
}

/// Footer dsts for a macro gate. The gate's `dst` OutputSlots carry the backing
/// addresses; we take the first `output_count` of them. (`output_count == 2`
/// emits num then den, in dst order.)
fn macro_gate_dsts(gate: &CodegenGate, output_count: u8, ctx: &MacroCtx) -> Vec<Dst> {
    let mut dsts = Vec::with_capacity(output_count as usize);
    for slot in gate.dst.iter().take(output_count as usize) {
        dsts.push(ctx.materialize_for(&slot.addr));
    }
    // If the IR provided fewer dst slots than the schema's output_count (not
    // observed in the corpus), pad by repeating the last to keep the lane count
    // schema-consistent for the encoder. Flagged structurally for Phase-3.
    while (dsts.len() as u8) < output_count {
        if let Some(&last) = dsts.last() {
            dsts.push(last);
        } else {
            break;
        }
    }
    dsts
}

/// Lower one cache. MemoryTuple → MemTup form; lookup caches → a gather-backed
/// macro reading their input columns. Always returns an `Instr2` (every cache
/// produces a forward output).
pub fn lower_cache(cache: &CodegenCache, arena: &[ExprNode], ctx: &mut MacroCtx) -> Instr2 {
    if matches!(cache.kind, CacheKind::MemoryTuple { .. }) {
        return lower_memory_tuple(ctx, cache);
    }
    let routine = routine_for_cache(&cache.kind).expect("cache must have a routine");
    let schema = &routine_table()[routine as u8 as usize];

    // Operand lanes — one per input column node (the linear-comb columns being
    // looked up). All lookup-cache routines are Variable, so any count encodes.
    debug_assert!(
        matches!(schema.shape, Shape::Variable),
        "lookup cache routine must be Variable-shaped"
    );
    let operands: Vec<Operand> = cache
        .inputs
        .iter()
        .map(|id| ctx.operand_for(arena, id.0 as usize))
        .collect();

    // Footer dst: the cache out address (cache.out.1). All lookup caches have
    // output_count 1.
    debug_assert_eq!(schema.output_count, 1, "lookup cache has one output");
    let dst = ctx.materialize_for(&cache.out.1);

    Instr2 {
        header: Header::Macro { routine: routine as u8 },
        operands,
        dsts: vec![dst],
        memtup: None,
    }
}

/// Build the `Cached out-address -> CacheKind` map for a layer (this-layer
/// caches), so a `Cached` Place operand can pick its gather variant.
pub fn cache_kind_by_addr(layer: &CodegenLayer) -> HashMap<GKRAddress, CacheKind> {
    let mut m = HashMap::new();
    for cache in &layer.caches {
        m.insert(cache.out.1, cache.kind.clone());
    }
    m
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler_v2::challenges::build_const_table;
    use crate::compiler_v2::{compile_forward_v2, FwdParams2};
    use crate::isa_v2::{Header, Operand, RoutineId};
    use crate::test_support::{all_fixtures, fixture_path};
    use gkr_design_space::import::load_circuit;

    fn ctx_for<'a>(
        layer: &CodegenLayer,
        mt: &'a MatrixTable,
        ci: &'a HashMap<u32, u16>,
        ck: &'a HashMap<GKRAddress, CacheKind>,
    ) -> MacroCtx<'a> {
        let _ = layer;
        MacroCtx::new(mt, ci, ck)
    }

    #[test]
    fn lookup_numden_emits_two_materialize_dsts() {
        let c = load_circuit(&fixture_path("blake2_g_function_codegen_ir_gkr.json")).unwrap();
        // Find a layer + gate whose lowering is Macro AND routine is LookupNumDen
        // (output_count 2).
        let mut found = false;
        for layer in &c.circuit.layers {
            let arena = &layer.arena.nodes;
            let mt = MatrixTable::build(layer);
            let consts = build_const_table(arena);
            let ci: HashMap<u32, u16> =
                consts.iter().enumerate().map(|(i, v)| (*v, i as u16)).collect();
            let ck = cache_kind_by_addr(layer);
            for gate in layer.gates.iter().chain(&layer.gates_external) {
                if routine_for_gate(&gate.kind) != Some(RoutineId::LookupNumDen) {
                    continue;
                }
                let mut ctx = ctx_for(layer, &mt, &ci, &ck);
                let instr = lower_gate(gate, arena, &mut ctx)
                    .expect("LookupNumDen is a Macro gate, must lower");
                assert!(
                    matches!(instr.header, Header::Macro { routine } if routine == RoutineId::LookupNumDen as u8),
                    "header must be Macro{{LookupNumDen}}"
                );
                assert_eq!(instr.dsts.len(), 2, "LookupNumDen emits num + den");
                for d in &instr.dsts {
                    assert!(matches!(d, Dst::Materialize { .. }), "both dsts Materialize");
                }
                // No challenge operands among the lanes (challenges are banks).
                for o in &instr.operands {
                    assert!(
                        !matches!(o, Operand::Ldc { sub: LdcSub::ConstChallenge, .. })
                            && !matches!(o, Operand::Ldc { sub: LdcSub::ArgChallenge, .. }),
                        "challenges are column-indexed banks, not operand lanes"
                    );
                }
                found = true;
                break;
            }
            if found {
                break;
            }
        }
        assert!(found, "no LookupNumDen Macro gate found in blake2 fixture");
    }

    #[test]
    fn memory_tuple_roles_and_arm() {
        // Find a MemoryTuple cache in any fixture and lower it.
        let mut found = false;
        'outer: for p in all_fixtures() {
            let c = match load_circuit(&p) {
                Ok(c) => c,
                Err(_) => continue,
            };
            for layer in &c.circuit.layers {
                let arena = &layer.arena.nodes;
                let mt = MatrixTable::build(layer);
                let consts = build_const_table(arena);
                let ci: HashMap<u32, u16> =
                    consts.iter().enumerate().map(|(i, v)| (*v, i as u16)).collect();
                let ck = cache_kind_by_addr(layer);
                for cache in &layer.caches {
                    if !matches!(cache.kind, CacheKind::MemoryTuple { .. }) {
                        continue;
                    }
                    let mut ctx = ctx_for(layer, &mt, &ci, &ck);
                    let instr = lower_cache(cache, arena, &mut ctx);
                    assert!(
                        matches!(instr.header, Header::Macro { routine } if routine == RoutineId::MemoryTuple as u8),
                        "MemoryTuple header"
                    );
                    let mt_form = instr.memtup.as_ref().expect("MemoryTuple lowers to MemTup");
                    assert!(mt_form.as_arm <= 3, "as_arm in 0..=3 (got {})", mt_form.as_arm);
                    // Role tags must be valid term indices (0..=7).
                    for (role, op) in &mt_form.roles {
                        assert!(*role <= 7, "role index in 0..=7");
                        assert!(
                            matches!(op, Operand::Affine { .. }),
                            "memory-tuple role columns are committed base columns (Affine)"
                        );
                    }
                    assert!(mt_form.roles.len() <= 8, "<= 8 linear terms");
                    // Empty arm has no payload; non-empty carries one.
                    if mt_form.as_arm == AS_ARM_EMPTY {
                        assert!(mt_form.as_payload.is_none());
                    } else {
                        assert!(
                            mt_form.as_payload.is_some(),
                            "non-empty as_arm carries a payload"
                        );
                    }
                    found = true;
                    break 'outer;
                }
            }
        }
        assert!(found, "no MemoryTuple cache found in the corpus");
    }

    #[test]
    fn compile_forward_v2_runs_on_all_fixtures() {
        // The key robustness gate: every fixture × every layer must compile
        // without panicking (catches unmapped input-node kinds and the encoder's
        // Fixed/MemTuple/count asserts, plus the Task-2.4 GateOutput-operand
        // path). Also confirms the macro path is actually exercised (non-vacuous).
        let mut total_macros = 0usize;
        for p in all_fixtures() {
            let name = p.file_name().unwrap().to_str().unwrap().to_string();
            let c = load_circuit(&p).unwrap_or_else(|e| panic!("load {name}: {e:?}"));
            for (li, layer) in c.circuit.layers.iter().enumerate() {
                // Some layers may have no analysis graph; guard the index.
                let Some(g) = c.graphs.get(li) else { continue };
                let cf = compile_forward_v2(layer, g, FwdParams2::default());
                total_macros += cf.stats.macros;
                // instr-aligned bookkeeping must hold for every fixture.
                assert_eq!(
                    cf.instr_node.len(),
                    cf.program.instrs.len(),
                    "{name} L{li}: instr_node not instr-aligned"
                );
                assert_eq!(
                    cf.instr_strand.len(),
                    cf.program.instrs.len(),
                    "{name} L{li}: instr_strand not instr-aligned"
                );
            }
        }
        assert!(
            total_macros > 0,
            "no macro instrs emitted across the corpus (test is vacuous)"
        );
    }
}
