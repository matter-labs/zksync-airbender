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
//!
//! # R2 (Phase 2.5) LANE CONTRACT — per cache routine id (R3 consumes this)
//!
//! Before R2 the lowering const-folded the cache coefficients/constants away
//! (one operand per source column only), so the value was NOT reconstructible
//! from the lane stream. R2 emits those scalars as explicit recoverable `Ldc`
//! lanes (every non-special scalar is a real entry in `build_const_table_v2`, so
//! `Ldc{Const,idx}` resolves to the exact value — NEVER a placeholder). The
//! per-routine layouts below are decodable from the lane stream + the header
//! `n_operands` ALONE. Challenges remain banks, not lanes (spec §5): the α-power
//! for VectorizedLookup column `k` is implicit by group index `k`, and the
//! memory-tuple `perm_additive` + per-role permutation challenges are read by
//! role from the perm/additive bank.
//!
//! - **id 16 `SingleColumnLookup`** (Plain, base). `value = constant + Σ_j
//!   coeff_j·col_j` (bench_interp/tests.rs::indep_lincomb). Operands:
//!   `[Ldc(constant), Ldc(coeff_0), col_0, Ldc(coeff_1), col_1, …]`.
//!   `n_operands = 1 + 2·terms.len()`. Decode: lane 0 is the constant; thereafter
//!   consecutive `(Ldc coeff, column operand)` pairs to end of stream.
//!
//! - **id 17 `VectorizedLookup`** (Plain, mixed). `value = Σ_k α^k·(constant_k +
//!   Σ_j coeff·col)` (bench_interp/tests.rs::indep_vec_lookup); α^k is implicit by
//!   COLUMN index `k` (challenge bank, not a lane). The columns are a
//!   `Vec<LinearComb>` whose per-column term counts VARY (corpus: up to 4 distinct
//!   counts within one cache), so the layout is SELF-DESCRIBING: each column `k`
//!   contributes a group `[Ldc(term_count_k), Ldc(constant_k), Ldc(coeff_0),
//!   col_0, …]`. `n_operands = Σ_k (2 + 2·terms_k)`. Decode: read a `term_count`
//!   lane (an `Ldc` whose VALUE is the count — counts ≥ 2 are real const-table
//!   entries; 0/1 are Special), then a `constant` lane, then `term_count`
//!   `(coeff, column)` pairs; repeat until the stream is consumed (column index =
//!   group ordinal = `k`). The leading count lane per column is what makes the
//!   stream round-trip-decodable despite the varying term counts.
//!
//! - **id 18 `VectorizedLookupSetup`** (Plain, ext). The value is the row-indexed
//!   gather `n[gid]` (lookup_helpers.cuh:70), NOT a function of input columns.
//!   Operand: a SINGLE `Operand::Indirect { e4: true, desc }` whose descriptor is
//!   `IndirectKind::RowIndexedSetupE4` for the cache's own output address.
//!   `n_operands = 1`. Decode: resolve the gather to `n[gid]`.
//!
//! - **id 19 `MemoryTuple`** (MemTuple shape). `value = perm_additive +
//!   address_space_term + Σ_role chal[role]·(lane value or constant)`
//!   (bench_interp/tests.rs::indep_mem_tuple). The MemTup carries: (a) up to 8
//!   DYNAMIC role-tagged terms in `roles` (the GPU term slots; the header
//!   `n_operands == roles.len()`), each a base-column `Affine` tagged by its
//!   forward role index (0..=7); (b) the address-space `as_arm` (0 Empty / 1
//!   Constant / 2 IsRegister / 3 IsRam) + `as_payload` (Const `Ldc` for Constant,
//!   else an `Affine` column); (c) the R2 folded CONSTANTS in `consts`, each a
//!   `(MT_CONST_* role, Ldc value)` pair — the constant address term
//!   (`MT_CONST_ADDR_LOW`, folded under `chal(R_ADDR_LOW)`), the `timestamp_offset`
//!   (`MT_CONST_TS_LOW_OFFSET`, under `chal(R_TS_LOW)`), and the special-indirect
//!   `low_offset` (`MT_CONST_ADDR_LOW_OFFSET`) + dynamic-offset coefficient
//!   (`MT_CONST_ADDR_LOW_DYN_COEFF`, scaling its value-extra-slot column under
//!   `chal(R_ADDR_LOW)`). The `consts` block is self-described by a leading count
//!   lane in `encode2` (NOT the header `n_operands`). `perm_additive` and the
//!   per-role challenges are NOT lanes — R3 reads them from the perm/additive bank
//!   by role.

use crate::compiler_v2::gather::{
    build_descriptor, build_inits_td_high_addr_descriptor, GatherDescriptor,
};
use crate::compiler_v2::matrix_table::MatrixTable;
use crate::isa::NEG_ONE_U32;
use crate::isa_v2::{
    lowering_kind, routine_for_cache, routine_for_gate, routine_table, Dst, Header, Instr2, LdcSub,
    LoweringKind, MemTup, Operand, RoutineId, Shape, MT_CONST_ADDR_HIGH, MT_CONST_ADDR_LOW,
    MT_CONST_ADDR_LOW_DYN_COEFF, MT_CONST_ADDR_LOW_OFFSET, MT_CONST_TS_LOW_OFFSET, SPECIAL_NEG_ONE,
    SPECIAL_ONE, SPECIAL_ZERO,
};
use cs::definitions::GKRAddress;
use cs::gkr_compiler::codegen_ir::{
    gate_kind_input_nodes, CacheKind, CodegenCache, CodegenGate, CodegenLayer, Domain, ExprNode,
    GateKind, LinearComb, MemTupleDescriptor, NodeId,
};
use cs::gkr_compiler::InitsOrTeardownsTimestampAndValue;
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
                inits_td_set_idx: None,
            },
        };
        let i = self.gathers.len() as u16;
        self.gathers.push(desc);
        self.gather_idx.insert(addr, i);
        i
    }

    /// Mint a launcher-deferred `Operand::Indirect` for the id-20 high-address
    /// constant `inits_and_teardowns_top_bits[set_idx] << high_bits_offset`. The
    /// value is a prover-runtime scalar absent from the codegen IR, so it rides an
    /// `InitsTeardownsHighAddr` gather descriptor (base field) that Phase-5
    /// resolves; only the descriptor INDEX is structural here. Not deduped — each
    /// id-20 key tuple mints its own descriptor for its `set_idx`.
    fn inits_td_high_addr_operand(&mut self, set_idx: u8) -> Operand {
        let i = self.gathers.len() as u16;
        self.gathers.push(build_inits_td_high_addr_descriptor(set_idx));
        Operand::Indirect { e4: false, desc: i }
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

    /// Descriptor-sourced base-field scalar → a RECOVERABLE `Ldc` lane (R2). The
    /// memory-tuple address-space `Constant(c)` payload, the cache `LinearComb`
    /// coefficients/constants, and the memory-tuple folded constants are routine
    /// scalars, NOT arena Constant nodes — but `build_const_table_v2` now collects
    /// every one of them, so a non-special value MUST resolve to a real index.
    /// 0/1/-1 ride the Special lanes. A miss is a bug (the table augmentation
    /// dropped a scalar): R2 forbids placeholder lanes — the VALUE must be
    /// recoverable from the lane stream alone.
    fn const_scalar_operand(&self, c: u32) -> Operand {
        if let Some(o) = special_const(c) {
            return o;
        }
        let idx = *self
            .const_idx
            .get(&c)
            .expect("R2: cache/memtup scalar must be in the v2 const table");
        Operand::Ldc { sub: LdcSub::Const, idx }
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

/// Lower a MemoryTuple cache to the `MemTup` form: role-tagged DYNAMIC terms (the
/// fixed addr/ts/value term indices) + the address-space arm/payload + the R2
/// folded-CONSTANT lanes. Mirrors the term assignment in `build_memory_expr`
/// (cache_relation.rs:91+) AND the value semantics of
/// `bench_interp/tests.rs::indep_mem_tuple`.
///
/// R2: the GPU forward path folds the constant address term, the
/// `timestamp_offset`, and the special-indirect `low_offset` + dynamic-offset
/// coefficient into the tuple's permutation/additive seed, so they never occupy a
/// GPU term slot. They are dropped from `roles` (kept ≤ 8) and instead emitted as
/// `MemTup::consts` `(MT_CONST_* role, Ldc value)` lanes so R3 can reconstruct the
/// value. `perm_additive` + the per-role permutation challenges stay in the
/// challenge bank (read by role), NOT as lanes.
/// Build the `MemTup` (roles / as_arm / as_payload / consts) for ONE
/// `MemTupleDescriptor` (its `.descriptor` is the
/// `NoFieldSpecialMemoryContributionRelation`). Shared by the id-19 MemoryTuple
/// cache lowering and the id-14/id-15 grand-product gate lowerings (each tuple is
/// byte-identical to the id-19 cache combination). See `lower_memory_tuple` for
/// the R2 folded-constant contract.
fn mem_tup_from_descriptor(ctx: &mut MacroCtx, desc: &MemTupleDescriptor) -> MemTup {
    use cs::gkr_compiler::{CompiledAddressStrict, CompiledMemoryTimestamp};
    use cs::definitions::gkr::RamWordRepresentation;

    let rel = &desc.descriptor;
    let mut roles: Vec<(u8, Operand)> = Vec::new();
    // R2 folded-constant lanes (recoverable `Ldc` values, tagged by the perm
    // challenge that multiplies them).
    let mut consts: Vec<(u8, Operand)> = Vec::new();

    // address-space arm/payload.
    let (as_arm, as_payload) = address_space_arm(ctx, &rel.address_space);

    // address terms (low/high). Dynamic columns become role-tagged terms; the
    // constant address terms (`Constant`/`ConstantU16`) — previously dropped —
    // become an `MT_CONST_ADDR_LOW` lane (the GPU folds them into the seed,
    // multiplied by chal(R_ADDR_LOW): bench_interp/tests.rs:266-271).
    match &rel.address {
        CompiledAddressStrict::ConstantU16(c) => {
            consts.push((MT_CONST_ADDR_LOW, ctx.const_scalar_operand(*c as u32)));
        }
        CompiledAddressStrict::Constant(c) => {
            consts.push((MT_CONST_ADDR_LOW, ctx.const_scalar_operand(*c)));
        }
        CompiledAddressStrict::U16Space(off) => {
            push_role(ctx, &mut roles, MEMORY_TUPLE_ADDRESS_LOW_TERM, *off)
        }
        CompiledAddressStrict::U32Space([low, high]) => {
            push_role(ctx, &mut roles, MEMORY_TUPLE_ADDRESS_LOW_TERM, *low);
            push_role(ctx, &mut roles, MEMORY_TUPLE_ADDRESS_HIGH_TERM, *high);
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base, low_dynamic_offset, low_offset, high,
        } => {
            push_role(ctx, &mut roles, MEMORY_TUPLE_ADDRESS_LOW_TERM, *low_base);
            push_role(ctx, &mut roles, MEMORY_TUPLE_ADDRESS_HIGH_TERM, *high);
            // The deferred low-dynamic term: the column rides a value-extra term
            // slot (build_memory_expr appends it last); its COEFFICIENT
            // (`dyn_coeff`) is a folded constant scaling that column under
            // chal(R_ADDR_LOW) (bench_interp/tests.rs:291-295).
            if let Some((dyn_coeff, dyn_off)) = low_dynamic_offset {
                push_role(ctx, &mut roles, MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM, *dyn_off);
                consts.push((
                    MT_CONST_ADDR_LOW_DYN_COEFF,
                    ctx.const_scalar_operand(*dyn_coeff as u32),
                ));
            }
            // The constant low_offset folds into the seed under chal(R_ADDR_LOW)
            // (bench_interp/tests.rs:296).
            consts.push((MT_CONST_ADDR_LOW_OFFSET, ctx.const_scalar_operand(*low_offset)));
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {
            // Unsupported on the GPU memory path too (cache_relation.rs:198).
            // Not produced by the in-tree corpus; leave no role for it.
        }
    }

    // timestamp terms (low/high). The dynamic columns are role-tagged; the
    // constant `timestamp_offset` — previously dropped — becomes an
    // `MT_CONST_TS_LOW_OFFSET` lane (folded under chal(R_TS_LOW):
    // bench_interp/tests.rs:306).
    if let CompiledMemoryTimestamp::Normal(ts) = &rel.timestamp {
        push_role(ctx, &mut roles, MEMORY_TUPLE_TIMESTAMP_LOW_TERM, ts[0]);
        push_role(ctx, &mut roles, MEMORY_TUPLE_TIMESTAMP_HIGH_TERM, ts[1]);
        consts.push((
            MT_CONST_TS_LOW_OFFSET,
            ctx.const_scalar_operand(rel.timestamp_offset),
        ));
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

    // The MemTup carries up to 8 DYNAMIC linear terms (forward/kernels/mod.rs:31);
    // folded constants live in `consts`, NOT the 8 term slots.
    debug_assert!(roles.len() <= 8, "memory-tuple over 8 linear terms");

    MemTup { roles, as_arm, as_payload, consts }
}

/// Lower a MemoryTuple cache (id-19) to the single-tuple `Instr2`: one `MemTup`
/// built from the cache descriptor, materialized to the cache out address.
fn lower_memory_tuple(ctx: &mut MacroCtx, cache: &CodegenCache) -> Instr2 {
    let CacheKind::MemoryTuple { descriptor } = &cache.kind else {
        unreachable!("lower_memory_tuple called on non-MemoryTuple cache");
    };
    let memtup = mem_tup_from_descriptor(ctx, descriptor);
    let dst = ctx.materialize_for(&cache.out.1);
    // n_operands = the number of role-tagged DYNAMIC terms (carried in the
    // header). The folded-constant count is self-described in the serialization.
    let n_operands = memtup.roles.len() as u8;
    Instr2 {
        header: Header::Macro { routine: RoutineId::MemoryTuple as u8, n_operands },
        operands: Vec::new(),
        dsts: vec![dst],
        memtup: Some(memtup),
        memtup2: None,
    }
}

/// Teardown ts/value BaseLayerMemory column offsets for ONE id-20 key. The Init
/// arm carries `None` (its ts/value contributions are zero — evaluate_init only
/// folds the address terms); the Teardown arm carries the per-key `lhs_*`/`rhs_*`
/// offsets (inits_and_teardowns.rs evaluate_teardown).
struct TeardownCols {
    timestamp: [usize; cs::definitions::NUM_TIMESTAMP_COLUMNS_FOR_RAM],
    value: [usize; 2],
}

/// Build ONE id-20 KEY `MemTup`: `KEY(slot) = perm_additive + RAM(=1) +
/// chal(R_ADDR_LOW)·address_low + chal(R_ADDR_HIGH)·(address_high +
/// (top_bits<<shift)) [+ ts/value terms for the Teardown arm]`
/// (inits_and_teardowns.rs evaluate_init / evaluate_teardown). The address-space
/// arm is the RAM constant; `setup[0]`/`setup[1]` are the (Base) address_low /
/// address_high arena NodeIds; the high-bits `top_bits<<shift` constant is a
/// launcher-deferred `MT_CONST_ADDR_HIGH` const (prover-runtime, not in the IR).
///
/// KNOWN LIMITATION (Phase-5): `address_low`/`address_high` are the VIRTUAL setup
/// polys `InitsAndTeardownsLow`/`High`, which the matrix table collapses to the
/// SAME `Affine{slot,col}` (`column_offset` is 0 for every `VirtualSetup` and
/// both share one backing class), so the emitted ADDR_LOW and ADDR_HIGH lanes are
/// indistinguishable here. This is inherent to v2's `VirtualSetup` operand
/// encoding (not specific to id-20) and is INVISIBLE to the decomposition-only
/// oracle (interp + reference read the same staged bank for both). The Phase-5
/// GPU launcher — which computes the two virtual polys per row
/// (`Low=(row<<2)&0xffff`, `High=row>>14`) — is where the distinction (and the
/// `top_bits` resolution) actually lands. Tracked for the GPU bit-exact gate.
fn inits_teardowns_key_tuple(
    ctx: &mut MacroCtx,
    arena: &[ExprNode],
    setup: &[NodeId; 2],
    set_idx: usize,
    td_cols: Option<&TeardownCols>,
) -> MemTup {
    // address space is RAM (AddressSpaceType::RAM as u32 == 1).
    let ram = cs::definitions::gkr::AddressSpaceType::RAM as u32;
    let as_arm = AS_ARM_CONSTANT;
    let as_payload = Some(ctx.const_scalar_operand(ram));

    let mut roles: Vec<(u8, Operand)> = Vec::new();
    // address_low / address_high are the two (Base) setup NodeIds — resolved via
    // `operand_for` (arena NodeIds, NOT BaseLayerMemory offsets, so NOT push_role).
    roles.push((
        MEMORY_TUPLE_ADDRESS_LOW_TERM,
        ctx.operand_for(arena, setup[0].0 as usize),
    ));
    roles.push((
        MEMORY_TUPLE_ADDRESS_HIGH_TERM,
        ctx.operand_for(arena, setup[1].0 as usize),
    ));

    // Teardown arm only: timestamp + value terms (BaseLayerMemory offsets).
    if let Some(td) = td_cols {
        push_role(ctx, &mut roles, MEMORY_TUPLE_TIMESTAMP_LOW_TERM, td.timestamp[0]);
        push_role(ctx, &mut roles, MEMORY_TUPLE_TIMESTAMP_HIGH_TERM, td.timestamp[1]);
        push_role(ctx, &mut roles, MEMORY_TUPLE_VALUE_LOW_TERM, td.value[0]);
        push_role(ctx, &mut roles, MEMORY_TUPLE_VALUE_HIGH_TERM, td.value[1]);
    }

    // The high-bits constant `top_bits<<shift` folds under chal(R_ADDR_HIGH); its
    // value is prover-runtime, carried as a launcher-deferred Indirect operand.
    let consts = vec![(MT_CONST_ADDR_HIGH, ctx.inits_td_high_addr_operand(set_idx as u8))];

    MemTup { roles, as_arm, as_payload, consts }
}

/// Lower one forward gate. `Some(Instr2)` only for `LoweringKind::Macro` gates;
/// `None` for Arith/Alias/Constraint/ScratchSkip (handled elsewhere / no emit).
/// Every Macro gate now emits an `Instr2` whose `n_operands` is the actual IR
/// input operand count — the grand-product gates that flatten 4-14 columns lower
/// normally (no skip path; the operand count rides the header, not a Fixed(n)
/// shape).
///
/// Three GateKinds lower to a STRUCTURED tuple form (not the lossy flattened
/// operand path): id-14 `InitialGrandProductWithoutCaches` (product of two
/// inlined memory tuples), id-15 `MaterializeGrandProductTermExpression` (one
/// inlined memory tuple), id-20 `InitsOrTeardownsInitialPair` (product of two
/// inits/teardowns KEY tuples). They are matched BEFORE the generic path so the
/// tuple structure (address-space arm, role tags, folded constants) is preserved.
pub fn lower_gate(gate: &CodegenGate, arena: &[ExprNode], ctx: &mut MacroCtx) -> Option<Instr2> {
    if lowering_kind(&gate.kind) != LoweringKind::Macro {
        return None;
    }
    let routine = routine_for_gate(&gate.kind).expect("Macro gate must have a routine");
    let schema = &routine_table()[routine as u8 as usize];

    // STRUCTURED tuple lowerings (lossless) — matched before the generic flattened
    // operand path so the tuple structure survives for the interpreter (R4).
    match &gate.kind {
        // id-14: `out = tuple(input[0]) · tuple(input[1])` — two inlined memory
        // tuples, single ext product. Each tuple is byte-identical to id-19.
        GateKind::InitialGrandProductWithoutCaches { input } => {
            let t0 = mem_tup_from_descriptor(ctx, &input[0]);
            let t1 = mem_tup_from_descriptor(ctx, &input[1]);
            let n_operands = (t0.roles.len() + t1.roles.len()) as u8;
            let dsts = macro_gate_dsts(gate, 1, ctx);
            return Some(Instr2 {
                header: Header::Macro {
                    routine: RoutineId::GrandProductWithoutCaches as u8,
                    n_operands,
                },
                operands: Vec::new(),
                dsts,
                memtup: Some(t0),
                memtup2: Some(t1),
            });
        }
        // id-15: `out = tuple(input)` — materialize ONE inlined memory tuple
        // (identical to id-19, single output).
        GateKind::MaterializeGrandProductTermExpression { input } => {
            let t0 = mem_tup_from_descriptor(ctx, input);
            let n_operands = t0.roles.len() as u8;
            let dsts = macro_gate_dsts(gate, 1, ctx);
            return Some(Instr2 {
                header: Header::Macro {
                    routine: RoutineId::MaterializeGrandProductTerm as u8,
                    n_operands,
                },
                operands: Vec::new(),
                dsts,
                memtup: Some(t0),
                memtup2: None,
            });
        }
        // id-20: `out = KEY(lhs) · KEY(rhs)` — single ext product of two
        // inits/teardowns key tuples (output_count 1). Init vs Teardown is the
        // `timestamp_and_value` arm (Init => no ts/value cols; Teardown => the
        // per-key lhs/rhs ts/value offsets).
        GateKind::InitsOrTeardownsInitialPair {
            timestamp_and_value,
            setup,
            set_idxes,
        } => {
            let (lhs_cols, rhs_cols) = match timestamp_and_value {
                InitsOrTeardownsTimestampAndValue::Init => (None, None),
                InitsOrTeardownsTimestampAndValue::Teardown {
                    lhs_timestamp,
                    lhs_value,
                    rhs_timestamp,
                    rhs_value,
                } => (
                    Some(TeardownCols { timestamp: *lhs_timestamp, value: *lhs_value }),
                    Some(TeardownCols { timestamp: *rhs_timestamp, value: *rhs_value }),
                ),
            };
            let t0 = inits_teardowns_key_tuple(ctx, arena, setup, set_idxes[0], lhs_cols.as_ref());
            let t1 = inits_teardowns_key_tuple(ctx, arena, setup, set_idxes[1], rhs_cols.as_ref());
            let n_operands = (t0.roles.len() + t1.roles.len()) as u8;
            let dsts = macro_gate_dsts(gate, 1, ctx);
            return Some(Instr2 {
                header: Header::Macro {
                    routine: RoutineId::MemoryInitTeardownPair as u8,
                    n_operands,
                },
                operands: Vec::new(),
                dsts,
                memtup: Some(t0),
                memtup2: Some(t1),
            });
        }
        _ => {}
    }

    // Operand lanes — one per IR input node, in IR order. `n_operands` (the
    // operand count) rides the header; there is no count lane and no Fixed(n)
    // shape, so flattening grand-product gates lower with their true column count.
    let input_nodes: Vec<usize> =
        gate_kind_input_nodes(&gate.kind).iter().map(|id| id.0 as usize).collect();

    let operands: Vec<Operand> =
        input_nodes.iter().map(|&c| ctx.operand_for(arena, c)).collect();
    let n_operands = operands.len() as u8;

    // Footer dsts: one Materialize per gate output address. `output_count == 2`
    // (a lookup num/den pair) derives both from the gate's dst slots.
    let dsts: Vec<Dst> = macro_gate_dsts(gate, schema.output_count, ctx);

    Some(Instr2 {
        header: Header::Macro { routine: routine as u8, n_operands },
        operands,
        dsts,
        memtup: None,
        memtup2: None,
    })
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

/// Emit the operand lanes for one `LinearComb` column: lane 0 = `Ldc(constant)`,
/// then per term an `Ldc(coeff)` IMMEDIATELY FOLLOWED by the term's column
/// `Operand`. So `[Ldc(constant), Ldc(coeff_0), col_0, Ldc(coeff_1), col_1, …]`
/// (`1 + 2·terms.len()` lanes). R2: the coefficients + constant were previously
/// dropped (const-folded); they now ride recoverable `Ldc` lanes so R3 can
/// reconstruct `constant + Σ coeff·col` (bench_interp/tests.rs::indep_lincomb).
/// The term's source node is the `LinearComb.terms[j].1` NodeId (NOT the cache's
/// flattened `inputs` list, whose order is the dependency walk, not the column
/// walk).
fn push_lincomb_lanes(ctx: &mut MacroCtx, arena: &[ExprNode], col: &LinearComb, out: &mut Vec<Operand>) {
    out.push(ctx.const_scalar_operand(col.constant));
    for &(coeff, node) in &col.terms {
        out.push(ctx.const_scalar_operand(coeff));
        out.push(ctx.operand_for(arena, node.0 as usize));
    }
}

/// Lower one cache. MemoryTuple → MemTup form; lookup caches → a macro carrying
/// the column coefficients + the source columns (R2) or the setup gather. Always
/// returns an `Instr2` (every cache produces a forward output).
///
/// LANE CONTRACT (R3 consumes this — see the module-level doc):
///  - id 16 SingleColumnLookup: `[Ldc(constant), (Ldc(coeff), col)…]` for the one
///    column. `n_operands = 1 + 2·terms`.
///  - id 17 VectorizedLookup: per column k, a self-describing group
///    `[Ldc(term_count_k), Ldc(constant_k), (Ldc(coeff), col)…]`; α^k is implicit
///    by group index k (challenge bank, not a lane). `n_operands = Σ_k (2 + 2·terms_k)`.
///  - id 18 VectorizedLookupSetup: a SINGLE `Operand::Indirect` (RowIndexedSetupE4)
///    resolving the row-indexed gather `n[gid]` of the cache's own output.
pub fn lower_cache(cache: &CodegenCache, arena: &[ExprNode], ctx: &mut MacroCtx) -> Instr2 {
    if matches!(cache.kind, CacheKind::MemoryTuple { .. }) {
        return lower_memory_tuple(ctx, cache);
    }
    let routine = routine_for_cache(&cache.kind).expect("cache must have a routine");
    let schema = &routine_table()[routine as u8 as usize];
    debug_assert!(
        matches!(schema.shape, Shape::Plain),
        "lookup cache routine must be Plain-shaped"
    );

    let operands: Vec<Operand> = match &cache.kind {
        // id 16: one base column. value = constant + Σ coeff·col.
        CacheKind::SingleColumnLookup { column, .. } => {
            let mut ops = Vec::with_capacity(1 + 2 * column.terms.len());
            push_lincomb_lanes(ctx, arena, column, &mut ops);
            ops
        }
        // id 17: value = Σ_k α^k·(constant_k + Σ coeff·col). Self-describing per
        // column: a `Ldc(term_count_k)` lane, then the lincomb group. The count
        // lane lets R3 segment the stream unambiguously even though columns have
        // differing term counts (corpus: up to 4 distinct counts within one cache).
        CacheKind::VectorizedLookup { columns, .. } => {
            let mut ops = Vec::new();
            for col in columns {
                ops.push(ctx.const_scalar_operand(col.terms.len() as u32));
                push_lincomb_lanes(ctx, arena, col, &mut ops);
            }
            ops
        }
        // id 18: the value is the row-indexed setup gather n[gid] (NOT a function
        // of input columns); emit it as a single RowIndexedSetupE4 Indirect of the
        // cache's own output address so R3 resolves n[gid] (lookup_helpers.cuh:70).
        CacheKind::VectorizedLookupSetup => {
            vec![Operand::Indirect { e4: true, desc: ctx.gather_index_for(cache.out.1, true) }]
        }
        CacheKind::MemoryTuple { .. } => unreachable!("MemoryTuple handled above"),
    };
    let n_operands = operands.len() as u8;

    // Footer dst: the cache out address (cache.out.1). All lookup caches have
    // output_count 1.
    debug_assert_eq!(schema.output_count, 1, "lookup cache has one output");
    let dst = ctx.materialize_for(&cache.out.1);

    Instr2 {
        header: Header::Macro { routine: routine as u8, n_operands },
        operands,
        dsts: vec![dst],
        memtup: None,
        memtup2: None,
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
    use crate::compiler_v2::challenges::build_const_table_v2;
    use crate::compiler_v2::{compile_forward_v2, FwdParams2};
    use crate::isa::NEG_ONE_U32;
    use crate::isa_v2::{Header, LdcSub, Operand, RoutineId};
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

    /// Resolve an `Ldc` operand back to the base-field u32 it encodes, using the
    /// const table (Const lanes) and the fixed Special lanes (0/1/-1). Panics on
    /// a non-Ldc operand or an out-of-range Const index — exactly the property
    /// R2 must guarantee: every emitted coefficient/constant lane is a *value*,
    /// not a placeholder. `consts` is `build_const_table_v2(layer)`.
    fn ldc_value(op: &Operand, consts: &[u32]) -> u32 {
        match op {
            Operand::Ldc { sub: LdcSub::Special, idx } => match *idx {
                SPECIAL_ZERO => 0,
                SPECIAL_ONE => 1,
                SPECIAL_NEG_ONE => NEG_ONE_U32,
                other => panic!("unknown Special idx {other}"),
            },
            Operand::Ldc { sub: LdcSub::Const, idx } => consts
                .get(*idx as usize)
                .copied()
                .unwrap_or_else(|| panic!("Const idx {idx} out of table (len {})", consts.len())),
            other => panic!("expected an Ldc lane, got {other:?}"),
        }
    }

    // R4: the three grand-product/inits-teardowns gates must lower LOSSLESSLY to
    // structured memory tuples (NOT the old flattened-operand path with
    // `memtup: None`). id-14/id-20 carry TWO tuples (product); id-15 one. id-20's
    // KEY tuples use the RAM `as_arm` constant + the launcher-deferred
    // MT_CONST_ADDR_HIGH high-bits const. This locks the lossless property the
    // corpus-wide round-trip relies on, per emitting fixture.
    #[test]
    fn grand_product_and_inits_teardowns_lower_losslessly() {
        use crate::isa_v2::MT_CONST_ADDR_HIGH;
        let mut saw_14 = false;
        let mut saw_15 = false;
        let mut saw_20 = false;
        for p in all_fixtures() {
            let c = load_circuit(&p).unwrap();
            for layer in &c.circuit.layers {
                let arena = &layer.arena.nodes;
                let mt = MatrixTable::build(layer);
                let consts = build_const_table_v2(layer);
                let ci: HashMap<u32, u16> =
                    consts.iter().enumerate().map(|(i, v)| (*v, i as u16)).collect();
                let ck = cache_kind_by_addr(layer);
                for gate in layer.gates.iter().chain(&layer.gates_external) {
                    let Some(routine) = routine_for_gate(&gate.kind) else { continue };
                    let is_target = matches!(
                        routine,
                        RoutineId::GrandProductWithoutCaches
                            | RoutineId::MaterializeGrandProductTerm
                            | RoutineId::MemoryInitTeardownPair
                    );
                    if !is_target {
                        continue;
                    }
                    let mut ctx = MacroCtx::new(&mt, &ci, &ck);
                    let instr = lower_gate(gate, arena, &mut ctx).expect("target gate must lower");
                    assert!(instr.operands.is_empty(), "memtup gate carries no operand lanes");
                    // Presence of the primary tuple is the lossless invariant; a
                    // memory tuple with an all-constant address/value legitimately
                    // carries ZERO dynamic role terms (everything folds into
                    // `as_arm`/`consts`), so don't require non-empty roles.
                    let _t0 = instr.memtup.as_ref().expect("primary tuple must be present");
                    assert_eq!(instr.dsts.len(), 1, "single ext output");
                    match routine {
                        RoutineId::MaterializeGrandProductTerm => {
                            assert!(instr.memtup2.is_none(), "id-15 is single-tuple");
                            saw_15 = true;
                        }
                        RoutineId::GrandProductWithoutCaches => {
                            assert!(instr.memtup2.is_some(), "id-14 product needs two tuples");
                            saw_14 = true;
                        }
                        RoutineId::MemoryInitTeardownPair => {
                            let t1 = instr.memtup2.as_ref().expect("id-20 product needs two tuples");
                            for t in [_t0, t1] {
                                assert_eq!(t.as_arm, AS_ARM_CONSTANT, "id-20 key uses the RAM arm");
                                let hi: Vec<_> = t
                                    .consts
                                    .iter()
                                    .filter(|(r, _)| *r == MT_CONST_ADDR_HIGH)
                                    .collect();
                                assert_eq!(hi.len(), 1, "exactly one high-bits const per key");
                                assert!(
                                    matches!(hi[0].1, Operand::Indirect { .. }),
                                    "high-bits is a launcher-deferred Indirect"
                                );
                            }
                            saw_20 = true;
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }
        assert!(saw_14, "corpus emits no id-14 (test vacuous)");
        assert!(saw_15, "corpus emits no id-15 (test vacuous)");
        assert!(saw_20, "corpus emits no id-20 (test vacuous)");
    }

    #[test]
    fn lookup_pair_emits_two_materialize_dsts() {
        let c = load_circuit(&fixture_path("blake2_g_function_codegen_ir_gkr.json")).unwrap();
        // Find a layer + gate whose lowering is Macro AND whose routine is a
        // lookup num/den pair (output_count == 2) — post-R1 the single lossy
        // `LookupNumDen` id fans out to several formula ids (LookupBasePair,
        // LookupExtPair, …); any of them must still emit num + den.
        let mut found = false;
        for layer in &c.circuit.layers {
            let arena = &layer.arena.nodes;
            let mt = MatrixTable::build(layer);
            let consts = build_const_table_v2(layer);
            let ci: HashMap<u32, u16> =
                consts.iter().enumerate().map(|(i, v)| (*v, i as u16)).collect();
            let ck = cache_kind_by_addr(layer);
            for gate in layer.gates.iter().chain(&layer.gates_external) {
                let Some(routine) = routine_for_gate(&gate.kind) else { continue };
                // Restrict to the lookup-pair (num/den) ids: output_count 2 AND a
                // lookup-family routine (not the aggregate or memory-init pair).
                if routine_table()[routine as usize].output_count != 2 {
                    continue;
                }
                if !matches!(
                    routine,
                    RoutineId::LookupBasePair
                        | RoutineId::LookupExtPair
                        | RoutineId::LookupBaseMinusMult
                        | RoutineId::LookupExtMinusMult
                        | RoutineId::LookupCachedDens
                        | RoutineId::LookupUnbalancedBase
                        | RoutineId::LookupUnbalancedExt
                        | RoutineId::LookupDecoderDensSetup
                ) {
                    continue;
                }
                let mut ctx = ctx_for(layer, &mt, &ci, &ck);
                let instr = lower_gate(gate, arena, &mut ctx)
                    .expect("lookup-pair is a Macro gate, must lower");
                assert!(
                    matches!(instr.header, Header::Macro { routine: r, .. } if r == routine as u8),
                    "header must be Macro{{lookup pair}}"
                );
                assert_eq!(instr.dsts.len(), 2, "lookup pair emits num + den");
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
        assert!(found, "no lookup-pair Macro gate found in blake2 fixture");
    }

    #[test]
    fn memory_tuple_roles_and_arm() {
        use crate::isa_v2::{
            MT_CONST_ADDR_LOW, MT_CONST_ADDR_LOW_DYN_COEFF, MT_CONST_ADDR_LOW_OFFSET,
            MT_CONST_TS_LOW_OFFSET,
        };
        use cs::gkr_compiler::{CompiledAddressStrict, CompiledMemoryTimestamp};

        // Lower EVERY MemoryTuple cache in the corpus and check the dynamic
        // role-tagged terms (≤ 8 Affine columns) AND the R2 folded-CONSTANT lanes
        // (recoverable `Ldc` values tagged by a `MT_CONST_*` role).
        let mut found = false;
        // Non-vacuity: at least one memtup must carry each folded-constant kind.
        let mut saw_addr_const = false;
        let mut saw_ts_offset = false;
        let mut saw_indirect_offset = false;
        let mut saw_indirect_dyn = false;
        for p in all_fixtures() {
            let c = match load_circuit(&p) {
                Ok(c) => c,
                Err(_) => continue,
            };
            for layer in &c.circuit.layers {
                let arena = &layer.arena.nodes;
                let mt = MatrixTable::build(layer);
                let consts = build_const_table_v2(layer);
                let ci: HashMap<u32, u16> =
                    consts.iter().enumerate().map(|(i, v)| (*v, i as u16)).collect();
                let ck = cache_kind_by_addr(layer);
                for cache in &layer.caches {
                    let CacheKind::MemoryTuple { descriptor } = &cache.kind else { continue };
                    let rel = &descriptor.descriptor;
                    let mut ctx = ctx_for(layer, &mt, &ci, &ck);
                    let instr = lower_cache(cache, arena, &mut ctx);
                    assert!(
                        matches!(instr.header, Header::Macro { routine, .. } if routine == RoutineId::MemoryTuple as u8),
                        "MemoryTuple header"
                    );
                    let mt_form = instr.memtup.as_ref().expect("MemoryTuple lowers to MemTup");
                    assert!(mt_form.as_arm <= 3, "as_arm in 0..=3 (got {})", mt_form.as_arm);
                    // n_operands carries the DYNAMIC term count only (header).
                    if let Header::Macro { n_operands, .. } = instr.header {
                        assert_eq!(
                            n_operands as usize,
                            mt_form.roles.len(),
                            "memtup n_operands == dynamic role count (consts are out-of-band)"
                        );
                    }
                    // Role tags must be valid term indices (0..=7) on Affine cols.
                    for (role, op) in &mt_form.roles {
                        assert!(*role <= 7, "role index in 0..=7");
                        assert!(
                            matches!(op, Operand::Affine { .. }),
                            "memory-tuple role columns are committed base columns (Affine)"
                        );
                    }
                    assert!(mt_form.roles.len() <= 8, "<= 8 dynamic linear terms");
                    // Empty arm has no payload; non-empty carries one.
                    if mt_form.as_arm == AS_ARM_EMPTY {
                        assert!(mt_form.as_payload.is_none());
                    } else {
                        assert!(
                            mt_form.as_payload.is_some(),
                            "non-empty as_arm carries a payload"
                        );
                    }
                    // R2 folded constants: each is a recoverable `Ldc` value on a
                    // known `MT_CONST_*` role.
                    for (role, op) in &mt_form.consts {
                        assert!(
                            matches!(
                                *role,
                                MT_CONST_ADDR_LOW
                                    | MT_CONST_ADDR_LOW_OFFSET
                                    | MT_CONST_ADDR_LOW_DYN_COEFF
                                    | MT_CONST_TS_LOW_OFFSET
                            ),
                            "unknown memtup const role {role}"
                        );
                        assert!(
                            matches!(op, Operand::Ldc { .. }),
                            "folded constant lanes are Ldc (value recoverable)"
                        );
                    }
                    // Cross-check the const lanes against the descriptor: every
                    // expected folded constant must appear with the right value.
                    let val_of = |role: u8| -> Option<u32> {
                        mt_form
                            .consts
                            .iter()
                            .find(|(r, _)| *r == role)
                            .map(|(_, op)| ldc_value(op, &consts))
                    };
                    match &rel.address {
                        CompiledAddressStrict::ConstantU16(c) => {
                            assert_eq!(val_of(MT_CONST_ADDR_LOW), Some(*c as u32));
                            saw_addr_const = true;
                        }
                        CompiledAddressStrict::Constant(c) => {
                            assert_eq!(val_of(MT_CONST_ADDR_LOW), Some(*c));
                            saw_addr_const = true;
                        }
                        CompiledAddressStrict::U32SpaceSpecialIndirect {
                            low_dynamic_offset,
                            low_offset,
                            ..
                        } => {
                            assert_eq!(val_of(MT_CONST_ADDR_LOW_OFFSET), Some(*low_offset));
                            saw_indirect_offset = true;
                            if let Some((dyn_coeff, _)) = low_dynamic_offset {
                                assert_eq!(
                                    val_of(MT_CONST_ADDR_LOW_DYN_COEFF),
                                    Some(*dyn_coeff as u32)
                                );
                                saw_indirect_dyn = true;
                            }
                        }
                        _ => {}
                    }
                    if let CompiledMemoryTimestamp::Normal(_) = &rel.timestamp {
                        assert_eq!(val_of(MT_CONST_TS_LOW_OFFSET), Some(rel.timestamp_offset));
                        saw_ts_offset = true;
                    }
                    found = true;
                }
            }
        }
        assert!(found, "no MemoryTuple cache found in the corpus");
        assert!(saw_addr_const, "no constant-address memtup (folded-const test vacuous)");
        assert!(saw_ts_offset, "no normal-timestamp memtup (ts-offset const test vacuous)");
        assert!(saw_indirect_offset, "no special-indirect memtup (low_offset test vacuous)");
        assert!(saw_indirect_dyn, "no special-indirect dyn-offset memtup (dyn-coeff test vacuous)");
    }

    #[test]
    fn single_column_lookup_emits_constant_and_coeff_lanes() {
        // id 16: operands = [Ldc(constant), (Ldc(coeff), col)…]; the value
        // `constant + Σ coeff·col` must be reconstructible from the lanes alone
        // (bench_interp/tests.rs::indep_lincomb). Lower every such cache and check
        // the layout + that each coeff/constant resolves to its descriptor value.
        let mut found = false;
        for p in all_fixtures() {
            let Ok(c) = load_circuit(&p) else { continue };
            for layer in &c.circuit.layers {
                let arena = &layer.arena.nodes;
                let mt = MatrixTable::build(layer);
                let consts = build_const_table_v2(layer);
                let ci: HashMap<u32, u16> =
                    consts.iter().enumerate().map(|(i, v)| (*v, i as u16)).collect();
                let ck = cache_kind_by_addr(layer);
                for cache in &layer.caches {
                    let CacheKind::SingleColumnLookup { column, .. } = &cache.kind else { continue };
                    let mut ctx = ctx_for(layer, &mt, &ci, &ck);
                    let instr = lower_cache(cache, arena, &mut ctx);
                    let Header::Macro { routine, n_operands } = instr.header else {
                        panic!("SingleColumnLookup must lower to a Macro header");
                    };
                    assert_eq!(routine, RoutineId::SingleColumnLookup as u8);
                    assert_eq!(
                        n_operands as usize,
                        1 + 2 * column.terms.len(),
                        "id16 layout: 1 const + 2 lanes per term"
                    );
                    assert_eq!(n_operands as usize, instr.operands.len());
                    // lane 0 = constant.
                    assert_eq!(ldc_value(&instr.operands[0], &consts), column.constant);
                    // per term: (Ldc coeff, column operand).
                    for (j, &(coeff, _node)) in column.terms.iter().enumerate() {
                        let coeff_lane = &instr.operands[1 + 2 * j];
                        let col_lane = &instr.operands[1 + 2 * j + 1];
                        assert_eq!(ldc_value(coeff_lane, &consts), coeff, "coeff lane {j}");
                        assert!(
                            !matches!(col_lane, Operand::Ldc { sub: LdcSub::Const, .. })
                                || ldc_value(col_lane, &consts) == coeff,
                            "column lane must be a source operand, not the coeff again"
                        );
                    }
                    found = true;
                }
            }
        }
        assert!(found, "no SingleColumnLookup cache in the corpus (test vacuous)");
    }

    #[test]
    fn vectorized_lookup_emits_self_describing_column_groups() {
        // id 17: per column k a group [Ldc(term_count_k), Ldc(constant_k),
        // (Ldc(coeff), col)…]. Decode the stream using ONLY the count lanes +
        // n_operands and confirm it segments into exactly `columns.len()` groups
        // matching each column's term count, constant, and coefficients.
        let mut found = false;
        let mut saw_varying = false; // a cache with >1 distinct term count
        for p in all_fixtures() {
            let Ok(c) = load_circuit(&p) else { continue };
            for layer in &c.circuit.layers {
                let arena = &layer.arena.nodes;
                let mt = MatrixTable::build(layer);
                let consts = build_const_table_v2(layer);
                let ci: HashMap<u32, u16> =
                    consts.iter().enumerate().map(|(i, v)| (*v, i as u16)).collect();
                let ck = cache_kind_by_addr(layer);
                for cache in &layer.caches {
                    let CacheKind::VectorizedLookup { columns, .. } = &cache.kind else { continue };
                    let mut ctx = ctx_for(layer, &mt, &ci, &ck);
                    let instr = lower_cache(cache, arena, &mut ctx);
                    let Header::Macro { routine, n_operands } = instr.header else {
                        panic!("VectorizedLookup must lower to a Macro header");
                    };
                    assert_eq!(routine, RoutineId::VectorizedLookup as u8);
                    let expected: usize =
                        columns.iter().map(|col| 2 + 2 * col.terms.len()).sum();
                    assert_eq!(n_operands as usize, expected, "id17 group layout");
                    assert_eq!(n_operands as usize, instr.operands.len());

                    let distinct: std::collections::BTreeSet<usize> =
                        columns.iter().map(|col| col.terms.len()).collect();
                    if distinct.len() > 1 {
                        saw_varying = true;
                    }

                    // SELF-DESCRIBING DECODE: walk the stream using only count
                    // lanes + n_operands; reconstruct the column segmentation and
                    // match it against the descriptor columns.
                    let ops = &instr.operands;
                    let mut pos = 0usize;
                    for (k, col) in columns.iter().enumerate() {
                        let term_count = ldc_value(&ops[pos], &consts) as usize;
                        pos += 1;
                        assert_eq!(term_count, col.terms.len(), "col {k} term-count lane");
                        let constant = ldc_value(&ops[pos], &consts);
                        pos += 1;
                        assert_eq!(constant, col.constant, "col {k} constant lane");
                        for (j, &(coeff, _)) in col.terms.iter().enumerate() {
                            assert_eq!(
                                ldc_value(&ops[pos], &consts),
                                coeff,
                                "col {k} term {j} coeff lane"
                            );
                            pos += 1; // coeff
                            pos += 1; // column operand
                        }
                    }
                    assert_eq!(pos, ops.len(), "decode consumed exactly n_operands lanes");
                    found = true;
                }
            }
        }
        assert!(found, "no VectorizedLookup cache in the corpus (test vacuous)");
        assert!(
            saw_varying,
            "no VectorizedLookup with varying per-column term counts — the count-lane \
             scheme would be untested (the self-describing requirement is the whole point)"
        );
    }

    #[test]
    fn vectorized_lookup_setup_emits_row_indexed_gather() {
        // id 18: the value is the row-indexed setup gather n[gid], not a function
        // of input columns; it must lower to a SINGLE RowIndexedSetupE4 Indirect.
        use crate::isa_v2::IndirectKind;
        let mut found = false;
        for p in all_fixtures() {
            let Ok(c) = load_circuit(&p) else { continue };
            for layer in &c.circuit.layers {
                let arena = &layer.arena.nodes;
                let mt = MatrixTable::build(layer);
                let consts = build_const_table_v2(layer);
                let ci: HashMap<u32, u16> =
                    consts.iter().enumerate().map(|(i, v)| (*v, i as u16)).collect();
                let ck = cache_kind_by_addr(layer);
                for cache in &layer.caches {
                    if !matches!(cache.kind, CacheKind::VectorizedLookupSetup) {
                        continue;
                    }
                    let mut ctx = ctx_for(layer, &mt, &ci, &ck);
                    let instr = lower_cache(cache, arena, &mut ctx);
                    let Header::Macro { routine, n_operands } = instr.header else {
                        panic!("VectorizedLookupSetup must lower to a Macro header");
                    };
                    assert_eq!(routine, RoutineId::VectorizedLookupSetup as u8);
                    assert_eq!(n_operands, 1, "setup gather is a single Indirect lane");
                    let Operand::Indirect { e4, desc } = instr.operands[0] else {
                        panic!("setup operand must be Indirect, got {:?}", instr.operands[0]);
                    };
                    assert!(e4, "setup gather is ext (E4)");
                    assert_eq!(
                        ctx.gathers[desc as usize].kind,
                        IndirectKind::RowIndexedSetupE4,
                        "setup gather must be RowIndexedSetupE4"
                    );
                    found = true;
                }
            }
        }
        assert!(found, "no VectorizedLookupSetup cache in the corpus (test vacuous)");
    }

    #[test]
    fn compile_forward_v2_runs_on_all_fixtures() {
        // The key robustness gate: every fixture × every layer must compile
        // without panicking (catches unmapped input-node kinds and the encoder's
        // n_operands/MemTuple asserts, plus the Task-2.4 GateOutput-operand
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

    #[test]
    fn bounded_working_set_fits_slot_field() {
        // Fix B: the base-arith working set MUST fit the 7-bit slot-cell field
        // (`SLOT_CELL_BITS == 7` => cell index < 128). Order + Belady eviction +
        // rematerialization bound it; the default budget (120) sits under the
        // cap. Two halves so the bound is both correct AND non-vacuous:
        //   (1) load-bearing — some corpus layer's NATURAL (un-evicted) live set
        //       exceeds the field cap, so eviction is doing real work. Measured
        //       at budget 200: large enough that no eviction fires below the cap,
        //       small enough that cell indices stay < 256 (so the `cell as u8`
        //       store is lossless and `high_water_cells` is trustworthy). A huge
        //       budget would overflow u8 and corrupt the counter — see mod.rs.
        //   (2) bounded — under the default budget EVERY layer's high-water and
        //       EVERY emitted Slot cell index fit the field.
        use crate::isa_v2::{Dst, SLOT_CELL_BITS};
        let cell_cap = 1u32 << SLOT_CELL_BITS; // 128

        let mut max_natural = 0usize;
        let mut any_slots = false;
        for p in all_fixtures() {
            let Ok(c) = load_circuit(&p) else { continue };
            let name = p.file_name().unwrap().to_str().unwrap().to_string();
            for (li, layer) in c.circuit.layers.iter().enumerate() {
                let Some(g) = c.graphs.get(li) else { continue };

                // (1) Natural high-water at a no-eviction-below-cap budget.
                let nat = compile_forward_v2(
                    layer,
                    g,
                    FwdParams2 { budget_cells: 200, ..FwdParams2::default() },
                );
                max_natural = max_natural.max(nat.stats.max_live_cells);

                // (2) Default (bounded) compile: high-water + every Slot cell
                // index must fit the 7-bit field.
                let cf = compile_forward_v2(layer, g, FwdParams2::default());
                assert!(
                    (cf.stats.max_live_cells as u32) < cell_cap,
                    "{name} L{li}: bounded max_live_cells {} exceeds 7-bit cell field cap {cell_cap}",
                    cf.stats.max_live_cells
                );
                for ins in &cf.program.instrs {
                    for op in &ins.operands {
                        if let Operand::Slot { cell, .. } = op {
                            any_slots = true;
                            assert!(
                                (*cell as u32) < cell_cap,
                                "{name} L{li}: operand Slot cell {cell} over 7-bit field"
                            );
                        }
                    }
                    for d in &ins.dsts {
                        if let Dst::Slot { cell, .. } = d {
                            any_slots = true;
                            assert!(
                                (*cell as u32) < cell_cap,
                                "{name} L{li}: dst Slot cell {cell} over 7-bit field"
                            );
                        }
                    }
                }
            }
        }
        assert!(any_slots, "no Slot cells emitted across the corpus (test is vacuous)");
        assert!(
            max_natural >= cell_cap as usize,
            "natural (un-evicted) live set never exceeded the field cap (max {max_natural}); \
             eviction is not load-bearing, so the bounded half would be vacuous"
        );
    }

    #[test]
    fn no_macro_gate_is_skipped_corpus_wide() {
        // The Fixed/Variable shape split (and the GrandProductStep Fixed(2) skip
        // path that dropped 30 flattening grand-product gates) is gone: EVERY
        // Macro-classified gate must now lower to an Instr2. Assert exactly that
        // across the whole corpus — one lowering per Macro gate, zero skips.
        let mut total_macro_gates = 0usize;
        let mut lowered = 0usize;
        for p in all_fixtures() {
            let c = match load_circuit(&p) {
                Ok(c) => c,
                Err(_) => continue,
            };
            for layer in &c.circuit.layers {
                let arena = &layer.arena.nodes;
                let mt = MatrixTable::build(layer);
                let consts = build_const_table_v2(layer);
                let ci: HashMap<u32, u16> =
                    consts.iter().enumerate().map(|(i, v)| (*v, i as u16)).collect();
                let ck = cache_kind_by_addr(layer);
                let mut ctx = MacroCtx::new(&mt, &ci, &ck);
                for gate in layer.gates.iter().chain(&layer.gates_external) {
                    if lowering_kind(&gate.kind) != LoweringKind::Macro {
                        continue;
                    }
                    total_macro_gates += 1;
                    let instr = lower_gate(gate, arena, &mut ctx)
                        .expect("every Macro gate must lower (no skip path)");
                    // The operand count now rides the header.
                    let Header::Macro { n_operands, .. } = instr.header else {
                        panic!("Macro gate lowered to a non-Macro header");
                    };
                    if instr.memtup.is_some() {
                        // MemTuple-shaped gates (id-14/id-15/id-20) carry their
                        // data in `memtup`/`memtup2`, NOT operand lanes; the header
                        // n_operands is the SUM of the carried tuples' role counts.
                        let roles = instr.memtup.as_ref().map_or(0, |m| m.roles.len())
                            + instr.memtup2.as_ref().map_or(0, |m| m.roles.len());
                        assert!(
                            instr.operands.is_empty(),
                            "memtup-carrying gate must have no operand lanes"
                        );
                        assert_eq!(
                            n_operands as usize, roles,
                            "header n_operands must equal the total memtup role count"
                        );
                    } else {
                        assert_eq!(
                            n_operands as usize,
                            instr.operands.len(),
                            "header n_operands must equal the emitted operand-lane count"
                        );
                    }
                    lowered += 1;
                }
            }
        }
        assert!(total_macro_gates > 0, "no Macro gates in the corpus (test is vacuous)");
        assert_eq!(
            lowered, total_macro_gates,
            "every Macro gate must produce exactly one lowering (zero skipped)"
        );
    }

    #[test]
    fn compiled_programs_encode_decode_roundtrip_corpus_wide() {
        // The R2 lane changes (the larger lookup operand streams + the memtup
        // folded-constant block) must round-trip through the real encoder on every
        // compiled program — otherwise R3 cannot read them back. Non-vacuous:
        // every fixture × layer compiles AND at least one memtup with folded
        // constants round-trips bit-exact.
        use crate::isa_v2::encode::{decode2, encode2};
        let mut saw_memtup_consts = false;
        for p in all_fixtures() {
            let name = p.file_name().unwrap().to_str().unwrap().to_string();
            let c = load_circuit(&p).unwrap_or_else(|e| panic!("load {name}: {e:?}"));
            for (li, layer) in c.circuit.layers.iter().enumerate() {
                let Some(g) = c.graphs.get(li) else { continue };
                let cf = compile_forward_v2(layer, g, FwdParams2::default());
                for ins in &cf.program.instrs {
                    if let Some(mt) = &ins.memtup {
                        if !mt.consts.is_empty() {
                            saw_memtup_consts = true;
                        }
                    }
                }
                let lanes = encode2(&cf.program);
                let back = decode2(&lanes, cf.program.instrs.len());
                assert_eq!(
                    back, cf.program.instrs,
                    "{name} L{li}: encode2/decode2 not bit-exact (R2 lane layout)"
                );
            }
        }
        assert!(
            saw_memtup_consts,
            "no memtup folded-constant block in the corpus (round-trip test under-covers R2)"
        );
    }
}
