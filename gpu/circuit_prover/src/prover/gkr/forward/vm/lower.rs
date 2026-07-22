//! fwd-VM v2 production descriptor lowering (Task 9): `CompiledLayer` →
//! by-value [`FwdVmDesc`] + owning [`FwdVmLayerSetup`].
//!
//! The one non-obvious transformation here is the **Global slot/column
//! renumber** (spec §2 "the lowering renumbers Global cols from layer-offsets
//! to dense matrix-column indices per slot"): the compiled program's `Global
//! { slot, col }` operands carry the `BackingTable`'s per-slot DENSE column
//! indices (assignment order — meaningless outside the table), while the
//! kernel addresses column `c` of slot `s` as `base[s] + c * stride_bytes[s]`
//! (`fwd_vm.cuh`). The lowering therefore resolves every dense column through
//! the first-class reverse map (`slot_col_to_read_place`) to its storage
//! column and rewrites each Global to `(wire slot, matrix col)` before
//! encoding.
//!
//! **Wire-slot splitting**: the ABI contract "a slot IS one homogeneous
//! matrix `(base, stride)`" is a WIRE-level contract, and production flat
//! storage does not honor it at compile-slot granularity — CopyAlias
//! cache/output columns are VIEWS into OTHER consolidated matrices
//! (`storage/views.rs`), so one compile-time slot's columns can span several
//! matrices (every inner layer does; Task 10 Finding 2). The lowering
//! therefore groups each compile slot's resolved columns by distinct
//! `(matrix_base, stride_bytes)` and allocates one WIRE slot per group
//! (first-appearance order); `base[16]`/`stride_bytes[16]` are indexed by
//! WIRE slot, and the program rewrite renumbers the slot field alongside the
//! col field. Total wire slots must fit `SLOT_COUNT` (SLOT_BITS=4 on the
//! wire) — a hard error, guarded corpus-wide by the
//! `wire_slot_census_fits_slot_count_on_all_fixtures` test (max observed: 6).
//! Field homogeneity per wire slot holds by construction: a wire slot serves
//! exactly one compile slot, and every column is checked against that compile
//! slot's field (`SlotFieldMismatch`).
//!
//! Overflow policy (spec §2): program overflow falls back to `program_ldg`
//! (a device allocation staged per the `SchedulerHostAllocator` rules —
//! scheduling-time-known immutable data, written once on the scheduling
//! thread); every other cap is a hard error, no fallback.

use std::ptr;

use era_cudart::memory::memory_copy_async;

use gkr_eval_isa::fwd::context::CompiledLayer;
use gkr_eval_isa::fwd::encode::encode;
use gkr_eval_isa::fwd::error::EncodeError;
use gkr_eval_isa::fwd::isa::{
    DstLine, Instr, LdcSub, OperandField, OperandLine, Program, MAX_COLS,
};
use gkr_eval_isa::fwd::source::{virtual_setup_kind_code, SpecialStrategy};

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::primitives::static_host::{alloc_static_pinned_box_from_slice, StaticPinnedBox};
use crate::prover::ProverContext;
use crate::upstream::{ChallengeRef, GKRAddress, PrimeField, RangeWidth, ReadPlace};

use super::desc::{
    pack_desc, FwdVmDesc, ARENA_GENERIC_FAMILY, ARENA_RANGE_CHECK_16, ARENA_TIMESTAMP,
    ARG_DERIVED_E4_CAP, CONST_CAP, CONST_DERIVED_E4_CAP, DESC_CAP, FILL_BANK_NONE,
    MAPPING_ARENA_COUNT, PROGRAM_CAP, SD_AGGREGATE, SD_DECODER, SD_SETUP, SD_SINGLE_COLUMN,
    SD_VIRTUAL, SLOT_COUNT,
};

/// One resolved storage column: the column's device pointer plus the geometry
/// of the consolidated homogeneous matrix it belongs to (`storage/views.rs`:
/// per-(layer, class, field) backing, column `poly_idx` at
/// `matrix_base + poly_idx * stride_bytes`).
#[derive(Clone, Copy, Debug)]
pub(crate) struct ResolvedColumn {
    /// Storage field of the matrix (16-B `E4` columns vs 4-B `BF` columns).
    pub is_e4: bool,
    /// Device pointer of THIS column (`matrix_base + poly_idx * stride_bytes`).
    pub ptr: *const u8,
    /// Device pointer of the consolidated matrix the column lives in.
    pub matrix_base: *mut u8,
    /// Matrix column stride in bytes.
    pub stride_bytes: u32,
}

/// Per-layer header inputs sourced from the prover buffers (Task 7
/// investigation): the 3 stage-1 mapping arenas (`GpuGKRLookupMappings`
/// generic_family / range_check_16 / timestamp — column-major, column stride =
/// `count`), the ONE shared α-folded generic-lookup table
/// (`GpuGKRForwardSetup::generic_lookup`), and the row count. Unused pointers
/// may be null — the lowering only requires (and only emits) the ones the
/// layer's specials actually reference.
///
/// The decoder FILL value is NOT a header input: the lowering only reserves
/// its const-derived-e4 bank slot (`FwdVmDesc::fill_bank_idx`); the caller
/// supplies the value in the bank upload (see [`lower_layer_desc`]).
#[derive(Clone, Copy, Debug)]
pub(crate) struct FwdVmHeaderInputs {
    pub mapping_arena: [*const u32; MAPPING_ARENA_COUNT],
    /// `generic_family` column of the decoder mapping (`num_generic_sets`,
    /// the arena's last column). Required iff the layer has a `PeekDecoder`.
    pub decoder_mapping_col: Option<u16>,
    pub table: *const E4,
    pub table_len: u32,
    /// Rows (= trace_len = mapping-arena column stride).
    pub count: u32,
}

#[derive(Debug)]
pub(crate) enum FwdVmLowerError {
    /// Wire-format encode failed (cap guard inside `gkr_eval_isa`).
    Encode(EncodeError),
    /// Program exceeds `PROGRAM_CAP` and no fallback context was provided.
    ProgramOverflow {
        lanes: usize,
    },
    /// CUDA error while staging the `program_ldg` fallback.
    Cuda(era_cudart_sys::CudaError),
    ConstBankOverflow {
        n: usize,
    },
    ArgDerivedE4Overflow {
        n: usize,
    },
    ConstDerivedE4Overflow {
        n: usize,
    },
    DescOverflow {
        n: usize,
    },
    SetIndexOverflow {
        desc: usize,
        set_index: usize,
    },
    /// A slot column's address did not resolve to resident storage.
    UnresolvedColumn {
        slot: u8,
        col: u16,
        addr: GKRAddress,
    },
    /// Storage field disagrees with the slot's `BackingKey::field`.
    SlotFieldMismatch {
        slot: u8,
        col: u16,
        expect_e4: bool,
        got_e4: bool,
    },
    /// Splitting compile slots into per-matrix wire slots needs more than
    /// `SLOT_COUNT` wire slots (SLOT_BITS=4 on the wire; `slot`/`col` locate
    /// the column whose fresh `(base, stride)` group did not fit).
    WireSlotOverflow {
        slot: u8,
        col: u16,
    },
    /// Column pointer is not `matrix_base + k * stride_bytes` for integer `k`.
    ColumnOffStride {
        slot: u8,
        col: u16,
    },
    /// Matrix column index exceeds the 10-bit wire `col` field.
    MatrixColOverflow {
        slot: u8,
        col: u16,
        matrix_col: usize,
    },
    /// The program references a `(slot, col)` the backing table never assigned.
    UnmappedGlobal {
        slot: u8,
        col: u16,
    },
    /// A special needs a mapping arena the header did not provide.
    MissingMappingArena {
        arena: u32,
    },
    MissingDecoderMappingCol,
    MissingTable,
    DecoderPredicateUnresolved {
        addr: GKRAddress,
    },
    DecoderPredicateNotBase {
        addr: GKRAddress,
    },
    /// Two decoder descs resolved to different execute-predicate columns
    /// (the desc header holds ONE mask pointer).
    DecoderMaskConflict,
    /// Two dense columns resolved to the SAME matrix column of one WIRE slot —
    /// a resolver bug would otherwise silently alias two distinct dense
    /// columns onto one wire `(slot, col)`, producing a well-formed-but-wrong
    /// program. Hard error: this is the last line of defense before an
    /// expensive GPU parity debug cycle. `slot` is the COMPILE slot of the
    /// colliding column (the wire slot is derived, the compile slot is what a
    /// human can map back to the backing table).
    ColRemapCollision {
        slot: u8,
        matrix_col: usize,
    },
}

/// Owning wrapper for one lowered layer. The descriptor is passed BY VALUE at
/// launch, but an oversize program leaves a raw `program_ldg` device pointer
/// embedded in it — per the GPU scheduling contract the backing allocations
/// must stay alive until every launch scheduled with this descriptor has been
/// enqueued, so they ride along here. `_program_fallback_host` is the pinned
/// staging source of the H2D copy scheduled at lowering time; it is a
/// dedicated (non-pool) pinned allocation, so it is retained conservatively
/// until the setup drops rather than relying on stream-ordered pool reuse.
pub(crate) struct FwdVmLayerSetup {
    pub desc: FwdVmDesc,
    _program_fallback: Option<DeviceAllocation<u16>>,
    _program_fallback_host: Option<StaticPinnedBox<u16>>,
}

/// Compact summary (the 26 KB descriptor's arrays are not useful output).
impl core::fmt::Debug for FwdVmLayerSetup {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("FwdVmLayerSetup")
            .field("n_instr", &self.desc.n_instr)
            .field("program_lanes", &self.desc.program_lanes)
            .field("program_inline", &self.desc.program_ldg.is_null())
            .field("n_consts", &self.desc.n_consts)
            .field("n_arg_derived_e4", &self.desc.n_arg_derived_e4)
            .field("n_const_derived_e4", &self.desc.n_const_derived_e4)
            .field("fill_bank_idx", &self.desc.fill_bank_idx)
            .field("n_descs", &self.desc.n_descs)
            .field("count", &self.desc.count)
            .finish_non_exhaustive()
    }
}

/// The flat `GKRAddress` behind a DAG-IR `ReadPlace` (inverse of `lower_dag`'s
/// `map_address`; same mapping as the bench harness'
/// `read_place_to_gkr_address`). Total: `VirtualSetup` is never a `ReadPlace`.
pub(crate) fn read_place_to_gkr_address(place: &ReadPlace) -> GKRAddress {
    match *place {
        ReadPlace::BaseLayerMemory { column } => GKRAddress::BaseLayerMemory(column),
        ReadPlace::BaseLayerWitness { column } => GKRAddress::BaseLayerWitness(column),
        ReadPlace::Setup { column } => GKRAddress::Setup(column),
        ReadPlace::Scratch { slot } => GKRAddress::ScratchSpace(slot),
        ReadPlace::LayerOutput { layer, offset } => GKRAddress::InnerLayer { layer, offset },
        ReadPlace::CacheOutput { layer, offset } => GKRAddress::Cached { layer, offset },
    }
}

/// Wire-slot geometry derived from the storage resolver (module doc,
/// "wire-slot splitting"): `base`/`stride_bytes` are indexed by WIRE slot —
/// one wire slot per distinct `(matrix_base, stride_bytes)` group WITHIN each
/// compile slot, allocated in first-appearance order — plus the
/// `(compile slot, dense col)` → `(wire slot, matrix col)` renumbering.
struct SlotGeometry {
    base: [*mut u8; SLOT_COUNT],
    stride_bytes: [u32; SLOT_COUNT],
    /// Wire slots allocated so far (`base`/`stride_bytes` valid for
    /// `0..n_wire_slots`, null/zero beyond).
    n_wire_slots: usize,
    /// `remap[compile_slot][dense_col]` = `(wire slot, matrix col)` — the
    /// rewritten `Global` encoding. Empty vec for slots without columns.
    remap: Vec<Vec<(u8, u16)>>,
    /// Matrix columns already claimed per wire slot (`ColRemapCollision`).
    claimed: Vec<Vec<u16>>,
}

impl SlotGeometry {
    /// Wire slot for `(base, stride)` within this compile slot's group list,
    /// allocating a fresh one on first appearance. Wire slots are NOT shared
    /// across compile slots (a wire slot inherits its compile slot's field;
    /// alias views may legitimately map two compile slots onto one matrix,
    /// and merging them would false-positive the collision guard).
    fn wire_slot_for(
        &mut self,
        slot_groups: &mut Vec<(*mut u8, u32, u8)>,
        resolved: &ResolvedColumn,
        slot: u8,
        col: u16,
    ) -> Result<u8, FwdVmLowerError> {
        if let Some(&(_, _, wire)) = slot_groups
            .iter()
            .find(|(b, s, _)| *b == resolved.matrix_base && *s == resolved.stride_bytes)
        {
            return Ok(wire);
        }
        if self.n_wire_slots >= SLOT_COUNT {
            return Err(FwdVmLowerError::WireSlotOverflow { slot, col });
        }
        let wire = self.n_wire_slots as u8;
        self.base[self.n_wire_slots] = resolved.matrix_base;
        self.stride_bytes[self.n_wire_slots] = resolved.stride_bytes;
        self.n_wire_slots += 1;
        slot_groups.push((resolved.matrix_base, resolved.stride_bytes, wire));
        Ok(wire)
    }
}

fn derive_slot_geometry(
    cl: &CompiledLayer,
    resolve_column: &dyn Fn(GKRAddress) -> Option<ResolvedColumn>,
) -> Result<SlotGeometry, FwdVmLowerError> {
    let backings = &cl.ctx.backings;
    let mut geom = SlotGeometry {
        base: [ptr::null_mut(); SLOT_COUNT],
        stride_bytes: [0; SLOT_COUNT],
        n_wire_slots: 0,
        remap: vec![Vec::new(); SLOT_COUNT],
        claimed: vec![Vec::new(); SLOT_COUNT],
    };
    for slot in 0..SLOT_COUNT as u8 {
        let Some(field) = backings.slot_field(slot) else {
            continue;
        };
        let expect_e4 = field == OperandField::Ext;
        // This compile slot's `(base, stride) -> wire slot` groups. Field
        // homogeneity per wire slot follows from the per-column field check
        // below: every group member matches THIS compile slot's field.
        let mut slot_groups: Vec<(*mut u8, u32, u8)> = Vec::new();
        let n_cols = backings.slot_columns(slot).len();
        for col in 0..n_cols as u16 {
            // Total for assigned columns by construction of the reverse map.
            let place = backings
                .slot_col_to_read_place(slot, col)
                .expect("slot_columns index must have a reverse-map entry");
            let addr = read_place_to_gkr_address(&place);
            let resolved = resolve_column(addr).ok_or(FwdVmLowerError::UnresolvedColumn {
                slot,
                col,
                addr,
            })?;
            if resolved.is_e4 != expect_e4 {
                return Err(FwdVmLowerError::SlotFieldMismatch {
                    slot,
                    col,
                    expect_e4,
                    got_e4: resolved.is_e4,
                });
            }
            if resolved.stride_bytes == 0 {
                return Err(FwdVmLowerError::ColumnOffStride { slot, col });
            }
            let wire = geom.wire_slot_for(&mut slot_groups, &resolved, slot, col)?;
            let off = (resolved.ptr as usize)
                .checked_sub(resolved.matrix_base as usize)
                .ok_or(FwdVmLowerError::ColumnOffStride { slot, col })?;
            if off % resolved.stride_bytes as usize != 0 {
                return Err(FwdVmLowerError::ColumnOffStride { slot, col });
            }
            let matrix_col = off / resolved.stride_bytes as usize;
            if matrix_col >= MAX_COLS as usize {
                return Err(FwdVmLowerError::MatrixColOverflow {
                    slot,
                    col,
                    matrix_col,
                });
            }
            if geom.claimed[wire as usize].contains(&(matrix_col as u16)) {
                return Err(FwdVmLowerError::ColRemapCollision { slot, matrix_col });
            }
            geom.claimed[wire as usize].push(matrix_col as u16);
            geom.remap[slot as usize].push((wire, matrix_col as u16));
        }
    }
    Ok(geom)
}

fn remap_global(geom: &SlotGeometry, slot: u8, col: u16) -> Result<(u8, u16), FwdVmLowerError> {
    geom.remap
        .get(slot as usize)
        .and_then(|cols| cols.get(col as usize))
        .copied()
        .ok_or(FwdVmLowerError::UnmappedGlobal { slot, col })
}

fn remap_operand(geom: &SlotGeometry, o: OperandLine) -> Result<OperandLine, FwdVmLowerError> {
    Ok(match o {
        OperandLine::Global { slot, col } => {
            let (slot, col) = remap_global(geom, slot, col)?;
            OperandLine::Global { slot, col }
        }
        other => other,
    })
}

fn remap_dst(geom: &SlotGeometry, d: DstLine) -> Result<DstLine, FwdVmLowerError> {
    Ok(match d {
        DstLine::GlobalMaterialize { slot, col } => {
            let (slot, col) = remap_global(geom, slot, col)?;
            DstLine::GlobalMaterialize { slot, col }
        }
        other => other,
    })
}

/// Rewrite every `Global` operand/dst from the backing table's dense
/// `(compile slot, col)` to the storage `(wire slot, matrix col)` (module
/// doc). Structure-preserving: only `Global`/`GlobalMaterialize` slot/col
/// fields change, and the rewritten program goes back through the
/// cap-guarded `encode` (`SlotOutOfRange` at `MAX_SLOTS`, `ColOutOfRange`
/// at `MAX_COLS`), so a malformed remap cannot reach the wire.
fn rewrite_program(cl: &CompiledLayer, geom: &SlotGeometry) -> Result<Program, FwdVmLowerError> {
    let mut instrs = Vec::with_capacity(cl.program.instrs.len());
    for instr in &cl.program.instrs {
        instrs.push(match instr {
            Instr::Add {
                field,
                sign,
                promote,
                operands,
            } => Instr::Add {
                field: *field,
                sign: *sign,
                promote: *promote,
                operands: operands
                    .iter()
                    .map(|o| remap_operand(geom, *o))
                    .collect::<Result<_, _>>()?,
            },
            Instr::Mul {
                field,
                promote,
                negate_acc,
                operands,
            } => Instr::Mul {
                field: *field,
                promote: *promote,
                negate_acc: *negate_acc,
                operands: operands
                    .iter()
                    .map(|o| remap_operand(geom, *o))
                    .collect::<Result<_, _>>()?,
            },
            Instr::Fma {
                field_lhs,
                field_rhs,
                sign,
                promote,
                pairs,
            } => Instr::Fma {
                field_lhs: *field_lhs,
                field_rhs: *field_rhs,
                sign: *sign,
                promote: *promote,
                pairs: pairs
                    .iter()
                    .map(|(l, r)| Ok((remap_operand(geom, *l)?, remap_operand(geom, *r)?)))
                    .collect::<Result<_, FwdVmLowerError>>()?,
            },
            Instr::Mov {
                dir,
                field,
                dst,
                src,
            } => Instr::Mov {
                dir: *dir,
                field: *field,
                dst: dst.map(|d| remap_dst(geom, d)).transpose()?,
                src: src.map(|s| remap_operand(geom, s)).transpose()?,
            },
        });
    }
    Ok(Program { instrs })
}

/// Length of a `DerivedE4Banks` channel — the banks expose no length accessor,
/// so probe `get` upward from 0 (dense `Vec` internally, terminates at the
/// real length; same technique as the bench harness).
///
/// `cap` structurally bounds the probe at `cap + 1`: the caller's own cap
/// check (`n > cap` → hard error) fires right after, so a corrupt/oversized
/// bank can never drive `n` past `cap + 1` and wrap `n as u16` into an
/// infinite loop (`ARG_DERIVED_E4_CAP`/`CONST_DERIVED_E4_CAP` are both « 2^16).
fn derived_e4_bank_len(cl: &CompiledLayer, sub: LdcSub, cap: usize) -> usize {
    let mut n = 0usize;
    while n <= cap && cl.ctx.derived_e4.get(sub, n as u16).is_some() {
        n += 1;
    }
    n
}

/// Assemble the full by-value fwd-VM v2 descriptor for one compiled layer.
///
/// - `resolve_column` maps a flat `GKRAddress` to its resident storage column
///   (production: the consolidated `storage/views.rs` matrices; tests: mocks).
/// - `challenge` yields the concrete `E4` value of a schedule-time
///   (`ArgDerivedE4`) reference. `ConstDerivedE4` values are NOT part of the
///   descriptor — upload them via [`super::upload_const_derived_e4`]; only the
///   bank LENGTH rides the desc (`n_const_derived_e4`, VALIDATE bounds check).
/// - **Decoder fill**: for a layer with a `PeekDecoder` special, the lowering
///   APPENDS one bank slot after the real `ConstDerivedE4` entries
///   (`fill_bank_idx` = pre-append length, `n_const_derived_e4` includes it)
///   but does NOT supply the value. ORDERING CONTRACT (mechanism (a), fill
///   value host-known): the caller must place the — final — fill value at
///   `values[fill_bank_idx]` of the [`super::upload_const_derived_e4`] upload
///   and enqueue that upload on `exec_stream` BEFORE any launch of this
///   layer's descriptor (`gpu_tests::const_derived_e4_values` implements the
///   append for the harness/gate callers). If a future production caller only
///   has the fill device-resident (`device_decoder_lookup_fill_value`), the
///   alternative is a 16-B D2D `memcpyToSymbolAsync` into bank slot
///   `fill_bank_idx` enqueued after the bank upload — same ordering contract
///   against the launches.
/// - `fallback_context`: required only if the encoded program exceeds
///   `PROGRAM_CAP` (never for the committed corpus); `None` turns program
///   overflow into a hard error.
pub(crate) fn lower_layer_desc(
    cl: &CompiledLayer,
    header: &FwdVmHeaderInputs,
    resolve_column: &dyn Fn(GKRAddress) -> Option<ResolvedColumn>,
    challenge: &dyn Fn(&ChallengeRef) -> E4,
    fallback_context: Option<&ProverContext>,
) -> Result<FwdVmLayerSetup, FwdVmLowerError> {
    // SAFETY: all-zero bytes are a valid `FwdVmDesc` — plain-old-data fields
    // plus nullable raw pointers; every meaningful field is filled below.
    let mut desc: FwdVmDesc = unsafe { core::mem::zeroed() };

    // ----- column geometry + program rewrite + encode. -----
    let geom = derive_slot_geometry(cl, resolve_column)?;
    let program = rewrite_program(cl, &geom)?;
    let lanes = encode(&program).map_err(FwdVmLowerError::Encode)?;
    desc.base = geom.base;
    desc.stride_bytes = geom.stride_bytes;
    desc.n_instr = program.instrs.len() as u32;
    desc.program_lanes = lanes.len() as u32;

    // ----- program residency: inline when it fits, LDG fallback otherwise. -----
    let (fallback_dev, fallback_host) = if lanes.len() <= PROGRAM_CAP {
        desc.program[..lanes.len()].copy_from_slice(&lanes);
        desc.program_ldg = ptr::null();
        (None, None)
    } else {
        let context =
            fallback_context.ok_or(FwdVmLowerError::ProgramOverflow { lanes: lanes.len() })?;
        // SchedulerHostAllocator rules: scheduling-time-known immutable data,
        // written once here on the scheduling thread; the stream only reads.
        let host = alloc_static_pinned_box_from_slice(&lanes).map_err(FwdVmLowerError::Cuda)?;
        let mut dev: DeviceAllocation<u16> = context
            .alloc(lanes.len(), AllocationPlacement::BestFit)
            .map_err(FwdVmLowerError::Cuda)?;
        memory_copy_async(
            &mut dev[0..lanes.len()],
            &host[..],
            context.get_exec_stream(),
        )
        .map_err(FwdVmLowerError::Cuda)?;
        desc.program_ldg = dev.as_ptr();
        (Some(dev), Some(host))
    };

    // ----- banks (hard caps, no fallback). -----
    let consts = cl.ctx.consts.values();
    if consts.len() > CONST_CAP {
        return Err(FwdVmLowerError::ConstBankOverflow { n: consts.len() });
    }
    for (i, &v) in consts.iter().enumerate() {
        desc.consts[i] = BF::from_u32_with_reduction(v);
    }
    desc.n_consts = consts.len() as u32;

    let n_arg = derived_e4_bank_len(cl, LdcSub::ArgDerivedE4, ARG_DERIVED_E4_CAP);
    if n_arg > ARG_DERIVED_E4_CAP {
        return Err(FwdVmLowerError::ArgDerivedE4Overflow { n: n_arg });
    }
    for i in 0..n_arg {
        let r = cl
            .ctx
            .derived_e4
            .get(LdcSub::ArgDerivedE4, i as u16)
            .unwrap();
        desc.arg_derived_e4[i] = challenge(r);
    }
    desc.n_arg_derived_e4 = n_arg as u32;

    // The decoder fill slot (reserved below) also lives in this bank, so the
    // final `n_const_derived_e4`/cap check happen after the specials loop.
    let mut n_const_derived_e4 =
        derived_e4_bank_len(cl, LdcSub::ConstDerivedE4, CONST_DERIVED_E4_CAP);

    // ----- special descriptors (packed u32 each) + header pointers. -----
    let n_descs = cl.ctx.specials.len();
    if n_descs > DESC_CAP {
        return Err(FwdVmLowerError::DescOverflow { n: n_descs });
    }
    let mut uses_table = false;
    let mut fill_bank_idx = FILL_BANK_NONE;
    let mut mask: *const BF = ptr::null();
    let require_arena = |arena: u32| -> Result<u32, FwdVmLowerError> {
        if header.mapping_arena[arena as usize].is_null() {
            Err(FwdVmLowerError::MissingMappingArena { arena })
        } else {
            Ok(arena)
        }
    };
    let set_index_u16 = |d: usize, set_index: usize| -> Result<u16, FwdVmLowerError> {
        u16::try_from(set_index)
            .map_err(|_| FwdVmLowerError::SetIndexOverflow { desc: d, set_index })
    };
    for (d, sd) in cl.ctx.specials.iter().enumerate() {
        desc.descs[d] = match &sd.strategy {
            SpecialStrategy::PeekSingleColumn { set_index, width } => {
                let arena = require_arena(match width {
                    RangeWidth::Bits16 => ARENA_RANGE_CHECK_16,
                    RangeWidth::Timestamp => ARENA_TIMESTAMP,
                })?;
                pack_desc(SD_SINGLE_COLUMN, arena, set_index_u16(d, *set_index)?, 0)
            }
            SpecialStrategy::PeekAggregate { set_index } => {
                uses_table = true;
                let arena = require_arena(ARENA_GENERIC_FAMILY)?;
                pack_desc(SD_AGGREGATE, arena, set_index_u16(d, *set_index)?, 0)
            }
            SpecialStrategy::PeekSetup => {
                uses_table = true;
                pack_desc(SD_SETUP, 0, 0, 0)
            }
            SpecialStrategy::PeekDecoder { predicate, .. } => {
                uses_table = true;
                // Reserve ONE const-derived-e4 bank slot for the per-circuit
                // fill value (shared by every decoder desc of the layer);
                // the caller uploads the value there (see the fn doc).
                if fill_bank_idx == FILL_BANK_NONE {
                    fill_bank_idx = n_const_derived_e4 as u32;
                    n_const_derived_e4 += 1;
                }
                let arena = require_arena(ARENA_GENERIC_FAMILY)?;
                let col = header
                    .decoder_mapping_col
                    .ok_or(FwdVmLowerError::MissingDecoderMappingCol)?;
                let addr = read_place_to_gkr_address(predicate);
                let pred = resolve_column(addr)
                    .ok_or(FwdVmLowerError::DecoderPredicateUnresolved { addr })?;
                if pred.is_e4 {
                    return Err(FwdVmLowerError::DecoderPredicateNotBase { addr });
                }
                let pred_ptr = pred.ptr as *const BF;
                if mask.is_null() {
                    mask = pred_ptr;
                } else if mask != pred_ptr {
                    return Err(FwdVmLowerError::DecoderMaskConflict);
                }
                pack_desc(SD_DECODER, arena, col, 0)
            }
            SpecialStrategy::VirtualSetup { kind } => {
                // vkind = the NATIVE `gkr_base_source_kind` value VERBATIM:
                // `KIND_ORDER` code + 2 (pinned by desc.rs const asserts).
                pack_desc(SD_VIRTUAL, 0, 0, virtual_setup_kind_code(kind) + 2)
            }
        };
    }
    desc.n_descs = n_descs as u32;
    if n_const_derived_e4 > CONST_DERIVED_E4_CAP {
        return Err(FwdVmLowerError::ConstDerivedE4Overflow {
            n: n_const_derived_e4,
        });
    }
    desc.n_const_derived_e4 = n_const_derived_e4 as u32;
    desc.fill_bank_idx = fill_bank_idx;
    desc.mapping_arena = header.mapping_arena;
    if uses_table {
        if header.table.is_null() {
            return Err(FwdVmLowerError::MissingTable);
        }
        desc.table = header.table;
        desc.table_len = header.table_len;
    }
    desc.mask = mask;

    // ----- geometry. -----
    desc.count = header.count;

    Ok(FwdVmLayerSetup {
        desc,
        _program_fallback: fallback_dev,
        _program_fallback_host: fallback_host,
    })
}
