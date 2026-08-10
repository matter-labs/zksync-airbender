//! Lowers a compiled forward layer to its CUDA descriptor.
//!
//! Compile-time columns are dense backing-table indices. Lowering resolves
//! them to storage columns and splits each compile slot by distinct
//! `(matrix_base, stride_bytes)` so every wire slot names one homogeneous
//! matrix.
use std::{
    collections::{BTreeMap, BTreeSet},
    ptr,
};

use gpu_gkr_compiler::{
    encode_forward_program as encode, virtual_setup_kind_code, CompiledLayer,
    ForwardDstLine as DstLine, ForwardEncodeError as EncodeError, ForwardInstr as Instr,
    ForwardOperandField as OperandField, ForwardOperandLine as OperandLine,
    ForwardProgram as Program, ForwardSpecialStrategy as SpecialStrategy,
    FORWARD_MAX_COLS as MAX_COLS, FORWARD_SOURCE_WINDOW_COLUMNS as SOURCE_WINDOW_COLUMNS,
};

use crate::upstream::{ChallengeRef, GKRAddress, PrimeField, RangeWidth, ReadPlace};
use gpu_core::primitives::field::{BF, E4};

use super::desc::{
    pack_desc, FwdVmDesc, ARENA_GENERIC_FAMILY, ARENA_RANGE_CHECK_16, ARENA_TIMESTAMP,
    ARG_DERIVED_E4_CAP, CONST_CAP, CONST_DERIVED_E4_CAP, DESC_CAP, DST_SLOT_COUNT,
    MAPPING_ARENA_COUNT, PROGRAM_CAP, SD_AGGREGATE, SD_DECODER, SD_INITS_TOP_BITS, SD_SETUP,
    SD_SINGLE_COLUMN, SD_VIRTUAL, SOURCE_WINDOW_COUNT,
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

/// Per-layer inputs sourced from prover buffers. Unused pointers may be null.
///
/// The decoder fill value occupies the final const-derived-E4 bank slot.
#[derive(Clone, Copy, Debug)]
pub(crate) struct FwdVmHeaderInputs<'a> {
    pub mapping_arena: [*const u32; MAPPING_ARENA_COUNT],
    /// `generic_family` column of the decoder mapping (`num_generic_sets`,
    /// the arena's last column). Required iff the layer has a `PeekDecoder`.
    pub decoder_mapping_col: Option<u16>,
    pub table: *const E4,
    pub table_len: u32,
    /// Rows (= trace_len = mapping-arena column stride).
    pub count: u32,
    pub inits_and_teardowns_top_bits: &'a [u32],
}

#[expect(
    dead_code,
    reason = "error payloads are emitted by the derived Debug implementation"
)]
#[derive(Debug)]
pub(crate) enum FwdVmLowerError {
    /// Wire-format encode failed (cap guard inside `gpu_gkr_compiler`).
    Encode(EncodeError),
    /// Program exceeds the inline descriptor capacity.
    ProgramOverflow {
        lanes: usize,
    },
    GroupSourceWindowOverflow {
        required: usize,
    },
    MissingLookupAdditiveSlot,
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
    /// `DST_SLOT_COUNT` wire slots (SLOT_BITS=4 on the wire; `slot`/`col` locate
    /// the column whose fresh `(base, stride)` group did not fit).
    WireSlotOverflow {
        slot: u8,
        col: u16,
    },
    SourceWindowOverflow {
        window: u8,
        column: u16,
    },
    UnmappedSource {
        window: u8,
        column: u16,
    },
    SourceFieldMismatch {
        window: u8,
        column: u16,
        expect_e4: bool,
        got_e4: bool,
    },
    SourceColumnOffStride {
        window: u8,
        column: u16,
    },
    SourceColRemapCollision {
        window: u8,
        matrix_col: usize,
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
    /// Distinct dense columns mapped to the same wire matrix column.
    ColRemapCollision {
        slot: u8,
        matrix_col: usize,
    },
}

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

struct SourceGeometry {
    base: [*mut u8; SOURCE_WINDOW_COUNT],
    stride_bytes: [u32; SOURCE_WINDOW_COUNT],
    remap: BTreeMap<(u8, u16), (u8, u16)>,
    n_windows: usize,
}

fn source_coordinates(program: &Program) -> BTreeSet<(u8, u16)> {
    let mut coordinates = BTreeSet::new();
    let mut record = |operand: &OperandLine| {
        if let OperandLine::Source { window, column, .. } = *operand {
            coordinates.insert((window, column));
        }
    };
    for instr in &program.instrs {
        match instr {
            Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                operands.iter().for_each(&mut record);
            }
            Instr::Fma { pairs, .. } => {
                for (lhs, rhs) in pairs {
                    record(lhs);
                    record(rhs);
                }
            }
            Instr::Mov { src: Some(src), .. } => record(src),
            Instr::Mov { src: None, .. } => {}
        }
    }
    coordinates
}

fn derive_source_geometry(
    cl: &CompiledLayer,
    resolve_column: &dyn Fn(GKRAddress) -> Option<ResolvedColumn>,
) -> Result<SourceGeometry, FwdVmLowerError> {
    let mut geometry = SourceGeometry {
        base: [ptr::null_mut(); SOURCE_WINDOW_COUNT],
        stride_bytes: [0; SOURCE_WINDOW_COUNT],
        remap: BTreeMap::new(),
        n_windows: 0,
    };
    let coordinates = source_coordinates(&cl.program);
    for compiler_window in 0..cl.source_windows.len() as u8 {
        let expect_e4 = cl
            .source_windows
            .source_field(compiler_window)
            .expect("dense source-window table")
            == OperandField::Ext;
        let mut groups = Vec::<(*mut u8, u32, Vec<(u16, usize)>)>::new();
        for &(window, column) in coordinates
            .iter()
            .filter(|(window, _)| *window == compiler_window)
        {
            let place = cl
                .source_windows
                .resolve_read_place(window, column)
                .ok_or(FwdVmLowerError::UnmappedSource { window, column })?;
            let addr = read_place_to_gkr_address(&place);
            let resolved = resolve_column(addr).ok_or(FwdVmLowerError::UnresolvedColumn {
                slot: window,
                col: column as u16,
                addr,
            })?;
            if resolved.is_e4 != expect_e4 {
                return Err(FwdVmLowerError::SourceFieldMismatch {
                    window,
                    column,
                    expect_e4,
                    got_e4: resolved.is_e4,
                });
            }
            if resolved.stride_bytes == 0 {
                return Err(FwdVmLowerError::SourceColumnOffStride { window, column });
            }
            let offset = (resolved.ptr as usize)
                .checked_sub(resolved.matrix_base as usize)
                .ok_or(FwdVmLowerError::SourceColumnOffStride { window, column })?;
            if offset % resolved.stride_bytes as usize != 0 {
                return Err(FwdVmLowerError::SourceColumnOffStride { window, column });
            }
            let matrix_col = offset / resolved.stride_bytes as usize;
            let group = if let Some(index) = groups.iter().position(|(base, stride, _)| {
                *base == resolved.matrix_base && *stride == resolved.stride_bytes
            }) {
                index
            } else {
                groups.push((resolved.matrix_base, resolved.stride_bytes, Vec::new()));
                groups.len() - 1
            };
            if groups[group]
                .2
                .iter()
                .any(|(_, existing)| *existing == matrix_col)
            {
                return Err(FwdVmLowerError::SourceColRemapCollision { window, matrix_col });
            }
            groups[group].2.push((column, matrix_col));
        }

        for (matrix_base, stride, mut columns) in groups {
            columns.sort_by_key(|(_, matrix_col)| *matrix_col);
            let mut active = None::<(u8, usize)>;
            for (column, matrix_col) in columns {
                let (wire, first_matrix_col) = match active {
                    Some((wire, first)) if matrix_col < first + SOURCE_WINDOW_COLUMNS as usize => {
                        (wire, first)
                    }
                    _ => {
                        if geometry.n_windows >= SOURCE_WINDOW_COUNT {
                            return Err(FwdVmLowerError::SourceWindowOverflow {
                                window: compiler_window,
                                column,
                            });
                        }
                        let wire = geometry.n_windows as u8;
                        let byte_offset = matrix_col
                            .checked_mul(stride as usize)
                            .and_then(|offset| (matrix_base as usize).checked_add(offset))
                            .ok_or(FwdVmLowerError::SourceColumnOffStride {
                                window: compiler_window,
                                column,
                            })?;
                        geometry.base[geometry.n_windows] = byte_offset as *mut u8;
                        geometry.stride_bytes[geometry.n_windows] = stride;
                        geometry.n_windows += 1;
                        active = Some((wire, matrix_col));
                        (wire, matrix_col)
                    }
                };
                geometry.remap.insert(
                    (compiler_window, column),
                    (wire, (matrix_col - first_matrix_col) as u16),
                );
            }
        }
    }
    Ok(geometry)
}

struct SlotGeometry {
    base: [*mut u8; DST_SLOT_COUNT],
    stride_bytes: [u32; DST_SLOT_COUNT],
    n_wire_slots: usize,
    remap: BTreeMap<(u8, u16), (u8, u16)>,
    claimed: Vec<Vec<u16>>,
}

impl SlotGeometry {
    /// Wire slots are not shared across compile slots.
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
        if self.n_wire_slots >= DST_SLOT_COUNT {
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
    let backings = &cl.backings;
    let mut geom = SlotGeometry {
        base: [ptr::null_mut(); DST_SLOT_COUNT],
        stride_bytes: [0; DST_SLOT_COUNT],
        n_wire_slots: 0,
        remap: BTreeMap::new(),
        claimed: vec![Vec::new(); DST_SLOT_COUNT],
    };
    let dst_coordinates: BTreeSet<(u8, u16)> = cl
        .program
        .instrs
        .iter()
        .filter_map(|instr| match instr {
            Instr::Mov {
                dst: Some(DstLine::GlobalMaterialize { slot, col }),
                ..
            } => Some((*slot, *col)),
            _ => None,
        })
        .collect();
    for slot in 0..DST_SLOT_COUNT as u8 {
        let slot_columns: Vec<u16> = dst_coordinates
            .range((slot, 0)..=(slot, u16::MAX))
            .map(|&(_, col)| col)
            .collect();
        if slot_columns.is_empty() {
            continue;
        }
        let field = backings
            .slot_field(slot)
            .ok_or(FwdVmLowerError::UnmappedGlobal {
                slot,
                col: slot_columns[0],
            })?;
        let expect_e4 = field == OperandField::Ext;
        // This compile slot's `(base, stride) -> wire slot` groups. Field
        // homogeneity per wire slot follows from the per-column field check
        // below: every group member matches THIS compile slot's field.
        let mut slot_groups: Vec<(*mut u8, u32, u8)> = Vec::new();
        for col in slot_columns {
            let place = backings
                .slot_col_to_read_place(slot, col)
                .ok_or(FwdVmLowerError::UnmappedGlobal { slot, col })?;
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
            geom.remap.insert((slot, col), (wire, matrix_col as u16));
        }
    }
    Ok(geom)
}

fn remap_global(geom: &SlotGeometry, slot: u8, col: u16) -> Result<(u8, u16), FwdVmLowerError> {
    geom.remap
        .get(&(slot, col))
        .copied()
        .ok_or(FwdVmLowerError::UnmappedGlobal { slot, col })
}

fn remap_operand(geom: &SourceGeometry, o: OperandLine) -> Result<OperandLine, FwdVmLowerError> {
    Ok(match o {
        OperandLine::Source { window, column } => {
            let &(window, column) = geom
                .remap
                .get(&(window, column))
                .ok_or(FwdVmLowerError::UnmappedSource { window, column })?;
            OperandLine::Source { window, column }
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
fn rewrite_program(
    cl: &CompiledLayer,
    source_geom: &SourceGeometry,
    dst_geom: &SlotGeometry,
) -> Result<Program, FwdVmLowerError> {
    let mut instrs = Vec::with_capacity(cl.program.instrs.len());
    for instr in &cl.program.instrs {
        instrs.push(match instr {
            Instr::Add {
                field,
                sign,
                operands,
            } => Instr::Add {
                field: *field,
                sign: *sign,
                operands: operands
                    .iter()
                    .map(|o| remap_operand(source_geom, *o))
                    .collect::<Result<_, _>>()?,
            },
            Instr::Mul {
                field,
                negate_acc,
                operands,
            } => Instr::Mul {
                field: *field,
                negate_acc: *negate_acc,
                operands: operands
                    .iter()
                    .map(|o| remap_operand(source_geom, *o))
                    .collect::<Result<_, _>>()?,
            },
            Instr::Fma {
                field_lhs,
                field_rhs,
                sign,
                pairs,
            } => Instr::Fma {
                field_lhs: *field_lhs,
                field_rhs: *field_rhs,
                sign: *sign,
                pairs: pairs
                    .iter()
                    .map(|(l, r)| {
                        Ok((
                            remap_operand(source_geom, *l)?,
                            remap_operand(source_geom, *r)?,
                        ))
                    })
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
                dst: dst.map(|d| remap_dst(dst_geom, d)).transpose()?,
                src: src.map(|s| remap_operand(source_geom, s)).transpose()?,
            },
        });
    }
    Ok(Program { instrs })
}

/// Assemble the by-value forward VM descriptor for one compiled layer.
///
/// - `resolve_column` maps a flat `GKRAddress` to its resident storage column
///   (production: the consolidated `storage/views.rs` matrices; tests: mocks).
/// - `challenge` resolves schedule-time `ArgDerivedE4` references.
/// - `ConstDerivedE4` values and the optional decoder fill are staged by the
///   production binding before the layer launch; only their bank indices and
///   count live in the descriptor.
pub(crate) fn lower_layer_desc(
    cl: &CompiledLayer,
    header: &FwdVmHeaderInputs<'_>,
    resolve_column: &dyn Fn(GKRAddress) -> Option<ResolvedColumn>,
    challenge: &dyn Fn(&ChallengeRef) -> E4,
) -> Result<FwdVmDesc, FwdVmLowerError> {
    // SAFETY: all-zero bytes are a valid `FwdVmDesc` — plain-old-data fields
    // plus nullable raw pointers; every meaningful field is filled below.
    let mut desc: FwdVmDesc = unsafe { core::mem::zeroed() };

    // ----- column geometry + program rewrite + encode. -----
    let source_geom = derive_source_geometry(cl, resolve_column)?;
    let dst_geom = derive_slot_geometry(cl, resolve_column)?;
    let program = rewrite_program(cl, &source_geom, &dst_geom)?;
    let lanes = encode(&program).map_err(FwdVmLowerError::Encode)?;
    desc.source_base = source_geom.base;
    desc.source_stride_bytes = source_geom.stride_bytes;
    desc.dst_base = dst_geom.base;
    desc.dst_stride_bytes = dst_geom.stride_bytes;
    desc.n_instr = program.instrs.len() as u32;

    if lanes.len() > PROGRAM_CAP {
        return Err(FwdVmLowerError::ProgramOverflow { lanes: lanes.len() });
    }
    desc.program[..lanes.len()].copy_from_slice(&lanes);

    // ----- banks (hard caps, no fallback). -----
    let consts = cl.consts.values();
    if consts.len() > CONST_CAP {
        return Err(FwdVmLowerError::ConstBankOverflow { n: consts.len() });
    }
    for (i, &v) in consts.iter().enumerate() {
        desc.consts[i] = BF::from_u32_with_reduction(v);
    }
    let mut n_consts = consts.len();

    let n_arg = cl.derived_e4.arg_refs().len();
    if n_arg > ARG_DERIVED_E4_CAP {
        return Err(FwdVmLowerError::ArgDerivedE4Overflow { n: n_arg });
    }
    for (i, r) in cl.derived_e4.arg_refs().iter().enumerate() {
        desc.arg_derived_e4[i] = challenge(r);
    }
    let n_const_derived_e4 = usize::from(cl.derived_e4.uses_lookup_additive())
        + usize::from(
            cl.specials
                .iter()
                .any(|special| matches!(special, SpecialStrategy::PeekDecoder { .. })),
        );
    if n_const_derived_e4 > CONST_DERIVED_E4_CAP {
        return Err(FwdVmLowerError::ConstDerivedE4Overflow {
            n: n_const_derived_e4,
        });
    }

    // ----- special descriptors (packed u32 each) + header pointers. -----
    let n_descs = cl.specials.len();
    if n_descs > DESC_CAP {
        return Err(FwdVmLowerError::DescOverflow { n: n_descs });
    }
    let mut uses_table = false;
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
    for (d, sd) in cl.specials.iter().enumerate() {
        desc.descs[d] = match sd {
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
                pack_desc(SD_DECODER, arena, col, (CONST_DERIVED_E4_CAP - 1) as u32)
            }
            SpecialStrategy::VirtualSetup { kind } => {
                // vkind = the NATIVE `gkr_base_source_kind` value VERBATIM:
                // `KIND_ORDER` code + 2 (pinned by desc.rs const asserts).
                pack_desc(SD_VIRTUAL, 0, 0, virtual_setup_kind_code(kind) + 2)
            }
            SpecialStrategy::InitsAndTeardownsTopBits { reference } => {
                let raw = *header
                    .inits_and_teardowns_top_bits
                    .get(reference.set_index)
                    .ok_or(FwdVmLowerError::SetIndexOverflow {
                        desc: d,
                        set_index: reference.set_index,
                    })?;
                if n_consts >= CONST_CAP {
                    return Err(FwdVmLowerError::ConstBankOverflow { n: n_consts + 1 });
                }
                let raw = raw.checked_shl(reference.shift).unwrap_or(0);
                desc.consts[n_consts] = BF::from_u32_with_reduction(raw);
                let slot = u16::try_from(n_consts).expect("CONST_CAP fits u16");
                n_consts += 1;
                pack_desc(SD_INITS_TOP_BITS, 0, slot, 0)
            }
        };
    }
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

    Ok(desc)
}
