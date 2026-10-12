use std::{collections::BTreeMap, ptr};

use crate::upstream::{Field, PR};
use gpu_gkr_compiler::{
    encode_forward_runtime_program, virtual_setup_kind_code, CompiledLayer,
    ForwardDstLine as DstLine, ForwardEncodeError as EncodeError, ForwardInstr as Instr,
    ForwardLdcSub as LdcSub, ForwardOperandField as OperandField,
    ForwardOperandLine as OperandLine, ForwardProgram as Program,
    ForwardSpecialStrategy as SpecialStrategy, FORWARD_MAX_COLS as MAX_COLS,
};

use super::desc::{
    pack_desc, FwdVmDesc, FwdVmLayer, ARENA_GENERIC_FAMILY, ARENA_RANGE_CHECK_16, ARENA_TIMESTAMP,
    ARG_DERIVED_E4_CAP, CONST_CAP, CONST_DERIVED_E4_CAP, DESC_CAP, DST_SLOT_COUNT, LAYER_CAP,
    MAPPING_ARENA_COUNT, PROGRAM_CAP, SD_AGGREGATE, SD_DECODER, SD_INITS_TOP_BITS, SD_SETUP,
    SD_SINGLE_COLUMN, SD_VIRTUAL, SOURCE_WINDOW_COUNT,
};
use crate::upstream::{ChallengeRef, GKRAddress, PrimeField, RangeWidth, ReadPlace};

#[derive(Clone, Copy, Debug)]
pub(crate) struct ResolvedColumn {
    pub is_e4: bool,
    pub ptr: *const u8,
    pub matrix_base: *mut u8,
    pub stride_bytes: u32,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct FwdVmInputs<'a> {
    pub mapping_arena: [*const u32; MAPPING_ARENA_COUNT],
    pub decoder_mapping_col: Option<u16>,
    pub table: *const PR,
    pub decoder_mapping: *const u32,
    pub table_len: u32,
    pub count: u32,
    pub inits_and_teardowns_top_bits: &'a [u32],
}

#[expect(
    dead_code,
    reason = "error payloads are emitted by the derived Debug implementation"
)]
#[derive(Debug)]
pub(crate) enum FwdVmLowerError {
    Encode(EncodeError),
    ProgramOverflow {
        lanes: usize,
    },
    SourceWindowOverflow {
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
    UnresolvedColumn {
        slot: u8,
        col: u16,
        addr: GKRAddress,
    },
    SlotFieldMismatch {
        slot: u8,
        col: u16,
        expect_e4: bool,
        got_e4: bool,
    },
    WireSlotOverflow {
        slot: u8,
        col: u16,
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
    MatrixColOverflow {
        slot: u8,
        col: u16,
        matrix_col: usize,
    },
    UnmappedGlobal {
        slot: u8,
        col: u16,
    },
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
    DecoderMaskConflict,
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

const SOURCE_COLUMN_BITS: u32 = 9;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct SourceUseKey {
    layer: usize,
    window: u8,
    column: u16,
}

#[derive(Clone, Copy, Debug)]
struct PhysicalSourceUse {
    key: SourceUseKey,
    is_e4: bool,
    matrix_base: *mut u8,
    stride_bytes: u32,
    matrix_column: usize,
}

struct SourceGeometry {
    base: [*mut u8; SOURCE_WINDOW_COUNT],
    stride_bytes: [u32; SOURCE_WINDOW_COUNT],
    remap: BTreeMap<SourceUseKey, (u8, u16)>,
    n_windows: usize,
}

fn pack_source_geometry(uses: &[PhysicalSourceUse]) -> Result<SourceGeometry, FwdVmLowerError> {
    let mut sorted = uses.to_vec();
    sorted.sort_by_key(|source| {
        (
            source.is_e4,
            source.matrix_base as usize,
            source.stride_bytes,
            source.matrix_column,
        )
    });

    let mut geometry = SourceGeometry {
        base: [std::ptr::null_mut(); SOURCE_WINDOW_COUNT],
        stride_bytes: [0; SOURCE_WINDOW_COUNT],
        remap: BTreeMap::new(),
        n_windows: 0,
    };
    let mut active = None::<(bool, usize, u32, u8, usize)>;
    for source in sorted {
        let (window, first_column) = match active {
            Some((is_e4, base, stride, window, first))
                if is_e4 == source.is_e4
                    && base == source.matrix_base as usize
                    && stride == source.stride_bytes
                    && source.matrix_column < first + (1 << SOURCE_COLUMN_BITS) =>
            {
                (window, first)
            }
            _ => {
                if geometry.n_windows == SOURCE_WINDOW_COUNT {
                    return Err(FwdVmLowerError::SourceWindowOverflow {
                        required: geometry.n_windows + 1,
                    });
                }
                let window = geometry.n_windows as u8;
                let byte_offset = source
                    .matrix_column
                    .checked_mul(source.stride_bytes as usize)
                    .and_then(|offset| (source.matrix_base as usize).checked_add(offset))
                    .ok_or(FwdVmLowerError::SourceColumnOffStride {
                        window: source.key.window,
                        column: source.key.column,
                    })?;
                geometry.base[geometry.n_windows] = byte_offset as *mut u8;
                geometry.stride_bytes[geometry.n_windows] = source.stride_bytes;
                geometry.n_windows += 1;
                active = Some((
                    source.is_e4,
                    source.matrix_base as usize,
                    source.stride_bytes,
                    window,
                    source.matrix_column,
                ));
                (window, source.matrix_column)
            }
        };
        let coordinate = (
            window,
            u16::try_from(source.matrix_column - first_column)
                .expect("source column fits nine bits"),
        );
        if let Some(previous) = geometry.remap.insert(source.key, coordinate) {
            assert_eq!(previous, coordinate, "one logical source resolved two ways");
        }
    }
    Ok(geometry)
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct DestinationUseKey {
    layer: usize,
    slot: u8,
    column: u16,
}

#[derive(Clone, Copy)]
struct LayerBankBases {
    constant: u16,
    arg_derived_e4: u16,
    descriptor: u16,
    lookup_additive: Option<u16>,
}

fn rewrite_operand(
    layer: usize,
    operand: OperandLine,
    sources: &BTreeMap<SourceUseKey, (u8, u16)>,
    bases: LayerBankBases,
) -> Result<OperandLine, FwdVmLowerError> {
    Ok(match operand {
        OperandLine::Source { window, column } => {
            let &(window, column) = sources
                .get(&SourceUseKey {
                    layer,
                    window,
                    column,
                })
                .ok_or(FwdVmLowerError::UnmappedSource { window, column })?;
            OperandLine::Source { window, column }
        }
        OperandLine::Ldc { sub, idx } => match sub {
            LdcSub::Const => OperandLine::Ldc {
                sub,
                idx: bases.constant + idx,
            },
            LdcSub::ArgDerivedE4 => OperandLine::Ldc {
                sub,
                idx: bases.arg_derived_e4 + idx,
            },
            LdcSub::ConstDerivedE4 => {
                assert_eq!(idx, 0, "unsupported const-derived-PR index");
                OperandLine::Ldc {
                    sub,
                    idx: bases
                        .lookup_additive
                        .ok_or(FwdVmLowerError::MissingLookupAdditiveSlot)?,
                }
            }
            LdcSub::Special => operand,
        },
        OperandLine::Special { desc } => OperandLine::Special {
            desc: bases.descriptor + desc,
        },
        other => other,
    })
}

fn rewrite_dst(
    layer: usize,
    dst: DstLine,
    destinations: &BTreeMap<DestinationUseKey, (u8, u16)>,
) -> Result<DstLine, FwdVmLowerError> {
    Ok(match dst {
        DstLine::GlobalMaterialize { slot, col } => {
            let &(slot, col) = destinations
                .get(&DestinationUseKey {
                    layer,
                    slot,
                    column: col,
                })
                .ok_or(FwdVmLowerError::UnmappedGlobal { slot, col })?;
            DstLine::GlobalMaterialize { slot, col }
        }
        other => other,
    })
}

fn rewrite_program(
    layer: usize,
    program: &Program,
    sources: &BTreeMap<SourceUseKey, (u8, u16)>,
    destinations: &BTreeMap<DestinationUseKey, (u8, u16)>,
    bases: LayerBankBases,
) -> Result<Program, FwdVmLowerError> {
    let mut instrs = Vec::with_capacity(program.instrs.len());
    for instruction in &program.instrs {
        instrs.push(match instruction {
            Instr::Add {
                field,
                sign,
                operands,
            } => Instr::Add {
                field: *field,
                sign: *sign,
                operands: operands
                    .iter()
                    .map(|operand| rewrite_operand(layer, *operand, sources, bases))
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
                    .map(|operand| rewrite_operand(layer, *operand, sources, bases))
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
                    .map(|(lhs, rhs)| {
                        Ok((
                            rewrite_operand(layer, *lhs, sources, bases)?,
                            rewrite_operand(layer, *rhs, sources, bases)?,
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
                dst: dst
                    .map(|dst| rewrite_dst(layer, dst, destinations))
                    .transpose()?,
                src: src
                    .map(|src| rewrite_operand(layer, src, sources, bases))
                    .transpose()?,
            },
        });
    }
    Ok(Program { instrs })
}

fn empty_desc() -> FwdVmDesc {
    unsafe { core::mem::zeroed() }
}

fn append_program(
    desc: &mut FwdVmDesc,
    next_lane: &mut usize,
    layer: usize,
    program: &Program,
) -> Result<(), FwdVmLowerError> {
    assert!(layer < LAYER_CAP);
    let lanes = encode_forward_runtime_program(program).map_err(FwdVmLowerError::Encode)?;
    let end = next_lane
        .checked_add(lanes.len())
        .ok_or(FwdVmLowerError::ProgramOverflow { lanes: usize::MAX })?;
    if end > PROGRAM_CAP {
        return Err(FwdVmLowerError::ProgramOverflow { lanes: end });
    }
    desc.layers[layer] = FwdVmLayer {
        program_offset: u16::try_from(*next_lane).expect("PROGRAM_CAP fits u16"),
        instruction_count: u16::try_from(program.instrs.len())
            .expect("forward instruction count fits u16"),
    };
    desc.program[*next_lane..end].copy_from_slice(&lanes);
    *next_lane = end;
    Ok(())
}

#[derive(Clone, Copy, Debug)]
struct PhysicalDestinationUse {
    key: DestinationUseKey,
    is_e4: bool,
    matrix_base: *mut u8,
    stride_bytes: u32,
    matrix_column: usize,
}

struct DestinationGeometry {
    base: [*mut u8; DST_SLOT_COUNT],
    stride_bytes: [u32; DST_SLOT_COUNT],
    remap: BTreeMap<DestinationUseKey, (u8, u16)>,
}

fn pack_destination_geometry(
    uses: &[PhysicalDestinationUse],
) -> Result<DestinationGeometry, FwdVmLowerError> {
    let mut sorted = uses.to_vec();
    sorted.sort_by_key(|destination| {
        (
            destination.is_e4,
            destination.matrix_base as usize,
            destination.stride_bytes,
            destination.matrix_column,
        )
    });
    let mut geometry = DestinationGeometry {
        base: [ptr::null_mut(); DST_SLOT_COUNT],
        stride_bytes: [0; DST_SLOT_COUNT],
        remap: BTreeMap::new(),
    };
    let mut active = None::<(bool, usize, u32, u8)>;
    let mut n_slots = 0usize;
    for destination in sorted {
        if destination.matrix_column >= MAX_COLS as usize {
            return Err(FwdVmLowerError::MatrixColOverflow {
                slot: destination.key.slot,
                col: destination.key.column,
                matrix_col: destination.matrix_column,
            });
        }
        let slot = match active {
            Some((is_e4, base, stride, slot))
                if is_e4 == destination.is_e4
                    && base == destination.matrix_base as usize
                    && stride == destination.stride_bytes =>
            {
                slot
            }
            _ => {
                if n_slots == DST_SLOT_COUNT {
                    return Err(FwdVmLowerError::WireSlotOverflow {
                        slot: destination.key.slot,
                        col: destination.key.column,
                    });
                }
                let slot = n_slots as u8;
                geometry.base[n_slots] = destination.matrix_base;
                geometry.stride_bytes[n_slots] = destination.stride_bytes;
                n_slots += 1;
                active = Some((
                    destination.is_e4,
                    destination.matrix_base as usize,
                    destination.stride_bytes,
                    slot,
                ));
                slot
            }
        };
        let coordinate = (slot, destination.matrix_column as u16);
        if let Some(previous) = geometry.remap.insert(destination.key, coordinate) {
            assert_eq!(
                previous, coordinate,
                "one logical destination resolved two ways"
            );
        }
    }
    Ok(geometry)
}

fn physical_matrix_column(
    resolved: ResolvedColumn,
    slot: u8,
    column: u16,
) -> Result<usize, FwdVmLowerError> {
    if resolved.stride_bytes == 0 {
        return Err(FwdVmLowerError::SourceColumnOffStride {
            window: slot,
            column,
        });
    }
    let offset = (resolved.ptr as usize)
        .checked_sub(resolved.matrix_base as usize)
        .ok_or(FwdVmLowerError::SourceColumnOffStride {
            window: slot,
            column,
        })?;
    if offset % resolved.stride_bytes as usize != 0 {
        return Err(FwdVmLowerError::SourceColumnOffStride {
            window: slot,
            column,
        });
    }
    Ok(offset / resolved.stride_bytes as usize)
}

fn visit_layer_source_operands(
    layer_index: usize,
    layer: &CompiledLayer,
    mut visit: impl FnMut(SourceUseKey, OperandField) -> Result<(), FwdVmLowerError>,
) -> Result<(), FwdVmLowerError> {
    let mut record = |operand: &OperandLine, field: OperandField| {
        if let OperandLine::Source { window, column } = *operand {
            visit(
                SourceUseKey {
                    layer: layer_index,
                    window,
                    column,
                },
                field,
            )?;
        }
        Ok(())
    };
    for instruction in &layer.program.instrs {
        match instruction {
            Instr::Add {
                field, operands, ..
            }
            | Instr::Mul {
                field, operands, ..
            } => {
                for operand in operands {
                    record(operand, *field)?;
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                pairs,
                ..
            } => {
                for (lhs, rhs) in pairs {
                    record(lhs, *field_lhs)?;
                    record(rhs, *field_rhs)?;
                }
            }
            Instr::Mov {
                field,
                src: Some(src),
                ..
            } => record(src, *field)?,
            Instr::Mov { src: None, .. } => {}
        }
    }
    Ok(())
}

pub(crate) struct LoweredFwdVm {
    pub desc: FwdVmDesc,
    pub lookup_additive_slot: Option<usize>,
    pub decoder_fill_slot: Option<usize>,
    pub constant_count: usize,
    pub source_window_count: usize,
    pub destination_slot_count: usize,
}

pub(crate) fn lower_desc(
    layers: &[CompiledLayer],
    header: &FwdVmInputs<'_>,
    resolve_column: &dyn Fn(GKRAddress) -> Option<ResolvedColumn>,
) -> Result<LoweredFwdVm, FwdVmLowerError> {
    assert!(
        !layers.is_empty(),
        "forward VM must have at least one layer"
    );
    assert!(layers.len() <= LAYER_CAP, "forward VM exceeds LAYER_CAP");

    let mut physical_sources = Vec::new();
    let mut physical_destinations = Vec::new();
    for (layer_index, layer) in layers.iter().enumerate() {
        visit_layer_source_operands(layer_index, layer, |key, field| {
            let source_field = layer
                .source_windows
                .source_field(key.window)
                .expect("compiled source window has a field");
            if source_field != field {
                return Err(FwdVmLowerError::SourceFieldMismatch {
                    window: key.window,
                    column: key.column,
                    expect_e4: field == OperandField::Ext,
                    got_e4: source_field == OperandField::Ext,
                });
            }
            let place = layer
                .source_windows
                .resolve_read_place(key.window, key.column)
                .ok_or(FwdVmLowerError::UnmappedSource {
                    window: key.window,
                    column: key.column,
                })?;
            let address = read_place_to_gkr_address(&place);
            let resolved = resolve_column(address).ok_or(FwdVmLowerError::UnresolvedColumn {
                slot: key.window,
                col: key.column,
                addr: address,
            })?;
            let expect_e4 = field == OperandField::Ext;
            if resolved.is_e4 != expect_e4 {
                return Err(FwdVmLowerError::SourceFieldMismatch {
                    window: key.window,
                    column: key.column,
                    expect_e4,
                    got_e4: resolved.is_e4,
                });
            }
            physical_sources.push(PhysicalSourceUse {
                key,
                is_e4: resolved.is_e4,
                matrix_base: resolved.matrix_base,
                stride_bytes: resolved.stride_bytes,
                matrix_column: physical_matrix_column(resolved, key.window, key.column)?,
            });
            Ok(())
        })?;

        for instruction in &layer.program.instrs {
            let Instr::Mov {
                field,
                dst: Some(DstLine::GlobalMaterialize { slot, col }),
                ..
            } = instruction
            else {
                continue;
            };
            let place = layer.backings.slot_col_to_read_place(*slot, *col).ok_or(
                FwdVmLowerError::UnmappedGlobal {
                    slot: *slot,
                    col: *col,
                },
            )?;
            let address = read_place_to_gkr_address(&place);
            let resolved = resolve_column(address).ok_or(FwdVmLowerError::UnresolvedColumn {
                slot: *slot,
                col: *col,
                addr: address,
            })?;
            let expect_e4 = *field == OperandField::Ext;
            if resolved.is_e4 != expect_e4 {
                return Err(FwdVmLowerError::SlotFieldMismatch {
                    slot: *slot,
                    col: *col,
                    expect_e4,
                    got_e4: resolved.is_e4,
                });
            }
            physical_destinations.push(PhysicalDestinationUse {
                key: DestinationUseKey {
                    layer: layer_index,
                    slot: *slot,
                    column: *col,
                },
                is_e4: resolved.is_e4,
                matrix_base: resolved.matrix_base,
                stride_bytes: resolved.stride_bytes,
                matrix_column: physical_matrix_column(resolved, *slot, *col)?,
            });
        }
    }

    let source_geometry = pack_source_geometry(&physical_sources)?;
    let destination_geometry = pack_destination_geometry(&physical_destinations)?;
    let uses_lookup_additive = layers
        .iter()
        .any(|layer| layer.derived_e4.uses_lookup_additive());
    let uses_decoder_fill = layers.iter().any(|layer| {
        layer
            .specials
            .iter()
            .any(|special| matches!(special, SpecialStrategy::PeekDecoder { .. }))
    });
    let lookup_additive_slot = uses_lookup_additive.then_some(0usize);
    let decoder_fill_slot = uses_decoder_fill.then_some(usize::from(uses_lookup_additive));
    let n_const_derived = usize::from(uses_lookup_additive) + usize::from(uses_decoder_fill);
    if n_const_derived > CONST_DERIVED_E4_CAP {
        return Err(FwdVmLowerError::ConstDerivedE4Overflow { n: n_const_derived });
    }

    let mut desc = empty_desc();
    desc.source_base = source_geometry.base;
    desc.source_stride_bytes = source_geometry.stride_bytes;
    desc.dst_base = destination_geometry.base;
    desc.dst_stride_bytes = destination_geometry.stride_bytes;
    desc.mapping_arena = header.mapping_arena;
    desc.decoder_mapping = header.decoder_mapping;
    desc.count = header.count;
    desc.layer_count = layers.len() as u32;

    let mut n_consts = 0usize;
    let mut n_args = 0usize;
    let mut n_descs = 0usize;
    let mut next_lane = 0usize;
    let mut uses_table = false;
    let mut mask: *const PR = ptr::null();
    for (layer_index, layer) in layers.iter().enumerate() {
        let constant_base = n_consts;
        for &value in layer.consts.values() {
            if n_consts == CONST_CAP {
                return Err(FwdVmLowerError::ConstBankOverflow { n: n_consts + 1 });
            }
            assert!(
                value < PR::CHARACTERISTICS_U128,
                "Proth120 forward constant is not canonical"
            );
            desc.consts[n_consts] = PR::from_u128_with_reduction(value);
            n_consts += 1;
        }

        let arg_base = n_args;
        for _reference in layer.derived_e4.arg_refs() {
            if n_args == ARG_DERIVED_E4_CAP {
                return Err(FwdVmLowerError::ArgDerivedE4Overflow { n: n_args + 1 });
            }
            n_args += 1;
        }

        let descriptor_base = n_descs;
        let require_arena = |arena: u32| -> Result<u32, FwdVmLowerError> {
            if header.mapping_arena[arena as usize].is_null() {
                Err(FwdVmLowerError::MissingMappingArena { arena })
            } else {
                Ok(arena)
            }
        };
        for special in layer.specials.iter() {
            if n_descs == DESC_CAP {
                return Err(FwdVmLowerError::DescOverflow { n: n_descs + 1 });
            }
            let local_desc = n_descs - descriptor_base;
            desc.descs[n_descs] = match special {
                SpecialStrategy::PeekSingleColumn { set_index, width } => {
                    let arena = require_arena(match width {
                        RangeWidth::Bits16 => ARENA_RANGE_CHECK_16,
                        RangeWidth::Timestamp => ARENA_TIMESTAMP,
                    })?;
                    pack_desc(
                        SD_SINGLE_COLUMN,
                        arena,
                        u16::try_from(*set_index).map_err(|_| {
                            FwdVmLowerError::SetIndexOverflow {
                                desc: n_descs,
                                set_index: *set_index,
                            }
                        })?,
                        0,
                    )
                }
                SpecialStrategy::PeekAggregate { set_index } => {
                    uses_table = true;
                    let arena = require_arena(ARENA_GENERIC_FAMILY)?;
                    pack_desc(
                        SD_AGGREGATE,
                        arena,
                        u16::try_from(*set_index).map_err(|_| {
                            FwdVmLowerError::SetIndexOverflow {
                                desc: n_descs,
                                set_index: *set_index,
                            }
                        })?,
                        0,
                    )
                }
                SpecialStrategy::PeekSetup => {
                    uses_table = true;
                    pack_desc(SD_SETUP, 0, 0, 0)
                }
                SpecialStrategy::PeekDecoder { predicate } => {
                    uses_table = true;
                    let arena = ARENA_GENERIC_FAMILY;
                    assert!(
                        !header.decoder_mapping.is_null(),
                        "Proth120 decoder mapping is missing"
                    );
                    let column = header
                        .decoder_mapping_col
                        .ok_or(FwdVmLowerError::MissingDecoderMappingCol)?;
                    let address = read_place_to_gkr_address(predicate);
                    let resolved = resolve_column(address)
                        .ok_or(FwdVmLowerError::DecoderPredicateUnresolved { addr: address })?;
                    if resolved.is_e4 {
                        return Err(FwdVmLowerError::DecoderPredicateNotBase { addr: address });
                    }
                    let predicate_mask = resolved.ptr as *const PR;
                    if mask.is_null() {
                        mask = predicate_mask;
                    } else if mask != predicate_mask {
                        return Err(FwdVmLowerError::DecoderMaskConflict);
                    }
                    pack_desc(
                        SD_DECODER,
                        arena,
                        column,
                        decoder_fill_slot.expect("decoder slot exists") as u32,
                    )
                }
                SpecialStrategy::VirtualSetup { kind } => {
                    pack_desc(SD_VIRTUAL, 0, 0, virtual_setup_kind_code(kind) + 2)
                }
                SpecialStrategy::InitsAndTeardownsTopBits { reference } => {
                    if n_consts == CONST_CAP {
                        return Err(FwdVmLowerError::ConstBankOverflow { n: n_consts + 1 });
                    }
                    let raw = *header
                        .inits_and_teardowns_top_bits
                        .get(reference.set_index)
                        .ok_or(FwdVmLowerError::SetIndexOverflow {
                            desc: local_desc,
                            set_index: reference.set_index,
                        })?;
                    desc.consts[n_consts] = PR::from_u128_with_reduction(
                        u128::from(raw).checked_shl(reference.shift).unwrap_or(0),
                    );
                    let slot = n_consts as u16;
                    n_consts += 1;
                    pack_desc(SD_INITS_TOP_BITS, 0, slot, 0)
                }
            };
            n_descs += 1;
        }

        let rewritten = rewrite_program(
            layer_index,
            &layer.program,
            &source_geometry.remap,
            &destination_geometry.remap,
            LayerBankBases {
                constant: constant_base as u16,
                arg_derived_e4: arg_base as u16,
                descriptor: descriptor_base as u16,
                lookup_additive: lookup_additive_slot.map(|slot| slot as u16),
            },
        )?;
        append_program(&mut desc, &mut next_lane, layer_index, &rewritten)?;
    }

    if uses_table {
        if header.table.is_null() {
            return Err(FwdVmLowerError::MissingTable);
        }
        desc.table = header.table;
        desc.table_len = header.table_len;
    }
    desc.mask = mask;

    Ok(LoweredFwdVm {
        desc,
        lookup_additive_slot,
        decoder_fill_slot,
        constant_count: n_consts,
        source_window_count: source_geometry
            .base
            .iter()
            .filter(|pointer| !pointer.is_null())
            .count(),
        destination_slot_count: destination_geometry
            .base
            .iter()
            .filter(|pointer| !pointer.is_null())
            .count(),
    })
}
