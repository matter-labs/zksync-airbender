//! Lowers consecutive forward layers into one compact by-value descriptor.

use std::{collections::BTreeMap, ptr};

use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::{
    encode_forward_program_with_source_layout, virtual_setup_kind_code, CompiledLayer,
    ForwardDstLine as DstLine, ForwardInstr as Instr, ForwardLdcSub as LdcSub,
    ForwardOperandField as OperandField, ForwardOperandLine as OperandLine,
    ForwardProgram as Program, ForwardSourceLayout, ForwardSpecialStrategy as SpecialStrategy,
    FORWARD_MAX_COLS as MAX_COLS,
};

use super::desc::{
    pack_desc, FwdVmGroupDesc, FwdVmGroupLayer, ARENA_GENERIC_FAMILY, ARENA_RANGE_CHECK_16,
    ARENA_TIMESTAMP, ARG_DERIVED_E4_CAP, CONST_CAP, CONST_DERIVED_E4_CAP, DESC_CAP, DST_SLOT_COUNT,
    GROUP_LAYER_CAP, GROUP_SOURCE_WINDOW_COUNT, PROGRAM_CAP, SD_AGGREGATE, SD_DECODER,
    SD_INITS_TOP_BITS, SD_SETUP, SD_SINGLE_COLUMN, SD_VIRTUAL,
};
use super::lower::{read_place_to_gkr_address, FwdVmHeaderInputs, FwdVmLowerError, ResolvedColumn};
use crate::upstream::{ChallengeRef, GKRAddress, PrimeField, RangeWidth};

const GROUP_SOURCE_COLUMN_BITS: u32 = 9;

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

struct GroupSourceGeometry {
    base: [*mut u8; GROUP_SOURCE_WINDOW_COUNT],
    stride_bytes: [u32; GROUP_SOURCE_WINDOW_COUNT],
    remap: BTreeMap<SourceUseKey, (u8, u16)>,
    n_windows: usize,
}

fn pack_source_geometry(
    uses: &[PhysicalSourceUse],
) -> Result<GroupSourceGeometry, FwdVmLowerError> {
    let mut sorted = uses.to_vec();
    sorted.sort_by_key(|source| {
        (
            source.is_e4,
            source.matrix_base as usize,
            source.stride_bytes,
            source.matrix_column,
        )
    });

    let mut geometry = GroupSourceGeometry {
        base: [std::ptr::null_mut(); GROUP_SOURCE_WINDOW_COUNT],
        stride_bytes: [0; GROUP_SOURCE_WINDOW_COUNT],
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
                    && source.matrix_column < first + (1 << GROUP_SOURCE_COLUMN_BITS) =>
            {
                (window, first)
            }
            _ => {
                if geometry.n_windows == GROUP_SOURCE_WINDOW_COUNT {
                    return Err(FwdVmLowerError::GroupSourceWindowOverflow {
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
                .expect("a grouped source column fits nine bits"),
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

fn rewrite_group_operand(
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
            LdcSub::ConstDerivedE4 => OperandLine::Ldc {
                sub,
                idx: bases
                    .lookup_additive
                    .ok_or(FwdVmLowerError::MissingLookupAdditiveSlot)?,
            },
            LdcSub::Special => operand,
        },
        OperandLine::Special { desc } => OperandLine::Special {
            desc: bases.descriptor + desc,
        },
        other => other,
    })
}

fn rewrite_group_dst(
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

fn rewrite_group_program(
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
                    .map(|operand| rewrite_group_operand(layer, *operand, sources, bases))
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
                    .map(|operand| rewrite_group_operand(layer, *operand, sources, bases))
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
                            rewrite_group_operand(layer, *lhs, sources, bases)?,
                            rewrite_group_operand(layer, *rhs, sources, bases)?,
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
                    .map(|dst| rewrite_group_dst(layer, dst, destinations))
                    .transpose()?,
                src: src
                    .map(|src| rewrite_group_operand(layer, src, sources, bases))
                    .transpose()?,
            },
        });
    }
    Ok(Program { instrs })
}

fn empty_group_desc() -> FwdVmGroupDesc {
    // SAFETY: the descriptor is plain data and all pointer fields may be null.
    unsafe { core::mem::zeroed() }
}

fn append_group_program(
    desc: &mut FwdVmGroupDesc,
    next_lane: &mut usize,
    layer: usize,
    program: &Program,
) -> Result<(), FwdVmLowerError> {
    assert!(layer < GROUP_LAYER_CAP);
    let layout = ForwardSourceLayout::new(4, 9).expect("the grouped source layout is valid");
    let lanes = encode_forward_program_with_source_layout(program, layout)
        .map_err(FwdVmLowerError::Encode)?;
    let end = next_lane
        .checked_add(lanes.len())
        .ok_or(FwdVmLowerError::ProgramOverflow { lanes: usize::MAX })?;
    if end > PROGRAM_CAP {
        return Err(FwdVmLowerError::ProgramOverflow { lanes: end });
    }
    desc.layers[layer] = FwdVmGroupLayer {
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

struct GroupDestinationGeometry {
    base: [*mut u8; DST_SLOT_COUNT],
    stride_bytes: [u32; DST_SLOT_COUNT],
    remap: BTreeMap<DestinationUseKey, (u8, u16)>,
}

fn pack_destination_geometry(
    uses: &[PhysicalDestinationUse],
) -> Result<GroupDestinationGeometry, FwdVmLowerError> {
    let mut sorted = uses.to_vec();
    sorted.sort_by_key(|destination| {
        (
            destination.is_e4,
            destination.matrix_base as usize,
            destination.stride_bytes,
            destination.matrix_column,
        )
    });
    let mut geometry = GroupDestinationGeometry {
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

pub(crate) struct LoweredFwdVmGroup {
    pub desc: FwdVmGroupDesc,
    pub lookup_additive_slot: Option<usize>,
    pub decoder_fill_slot: Option<usize>,
    pub source_window_count: usize,
}

pub(crate) fn lower_group_desc(
    layers: &[CompiledLayer],
    header: &FwdVmHeaderInputs<'_>,
    resolve_column: &dyn Fn(GKRAddress) -> Option<ResolvedColumn>,
    challenge: &dyn Fn(&ChallengeRef) -> E4,
) -> Result<LoweredFwdVmGroup, FwdVmLowerError> {
    assert!(!layers.is_empty(), "forward VM group must be non-empty");
    assert!(
        layers.len() <= GROUP_LAYER_CAP,
        "forward VM group exceeds GROUP_LAYER_CAP"
    );

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

    let mut desc = empty_group_desc();
    desc.source_base = source_geometry.base;
    desc.source_stride_bytes = source_geometry.stride_bytes;
    desc.dst_base = destination_geometry.base;
    desc.dst_stride_bytes = destination_geometry.stride_bytes;
    desc.mapping_arena = header.mapping_arena;
    desc.count = header.count;
    desc.layer_count = layers.len() as u32;

    let mut n_consts = 0usize;
    let mut n_args = 0usize;
    let mut n_descs = 0usize;
    let mut next_lane = 0usize;
    let mut uses_table = false;
    let mut mask: *const BF = ptr::null();
    for (layer_index, layer) in layers.iter().enumerate() {
        let constant_base = n_consts;
        for &value in layer.consts.values() {
            if n_consts == CONST_CAP {
                return Err(FwdVmLowerError::ConstBankOverflow { n: n_consts + 1 });
            }
            desc.consts[n_consts] = BF::from_u32_with_reduction(value);
            n_consts += 1;
        }

        let arg_base = n_args;
        for reference in layer.derived_e4.arg_refs() {
            if n_args == ARG_DERIVED_E4_CAP {
                return Err(FwdVmLowerError::ArgDerivedE4Overflow { n: n_args + 1 });
            }
            desc.arg_derived_e4[n_args] = challenge(reference);
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
                    let arena = require_arena(ARENA_GENERIC_FAMILY)?;
                    let column = header
                        .decoder_mapping_col
                        .ok_or(FwdVmLowerError::MissingDecoderMappingCol)?;
                    let address = read_place_to_gkr_address(predicate);
                    let resolved = resolve_column(address)
                        .ok_or(FwdVmLowerError::DecoderPredicateUnresolved { addr: address })?;
                    if resolved.is_e4 {
                        return Err(FwdVmLowerError::DecoderPredicateNotBase { addr: address });
                    }
                    let predicate_mask = resolved.ptr as *const BF;
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
                    desc.consts[n_consts] =
                        BF::from_u32_with_reduction(raw.checked_shl(reference.shift).unwrap_or(0));
                    let slot = n_consts as u16;
                    n_consts += 1;
                    pack_desc(SD_INITS_TOP_BITS, 0, slot, 0)
                }
            };
            n_descs += 1;
        }

        let rewritten = rewrite_group_program(
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
        append_group_program(&mut desc, &mut next_lane, layer_index, &rewritten)?;
    }

    if uses_table {
        if header.table.is_null() {
            return Err(FwdVmLowerError::MissingTable);
        }
        desc.table = header.table;
        desc.table_len = header.table_len;
    }
    desc.mask = mask;

    Ok(LoweredFwdVmGroup {
        desc,
        lookup_additive_slot,
        decoder_fill_slot,
        source_window_count: source_geometry.n_windows,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::path::Path;
    use std::sync::Arc;

    use gpu_core::primitives::field::{BF, E4};
    use gpu_gkr_compiler::{
        ForwardDstLine as DstLine, ForwardInstr as Instr, ForwardLdcSub as LdcSub,
        ForwardOperandField as OperandField, ForwardOperandLine as OperandLine,
        ForwardProgram as Program, ForwardSpecialStrategy,
    };
    use gpu_trace::witness::circuit_type::{
        CircuitType, UnrolledCircuitType, UnrolledNonMemoryCircuitType,
    };

    use super::*;
    use crate::forward::vm::lower::{read_place_to_gkr_address, FwdVmHeaderInputs, ResolvedColumn};
    use crate::programs::GkrPrograms;
    use crate::upstream::{GKRAddress, GKRCircuitArtifact, ReadPlace};

    fn source_use(
        layer: usize,
        compiler_column: u16,
        matrix_base: usize,
        matrix_column: usize,
    ) -> PhysicalSourceUse {
        PhysicalSourceUse {
            key: SourceUseKey {
                layer,
                window: 0,
                column: compiler_column,
            },
            is_e4: false,
            matrix_base: matrix_base as *mut u8,
            stride_bytes: 16,
            matrix_column,
        }
    }

    #[test]
    fn physical_sources_pack_into_five_hundred_twelve_column_windows() {
        let uses = [
            source_use(0, 0, 0x1000, 0),
            source_use(0, 1, 0x1000, 127),
            source_use(1, 0, 0x1000, 128),
            source_use(1, 1, 0x1000, 511),
            source_use(1, 2, 0x1000, 512),
        ];

        let geometry = pack_source_geometry(&uses).unwrap();
        assert_eq!(geometry.n_windows, 2);
        assert_eq!(geometry.base[0] as usize, 0x1000);
        assert_eq!(geometry.base[1] as usize, 0x1000 + 512 * 16);
        assert_eq!(geometry.remap[&uses[0].key], (0, 0));
        assert_eq!(geometry.remap[&uses[3].key], (0, 511));
        assert_eq!(geometry.remap[&uses[4].key], (1, 0));
    }

    #[test]
    fn seventeenth_physical_source_window_is_rejected() {
        let uses = (0..17)
            .map(|index| source_use(index, 0, 0x1000 + index * 0x1000, 0))
            .collect::<Vec<_>>();

        assert!(matches!(
            pack_source_geometry(&uses),
            Err(FwdVmLowerError::GroupSourceWindowOverflow { required: 17 })
        ));
    }

    #[test]
    fn group_rewrite_rebases_every_layer_local_bank() {
        let program = Program {
            instrs: vec![
                Instr::Add {
                    field: OperandField::Base,
                    sign: gpu_gkr_compiler::ForwardSign::Plus,
                    operands: vec![
                        OperandLine::Source {
                            window: 1,
                            column: 2,
                        },
                        OperandLine::Ldc {
                            sub: LdcSub::Const,
                            idx: 3,
                        },
                        OperandLine::Ldc {
                            sub: LdcSub::ArgDerivedE4,
                            idx: 4,
                        },
                        OperandLine::Ldc {
                            sub: LdcSub::ConstDerivedE4,
                            idx: 0,
                        },
                        OperandLine::Special { desc: 5 },
                        OperandLine::Smem { cell: 6 },
                        OperandLine::Ldc {
                            sub: LdcSub::Special,
                            idx: 1,
                        },
                    ],
                },
                Instr::Mov {
                    dir: gpu_gkr_compiler::ForwardMovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::GlobalMaterialize { slot: 2, col: 9 }),
                    src: None,
                },
            ],
        };
        let mut sources = BTreeMap::new();
        sources.insert(
            SourceUseKey {
                layer: 7,
                window: 1,
                column: 2,
            },
            (9, 400),
        );
        let mut destinations = BTreeMap::new();
        destinations.insert(
            DestinationUseKey {
                layer: 7,
                slot: 2,
                column: 9,
            },
            (8, 300),
        );
        let bases = LayerBankBases {
            constant: 10,
            arg_derived_e4: 20,
            descriptor: 30,
            lookup_additive: Some(1),
        };

        let rewritten = rewrite_group_program(7, &program, &sources, &destinations, bases).unwrap();
        let Instr::Add { operands, .. } = &rewritten.instrs[0] else {
            panic!("expected Add")
        };
        assert_eq!(
            operands[0],
            OperandLine::Source {
                window: 9,
                column: 400
            }
        );
        assert_eq!(
            operands[1],
            OperandLine::Ldc {
                sub: LdcSub::Const,
                idx: 13
            }
        );
        assert_eq!(
            operands[2],
            OperandLine::Ldc {
                sub: LdcSub::ArgDerivedE4,
                idx: 24,
            }
        );
        assert_eq!(
            operands[3],
            OperandLine::Ldc {
                sub: LdcSub::ConstDerivedE4,
                idx: 1,
            }
        );
        assert_eq!(operands[4], OperandLine::Special { desc: 35 });
        assert_eq!(operands[5], OperandLine::Smem { cell: 6 });
        assert_eq!(
            operands[6],
            OperandLine::Ldc {
                sub: LdcSub::Special,
                idx: 1,
            }
        );
        assert_eq!(
            rewritten.instrs[1],
            Instr::Mov {
                dir: gpu_gkr_compiler::ForwardMovDir::DstFromAcc,
                field: OperandField::Base,
                dst: Some(DstLine::GlobalMaterialize { slot: 8, col: 300 }),
                src: None,
            }
        );
    }

    #[test]
    fn encoded_group_programs_concatenate_and_record_layer_boundaries() {
        let first = Program {
            instrs: vec![Instr::Mov {
                dir: gpu_gkr_compiler::ForwardMovDir::AccFromSrc,
                field: OperandField::Base,
                dst: None,
                src: Some(OperandLine::Smem { cell: 1 }),
            }],
        };
        let second = Program {
            instrs: vec![
                Instr::Mov {
                    dir: gpu_gkr_compiler::ForwardMovDir::AccFromSrc,
                    field: OperandField::Base,
                    dst: None,
                    src: Some(OperandLine::Smem { cell: 2 }),
                },
                Instr::Mov {
                    dir: gpu_gkr_compiler::ForwardMovDir::DstFromAcc,
                    field: OperandField::Base,
                    dst: Some(DstLine::Smem { cell: 3 }),
                    src: None,
                },
            ],
        };
        let mut desc = empty_group_desc();
        let mut next_lane = 0;

        append_group_program(&mut desc, &mut next_lane, 0, &first).unwrap();
        append_group_program(&mut desc, &mut next_lane, 1, &second).unwrap();

        assert_eq!(desc.layers[0].program_offset, 0);
        assert_eq!(desc.layers[0].instruction_count, 1);
        assert_eq!(desc.layers[1].program_offset, 2);
        assert_eq!(desc.layers[1].instruction_count, 2);
        assert_eq!(next_lane, 6);
        assert_eq!(&desc.program[..6], &[3, 5, 3, 9, 7, 6]);
    }

    fn fake_column(place: ReadPlace, field: OperandField) -> ResolvedColumn {
        let field_index = usize::from(field == OperandField::Ext);
        let (backing, column) = match place {
            ReadPlace::BaseLayerMemory { column } => (1, column),
            ReadPlace::BaseLayerWitness { column } => (2, column),
            ReadPlace::Setup { column } => (3, column),
            ReadPlace::Scratch { slot } => (4, slot),
            ReadPlace::LayerOutput { layer, offset } => (100 + layer * 2 + field_index, offset),
            ReadPlace::CacheOutput { layer, offset } => (200 + layer * 2 + field_index, offset),
        };
        let matrix_base = (0x1000_0000usize + backing * 0x0010_0000) as *mut u8;
        let stride_bytes = if field == OperandField::Ext { 256 } else { 64 };
        ResolvedColumn {
            is_e4: field == OperandField::Ext,
            ptr: matrix_base.wrapping_add(column * stride_bytes as usize),
            matrix_base,
            stride_bytes,
        }
    }

    #[test]
    fn full_add_sub_group_lowers_to_the_census_shape() {
        use UnrolledCircuitType::NonMemory;
        use UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop;

        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json");
        let artifact: GKRCircuitArtifact<BF> =
            serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        let programs = GkrPrograms::compile(
            CircuitType::Unrolled(NonMemory(AddSubLuiAuipcMop)),
            Arc::new(artifact),
        )
        .unwrap();

        let mut resolved = Vec::<(GKRAddress, ResolvedColumn)>::new();
        let mut insert = |place: ReadPlace, field: OperandField| {
            let address = read_place_to_gkr_address(&place);
            let column = fake_column(place, field);
            if let Some((_, previous)) =
                resolved.iter().find(|(candidate, _)| *candidate == address)
            {
                assert_eq!(previous.is_e4, column.is_e4);
                assert_eq!(previous.ptr, column.ptr);
            } else {
                resolved.push((address, column));
            }
        };
        for layer in &programs.forward.layers {
            for instruction in &layer.program.instrs {
                let mut record = |operand: &OperandLine, field: OperandField| {
                    if let OperandLine::Source { window, column } = *operand {
                        let place = layer
                            .source_windows
                            .resolve_read_place(window, column)
                            .unwrap();
                        insert(place, field);
                    }
                };
                match instruction {
                    Instr::Add {
                        field, operands, ..
                    }
                    | Instr::Mul {
                        field, operands, ..
                    } => operands.iter().for_each(|operand| record(operand, *field)),
                    Instr::Fma {
                        field_lhs,
                        field_rhs,
                        pairs,
                        ..
                    } => pairs.iter().for_each(|(lhs, rhs)| {
                        record(lhs, *field_lhs);
                        record(rhs, *field_rhs);
                    }),
                    Instr::Mov {
                        field, dst, src, ..
                    } => {
                        if let Some(src) = src {
                            record(src, *field);
                        }
                        if let Some(DstLine::GlobalMaterialize { slot, col }) = dst {
                            let place = layer.backings.slot_col_to_read_place(*slot, *col).unwrap();
                            insert(place, *field);
                        }
                    }
                }
            }
            for special in layer.specials.iter() {
                if let ForwardSpecialStrategy::PeekDecoder { predicate } = special {
                    insert(*predicate, OperandField::Base);
                }
            }
        }
        let resolve = |address: GKRAddress| {
            resolved
                .iter()
                .find_map(|(candidate, column)| (*candidate == address).then_some(*column))
        };
        let header = FwdVmHeaderInputs {
            mapping_arena: [1 as *const u32, 2 as *const u32, 3 as *const u32],
            decoder_mapping_col: Some(0),
            table: 4 as *const E4,
            table_len: 16,
            count: 16,
            inits_and_teardowns_top_bits: &[0; 32],
        };

        let lowered = lower_group_desc(&programs.forward.layers, &header, &resolve, &|_| unsafe {
            core::mem::zeroed()
        })
        .unwrap();
        assert_eq!(lowered.desc.layer_count, 4);
        assert_eq!(lowered.source_window_count, 7);
        assert_eq!(
            lowered
                .desc
                .layers
                .iter()
                .take(4)
                .map(|layer| layer.program_offset)
                .collect::<Vec<_>>(),
            vec![0, 413, 511, 582],
        );
    }
}
