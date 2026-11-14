use std::{collections::BTreeMap, ptr};

use gpu_core::primitives::field::{BF, E4, PR};
use gpu_gkr_compiler::{
    encode_forward_runtime_program, virtual_setup_kind_code, CompiledLayer,
    ForwardDstLine as DstLine, ForwardInstr as Instr, ForwardLdcSub as LdcSub,
    ForwardOperandField as OperandField, ForwardOperandLine as OperandLine,
    ForwardProgram as Program, ForwardSpecialStrategy as SpecialStrategy,
    FORWARD_MAX_COLS as MAX_COLS,
};

use super::desc::{
    pack_desc, FwdVmLayer, ARENA_GENERIC_FAMILY, ARENA_RANGE_CHECK_16, ARENA_TIMESTAMP,
    ARG_DERIVED_E4_CAP, CONST_CAP, CONST_DERIVED_E4_CAP, DESC_CAP, DST_SLOT_COUNT, LAYER_CAP,
    MAPPING_ARENA_COUNT, PROGRAM_CAP, SD_AGGREGATE, SD_DECODER, SD_INITS_TOP_BITS, SD_SETUP,
    SD_SINGLE_COLUMN, SD_VIRTUAL, SOURCE_WINDOW_COUNT,
};
use crate::upstream::{ChallengeRef, Field, GKRAddress, PrimeField, RangeWidth, ReadPlace};

pub(crate) trait LoweringField: PrimeField {
    type Ext: Field;
    const NEEDS_SETUP_FILL: bool;
    const SEPARATE_DECODER_MAPPING: bool;
    fn canonical_constant(value: u128) -> Self;
    fn inits_top_bits(raw: u32, shift: u32) -> Self;
}

impl LoweringField for BF {
    type Ext = E4;
    const NEEDS_SETUP_FILL: bool = true;
    const SEPARATE_DECODER_MAPPING: bool = false;
    fn canonical_constant(value: u128) -> Self {
        let canonical = u32::try_from(value)
            .ok()
            .filter(|&v| v < BF::CHARACTERISTICS_U32)
            .unwrap_or_else(|| {
                panic!("forward constant {value} is not a canonical BabyBear value")
            });
        BF::from_u32_with_reduction(canonical)
    }
    fn inits_top_bits(raw: u32, shift: u32) -> Self {
        BF::from_u32_with_reduction(raw.checked_shl(shift).unwrap_or(0))
    }
}
impl LoweringField for PR {
    type Ext = PR;
    const NEEDS_SETUP_FILL: bool = false;
    const SEPARATE_DECODER_MAPPING: bool = true;
    fn canonical_constant(value: u128) -> Self {
        assert!(
            value < PR::CHARACTERISTICS_U128,
            "forward constant is not canonical"
        );
        PR::from_u128_with_reduction(value)
    }
    fn inits_top_bits(raw: u32, shift: u32) -> Self {
        PR::from_u128_with_reduction(u128::from(raw).checked_shl(shift).unwrap_or(0))
    }
}

pub(crate) struct DescFields<B, E> {
    pub arg_derived_e4: [E; ARG_DERIVED_E4_CAP],
    pub source_base: [*mut u8; SOURCE_WINDOW_COUNT],
    pub dst_base: [*mut u8; DST_SLOT_COUNT],
    pub mapping_arena: [*const u32; MAPPING_ARENA_COUNT],
    pub table: *const E,
    pub mask: *const B,
    pub decoder_mapping: *const u32,
    pub source_stride_bytes: [u32; SOURCE_WINDOW_COUNT],
    pub dst_stride_bytes: [u32; DST_SLOT_COUNT],
    pub consts: [B; CONST_CAP],
    pub table_len: u32,
    pub descs: [u32; DESC_CAP],
    pub count: u32,
    pub layer_count: u32,
    pub layers: [FwdVmLayer; LAYER_CAP],
    pub program: [u16; PROGRAM_CAP],
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ResolvedColumn {
    pub is_e4: bool,
    pub ptr: *const u8,
    pub matrix_base: *mut u8,
    pub stride_bytes: u32,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct FwdVmInputs<'a, E> {
    pub mapping_arena: [*const u32; MAPPING_ARENA_COUNT],
    pub decoder_mapping_col: Option<u16>,
    pub table: *const E,
    pub decoder_mapping: *const u32,
    pub table_len: u32,
    pub count: u32,
    pub inits_and_teardowns_top_bits: &'a [u32],
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

fn pack_source_geometry(uses: &[PhysicalSourceUse]) -> SourceGeometry {
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
                assert!(
                    geometry.n_windows != SOURCE_WINDOW_COUNT,
                    "forward source window overflow (required={:?})",
                    geometry.n_windows + 1
                );
                let window = geometry.n_windows as u8;
                let byte_offset = source
                    .matrix_column
                    .checked_mul(source.stride_bytes as usize)
                    .and_then(|offset| (source.matrix_base as usize).checked_add(offset))
                    .unwrap_or_else(|| {
                        panic!(
                            "forward source column off stride (window={:?}, column={:?})",
                            source.key.window, source.key.column
                        )
                    });
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
    geometry
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
) -> OperandLine {
    match operand {
        OperandLine::Source { window, column } => {
            let &(window, column) = sources
                .get(&SourceUseKey {
                    layer,
                    window,
                    column,
                })
                .unwrap_or_else(|| {
                    panic!(
                        "forward unmapped source (window={:?}, column={:?})",
                        window, column
                    )
                });
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
                        .unwrap_or_else(|| panic!("forward missing lookup additive slot")),
                }
            }
            LdcSub::Special => operand,
        },
        OperandLine::Special { desc } => OperandLine::Special {
            desc: bases.descriptor + desc,
        },
        other => other,
    }
}

fn rewrite_dst(
    layer: usize,
    dst: DstLine,
    destinations: &BTreeMap<DestinationUseKey, (u8, u16)>,
) -> DstLine {
    match dst {
        DstLine::GlobalMaterialize { slot, col } => {
            let &(slot, col) = destinations
                .get(&DestinationUseKey {
                    layer,
                    slot,
                    column: col,
                })
                .unwrap_or_else(|| {
                    panic!("forward unmapped global (slot={:?}, col={:?})", slot, col)
                });
            DstLine::GlobalMaterialize { slot, col }
        }
        other => other,
    }
}

fn rewrite_program(
    layer: usize,
    program: &Program,
    sources: &BTreeMap<SourceUseKey, (u8, u16)>,
    destinations: &BTreeMap<DestinationUseKey, (u8, u16)>,
    bases: LayerBankBases,
) -> Program {
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
                    .collect(),
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
                    .collect(),
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
                        (
                            rewrite_operand(layer, *lhs, sources, bases),
                            rewrite_operand(layer, *rhs, sources, bases),
                        )
                    })
                    .collect(),
            },
            Instr::Mov {
                dir,
                field,
                dst,
                src,
            } => Instr::Mov {
                dir: *dir,
                field: *field,
                dst: dst.map(|dst| rewrite_dst(layer, dst, destinations)),
                src: src.map(|src| rewrite_operand(layer, src, sources, bases)),
            },
        });
    }
    Program { instrs }
}

fn empty_desc<B, E>() -> DescFields<B, E> {
    unsafe { core::mem::zeroed() }
}

fn append_program<B, E>(
    desc: &mut DescFields<B, E>,
    next_lane: &mut usize,
    layer: usize,
    program: &Program,
) {
    assert!(layer < LAYER_CAP);
    let lanes = encode_forward_runtime_program(program).expect("forward program encoding failed");
    let end = next_lane
        .checked_add(lanes.len())
        .expect("forward encoded lane count overflow");
    assert!(
        end <= PROGRAM_CAP,
        "forward program overflow (lanes={:?})",
        end
    );
    desc.layers[layer] = FwdVmLayer {
        program_offset: u16::try_from(*next_lane).expect("PROGRAM_CAP fits u16"),
        instruction_count: u16::try_from(program.instrs.len())
            .expect("forward instruction count fits u16"),
    };
    desc.program[*next_lane..end].copy_from_slice(&lanes);
    *next_lane = end;
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

fn pack_destination_geometry(uses: &[PhysicalDestinationUse]) -> DestinationGeometry {
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
        assert!(
            destination.matrix_column < MAX_COLS as usize,
            "forward matrix col overflow (slot={:?}, col={:?}, matrix_col={:?})",
            destination.key.slot,
            destination.key.column,
            destination.matrix_column
        );
        let slot = match active {
            Some((is_e4, base, stride, slot))
                if is_e4 == destination.is_e4
                    && base == destination.matrix_base as usize
                    && stride == destination.stride_bytes =>
            {
                slot
            }
            _ => {
                assert!(
                    n_slots != DST_SLOT_COUNT,
                    "forward wire slot overflow (slot={:?}, col={:?})",
                    destination.key.slot,
                    destination.key.column
                );
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
    geometry
}

fn physical_matrix_column(resolved: ResolvedColumn, slot: u8, column: u16) -> usize {
    assert!(
        resolved.stride_bytes != 0,
        "forward source column off stride (window={:?}, column={:?})",
        slot,
        column
    );
    let offset = (resolved.ptr as usize)
        .checked_sub(resolved.matrix_base as usize)
        .unwrap_or_else(|| {
            panic!(
                "forward source column off stride (window={:?}, column={:?})",
                slot, column
            )
        });
    assert!(
        offset.is_multiple_of(resolved.stride_bytes as usize),
        "forward source column off stride (window={:?}, column={:?})",
        slot,
        column
    );
    offset / resolved.stride_bytes as usize
}

fn visit_layer_source_operands(
    layer_index: usize,
    layer: &CompiledLayer,
    mut visit: impl FnMut(SourceUseKey, OperandField),
) {
    let mut record = |operand: &OperandLine, field: OperandField| {
        if let OperandLine::Source { window, column } = *operand {
            visit(
                SourceUseKey {
                    layer: layer_index,
                    window,
                    column,
                },
                field,
            );
        }
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
                    record(operand, *field);
                }
            }
            Instr::Fma {
                field_lhs,
                field_rhs,
                pairs,
                ..
            } => {
                for (lhs, rhs) in pairs {
                    record(lhs, *field_lhs);
                    record(rhs, *field_rhs);
                }
            }
            Instr::Mov {
                field,
                src: Some(src),
                ..
            } => record(src, *field),
            Instr::Mov { src: None, .. } => {}
        }
    }
}

pub(crate) struct LoweredFwdVm<B, E> {
    pub desc: DescFields<B, E>,
    pub lookup_additive_slot: Option<usize>,
    pub decoder_fill_slot: Option<usize>,
    pub setup_fill_slot: Option<usize>,
}

pub(crate) fn lower_desc<B: LoweringField>(
    layers: &[CompiledLayer],
    header: &FwdVmInputs<'_, B::Ext>,
    resolve_column: &dyn Fn(GKRAddress) -> Option<ResolvedColumn>,
    challenge: &dyn Fn(&ChallengeRef) -> B::Ext,
) -> LoweredFwdVm<B, B::Ext> {
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
            assert!(source_field == field, "forward source field mismatch (window={:?}, column={:?}, expect_e4={:?}, got_e4={:?})", key.window, key.column, field == OperandField::Ext, source_field == OperandField::Ext);
            let place = layer
                .source_windows
                .resolve_read_place(key.window, key.column)
                .unwrap_or_else(|| {
                    panic!(
                        "forward unmapped source (window={:?}, column={:?})",
                        key.window, key.column
                    )
                });
            let address = read_place_to_gkr_address(&place);
            let resolved = resolve_column(address).unwrap_or_else(|| {
                panic!(
                    "forward unresolved column (slot={:?}, col={:?}, addr={:?})",
                    key.window, key.column, address
                )
            });
            let expect_e4 = field == OperandField::Ext;
            assert!(resolved.is_e4 == expect_e4, "forward source field mismatch (window={:?}, column={:?}, expect_e4={:?}, got_e4={:?})", key.window, key.column, expect_e4, resolved.is_e4);
            physical_sources.push(PhysicalSourceUse {
                key,
                is_e4: resolved.is_e4,
                matrix_base: resolved.matrix_base,
                stride_bytes: resolved.stride_bytes,
                matrix_column: physical_matrix_column(resolved, key.window, key.column),
            });
        });

        for instruction in &layer.program.instrs {
            let Instr::Mov {
                field,
                dst: Some(DstLine::GlobalMaterialize { slot, col }),
                ..
            } = instruction
            else {
                continue;
            };
            let place = layer
                .backings
                .slot_col_to_read_place(*slot, *col)
                .unwrap_or_else(|| {
                    panic!("forward unmapped global (slot={:?}, col={:?})", *slot, *col)
                });
            let address = read_place_to_gkr_address(&place);
            let resolved = resolve_column(address).unwrap_or_else(|| {
                panic!(
                    "forward unresolved column (slot={:?}, col={:?}, addr={:?})",
                    *slot, *col, address
                )
            });
            let expect_e4 = *field == OperandField::Ext;
            assert!(
                resolved.is_e4 == expect_e4,
                "forward slot field mismatch (slot={:?}, col={:?}, expect_e4={:?}, got_e4={:?})",
                *slot,
                *col,
                expect_e4,
                resolved.is_e4
            );
            physical_destinations.push(PhysicalDestinationUse {
                key: DestinationUseKey {
                    layer: layer_index,
                    slot: *slot,
                    column: *col,
                },
                is_e4: resolved.is_e4,
                matrix_base: resolved.matrix_base,
                stride_bytes: resolved.stride_bytes,
                matrix_column: physical_matrix_column(resolved, *slot, *col),
            });
        }
    }

    let source_geometry = pack_source_geometry(&physical_sources);
    let destination_geometry = pack_destination_geometry(&physical_destinations);
    let uses_lookup_additive = layers
        .iter()
        .any(|layer| layer.derived_e4.uses_lookup_additive());
    let uses_decoder_fill = layers.iter().any(|layer| {
        layer
            .specials
            .iter()
            .any(|special| matches!(special, SpecialStrategy::PeekDecoder { .. }))
    });
    let uses_setup_fill = B::NEEDS_SETUP_FILL
        && layers.iter().any(|layer| {
            layer
                .specials
                .iter()
                .any(|special| matches!(special, SpecialStrategy::PeekSetup))
        });
    let lookup_additive_slot = uses_lookup_additive.then_some(0usize);
    let decoder_fill_slot = uses_decoder_fill.then_some(usize::from(uses_lookup_additive));
    let setup_fill_slot = uses_setup_fill
        .then_some(usize::from(uses_lookup_additive) + usize::from(uses_decoder_fill));
    let n_const_derived = usize::from(uses_lookup_additive)
        + usize::from(uses_decoder_fill)
        + usize::from(uses_setup_fill);
    assert!(
        n_const_derived <= CONST_DERIVED_E4_CAP,
        "forward constant-derived field bank overflow (n={:?})",
        n_const_derived
    );

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
    let mut mask: *const B = ptr::null();
    for (layer_index, layer) in layers.iter().enumerate() {
        let constant_base = n_consts;
        for &value in layer.consts.values() {
            assert!(
                n_consts != CONST_CAP,
                "forward const bank overflow (n={:?})",
                n_consts + 1
            );
            desc.consts[n_consts] = B::canonical_constant(value);
            n_consts += 1;
        }

        let arg_base = n_args;
        for reference in layer.derived_e4.arg_refs() {
            assert!(
                n_args != ARG_DERIVED_E4_CAP,
                "forward argument-derived field bank overflow (n={:?})",
                n_args + 1
            );
            desc.arg_derived_e4[n_args] = challenge(reference);
            n_args += 1;
        }

        let descriptor_base = n_descs;
        let require_arena = |arena: u32| {
            assert!(
                !header.mapping_arena[arena as usize].is_null(),
                "forward mapping arena {arena} is missing"
            );
            arena
        };
        for special in layer.specials.iter() {
            assert!(
                n_descs != DESC_CAP,
                "forward desc overflow (n={:?})",
                n_descs + 1
            );
            let local_desc = n_descs - descriptor_base;
            desc.descs[n_descs] = match special {
                SpecialStrategy::PeekSingleColumn { set_index, width } => {
                    let arena = require_arena(match width {
                        RangeWidth::Bits16 => ARENA_RANGE_CHECK_16,
                        RangeWidth::Timestamp => ARENA_TIMESTAMP,
                    });
                    pack_desc(
                        SD_SINGLE_COLUMN,
                        arena,
                        u16::try_from(*set_index).unwrap_or_else(|_| {
                            panic!(
                                "forward set index overflow (desc={:?}, set_index={:?})",
                                n_descs, *set_index
                            )
                        }),
                        0,
                    )
                }
                SpecialStrategy::PeekAggregate { set_index } => {
                    uses_table = true;
                    let arena = require_arena(ARENA_GENERIC_FAMILY);
                    pack_desc(
                        SD_AGGREGATE,
                        arena,
                        u16::try_from(*set_index).unwrap_or_else(|_| {
                            panic!(
                                "forward set index overflow (desc={:?}, set_index={:?})",
                                n_descs, *set_index
                            )
                        }),
                        0,
                    )
                }
                SpecialStrategy::PeekSetup => {
                    uses_table = true;
                    pack_desc(SD_SETUP, 0, 0, setup_fill_slot.unwrap_or(0) as u32)
                }
                SpecialStrategy::PeekDecoder { predicate } => {
                    uses_table = true;
                    let arena = ARENA_GENERIC_FAMILY;
                    if B::SEPARATE_DECODER_MAPPING {
                        assert!(
                            !header.decoder_mapping.is_null(),
                            "forward decoder mapping is missing"
                        );
                    } else {
                        require_arena(arena);
                    }
                    let column = header
                        .decoder_mapping_col
                        .unwrap_or_else(|| panic!("forward missing decoder mapping col"));
                    let address = read_place_to_gkr_address(predicate);
                    let resolved = resolve_column(address).unwrap_or_else(|| {
                        panic!("forward decoder predicate unresolved (addr={:?})", address)
                    });
                    assert!(
                        !resolved.is_e4,
                        "forward decoder predicate not base (addr={:?})",
                        address
                    );
                    let predicate_mask = resolved.ptr as *const B;
                    if mask.is_null() {
                        mask = predicate_mask;
                    } else {
                        assert!(mask == predicate_mask, "forward decoder mask conflict");
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
                    assert!(
                        n_consts != CONST_CAP,
                        "forward const bank overflow (n={:?})",
                        n_consts + 1
                    );
                    let raw = *header
                        .inits_and_teardowns_top_bits
                        .get(reference.set_index)
                        .unwrap_or_else(|| {
                            panic!(
                                "forward set index overflow (desc={:?}, set_index={:?})",
                                local_desc, reference.set_index
                            )
                        });
                    desc.consts[n_consts] = B::inits_top_bits(raw, reference.shift);
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
        );
        append_program(&mut desc, &mut next_lane, layer_index, &rewritten);
    }

    if uses_table {
        assert!(!header.table.is_null(), "forward missing table");
        desc.table = header.table;
        desc.table_len = header.table_len;
    }
    desc.mask = mask;

    LoweredFwdVm {
        desc,
        lookup_additive_slot,
        decoder_fill_slot,
        setup_fill_slot,
    }
}

#[cfg(test)]
pub(crate) fn resolve_test_columns(
    layers: &[CompiledLayer],
    base_stride: u32,
) -> Vec<(GKRAddress, ResolvedColumn)> {
    fn fake_column(place: ReadPlace, field: OperandField, base_stride: u32) -> ResolvedColumn {
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
        let stride_bytes = if field == OperandField::Ext {
            256
        } else {
            base_stride
        };
        ResolvedColumn {
            is_e4: field == OperandField::Ext,
            ptr: matrix_base.wrapping_add(column * stride_bytes as usize),
            matrix_base,
            stride_bytes,
        }
    }

    let mut resolved = Vec::<(GKRAddress, ResolvedColumn)>::new();
    let mut insert = |place: ReadPlace, field: OperandField| {
        let address = read_place_to_gkr_address(&place);
        let column = fake_column(place, field, base_stride);
        if let Some((_, previous)) = resolved.iter().find(|(candidate, _)| *candidate == address) {
            assert_eq!(previous.is_e4, column.is_e4);
            assert_eq!(previous.ptr, column.ptr);
        } else {
            resolved.push((address, column));
        }
    };
    for layer in layers {
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
            if let SpecialStrategy::PeekDecoder { predicate } = special {
                insert(*predicate, OperandField::Base);
            }
        }
    }
    resolved
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::path::Path;
    use std::sync::Arc;

    use gpu_core::primitives::field::BF;
    use gpu_gkr_compiler::{
        ForwardDstLine as DstLine, ForwardInstr as Instr, ForwardLdcSub as LdcSub,
        ForwardOperandField as OperandField, ForwardOperandLine as OperandLine,
        ForwardProgram as Program,
    };
    use gpu_trace::witness::circuit_type::{
        CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
        UnrolledNonMemoryCircuitType,
    };

    use super::*;
    use crate::programs::GkrPrograms;
    use crate::upstream::{GKRAddress, GKRCircuitArtifact};

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
    fn cpu_physical_sources_pack_into_five_hundred_twelve_column_windows() {
        let uses = [
            source_use(0, 0, 0x1000, 0),
            source_use(0, 1, 0x1000, 127),
            source_use(1, 0, 0x1000, 128),
            source_use(1, 1, 0x1000, 511),
            source_use(1, 2, 0x1000, 512),
        ];

        let geometry = pack_source_geometry(&uses);
        assert_eq!(geometry.n_windows, 2);
        assert_eq!(geometry.base[0] as usize, 0x1000);
        assert_eq!(geometry.base[1] as usize, 0x1000 + 512 * 16);
        assert_eq!(geometry.remap[&uses[0].key], (0, 0));
        assert_eq!(geometry.remap[&uses[3].key], (0, 511));
        assert_eq!(geometry.remap[&uses[4].key], (1, 0));
    }

    #[test]
    #[should_panic(expected = "source window overflow")]
    fn cpu_seventeenth_physical_source_window_is_rejected() {
        let uses = (0..17)
            .map(|index| source_use(index, 0, 0x1000 + index * 0x1000, 0))
            .collect::<Vec<_>>();
        pack_source_geometry(&uses);
    }

    #[test]
    fn cpu_rewrite_rebases_every_layer_local_bank() {
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

        let rewritten = rewrite_program(7, &program, &sources, &destinations, bases);
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
    fn cpu_encoded_programs_concatenate_and_record_layer_boundaries() {
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
        let mut desc = empty_desc::<BF, E4>();
        let mut next_lane = 0;

        append_program(&mut desc, &mut next_lane, 0, &first);
        append_program(&mut desc, &mut next_lane, 1, &second);

        assert_eq!(desc.layers[0].program_offset, 0);
        assert_eq!(desc.layers[0].instruction_count, 1);
        assert_eq!(desc.layers[1].program_offset, 2);
        assert_eq!(desc.layers[1].instruction_count, 2);
        assert_eq!(next_lane, 6);
        assert_eq!(&desc.program[..6], &[3, 5, 3, 9, 7, 6]);
    }

    fn lower_embedded_circuit(layout: &str, circuit_type: CircuitType) {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../cs/compiled_circuits")
            .join(layout);
        let artifact: GKRCircuitArtifact<BF> =
            serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        let programs = GkrPrograms::compile(circuit_type, Arc::new(artifact)).unwrap();
        crate::forward::recompute_plan::check_recompute_bindings(&programs);

        let resolved = resolve_test_columns(&programs.forward.layers, 64);
        let resolve = |address: GKRAddress| {
            resolved
                .iter()
                .find_map(|(candidate, column)| (*candidate == address).then_some(*column))
        };
        let header = super::super::lower::FwdVmInputs {
            mapping_arena: [
                std::ptr::without_provenance(1),
                std::ptr::without_provenance(2),
                std::ptr::without_provenance(3),
            ],
            decoder_mapping_col: Some(0),
            table: std::ptr::without_provenance(4),
            table_len: 16,
            count: 16,
            inits_and_teardowns_top_bits: &[0; 32],
        };

        super::super::lower::lower_desc(&programs.forward.layers, &header, &resolve, &|_| unsafe {
            core::mem::zeroed()
        });
    }

    #[test]
    fn cpu_all_embedded_forward_circuits_fit_one_descriptor() {
        use DelegationCircuitType::*;
        use UnrolledCircuitType::*;
        use UnrolledMemoryCircuitType::*;
        use UnrolledNonMemoryCircuitType::*;

        let cases = [
            (
                "add_sub_lui_auipc_mop_layout_gkr.json",
                CircuitType::Unrolled(NonMemory(AddSubLuiAuipcMop)),
            ),
            (
                "jump_branch_slt_layout_gkr.json",
                CircuitType::Unrolled(NonMemory(JumpBranchSlt)),
            ),
            (
                "unsigned_mul_div_layout_gkr.json",
                CircuitType::Unrolled(NonMemory(MulDivUnsigned)),
            ),
            (
                "shift_binop_layout_gkr.json",
                CircuitType::Unrolled(NonMemory(ShiftBinary)),
            ),
            (
                "mem_word_only_layout_gkr.json",
                CircuitType::Unrolled(Memory(LoadStoreWordOnly)),
            ),
            (
                "mem_subword_only_layout_gkr.json",
                CircuitType::Unrolled(Memory(LoadStoreSubwordOnly)),
            ),
            (
                "inits_and_teardowns_layout_gkr.json",
                CircuitType::Unrolled(InitsAndTeardowns),
            ),
            (
                "unified_reduced_machine_layout_gkr.json",
                CircuitType::Unrolled(Unified),
            ),
            (
                "bigint_with_extended_control_layout_gkr.json",
                CircuitType::Delegation(BigIntWithControl),
            ),
            (
                "keccak_special5_layout_gkr.json",
                CircuitType::Delegation(KeccakSpecial5),
            ),
            (
                "blake2_with_extended_control_layout_gkr.json",
                CircuitType::Delegation(Blake2WithCompression),
            ),
            (
                "blake2_g_function_layout_gkr.json",
                CircuitType::Delegation(Blake2GFunction),
            ),
        ];

        for (layout, circuit_type) in cases {
            lower_embedded_circuit(layout, circuit_type);
        }
    }
}
