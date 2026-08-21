//! Binds backward VM programs to prover storage and prepares their launches.
//!
//! Source windows are rebound to actual storage geometry because aliases and
//! packing can make compiler windows non-contiguous.

use std::ptr::null_mut;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_gkr_compiler::{
    ContinuationLayerProgram, R0LayerProgram, WindowFamily, KIND_ORDER, SOURCE_WINDOW_COLUMNS,
};
use std::collections::{BTreeMap, BTreeSet};

use super::seg::{
    bwd_seg_coeff_bank_device_ptr, bwd_seg_continuation_blocks_per_sm, bwd_seg_r0_blocks_per_sm,
    launch_bwd_seg_continuation, launch_bwd_seg_r0,
};
use super::seg_coeff_eval::{
    build_seg_coeff_eval_tables_with_top_bits, schedule_bwd_seg_coeff_bank_fill,
    SegCoeffEvalTables, BWD_SEG_CHALLENGE_CLAIM_BATCHING, BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE,
    BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE, BWD_SEG_CHALLENGE_PERM_LINEARIZATION_BASE,
    BWD_SEG_CHALLENGE_SLOTS,
};
use super::seg_desc::{BWD_COEFF_PUBLISH_TARGET_DEPTH, BWD_SEG_ADDR_SLOTS};
use super::seg_lower::{
    lower_bwd_seg_continuation, lower_bwd_seg_r0, materializes, BwdSegRoundBinding, BwdSegSetup,
    ResolvedAddrSlot, ResolvedSourceAddr, SourceOrigin,
};
use crate::backward::{make_eq_sizes, record_active_eq_slot_fold, GkrEqSizes};
use crate::forward::vm::lower::{read_place_to_gkr_address, ResolvedColumn};
use crate::forward::vm::production_bind::resolve_storage_column;
use crate::transform::logical_protocol_address;
use crate::upstream::{
    BwdRegime, FieldKind, GKRAddress, ReadPlace, VirtualSetupKind, VirtualSetupPoly,
};
use crate::GpuGKRStorage;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

// ── The separate `K` policies ────────────────────────────────────────────────

const SEG_ALLOWED_K: [usize; 5] = [16, 8, 4, 2, 1];

const SEG_R0_WIDE_BYTES_PER_ROW: usize = 4 * 1024;
const SEG_CONTINUATION_WIDE_BYTES_PER_ROW: usize = 8 * 1024;

fn seg_r0_policy_k(bytes_per_row: usize, ceiling: usize) -> usize {
    let want = if bytes_per_row < SEG_R0_WIDE_BYTES_PER_ROW {
        4
    } else {
        16
    };
    clamp_policy_k(want, ceiling)
}

fn seg_continuation_policy_k(bytes_per_row: usize, ceiling: usize) -> usize {
    let want = if bytes_per_row < SEG_CONTINUATION_WIDE_BYTES_PER_ROW {
        8
    } else {
        16
    };
    clamp_policy_k(want, ceiling)
}

fn clamp_policy_k(want: usize, ceiling: usize) -> usize {
    let cap = want.min(ceiling);
    SEG_ALLOWED_K
        .into_iter()
        .filter(|k| *k <= cap)
        .max()
        .expect("the axis floor is below every ceiling, so some K always fits")
}

fn seg_k_ceiling(regime: BwdRegime) -> CudaResult<usize> {
    for k in SEG_ALLOWED_K {
        let blocks = match regime {
            BwdRegime::R0 => bwd_seg_r0_blocks_per_sm(k as u32)?,
            BwdRegime::Ext => bwd_seg_continuation_blocks_per_sm(k as u32)?,
        };
        if blocks > 0 {
            return Ok(k);
        }
    }
    panic!("no launchable segmented backward K for {regime:?}")
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum BwdVmBindError {
    UnresolvedWindow { window: u8, address: GKRAddress },
    WindowFieldMismatch { window: u8, expect_e4: bool },
    UnresolvableRank { window: u8 },
    TooManyWindows { windows: usize, parents: usize },
    ChainWithoutPriorFold { window: u8, source: u32 },
}

fn family_read_place(family: WindowFamily, column: usize) -> Option<ReadPlace> {
    match family {
        WindowFamily::BaseLayerMemory => Some(ReadPlace::BaseLayerMemory { column }),
        WindowFamily::BaseLayerWitness => Some(ReadPlace::BaseLayerWitness { column }),
        WindowFamily::Setup => Some(ReadPlace::Setup { column }),
        WindowFamily::Scratch => Some(ReadPlace::Scratch { slot: column }),
        WindowFamily::LayerOutput { layer, .. } => Some(ReadPlace::LayerOutput {
            layer,
            offset: column,
        }),
        WindowFamily::CacheOutput { layer, .. } => Some(ReadPlace::CacheOutput {
            layer,
            offset: column,
        }),
        WindowFamily::VirtualSetup { .. } => None,
    }
}

// ── The Ext shape phase (CPU) ────────────────────────────────────────────────

#[derive(Debug)]
struct ExtWindowShape {
    materialize: bool,
    chained: bool,
    backing_depth: u8,
}

fn ext_materialization_round(origin: SourceOrigin) -> u8 {
    match origin {
        SourceOrigin::E4 => 1,
        SourceOrigin::Bf | SourceOrigin::Procedural => BWD_COEFF_PUBLISH_TARGET_DEPTH,
    }
}

fn ext_round_window_shapes(coord: &ContinuationLayerProgram, round: u8) -> Vec<ExtWindowShape> {
    debug_assert!(round > 0);
    let mut shapes = Vec::with_capacity(coord.binding.windows.len());
    for window in coord.binding.windows.iter() {
        let address = family_read_place(window.family, window.first_column)
            .map(|place| read_place_to_gkr_address(&place));
        let is_e4_backing = window.backing_field() == FieldKind::Ext;
        let raw_origin = if address.is_none() {
            SourceOrigin::Procedural
        } else if is_e4_backing {
            SourceOrigin::E4
        } else {
            SourceOrigin::Bf
        };
        let chained = round > ext_materialization_round(raw_origin);
        let backing_depth = if chained { round - 1 } else { 0 };
        let delta = round - backing_depth;
        let origin = if chained {
            SourceOrigin::E4
        } else {
            raw_origin
        };
        let materialize = materializes(origin, delta);
        shapes.push(ExtWindowShape {
            materialize,
            chained,
            backing_depth,
        });
    }
    shapes
}

// ── The VM's own folding buffers ─────────────────────────────────────────────

#[derive(Clone, Copy, Debug)]
struct FoldingBufferShape {
    columns: usize,
    column_elems: usize,
}

impl FoldingBufferShape {
    fn stride_bytes(&self) -> u32 {
        (self.column_elems * size_of::<E4>()) as u32
    }

    fn elems(&self) -> usize {
        self.columns * self.column_elems
    }

    // The null base marks `ptr` as an offset patched after allocation.
    fn column(&self, column: usize) -> ResolvedColumn {
        let stride_bytes = self.stride_bytes();
        ResolvedColumn {
            is_e4: true,
            ptr: (column * stride_bytes as usize) as *const u8,
            matrix_base: null_mut(),
            stride_bytes,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FoldingBufferSlot {
    slot: usize,
    buffer_round: u8,
    byte_offset: usize,
}

fn virtual_setup_address(kind: u8) -> GKRAddress {
    GKRAddress::VirtualSetup(match KIND_ORDER[kind as usize] {
        VirtualSetupKind::RangeCheck16Bits => VirtualSetupPoly::RangeCheck16Bits,
        VirtualSetupKind::RangeCheckTimestamp => VirtualSetupPoly::RangeCheckTimestamp,
        VirtualSetupKind::InitsAndTeardownsLow => VirtualSetupPoly::InitsAndTeardownsLow,
        VirtualSetupKind::InitsAndTeardownsHigh => VirtualSetupPoly::InitsAndTeardownsHigh,
    })
}

// ── Pointer resolution (production) ──────────────────────────────────────────

struct BoundR0Sources {
    slots: Vec<ResolvedAddrSlot>,
    sources: Vec<ResolvedSourceAddr>,
}

#[derive(Default)]
struct SlotTable {
    slots: Vec<ResolvedAddrSlot>,
}

impl SlotTable {
    fn intern(
        &mut self,
        window: u8,
        column: ResolvedColumn,
        read_elements: u32,
    ) -> Result<(usize, usize), BwdVmBindError> {
        let stride = column.stride_bytes as usize;
        let ptr = column.ptr as usize;
        let base = column.matrix_base as usize;
        if stride == 0 || ptr < base || !(ptr - base).is_multiple_of(stride) {
            return Err(BwdVmBindError::UnresolvableRank { window });
        }
        let rank = (ptr - base) / stride;
        let chunk = rank / SOURCE_WINDOW_COLUMNS;
        let within = rank % SOURCE_WINDOW_COLUMNS;
        let chunk_base = base + chunk * SOURCE_WINDOW_COLUMNS * stride;
        let slot = match self.slots.iter().position(|entry| {
            entry.procedural_kind.is_none()
                && entry.base.is_some_and(|base| {
                    base.ptr as usize == chunk_base && base.stride_bytes == column.stride_bytes
                })
        }) {
            Some(slot) => {
                let entry = &mut self.slots[slot];
                entry.columns = entry.columns.max(within + 1);
                entry.read_elements = entry.read_elements.min(read_elements);
                slot
            }
            None => {
                self.slots.push(ResolvedAddrSlot {
                    base: Some(ResolvedColumn {
                        is_e4: column.is_e4,
                        ptr: chunk_base as *const u8,
                        matrix_base: column.matrix_base,
                        stride_bytes: column.stride_bytes,
                    }),
                    procedural_kind: None,
                    read_elements,
                    columns: within + 1,
                    deferred_base: column.matrix_base.is_null(),
                });
                self.slots.len() - 1
            }
        };
        Ok((slot, within))
    }

    fn intern_procedural(&mut self, kind: u8) -> (usize, usize) {
        if let Some(slot) = self
            .slots
            .iter()
            .position(|entry| entry.procedural_kind == Some(kind))
        {
            return (slot, 0);
        }
        self.slots.push(ResolvedAddrSlot {
            base: None,
            procedural_kind: Some(kind),
            read_elements: 0,
            columns: 1,
            deferred_base: false,
        });
        (self.slots.len() - 1, 0)
    }
}

/// Resolve one R0 coordinate's sources against production storage.
///
/// Every referenced column resolves independently and is interned into the slot
/// its own pointer implies ([`SlotTable`]). There is no re-partitioning of the
/// artifact's windows and no renumbering of its columns: the artifact's geometry
/// is simply not consulted, because a source's address is a fact about storage.
///
fn bind_r0_sources<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    coord: &R0LayerProgram,
) -> Result<BoundR0Sources, BwdVmBindError> {
    let mut table = SlotTable::default();
    let mut sources: Vec<Option<ResolvedSourceAddr>> = vec![None; coord.binding.source_slots.len()];

    for (index, artifact_window) in coord.binding.windows.iter().enumerate() {
        let window = index as u8;
        let expect_e4 = artifact_window.backing_field() == FieldKind::Ext;
        for entry in &artifact_window.columns {
            let (slot, column) = match family_read_place(artifact_window.family, entry.column) {
                None => match artifact_window.family {
                    WindowFamily::VirtualSetup { kind } => table.intern_procedural(kind),
                    _ => unreachable!("an addressless window is procedural"),
                },
                Some(place) => {
                    let address = read_place_to_gkr_address(&place);
                    let resolved = resolve_storage_column(storage, address)
                        .ok_or(BwdVmBindError::UnresolvedWindow { window, address })?;
                    if resolved.is_e4 != expect_e4 {
                        return Err(BwdVmBindError::WindowFieldMismatch { window, expect_e4 });
                    }
                    let width = if expect_e4 {
                        size_of::<E4>()
                    } else {
                        size_of::<BF>()
                    } as u32;
                    table.intern(window, resolved, resolved.stride_bytes / width)?
                }
            };
            sources[entry.source as usize] = Some(ResolvedSourceAddr {
                read_slot: slot,
                read_column: column,
                publish: None,
                backing_depth: 0,
            });
        }
    }

    let sources = sources
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .expect("every source slot belongs to exactly one artifact window column");
    let slots = table.slots;
    if slots.len() > BWD_SEG_ADDR_SLOTS {
        return Err(BwdVmBindError::TooManyWindows {
            windows: slots.len(),
            parents: coord.binding.windows.len(),
        });
    }

    Ok(BoundR0Sources { slots, sources })
}

// ── The Ext binding ──────────────────────────────────────────────────────────

struct BoundExtSources {
    rounds: Vec<BoundExtRound>,
    final_evaluations: BTreeMap<GKRAddress, usize>,
}

struct BoundExtRound {
    round: u8,
    rows: usize,
    slots: Vec<ResolvedAddrSlot>,
    sources: Vec<ResolvedSourceAddr>,
    folding_buffer: FoldingBufferShape,
    folding_buffer_slots: Vec<FoldingBufferSlot>,
}

fn note_folding_buffer_slot(
    patches: &mut BTreeMap<usize, FoldingBufferSlot>,
    slot: usize,
    buffer_round: u8,
    shape: &FoldingBufferShape,
    column: usize,
) {
    let chunk = column / SOURCE_WINDOW_COLUMNS;
    let entry = FoldingBufferSlot {
        slot,
        buffer_round,
        byte_offset: chunk * SOURCE_WINDOW_COLUMNS * shape.stride_bytes() as usize,
    };
    let previous = patches.insert(slot, entry);
    assert!(
        previous.is_none_or(|previous| previous == entry),
        "folding-buffer slot {slot} interned two different chunks: \
         {previous:?} then {entry:?}"
    );
}

fn bind_ext_round_sources<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    coord: &ContinuationLayerProgram,
    folding_steps: usize,
) -> Result<BoundExtSources, BwdVmBindError> {
    assert!(folding_steps >= 2, "a continuation sequence needs rounds");

    let logical = storage
        .layout
        .as_ref()
        .map(|layout| &layout.scratch_space_mapping_rev);
    let last_round = (folding_steps - 1) as u8;
    let mut rounds = Vec::with_capacity(folding_steps - 1);
    let mut final_evaluations: BTreeMap<GKRAddress, usize> = BTreeMap::new();
    let mut previous_buffer: Option<(FoldingBufferShape, BTreeMap<u32, usize>)> = None;
    for round in 1..folding_steps {
        let rows = 1usize << (folding_steps - round - 1);
        let round = round as u8;
        let shapes = ext_round_window_shapes(coord, round);
        let mut folding_buffer = FoldingBufferShape {
            columns: 0,
            column_elems: 2 * rows,
        };
        let mut destinations = BTreeMap::new();
        let chained_buffer = match round {
            1 => None,
            _ => previous_buffer.as_ref(),
        };
        let mut table = SlotTable::default();
        let mut patches: BTreeMap<usize, FoldingBufferSlot> = BTreeMap::new();
        let mut sources: Vec<Option<ResolvedSourceAddr>> = vec![None; coord.binding.source_slots.len()];

        for (parent, artifact_window) in coord.binding.windows.iter().enumerate() {
            let window = parent as u8;
            let shape = &shapes[parent];
            let e4_origin = artifact_window.backing_field() == FieldKind::Ext;
            for entry in &artifact_window.columns {
                let place = family_read_place(artifact_window.family, entry.column);
                let address = match &place {
                    Some(place) => read_place_to_gkr_address(place),
                    None => match artifact_window.family {
                        WindowFamily::VirtualSetup { kind } => virtual_setup_address(kind),
                        _ => unreachable!("an addressless window is procedural"),
                    },
                };

                let (read_slot, read_column) = if shape.chained {
                    let (buffer, columns) = chained_buffer.expect("a round-1 window cannot chain");
                    let column = *columns.get(&entry.source).ok_or(
                        BwdVmBindError::ChainWithoutPriorFold {
                            window,
                            source: entry.source,
                        },
                    )?;
                    let resolved = buffer.column(column);
                    let interned = table.intern(window, resolved, buffer.column_elems as u32)?;
                    note_folding_buffer_slot(&mut patches, interned.0, round - 1, buffer, column);
                    interned
                } else {
                    match &place {
                        Some(place) => {
                            let resolved =
                                resolve_storage_column(storage, read_place_to_gkr_address(place))
                                    .ok_or(BwdVmBindError::UnresolvedWindow { window, address })?;
                            if resolved.is_e4 != e4_origin {
                                return Err(BwdVmBindError::WindowFieldMismatch {
                                    window,
                                    expect_e4: e4_origin,
                                });
                            }
                            let width = if resolved.is_e4 {
                                size_of::<E4>()
                            } else {
                                size_of::<BF>()
                            } as u32;
                            table.intern(window, resolved, resolved.stride_bytes / width)?
                        }
                        None => match artifact_window.family {
                            WindowFamily::VirtualSetup { kind } => table.intern_procedural(kind),
                            _ => unreachable!("an addressless window is procedural"),
                        },
                    }
                };
                let publish = if shape.materialize {
                    let column = match destinations.get(&entry.source) {
                        Some(&column) => column,
                        None => {
                            let column = destinations.len();
                            destinations.insert(entry.source, column);
                            column
                        }
                    };
                    let resolved = folding_buffer.column(column);
                    let interned =
                        table.intern(window, resolved, folding_buffer.column_elems as u32)?;
                    note_folding_buffer_slot(
                        &mut patches,
                        interned.0,
                        round,
                        &folding_buffer,
                        column,
                    );
                    if round == last_round {
                        let address = match logical {
                            Some(rev) => logical_protocol_address(address, rev),
                            None => address,
                        };
                        final_evaluations
                            .entry(address)
                            .or_insert(column * folding_buffer.stride_bytes() as usize);
                    }
                    Some(interned)
                } else {
                    None
                };
                sources[entry.source as usize] = Some(ResolvedSourceAddr {
                    read_slot,
                    read_column,
                    publish,
                    backing_depth: shape.backing_depth,
                });
            }
        }

        folding_buffer.columns = destinations.len();
        let sources = sources
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .expect("every source slot belongs to exactly one artifact window column");
        let slots = table.slots;
        if slots.len() > BWD_SEG_ADDR_SLOTS {
            return Err(BwdVmBindError::TooManyWindows {
                windows: slots.len(),
                parents: coord.binding.windows.len(),
            });
        }
        rounds.push(BoundExtRound {
            round,
            rows,
            slots,
            sources,
            folding_buffer,
            folding_buffer_slots: patches.into_values().collect(),
        });
        previous_buffer = Some((folding_buffer, destinations));
    }

    Ok(BoundExtSources {
        rounds,
        final_evaluations,
    })
}

// ── The R0 launch ────────────────────────────────────────────────────────────

fn seg_r0_bytes_per_row(slots: &[ResolvedAddrSlot], sources: &[ResolvedSourceAddr]) -> usize {
    let mut bytes = 2 * size_of::<E4>();
    for (slot, columns) in addressed_columns(slots, sources) {
        let element = match slot.base {
            None => 0,
            Some(base) if base.is_e4 => size_of::<E4>(),
            Some(_) => size_of::<BF>(),
        };
        bytes += columns.len() * 2 * element;
    }
    bytes
}

fn addressed_columns<'a>(
    slots: &'a [ResolvedAddrSlot],
    sources: &[ResolvedSourceAddr],
) -> Vec<(&'a ResolvedAddrSlot, BTreeMap<usize, u8>)> {
    let mut addressed: Vec<(&ResolvedAddrSlot, BTreeMap<usize, u8>)> =
        slots.iter().map(|slot| (slot, BTreeMap::new())).collect();
    for source in sources {
        let depth = addressed[source.read_slot]
            .1
            .entry(source.read_column)
            .or_insert(source.backing_depth);
        *depth = (*depth).min(source.backing_depth);
    }
    addressed
}

pub(crate) struct BwdVmRound0Launch {
    setup: BwdSegSetup,
    tables: SegCoeffEvalTables,
    slab: DeviceAllocation<E4>,
}

pub(crate) fn build_bwd_vm_round0<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    program: &R0LayerProgram,
    rows: usize,
    eq_low: *const E4,
    eq_sizes: GkrEqSizes,
    contributions: *mut E4,
    inits_and_teardowns_top_bits: &[u32],
    context: &ProverContext,
) -> CudaResult<BwdVmRound0Launch> {
    let bound = bind_r0_sources(storage, program)
        .unwrap_or_else(|error| panic!("backward VM R0 source binding: {error:?}"));
    let tables = build_seg_coeff_eval_tables_with_top_bits(
        &program.coefficient_recipes,
        inits_and_teardowns_top_bits,
    )
    .unwrap_or_else(|error| panic!("backward VM R0 bank translation: {error:?}"));

    let bytes_per_row = seg_r0_bytes_per_row(&bound.slots, &bound.sources);
    let k = seg_r0_policy_k(bytes_per_row, seg_k_ceiling(BwdRegime::R0)?);
    let binding = BwdSegRoundBinding {
        round: 0,
        rows,
        slots: &bound.slots,
        sources: &bound.sources,
        claim_point_len: 0,
        coefficient_count: program.coefficient_recipes.len(),
        c_init: None,
        immediates: &[],
        eq_low,
        eq_sizes,
        contributions,
        acc_size: rows as u32,
    };
    let setup = lower_bwd_seg_r0(program, &binding, k)
        .unwrap_or_else(|error| panic!("backward VM R0 lowering (K = {k}): {error:?}"));

    let slab = context.alloc(BWD_SEG_CHALLENGE_SLOTS, AllocationPlacement::BestFit)?;
    Ok(BwdVmRound0Launch {
        setup,
        tables,
        slab,
    })
}

pub(crate) fn schedule_bwd_vm_round0(
    launch: &mut BwdVmRound0Launch,
    external_challenges: *const E4,
    lookup_multiplicative: *const E4,
    lookup_additive: *const E4,
    claim_batching: *const E4,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    // The descriptor was lowered at plan build for step 0's row count; a loop
    // handing it a different `acc_size` would compute garbage silently.
    let lowered_rows = launch.setup.logical_rows;
    assert_eq!(
        lowered_rows, acc_size,
        "the R0 descriptor was lowered for {lowered_rows} rows but round 0 runs at {acc_size}"
    );
    let stream = context.get_exec_stream();

    schedule_seg_challenge_slab(
        &mut launch.slab,
        external_challenges,
        lookup_multiplicative,
        lookup_additive,
        claim_batching,
        context,
    )?;
    schedule_bwd_seg_coeff_bank_fill(
        &launch.tables,
        launch.slab.as_ptr(),
        bwd_seg_coeff_bank_device_ptr(),
        stream,
    )?;
    launch_bwd_seg_r0(&launch.setup, context)
}

fn schedule_seg_challenge_slab(
    slab: &mut DeviceAllocation<E4>,
    external_challenges: *const E4,
    lookup_multiplicative: *const E4,
    lookup_additive: *const E4,
    claim_batching: *const E4,
    context: &ProverContext,
) -> CudaResult<()> {
    let stream = context.get_exec_stream();
    let prefix = BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE as usize;
    debug_assert_eq!(BWD_SEG_CHALLENGE_PERM_LINEARIZATION_BASE, 0);
    // SAFETY: all sources and the slab are device allocations of the copied size.
    unsafe {
        let external = DeviceSlice::from_raw_parts(external_challenges, prefix);
        memory_copy_async(&mut slab[..prefix], external, stream)?;
        for (slot, source) in [
            (
                BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE,
                lookup_multiplicative,
            ),
            (BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE, lookup_additive),
            (BWD_SEG_CHALLENGE_CLAIM_BATCHING, claim_batching),
        ] {
            let slot = slot as usize;
            let source = DeviceSlice::from_raw_parts(source, 1);
            memory_copy_async(&mut slab[slot..slot + 1], source, stream)?;
        }
    }
    Ok(())
}

// ── The Ext launch sequence ──────────────────────────────────────────────────

pub(crate) fn drained_eq_sizes(mut eq_sizes: GkrEqSizes, rounds: u8) -> GkrEqSizes {
    for _ in 0..rounds {
        record_active_eq_slot_fold(&mut eq_sizes);
    }
    eq_sizes
}

fn seg_ext_bytes_per_row(
    slots: &[ResolvedAddrSlot],
    sources: &[ResolvedSourceAddr],
    round: u8,
) -> usize {
    let mut bytes = 2 * size_of::<E4>();
    for (slot, columns) in addressed_columns(slots, sources) {
        let element = match slot.base {
            None => 0,
            Some(base) if base.is_e4 => size_of::<E4>(),
            Some(_) => size_of::<BF>(),
        };
        for backing_depth in columns.into_values() {
            let delta = round.saturating_sub(backing_depth);
            bytes += (2usize << delta) * element;
        }
    }
    let published: BTreeSet<(usize, usize)> = sources.iter().filter_map(|s| s.publish).collect();
    bytes += published.len() * 2 * size_of::<E4>();
    bytes
}

pub(crate) struct BwdVmExtLaunch {
    rounds: Vec<ExtRoundLaunch>,
    // The final buffer remains live for the layer's final gather.
    live: BTreeMap<u8, DeviceAllocation<E4>>,
    final_evaluations: BTreeMap<GKRAddress, usize>,
    tables: SegCoeffEvalTables,
    slab: DeviceAllocation<E4>,
    filled: bool,
}

struct ExtRoundLaunch {
    setup: BwdSegSetup,
    elems: usize,
    slots: Vec<FoldingBufferSlot>,
}

impl BwdVmExtLaunch {
    pub(crate) fn repoint_final_evaluations<E>(
        &self,
        sources: &mut BTreeMap<GKRAddress, *const E>,
    ) {
        let last_round = self.rounds.len() as u8;
        let buffer = self
            .live
            .get(&last_round)
            .expect("the last round's folding buffer must outlive the final gather");
        for (address, pointer) in sources.iter_mut() {
            let offset = self.final_evaluations.get(address).unwrap_or_else(|| {
                panic!(
                    "the final gather reads {address:?}, which no VM-owned round folds \
                     (the layer's lean coordinate is missing a source)"
                )
            });
            // SAFETY: the binder sized `buffer` for every recorded offset.
            *pointer = unsafe { buffer.as_ptr().cast::<u8>().add(*offset) }.cast::<E>();
        }
    }
}

pub(crate) fn build_bwd_vm_ext_rounds<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    program: &ContinuationLayerProgram,
    folding_steps: usize,
    eq_low: *const E4,
    partials: *mut E4,
    inits_and_teardowns_top_bits: &[u32],
    context: &ProverContext,
) -> CudaResult<BwdVmExtLaunch> {
    let bound = bind_ext_round_sources(storage, program, folding_steps)
        .unwrap_or_else(|error| panic!("backward VM Ext source binding: {error:?}"));
    let BoundExtSources {
        rounds: bound_rounds,
        final_evaluations,
    } = bound;
    let tables = build_seg_coeff_eval_tables_with_top_bits(
        &program.coefficient_recipes,
        inits_and_teardowns_top_bits,
    )
    .unwrap_or_else(|error| panic!("backward VM Ext bank translation: {error:?}"));

    let ceiling = seg_k_ceiling(BwdRegime::Ext)?;
    let mut rounds = Vec::with_capacity(bound_rounds.len());
    for round in bound_rounds {
        let bytes_per_row = seg_ext_bytes_per_row(&round.slots, &round.sources, round.round);
        let k = seg_continuation_policy_k(bytes_per_row, ceiling);
        let binding = BwdSegRoundBinding {
            round: u32::from(round.round),
            rows: round.rows,
            slots: &round.slots,
            sources: &round.sources,
            claim_point_len: folding_steps,
            coefficient_count: program.coefficient_recipes.len(),
            c_init: program.c_init,
            immediates: &program.immediates,
            eq_low,
            eq_sizes: drained_eq_sizes(make_eq_sizes(folding_steps - 1), round.round),
            contributions: partials,
            acc_size: round.rows as u32,
        };
        let setup = lower_bwd_seg_continuation(program, &binding, k).unwrap_or_else(|error| {
            panic!(
                "backward VM Ext lowering (round {}, K = {k}): {error:?}",
                round.round
            )
        });
        rounds.push(ExtRoundLaunch {
            setup,
            elems: round.folding_buffer.elems(),
            slots: round.folding_buffer_slots,
        });
    }
    let slab = context.alloc(BWD_SEG_CHALLENGE_SLOTS, AllocationPlacement::BestFit)?;
    Ok(BwdVmExtLaunch {
        rounds,
        live: BTreeMap::new(),
        final_evaluations,
        tables,
        slab,
        filled: false,
    })
}

pub(crate) fn schedule_bwd_vm_ext_bank_fill(
    launch: &mut BwdVmExtLaunch,
    external_challenges: *const E4,
    lookup_multiplicative: *const E4,
    lookup_additive: *const E4,
    claim_batching: *const E4,
    context: &ProverContext,
) -> CudaResult<()> {
    schedule_seg_challenge_slab(
        &mut launch.slab,
        external_challenges,
        lookup_multiplicative,
        lookup_additive,
        claim_batching,
        context,
    )?;
    schedule_bwd_seg_coeff_bank_fill(
        &launch.tables,
        launch.slab.as_ptr(),
        bwd_seg_coeff_bank_device_ptr(),
        context.get_exec_stream(),
    )?;
    launch.filled = true;
    Ok(())
}

pub(crate) fn schedule_bwd_vm_ext_round(
    launch: &mut BwdVmExtLaunch,
    round: u32,
    acc_size: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(
        launch.filled,
        "the Ext bank fill must be scheduled before any round launch"
    );
    let BwdVmExtLaunch { rounds, live, .. } = launch;
    let round_index = round as usize - 1;
    let ExtRoundLaunch {
        setup,
        elems,
        slots,
    } = &mut rounds[round_index];

    // ── This round's folding buffer, created JUST IN TIME ────────────────────
    // Allocation, launch, and reuse are ordered on the execution stream.
    let buffer: DeviceAllocation<E4> = context.alloc((*elems).max(1), AllocationPlacement::Top)?;
    live.insert(round as u8, buffer);

    // ── Fill in the addresses lowering deferred ──────────────────────────────
    for patch in slots {
        let buffer = live.get(&patch.buffer_round).unwrap_or_else(|| {
            panic!(
                "round {round} reads round {}'s folding buffer, which is no longer alive",
                patch.buffer_round
            )
        });
        let slot = &mut setup.slot[patch.slot];
        assert!(
            slot.base.is_null(),
            "round {round} slot {}: a deferred base was already resolved",
            patch.slot
        );
        // SAFETY: `byte_offset` is a chunk base inside the allocated buffer.
        slot.base = unsafe { buffer.as_ptr().cast::<u8>().add(patch.byte_offset) };
    }

    let lowered_rows = setup.logical_rows;
    assert_eq!(
        lowered_rows, acc_size,
        "the Ext descriptor for round {round} was lowered for {lowered_rows} rows but runs at {acc_size}"
    );
    launch_bwd_seg_continuation(round, setup, context)?;

    // ── Retire the buffer this launch just consumed ──────────────────────────
    // Retire the consumed buffer only after its reader is enqueued.
    if round > 1 {
        live.remove(&(round as u8 - 1));
    }
    Ok(())
}
