//! Binds backward VM programs to prover storage and prepares their launches.
//!
//! Source windows are rebound to actual storage geometry because aliases and
//! packing can make compiler windows non-contiguous.

use std::ptr::null_mut;

use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_gkr_compiler::{
    ContinuationLayerProgram, R0LayerProgram, WindowFamily, WindowProgram, KIND_ORDER,
    SOURCE_WINDOW_COLUMNS,
};
use std::collections::{BTreeMap, BTreeSet};

use super::continuation_golden::{
    BoundSourceDto, CanonicalPtr, CanonicalSlot, ContinuationGoldenDto, ContinuationRoundDto,
    FoldingBufferPatchDto, SourceRecordDto, GOLDEN_OFFSET_MASK, GOLDEN_REGION_CONTRIBUTIONS,
    GOLDEN_REGION_EQ_LOW, GOLDEN_REGION_MATRIX, GOLDEN_REGION_SHIFT, GOLDEN_TAG_SHIFT, NO_PUBLISH,
};
use super::seg::{
    bwd_seg_coeff_bank_device_ptr, bwd_seg_continuation_blocks_per_sm, bwd_seg_r0_blocks_per_sm,
    launch_bwd_seg_continuation, launch_bwd_seg_r0,
};
use super::seg_coeff_eval::{
    build_seg_coeff_eval_blob, build_seg_coeff_eval_window_blob, schedule_bwd_seg_coeff_bank_fill,
    SegCoeffEvalTables, BWD_SEG_CHALLENGE_CLAIM_BATCHING, BWD_SEG_CHALLENGE_LOOKUP_ADDITIVE,
    BWD_SEG_CHALLENGE_LOOKUP_MULTIPLICATIVE, BWD_SEG_CHALLENGE_PERM_LINEARIZATION_BASE,
    BWD_SEG_CHALLENGE_SLOTS,
};
use super::seg_desc::{BWD_COEFF_MAX_FOLD_DEPTH, BWD_SEG_ADDR_SLOTS};
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
use gpu_core::primitives::static_host::StaticPinnedBox;
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
    UnresolvedWindow {
        window: u8,
        address: GKRAddress,
    },
    WindowFieldMismatch {
        window: u8,
        expect_e4: bool,
    },
    UnresolvableRank {
        window: u8,
    },
    TooManyWindows {
        windows: usize,
        parents: usize,
    },
    BackingDeeperThanRound {
        window: u8,
        round: u8,
        backing_depth: u8,
    },
    FoldDepthExceeded {
        window: u8,
        round: u8,
        backing_depth: u8,
    },
}

pub(crate) fn family_read_place(family: WindowFamily, column: usize) -> Option<ReadPlace> {
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

// ── Where a continuation source's backing lives ──────────────────────────────

/// The binder's only view of storage. Production resolves against
/// [`GpuGKRStorage`]; the golden snapshot resolves against a synthetic address
/// space so the same construction can run without a device.
pub(crate) trait ExtSourceResolver {
    fn resolve(&self, place: ReadPlace, expect_e4: bool) -> Option<ResolvedColumn>;
    fn logical_address(&self, address: GKRAddress) -> GKRAddress;
}

struct StorageSourceResolver<'a, E: Copy>(&'a GpuGKRStorage<BF, E>);

impl<E: Copy> ExtSourceResolver for StorageSourceResolver<'_, E> {
    fn resolve(&self, place: ReadPlace, _expect_e4: bool) -> Option<ResolvedColumn> {
        resolve_storage_column(self.0, read_place_to_gkr_address(&place))
    }

    fn logical_address(&self, address: GKRAddress) -> GKRAddress {
        match self.0.layout.as_ref() {
            Some(layout) => logical_protocol_address(address, &layout.scratch_space_mapping_rev),
            None => address,
        }
    }
}

// ── The Ext shape phase (CPU) ────────────────────────────────────────────────

/// Where one continuation source's leaves come from at one ABSOLUTE round.
///
/// This is the only thing that fixes the round's fold delta, which is what makes
/// the sequence's first round a parameter rather than a constant 1: a source read
/// straight out of storage at round `r` folds `r` levels in the prologue, and one
/// read out of round `r - 1`'s folding buffer folds a single level.
#[derive(Clone, Debug)]
enum ContinuationBacking {
    RawColumn(ResolvedColumn),
    /// The `BwdSegAddrSlot` procedural-kind byte.
    Procedural(u8),
    PriorFoldingBuffer {
        round: u8,
        shape: FoldingBufferShape,
        /// This source's entry of the preceding round's publication map.
        column_map: BTreeMap<u32, usize>,
    },
}

impl ContinuationBacking {
    fn depth(&self) -> u8 {
        match self {
            Self::RawColumn(_) | Self::Procedural(_) => 0,
            Self::PriorFoldingBuffer { round, .. } => *round,
        }
    }

    fn origin(&self) -> SourceOrigin {
        match self {
            Self::RawColumn(column) if column.is_e4 => SourceOrigin::E4,
            Self::RawColumn(_) => SourceOrigin::Bf,
            Self::Procedural(_) => SourceOrigin::Procedural,
            Self::PriorFoldingBuffer { .. } => SourceOrigin::E4,
        }
    }
}

#[derive(Clone, Debug)]
struct ContinuationEntry {
    absolute_round: u8,
    backing: ContinuationBacking,
}

impl ContinuationEntry {
    fn backing_depth(&self) -> u8 {
        self.backing.depth()
    }

    /// The prologue's fold depth for this source, with both halves of the
    /// descriptor's depth contract enforced before the subtraction.
    fn delta(&self, window: u8) -> Result<u8, BwdVmBindError> {
        let backing_depth = self.backing_depth();
        let round = self.absolute_round;
        if backing_depth > round {
            return Err(BwdVmBindError::BackingDeeperThanRound {
                window,
                round,
                backing_depth,
            });
        }
        let delta = round - backing_depth;
        if delta > BWD_COEFF_MAX_FOLD_DEPTH {
            return Err(BwdVmBindError::FoldDepthExceeded {
                window,
                round,
                backing_depth,
            });
        }
        Ok(delta)
    }
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

fn bind_ext_round_sources(
    resolver: &dyn ExtSourceResolver,
    coord: &ContinuationLayerProgram,
    start_round: u8,
    folding_steps: usize,
) -> Result<BoundExtSources, BwdVmBindError> {
    assert!(folding_steps >= 2, "a continuation sequence needs rounds");
    assert!(start_round >= 1, "round 0 belongs to the R0 regime");
    let last_round = (folding_steps - 1) as u8;
    assert!(
        start_round <= last_round,
        "a continuation sequence starting at round {start_round} has no rounds \
         below the last round {last_round}"
    );

    let mut rounds = Vec::with_capacity(usize::from(last_round - start_round) + 1);
    let mut final_evaluations: BTreeMap<GKRAddress, usize> = BTreeMap::new();
    let mut previous_buffer: Option<(u8, FoldingBufferShape, BTreeMap<u32, usize>)> = None;
    for round in start_round..=last_round {
        let rows = 1usize << (folding_steps - usize::from(round) - 1);
        let mut folding_buffer = FoldingBufferShape {
            columns: 0,
            column_elems: 2 * rows,
        };
        let mut destinations = BTreeMap::new();
        let mut table = SlotTable::default();
        let mut patches: BTreeMap<usize, FoldingBufferSlot> = BTreeMap::new();
        let mut sources: Vec<Option<ResolvedSourceAddr>> =
            vec![None; coord.binding.source_slots.len()];

        for (parent, artifact_window) in coord.binding.windows.iter().enumerate() {
            let window = parent as u8;
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

                // A source chains exactly when the preceding round published it,
                // which is the fact the depth contract is stated against. The
                // sequence's first round has no preceding buffer at all.
                let backing = match previous_buffer.as_ref() {
                    Some((prior_round, shape, columns)) if columns.contains_key(&entry.source) => {
                        ContinuationBacking::PriorFoldingBuffer {
                            round: *prior_round,
                            shape: *shape,
                            column_map: BTreeMap::from([(entry.source, columns[&entry.source])]),
                        }
                    }
                    _ => match &place {
                        Some(place) => {
                            let resolved = resolver
                                .resolve(*place, e4_origin)
                                .ok_or(BwdVmBindError::UnresolvedWindow { window, address })?;
                            if resolved.is_e4 != e4_origin {
                                return Err(BwdVmBindError::WindowFieldMismatch {
                                    window,
                                    expect_e4: e4_origin,
                                });
                            }
                            ContinuationBacking::RawColumn(resolved)
                        }
                        None => match artifact_window.family {
                            WindowFamily::VirtualSetup { kind } => {
                                ContinuationBacking::Procedural(kind)
                            }
                            _ => unreachable!("an addressless window is procedural"),
                        },
                    },
                };
                let source_entry = ContinuationEntry {
                    absolute_round: round,
                    backing,
                };
                let delta = source_entry.delta(window)?;

                let (read_slot, read_column) = match &source_entry.backing {
                    ContinuationBacking::PriorFoldingBuffer {
                        round: prior_round,
                        shape,
                        column_map,
                    } => {
                        let column = column_map[&entry.source];
                        let resolved = shape.column(column);
                        let interned = table.intern(window, resolved, shape.column_elems as u32)?;
                        note_folding_buffer_slot(
                            &mut patches,
                            interned.0,
                            *prior_round,
                            shape,
                            column,
                        );
                        interned
                    }
                    ContinuationBacking::RawColumn(resolved) => {
                        let width = if resolved.is_e4 {
                            size_of::<E4>()
                        } else {
                            size_of::<BF>()
                        } as u32;
                        table.intern(window, *resolved, resolved.stride_bytes / width)?
                    }
                    ContinuationBacking::Procedural(kind) => table.intern_procedural(*kind),
                };
                let publish = if materializes(source_entry.backing.origin(), delta) {
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
                        let address = resolver.logical_address(address);
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
                    backing_depth: source_entry.backing_depth(),
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
        previous_buffer = Some((round, folding_buffer, destinations));
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

impl BwdVmRound0Launch {
    pub(crate) fn take_bank_staging(&mut self) -> Option<StaticPinnedBox<u8>> {
        self.tables.take_host_staging()
    }
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
    let blob =
        build_seg_coeff_eval_blob(&program.coefficient_recipes, inits_and_teardowns_top_bits)
            .unwrap_or_else(|error| panic!("backward VM R0 bank translation: {error:?}"));
    let tables = SegCoeffEvalTables::stage(&blob, context)?;

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
        &mut launch.tables,
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
    /// The absolute sumcheck round `rounds[0]` plays.
    start_round: u8,
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
    pub(crate) fn take_bank_staging(&mut self) -> Option<StaticPinnedBox<u8>> {
        self.tables.take_host_staging()
    }

    pub(crate) fn repoint_final_evaluations<E>(
        &self,
        sources: &mut BTreeMap<GKRAddress, *const E>,
    ) {
        let last_round = self.start_round + self.rounds.len() as u8 - 1;
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

/// One continuation round, bound and lowered but not yet allocated against.
struct PlannedExtRound {
    bound: BoundExtRound,
    setup: BwdSegSetup,
}

/// Bind and lower every continuation round of one layer. Shared by the
/// production launch builder and the golden snapshot, which differ only in the
/// resolver they hand it and in the `K` ceiling they pin.
fn plan_ext_rounds(
    resolver: &dyn ExtSourceResolver,
    program: &ContinuationLayerProgram,
    start_round: u8,
    folding_steps: usize,
    eq_low: *const E4,
    base_eq_sizes: GkrEqSizes,
    partials: *mut E4,
    ceiling: usize,
) -> (Vec<PlannedExtRound>, BTreeMap<GKRAddress, usize>) {
    let bound = bind_ext_round_sources(resolver, program, start_round, folding_steps)
        .unwrap_or_else(|error| panic!("backward VM Ext source binding: {error:?}"));
    let BoundExtSources {
        rounds: bound_rounds,
        final_evaluations,
    } = bound;

    let mut planned = Vec::with_capacity(bound_rounds.len());
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
            eq_sizes: drained_eq_sizes(base_eq_sizes, round.round - start_round + 1),
            contributions: partials,
            acc_size: round.rows as u32,
        };
        let setup = lower_bwd_seg_continuation(program, &binding, k).unwrap_or_else(|error| {
            panic!(
                "backward VM Ext lowering (round {}, K = {k}): {error:?}",
                round.round
            )
        });
        planned.push(PlannedExtRound {
            bound: round,
            setup,
        });
    }
    (planned, final_evaluations)
}

/// Build the continuation launch sequence for absolute rounds
/// `start_round..folding_steps`.
///
/// `base_eq_sizes` is the eq schedule as the sequence's PRODUCER left it — the
/// per-round arm hands over after round 0 (`make_eq_sizes(folding_steps - 1)`),
/// the windowed arm after the tail's own fold (`make_eq_sizes(folding_steps -
/// 3)`) — and each round drains it by its own position in the sequence.
pub(crate) fn build_bwd_vm_ext_rounds<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    program: &ContinuationLayerProgram,
    start_round: u8,
    folding_steps: usize,
    eq_low: *const E4,
    base_eq_sizes: GkrEqSizes,
    partials: *mut E4,
    inits_and_teardowns_top_bits: &[u32],
    context: &ProverContext,
) -> CudaResult<BwdVmExtLaunch> {
    let blob =
        build_seg_coeff_eval_blob(&program.coefficient_recipes, inits_and_teardowns_top_bits)
            .unwrap_or_else(|error| panic!("backward VM Ext bank translation: {error:?}"));
    let tables = SegCoeffEvalTables::stage(&blob, context)?;

    let ceiling = seg_k_ceiling(BwdRegime::Ext)?;
    let (planned, final_evaluations) = plan_ext_rounds(
        &StorageSourceResolver(storage),
        program,
        start_round,
        folding_steps,
        eq_low,
        base_eq_sizes,
        partials,
        ceiling,
    );
    let rounds = planned
        .into_iter()
        .map(|round| ExtRoundLaunch {
            setup: round.setup,
            elems: round.bound.folding_buffer.elems(),
            slots: round.bound.folding_buffer_slots,
        })
        .collect();
    let slab = context.alloc(BWD_SEG_CHALLENGE_SLOTS, AllocationPlacement::BestFit)?;
    Ok(BwdVmExtLaunch {
        start_round,
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
        &mut launch.tables,
        launch.slab.as_ptr(),
        bwd_seg_coeff_bank_device_ptr(),
        context.get_exec_stream(),
    )?;
    launch.filled = true;
    Ok(())
}

// ── The windowed arm's bank ──────────────────────────────────────────────────

/// The windowed arm's first fill: window-plan tables instead of R0 recipes. The
/// arm's second fill is the shared [`schedule_bwd_vm_ext_bank_fill`] above, so
/// both arms are two-fill and the ext refill is identical between them.
pub(crate) struct BwdVmWindowBank {
    tables: SegCoeffEvalTables,
    slab: DeviceAllocation<E4>,
}

impl BwdVmWindowBank {
    pub(crate) fn take_bank_staging(&mut self) -> Option<StaticPinnedBox<u8>> {
        self.tables.take_host_staging()
    }
}

#[allow(dead_code)]
pub(crate) fn build_bwd_vm_window_bank(
    program: &WindowProgram,
    inits_and_teardowns_top_bits: &[u32],
    context: &ProverContext,
) -> CudaResult<BwdVmWindowBank> {
    let blob =
        build_seg_coeff_eval_window_blob(&program.coefficient_plans, inits_and_teardowns_top_bits)
            .unwrap_or_else(|error| panic!("backward VM window bank translation: {error:?}"));
    let tables = SegCoeffEvalTables::stage(&blob, context)?;
    let slab = context.alloc(BWD_SEG_CHALLENGE_SLOTS, AllocationPlacement::BestFit)?;
    Ok(BwdVmWindowBank { tables, slab })
}

/// Fill the output bank with this layer's window plans.
///
/// Schedule position, fixed here and consumed by the windowed scheduler path:
/// window blob H2D copy + window-plan bank fill (this call) -> window kernel ->
/// ext blob copy + ext-recipe bank refill ([`schedule_bwd_vm_ext_bank_fill`]) ->
/// `TensorRoundTail` -> round-3 VM. The window kernel's bank reads must all be
/// enqueued before the ext refill overwrites the bank.
#[allow(dead_code)]
pub(crate) fn schedule_bwd_vm_window_bank_fill(
    bank: &mut BwdVmWindowBank,
    external_challenges: *const E4,
    lookup_multiplicative: *const E4,
    lookup_additive: *const E4,
    claim_batching: *const E4,
    context: &ProverContext,
) -> CudaResult<()> {
    schedule_seg_challenge_slab(
        &mut bank.slab,
        external_challenges,
        lookup_multiplicative,
        lookup_additive,
        claim_batching,
        context,
    )?;
    schedule_bwd_seg_coeff_bank_fill(
        &mut bank.tables,
        bank.slab.as_ptr(),
        bwd_seg_coeff_bank_device_ptr(),
        context.get_exec_stream(),
    )
}

// ── The continuation golden snapshot ─────────────────────────────────────────

/// The `K` ceiling the snapshot pins. Production reads its ceiling from device
/// occupancy; the golden is a builder-level differential, so it fixes the
/// highest admissible value and keeps the policy function itself in the loop.
const GOLDEN_K_CEILING: usize = 16;

/// A backing tag for the snapshot's synthetic address space: one matrix per
/// (family, layer, field), columns at their own rank inside it — the same
/// geometry production storage presents, with a semantic origin instead of a
/// device address.
fn golden_family_tag(place: ReadPlace, is_e4: bool) -> (usize, usize) {
    let field = usize::from(is_e4);
    match place {
        ReadPlace::BaseLayerMemory { column } => (1, column),
        ReadPlace::BaseLayerWitness { column } => (2, column),
        ReadPlace::Setup { column } => (3, column),
        ReadPlace::Scratch { slot } => (4, slot),
        ReadPlace::LayerOutput { layer, offset } => (0x100 + 2 * layer + field, offset),
        ReadPlace::CacheOutput { layer, offset } => (0x400 + 2 * layer + field, offset),
    }
}

struct GoldenSourceResolver {
    trace_len: usize,
    scratch_space_mapping_rev: BTreeMap<usize, GKRAddress>,
}

impl ExtSourceResolver for GoldenSourceResolver {
    fn resolve(&self, place: ReadPlace, expect_e4: bool) -> Option<ResolvedColumn> {
        let (tag, rank) = golden_family_tag(place, expect_e4);
        assert!(tag < 1 << 20, "golden family tag {tag} exceeds its field");
        let element = if expect_e4 {
            size_of::<E4>()
        } else {
            size_of::<BF>()
        };
        let stride_bytes = (self.trace_len * element) as u32;
        let matrix_base = (GOLDEN_REGION_MATRIX << GOLDEN_REGION_SHIFT) | (tag << GOLDEN_TAG_SHIFT);
        let offset = rank * stride_bytes as usize;
        assert!(
            offset <= GOLDEN_OFFSET_MASK,
            "golden column {rank} of {place:?} leaves its backing's offset field"
        );
        Some(ResolvedColumn {
            is_e4: expect_e4,
            ptr: (matrix_base + offset) as *const u8,
            matrix_base: matrix_base as *mut u8,
            stride_bytes,
        })
    }

    fn logical_address(&self, address: GKRAddress) -> GKRAddress {
        logical_protocol_address(address, &self.scratch_space_mapping_rev)
    }
}

fn golden_round_dto(round: &PlannedExtRound, immediates: usize) -> ContinuationRoundDto {
    let setup = &round.setup;
    let bound = &round.bound;
    let k = setup.k as usize;
    let program_words = setup.list_offset[k] as usize;
    ContinuationRoundDto {
        absolute_round: bound.round,
        rows: bound.rows as u64,
        k: setup.k,
        num_foldable: setup.num_foldable,
        logical_rows: setup.logical_rows,
        c_init_coeff: setup.c_init_coeff,
        eq_high: setup.eq_sizes.high.to_vec(),
        eq_low_size: setup.eq_sizes.low,
        eq_low: CanonicalPtr::of(setup.eq_low as usize),
        contributions: CanonicalPtr::of(setup.contributions as usize),
        folding_buffer_columns: bound.folding_buffer.columns as u32,
        folding_buffer_column_elems: bound.folding_buffer.column_elems as u64,
        folding_buffer_patches: bound
            .folding_buffer_slots
            .iter()
            .map(|patch| FoldingBufferPatchDto {
                slot: patch.slot as u32,
                buffer_round: patch.buffer_round,
                byte_offset: patch.byte_offset as u64,
            })
            .collect(),
        slots: bound
            .slots
            .iter()
            .zip(setup.slot.iter())
            .map(|(resolved, lowered)| CanonicalSlot {
                base: CanonicalPtr::of(lowered.base as usize),
                log2_stride: lowered.log2_stride,
                origin: lowered.origin,
                procedural_kind: lowered.procedural_kind,
                deferred_base: resolved.deferred_base,
                columns: resolved.columns as u32,
                read_elements: resolved.read_elements,
            })
            .collect(),
        sources: bound
            .sources
            .iter()
            .map(|source| BoundSourceDto {
                read_slot: source.read_slot as u32,
                read_column: source.read_column as u32,
                publish_slot: source.publish.map_or(NO_PUBLISH, |(slot, _)| slot as u32),
                publish_column: source
                    .publish
                    .map_or(NO_PUBLISH, |(_, column)| column as u32),
                backing_depth: source.backing_depth,
            })
            .collect(),
        records: setup.source[..bound.sources.len()]
            .iter()
            .map(|record| SourceRecordDto {
                src: record.src,
                cache: record.cache,
                class: record.class,
                delta: record.delta,
            })
            .collect(),
        fold_source: setup.fold_source[..setup.num_foldable as usize].to_vec(),
        list_offset: setup.list_offset[..k + 1].to_vec(),
        program: setup.program[..program_words].to_vec(),
        immediates: setup.immediates[..immediates].to_vec(),
    }
}

/// The continuation binder's construction for one layer, as a pointer-free DTO.
///
/// The eq base is the schedule the sequence's producer leaves behind, which is a
/// fresh build over the coordinates `start_round` onward — the same relation the
/// two production arms satisfy at `start_round` 1 and 3.
///
/// Deliberately `pub`: the capture bin is a separate crate and cannot reach the
/// crate-private binder. Nothing in production calls this.
#[doc(hidden)]
pub fn continuation_snapshot(
    programs: &crate::GkrPrograms,
    layer: usize,
    start_round: u8,
) -> ContinuationGoldenDto {
    let circuit = programs.runtime_circuit();
    assert!(
        circuit.trace_len.is_power_of_two(),
        "trace_len must be a power of two"
    );
    let folding_steps = circuit.trace_len.trailing_zeros() as usize;
    let resolver = GoldenSourceResolver {
        trace_len: circuit.trace_len,
        scratch_space_mapping_rev: circuit.scratch_space_mapping_rev.clone(),
    };
    let program = programs.continuation_layer(layer);
    let (planned, final_evaluations) = plan_ext_rounds(
        &resolver,
        program,
        start_round,
        folding_steps,
        (GOLDEN_REGION_EQ_LOW << GOLDEN_REGION_SHIFT) as *const E4,
        make_eq_sizes(folding_steps - usize::from(start_round)),
        (GOLDEN_REGION_CONTRIBUTIONS << GOLDEN_REGION_SHIFT) as *mut E4,
        GOLDEN_K_CEILING,
    );
    ContinuationGoldenDto {
        layer: layer as u32,
        start_round,
        folding_steps: folding_steps as u32,
        rounds: planned
            .iter()
            .map(|round| golden_round_dto(round, program.immediates.len()))
            .collect(),
        final_evaluations: ContinuationGoldenDto::final_evaluations_from(&final_evaluations),
    }
}

/// The golden's construction: the sequence as the per-round arm builds it.
#[doc(hidden)]
pub fn legacy_continuation_snapshot(
    programs: &crate::GkrPrograms,
    layer: usize,
) -> ContinuationGoldenDto {
    continuation_snapshot(programs, layer, 1)
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
    let start_round = u32::from(launch.start_round);
    assert!(
        round >= start_round,
        "round {round} is below the sequence's first round {start_round}"
    );
    let BwdVmExtLaunch { rounds, live, .. } = launch;
    let round_index = (round - start_round) as usize;
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
    if round > start_round {
        live.remove(&(round as u8 - 1));
    }
    Ok(())
}
