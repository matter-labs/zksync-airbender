use core::mem::{align_of, offset_of, size_of};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceVariable;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_gkr_compiler::{DrWindowInputProjection, DrWindowProgram, KERNEL_ARGUMENT_CEILING_BYTES};
use gpu_prover_context::ProverContext;

use super::{plan_dr_window_continuations_pr, DrWindowPassGeometryPr, PR_DR_WINDOW_COORDINATES};
use crate::backward::window_dr::{
    dr_window_partials_len, validate_dr_window_folding_steps, DrWindowBindError,
};
use crate::backward::{
    make_eq_sizes, pack_source_u16, FoldingArenaBinding, GkrEqSizes, GpuGKRDimensionReducingBatch,
    GpuGKRDimensionReducingSlot, GpuGKRDimensionReducingTables, GpuGKRSourceRecord,
    GKR_DIM_REDUCING_BASE_SLOTS, GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN,
    GKR_DIM_REDUCING_POLY_CAPACITY, GKR_EQ_GROUP_TABLE_LEN,
};
use crate::proth120::backward::eq::{launch_eq_high_low_pr, resolve_active_eq_slot_pr};
use crate::proth120::backward::window::{WindowTailStatePr, PR_WINDOW_TAIL_TENSOR_CELLS};
use crate::storage_layout::address_storage_layer;
use crate::upstream::{GKRAddress, PR};
use crate::{DrWindowLayerProgram, GpuGKRStorage};

const PR_DR_WINDOW_ROWS_PER_TILE: usize = 32;
const PR_DR_WINDOW_BLOCK_THREADS: u32 = 288;
const PR_DR_CONTINUATION_FIRST_ACCESS_BIT: u16 = 1 << 15;
const PR_DR_EQ_TABLE_SLOTS: usize = 3;

const _: () = assert!(PR_WINDOW_TAIL_TENSOR_CELLS == 27);

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct DrWindowLaunchBindingPr {
    pub(crate) batch: GpuGKRDimensionReducingBatch<PR>,
    pub(crate) batch_challenges: *const PR,
    pub(crate) eq_high_0: *const PR,
    pub(crate) eq_high_1: *const PR,
    pub(crate) partials: *mut PR,
    pub(crate) claim_point: *const PR,
    pub(crate) log_rows: u32,
    pub(crate) start_round: u32,
}

pub(crate) const PR_DR_WINDOW_ARGUMENT_BYTES: usize = size_of::<DrWindowLaunchBindingPr>();

const _: () = {
    assert!(size_of::<GpuGKRDimensionReducingBatch<PR>>() == 288);
    assert!(size_of::<DrWindowLaunchBindingPr>() == 336);
    assert!(align_of::<DrWindowLaunchBindingPr>() == 16);
    assert!(PR_DR_WINDOW_ARGUMENT_BYTES <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(offset_of!(DrWindowLaunchBindingPr, batch) == 0);
    assert!(offset_of!(DrWindowLaunchBindingPr, batch_challenges) == 288);
    assert!(offset_of!(DrWindowLaunchBindingPr, eq_high_0) == 296);
    assert!(offset_of!(DrWindowLaunchBindingPr, eq_high_1) == 304);
    assert!(offset_of!(DrWindowLaunchBindingPr, partials) == 312);
    assert!(offset_of!(DrWindowLaunchBindingPr, claim_point) == 320);
    assert!(offset_of!(DrWindowLaunchBindingPr, log_rows) == 328);
    assert!(offset_of!(DrWindowLaunchBindingPr, start_round) == 332);
};

cuda_kernel!(
    pub(crate) PrDrWindowR0,
    ab_pr_gkr_bwd_dr_window_r0_kernel(desc: DrWindowLaunchBindingPr)
);

cuda_kernel!(
    pub(crate) PrDrWindowContinuation,
    ab_pr_gkr_bwd_dr_window_continuation_kernel(desc: DrWindowLaunchBindingPr)
);

pub(crate) fn unwrap_dr_window_pr<T>(result: Result<T, DrWindowBindError>) -> CudaResult<T> {
    match result {
        Ok(value) => Ok(value),
        Err(DrWindowBindError::Cuda(error)) => Err(error),
        Err(error) => panic!("Proth120 DR window invariant failed: {error:?}"),
    }
}

pub(crate) fn schedule_dr_batch_challenge_table_pr(
    batching: *const PR,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<PR>> {
    assert!(
        !batching.is_null(),
        "Proth120 DR batch challenge base is null"
    );
    let mut table = context.alloc(
        GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN,
        AllocationPlacement::Top,
    )?;
    let base = unsafe { DeviceVariable::from_raw_parts(batching) };
    gpu_ops::powers::get_powers_by_ref::<PR>(base, 0, &mut table, context.get_exec_stream())?;
    Ok(table)
}

fn dr_window_row_tiles(folding_steps: usize) -> usize {
    (1usize << (folding_steps - PR_DR_WINDOW_COORDINATES))
        .div_ceil(PR_DR_WINDOW_ROWS_PER_TILE)
        .max(1)
}

fn dr_window_log_rows(folding_steps: usize) -> u32 {
    (folding_steps - PR_DR_WINDOW_COORDINATES) as u32
}

struct ResolvedStoragePr<'a> {
    backing: &'a Arc<DeviceAllocation<PR>>,
    log2_stride: u32,
    poly_index: usize,
}

fn resolve_storage_pr(
    storage: &GpuGKRStorage<PR, PR>,
    address: GKRAddress,
) -> Result<ResolvedStoragePr<'_>, DrWindowBindError> {
    let poly =
        storage
            .get_ext_poly_for_address(address)
            .ok_or(DrWindowBindError::MissingSource {
                address,
                logical_layer: address_storage_layer(address),
            })?;
    assert_eq!(
        poly.offset % poly.len,
        0,
        "Proth120 DR source must start at a column boundary"
    );
    Ok(ResolvedStoragePr {
        backing: &poly.backing,
        log2_stride: poly.len.ilog2(),
        poly_index: poly.offset / poly.len,
    })
}

pub(crate) struct DrWindowRawInputKeepalivePr {
    backings: Vec<Arc<DeviceAllocation<PR>>>,
}

impl DrWindowRawInputKeepalivePr {
    pub(crate) fn from_projection(
        storage: &GpuGKRStorage<PR, PR>,
        projection: &DrWindowInputProjection,
    ) -> Result<Self, DrWindowBindError> {
        let mut seen = BTreeSet::new();
        let mut backings = Vec::new();
        for &address in projection.canonical_sources() {
            let backing = Arc::clone(resolve_storage_pr(storage, address)?.backing);
            if seen.insert(Arc::as_ptr(&backing) as usize) {
                backings.push(backing);
            }
        }
        Ok(Self { backings })
    }

    pub(crate) fn canonical_source_pointers(
        &self,
        storage: &GpuGKRStorage<PR, PR>,
        projection: &DrWindowInputProjection,
    ) -> Result<Vec<*const PR>, DrWindowBindError> {
        projection
            .canonical_sources()
            .iter()
            .copied()
            .map(|address| {
                let resolved = resolve_storage_pr(storage, address)?;
                assert!(
                    self.backings
                        .iter()
                        .any(|backing| Arc::ptr_eq(backing, resolved.backing)),
                    "Proth120 DR raw-input keepalive must own the resolved backing"
                );
                let stride = 1usize.checked_shl(resolved.log2_stride).ok_or(
                    DrWindowBindError::ArenaGeometryOverflow {
                        log2_stride: resolved.log2_stride,
                        poly_count: resolved.poly_index + 1,
                    },
                )?;
                let offset = resolved.poly_index.checked_mul(stride).ok_or(
                    DrWindowBindError::ArenaGeometryOverflow {
                        log2_stride: resolved.log2_stride,
                        poly_count: resolved.poly_index + 1,
                    },
                )?;
                Ok(unsafe { resolved.backing.as_ptr().add(offset) })
            })
            .collect()
    }
}

struct DrCompactSourceTablePr {
    tables: GpuGKRDimensionReducingTables,
    by_backing: BTreeMap<usize, usize>,
    slot_count: usize,
}

impl DrCompactSourceTablePr {
    fn new() -> Self {
        Self {
            tables: GpuGKRDimensionReducingTables::default(),
            by_backing: BTreeMap::new(),
            slot_count: 0,
        }
    }

    fn intern_storage(
        &mut self,
        storage: &GpuGKRStorage<PR, PR>,
        address: GKRAddress,
    ) -> Result<u16, DrWindowBindError> {
        let resolved = resolve_storage_pr(storage, address)?;
        self.intern(
            resolved.backing.as_ptr().cast(),
            resolved.log2_stride,
            resolved.poly_index,
        )
    }

    fn intern_arena(
        &mut self,
        arena: FoldingArenaBinding,
        poly_index: usize,
    ) -> Result<u16, DrWindowBindError> {
        self.intern(arena.base, arena.log2_stride, poly_index)
    }

    fn finish(self) -> GpuGKRDimensionReducingTables {
        self.tables
    }

    fn intern(
        &mut self,
        backing: *const u8,
        log2_stride: u32,
        poly_index: usize,
    ) -> Result<u16, DrWindowBindError> {
        if poly_index >= GKR_DIM_REDUCING_POLY_CAPACITY {
            return Err(DrWindowBindError::PolyIndexOverflow {
                poly_index,
                capacity: GKR_DIM_REDUCING_POLY_CAPACITY,
            });
        }
        let backing_key = backing as usize;
        let slot = if let Some(&slot) = self.by_backing.get(&backing_key) {
            let expected_log2_stride = self.tables.log2_stride[slot];
            if expected_log2_stride != log2_stride {
                return Err(DrWindowBindError::StrideMismatch {
                    backing: backing_key,
                    expected_log2_stride,
                    observed_log2_stride: log2_stride,
                });
            }
            slot
        } else {
            if self.slot_count == GKR_DIM_REDUCING_BASE_SLOTS {
                return Err(DrWindowBindError::BaseSlotOverflow {
                    required: self.slot_count + 1,
                    capacity: GKR_DIM_REDUCING_BASE_SLOTS,
                });
            }
            let slot = self.slot_count;
            self.tables.bases[slot] = backing;
            self.tables.log2_stride[slot] = log2_stride;
            self.by_backing.insert(backing_key, slot);
            self.slot_count += 1;
            slot
        };
        Ok(pack_source_u16(false, slot as u8, poly_index as u16))
    }
}

struct DrEqCellsPr {
    cells: DeviceAllocation<PR>,
}

impl DrEqCellsPr {
    fn allocate(context: &ProverContext) -> CudaResult<Self> {
        Ok(Self {
            cells: context.alloc(
                PR_DR_EQ_TABLE_SLOTS * GKR_EQ_GROUP_TABLE_LEN,
                AllocationPlacement::Top,
            )?,
        })
    }

    fn high_0(&self) -> *mut PR {
        self.cells.as_ptr().cast_mut()
    }

    fn high_1(&self) -> *mut PR {
        unsafe { self.high_0().add(GKR_EQ_GROUP_TABLE_LEN) }
    }

    fn low(&self) -> *mut PR {
        unsafe { self.high_0().add(2 * GKR_EQ_GROUP_TABLE_LEN) }
    }
}

struct DrWindowArenaPr {
    allocation: DeviceAllocation<PR>,
    log2_stride: u32,
    poly_count: usize,
}

impl DrWindowArenaPr {
    fn allocate(
        context: &ProverContext,
        log2_stride: u32,
        poly_count: usize,
    ) -> Result<Self, DrWindowBindError> {
        let required = 1usize
            .checked_shl(log2_stride)
            .and_then(|len| len.checked_mul(poly_count))
            .ok_or(DrWindowBindError::ArenaGeometryOverflow {
                log2_stride,
                poly_count,
            })?;
        Ok(Self {
            allocation: context
                .alloc_with_extra_alignment::<PR, 1>(required, AllocationPlacement::Top)?,
            log2_stride,
            poly_count,
        })
    }

    fn binding(&self, log2_stride: u32) -> Result<FoldingArenaBinding, DrWindowBindError> {
        if log2_stride > self.log2_stride {
            return Err(DrWindowBindError::FinalPublicationStrideMismatch {
                owner_log2_stride: self.log2_stride,
                planned_log2_stride: log2_stride,
            });
        }
        Ok(FoldingArenaBinding::new(
            self.allocation.as_ptr().cast(),
            log2_stride,
        ))
    }
}

#[derive(Clone, Copy)]
pub(crate) struct DrLayerTranscriptPr {
    pub(crate) seed: *mut u8,
    pub(crate) claim: *mut PR,
    pub(crate) eq_prefactor: *mut PR,
    pub(crate) coeffs_out: *mut PR,
    pub(crate) point_out: *mut PR,
}

pub(crate) struct DrWindowContinuationPassPr {
    pub(crate) geometry: DrWindowPassGeometryPr,
    binding: Box<DrWindowLaunchBindingPr>,
    row_tiles: usize,
    slot_count: usize,
    eq_sizes: GkrEqSizes,
    eq_high_0: *mut PR,
    eq_high_1: *mut PR,
    eq_low: *mut PR,
}

impl DrWindowContinuationPassPr {
    #[cfg(test)]
    pub(crate) fn binding(&self) -> &DrWindowLaunchBindingPr {
        &self.binding
    }

    pub(crate) fn partial_rows(&self) -> usize {
        self.row_tiles * self.slot_count
    }

    pub(crate) fn launch(&self, context: &ProverContext) -> CudaResult<()> {
        let offset = self.geometry.eq_challenge_offset();
        let count = self.geometry.folding_steps - offset;
        debug_assert_eq!(self.binding.batch.eq_sizes, make_eq_sizes(count));
        launch_eq_high_low_pr(
            self.binding.claim_point,
            offset as u32,
            count as u32,
            self.eq_high_0,
            self.eq_high_1,
            self.eq_low,
            context,
        )?;
        let config = CudaLaunchConfig::basic(
            (self.row_tiles as u32, self.slot_count as u32),
            PR_DR_WINDOW_BLOCK_THREADS,
            context.get_exec_stream(),
        );
        PrDrWindowContinuationFunction::default().launch(
            &config,
            &PrDrWindowContinuationArguments::new(*self.binding),
        )
    }

    pub(crate) fn tail_state(&self, transcript: &DrLayerTranscriptPr) -> WindowTailStatePr {
        let start_round = self.geometry.start_round;
        let (active_eq_slot_base, active_eq_size_before_fold) =
            resolve_active_eq_slot_pr(&self.eq_sizes, self.eq_low, self.eq_high_0, self.eq_high_1);
        let point = unsafe { transcript.point_out.add(start_round) };
        WindowTailStatePr {
            partials: self.binding.partials,
            row_tiles: self.partial_rows(),
            reduced_tensor: unsafe {
                self.binding
                    .partials
                    .add(PR_WINDOW_TAIL_TENSOR_CELLS * self.partial_rows())
            },
            prev_claim_coords: point,
            seed: transcript.seed,
            claim: transcript.claim,
            eq_prefactor: transcript.eq_prefactor,
            coeffs_out: unsafe { transcript.coeffs_out.add(4 * start_round) },
            challenges_out: point,
            active_eq_slot_base,
            active_eq_size_before_fold,
        }
    }
}

pub(crate) struct DrWindowLayerHookPr {
    folding_steps: usize,
    #[cfg_attr(not(test), allow(dead_code))]
    entry_round: usize,
    claim_point: *const PR,
    r0: Box<DrWindowLaunchBindingPr>,
    r0_row_tiles: usize,
    r0_eq_sizes: GkrEqSizes,
    r0_eq: DrEqCellsPr,
    partials: DeviceAllocation<PR>,
    raw_inputs: DrWindowRawInputKeepalivePr,
    continuations: Vec<DrWindowContinuationPassPr>,
    continuation_eq: Option<DrEqCellsPr>,
    arenas: [Option<DrWindowArenaPr>; 2],
}

unsafe impl Send for DrWindowLayerHookPr {}
unsafe impl Sync for DrWindowLayerHookPr {}
unsafe impl Send for DrWindowContinuationPassPr {}
unsafe impl Sync for DrWindowContinuationPassPr {}
unsafe impl Send for DrLayerTranscriptPr {}
unsafe impl Sync for DrLayerTranscriptPr {}

fn build_r0_batch(
    program: &DrWindowProgram,
    storage: &GpuGKRStorage<PR, PR>,
    eq_low: *const PR,
    eq_sizes: GkrEqSizes,
) -> Result<GpuGKRDimensionReducingBatch<PR>, DrWindowBindError> {
    let mut batch = GpuGKRDimensionReducingBatch::<PR> {
        enabled_mask: program.enabled_mask(),
        eq_low,
        eq_sizes,
        ..Default::default()
    };
    let mut table = DrCompactSourceTablePr::new();
    for slot in program.slots() {
        let mut inputs = [GpuGKRSourceRecord::default(); 2];
        for (operand, source_id) in slot.source_ids().iter().copied().enumerate() {
            let address = program.sources()[usize::from(source_id)];
            inputs[operand] =
                GpuGKRSourceRecord::source_only(table.intern_storage(storage, address)?);
        }
        batch.slots[slot.slot()] = GpuGKRDimensionReducingSlot {
            inputs,
            batch_exp: *slot.batch_exponents(),
        };
    }
    batch.tables = table.finish();
    Ok(batch)
}

fn assemble_continuation_batch(
    program: &DrWindowProgram,
    projection: &DrWindowInputProjection,
    eq_low: *const PR,
    eq_sizes: GkrEqSizes,
    destination: FoldingArenaBinding,
    mut intern_source: impl FnMut(
        &mut DrCompactSourceTablePr,
        GKRAddress,
        u16,
    ) -> Result<u16, DrWindowBindError>,
) -> Result<GpuGKRDimensionReducingBatch<PR>, DrWindowBindError> {
    let mut batch = GpuGKRDimensionReducingBatch::<PR> {
        enabled_mask: program.enabled_mask(),
        eq_low,
        eq_sizes,
        ..Default::default()
    };
    let mut table = DrCompactSourceTablePr::new();
    let mut first_access_seen = BTreeSet::<u16>::new();
    for (dense_slot, slot) in program.slots().iter().enumerate() {
        let mut inputs = [GpuGKRSourceRecord::default(); 2];
        for (input_operand, record) in inputs.iter_mut().enumerate() {
            let publication_index = projection
                .publication_index(dense_slot, input_operand)
                .ok_or(DrWindowBindError::MissingPublicationIndex {
                    dense_slot,
                    input_operand,
                })?;
            let publication = usize::from(publication_index);
            if publication >= projection.canonical_sources().len() {
                return Err(DrWindowBindError::PublicationIndexOverflow {
                    publication_index: publication,
                    canonical_source_count: projection.canonical_sources().len(),
                });
            }
            let address = program.sources()[usize::from(slot.source_ids()[input_operand])];
            let source_base = intern_source(&mut table, address, publication_index)?;
            assert_eq!(
                source_base & PR_DR_CONTINUATION_FIRST_ACCESS_BIT,
                0,
                "Proth120 compact source tables must return a clear first-access bit"
            );
            let cache_base = table.intern_arena(destination, publication)?;
            assert_eq!(
                cache_base & PR_DR_CONTINUATION_FIRST_ACCESS_BIT,
                0,
                "Proth120 compact destination tables must return a clear first-access bit"
            );
            let source = if first_access_seen.insert(publication_index) {
                source_base | PR_DR_CONTINUATION_FIRST_ACCESS_BIT
            } else {
                source_base
            };
            *record = GpuGKRSourceRecord::new(source, cache_base);
        }
        batch.slots[slot.slot()] = GpuGKRDimensionReducingSlot {
            inputs,
            batch_exp: *slot.batch_exponents(),
        };
    }
    batch.tables = table.finish();
    Ok(batch)
}

fn validate_continuation_table_bases(
    batch: &GpuGKRDimensionReducingBatch<PR>,
) -> Result<(), DrWindowBindError> {
    for (slot, descriptor) in batch.slots.iter().enumerate() {
        if batch.enabled_mask & (1 << slot) == 0 {
            continue;
        }
        for input_operand in 0..2 {
            let record = descriptor.inputs[input_operand];
            for (table_slot, destination) in [
                (usize::from((record.src >> 11) & 0x0f), false),
                (usize::from((record.cache >> 11) & 0x0f), true),
            ] {
                if batch.tables.bases[table_slot].is_null() {
                    return Err(DrWindowBindError::NullContinuationTableBase {
                        slot,
                        input_operand,
                        table_slot,
                        destination,
                    });
                }
            }
        }
    }
    Ok(())
}

fn validate_continuation_eq(
    geometry: DrWindowPassGeometryPr,
    eq_sizes: GkrEqSizes,
    pointers: [(&'static str, *const PR); 3],
) -> Result<(), DrWindowBindError> {
    if eq_sizes != geometry.eq_entry_sizes() {
        return Err(DrWindowBindError::EqSizeMismatch);
    }
    for (name, pointer) in pointers {
        if pointer.is_null() {
            return Err(DrWindowBindError::NullContinuationPointer { pointer: name });
        }
    }
    for (first, second) in [(0, 1), (0, 2), (1, 2)] {
        if pointers[first].1 == pointers[second].1 {
            return Err(DrWindowBindError::ContinuationEqAliasedPointers {
                first: pointers[first].0,
                second: pointers[second].0,
            });
        }
    }
    Ok(())
}

impl DrWindowLayerHookPr {
    pub(crate) fn bind(
        program: &DrWindowLayerProgram,
        storage: &GpuGKRStorage<PR, PR>,
        entry_round: usize,
        batch_challenges: *const PR,
        claim_point_out: *const PR,
        context: &ProverContext,
    ) -> Result<Self, DrWindowBindError> {
        let folding_steps = program.folding_steps();
        validate_dr_window_folding_steps(folding_steps)?;
        let geometries = plan_dr_window_continuations_pr(folding_steps, entry_round)?;
        for (pointer, name) in [
            (batch_challenges, "batch_challenges"),
            (claim_point_out, "claim_point"),
        ] {
            if pointer.is_null() {
                return Err(DrWindowBindError::NullContinuationPointer { pointer: name });
            }
        }
        let projection = program.input_projection();
        let poly_count = projection.canonical_sources().len();
        let raw_inputs = DrWindowRawInputKeepalivePr::from_projection(storage, projection)?;

        let r0_row_tiles = dr_window_row_tiles(folding_steps);
        let slot_count = program.program().enabled_mask().count_ones() as usize;
        let partials_len = geometries
            .iter()
            .map(|geometry| {
                PR_WINDOW_TAIL_TENSOR_CELLS
                    * (dr_window_row_tiles(geometry.suffix_folding_steps()) * slot_count + 1)
            })
            .fold(dr_window_partials_len(folding_steps), usize::max);
        let mut partials = context.alloc(partials_len, AllocationPlacement::Top)?;
        let partials_ptr = partials.as_mut_ptr();

        let r0_eq = DrEqCellsPr::allocate(context)?;
        let r0_eq_sizes = make_eq_sizes(folding_steps - PR_DR_WINDOW_COORDINATES);
        let r0_batch = build_r0_batch(program.program(), storage, r0_eq.low(), r0_eq_sizes)?;
        let r0 = Box::new(DrWindowLaunchBindingPr {
            batch: r0_batch,
            batch_challenges,
            eq_high_0: r0_eq.high_0(),
            eq_high_1: r0_eq.high_1(),
            partials: partials_ptr,
            claim_point: core::ptr::null(),
            log_rows: dr_window_log_rows(folding_steps),
            start_round: 0,
        });

        let mut hook = Self {
            folding_steps,
            entry_round,
            claim_point: claim_point_out,
            r0,
            r0_row_tiles,
            r0_eq_sizes,
            r0_eq,
            partials,
            raw_inputs,
            continuations: Vec::with_capacity(geometries.len()),
            continuation_eq: None,
            arenas: [None, None],
        };
        if geometries.is_empty() {
            return Ok(hook);
        }

        let continuation_eq = DrEqCellsPr::allocate(context)?;
        for geometry in &geometries {
            let parity = geometry.destination();
            if hook.arenas[parity.index()].is_none() {
                hook.arenas[parity.index()] = Some(DrWindowArenaPr::allocate(
                    context,
                    geometry.log2_stride(),
                    poly_count,
                )?);
            }
        }
        let mut previous: Option<DrWindowPassGeometryPr> = None;
        for geometry in geometries {
            let eq_sizes = geometry.eq_entry_sizes();
            let destination_arena = hook.arenas[geometry.destination().index()]
                .as_ref()
                .expect("Proth120 DR destination arena was allocated");
            if destination_arena.poly_count < poly_count {
                return Err(DrWindowBindError::ArenaCapacity {
                    required: poly_count,
                    capacity: destination_arena.poly_count,
                });
            }
            let destination = destination_arena.binding(geometry.log2_stride())?;
            let batch = if geometry.reads_raw_storage() {
                assemble_continuation_batch(
                    program.program(),
                    projection,
                    continuation_eq.low(),
                    eq_sizes,
                    destination,
                    |table, address, _| table.intern_storage(storage, address),
                )?
            } else {
                let previous = previous.expect("Proth120 DR arena source follows a prior pass");
                debug_assert_eq!(previous.destination(), geometry.destination().opposite());
                let source = hook.arenas[previous.destination().index()]
                    .as_ref()
                    .expect("Proth120 DR source arena was allocated")
                    .binding(previous.log2_stride())?;
                assemble_continuation_batch(
                    program.program(),
                    projection,
                    continuation_eq.low(),
                    eq_sizes,
                    destination,
                    |table, _, publication_index| {
                        table.intern_arena(source, usize::from(publication_index))
                    },
                )?
            };
            validate_continuation_eq(
                geometry,
                batch.eq_sizes,
                [
                    ("eq_high_0", continuation_eq.high_0().cast_const()),
                    ("eq_high_1", continuation_eq.high_1().cast_const()),
                    ("eq_low", batch.eq_low),
                ],
            )?;
            validate_continuation_table_bases(&batch)?;
            let row_tiles = dr_window_row_tiles(geometry.suffix_folding_steps());
            let required = PR_WINDOW_TAIL_TENSOR_CELLS * (row_tiles * slot_count + 1);
            if hook.partials.len() < required {
                return Err(DrWindowBindError::ScratchCapacity {
                    required,
                    capacity: hook.partials.len(),
                });
            }
            hook.continuations.push(DrWindowContinuationPassPr {
                geometry,
                binding: Box::new(DrWindowLaunchBindingPr {
                    batch,
                    batch_challenges,
                    eq_high_0: continuation_eq.high_0(),
                    eq_high_1: continuation_eq.high_1(),
                    partials: partials_ptr,
                    claim_point: claim_point_out,
                    log_rows: dr_window_log_rows(geometry.suffix_folding_steps()),
                    start_round: geometry.start_round as u32,
                }),
                row_tiles,
                slot_count,
                eq_sizes,
                eq_high_0: continuation_eq.high_0(),
                eq_high_1: continuation_eq.high_1(),
                eq_low: continuation_eq.low(),
            });
            previous = Some(geometry);
        }
        debug_assert_eq!(
            hook.continuations.last().unwrap().geometry.start_round + PR_DR_WINDOW_COORDINATES,
            entry_round
        );
        hook.continuation_eq = Some(continuation_eq);
        Ok(hook)
    }

    pub(crate) fn folding_steps(&self) -> usize {
        self.folding_steps
    }

    #[cfg(test)]
    pub(crate) fn entry_round(&self) -> usize {
        self.entry_round
    }

    #[cfg(test)]
    pub(crate) fn r0_binding(&self) -> &DrWindowLaunchBindingPr {
        &self.r0
    }

    #[cfg(test)]
    pub(crate) fn r0_row_tiles(&self) -> usize {
        self.r0_row_tiles
    }

    pub(crate) fn continuations(&self) -> &[DrWindowContinuationPassPr] {
        &self.continuations
    }

    pub(crate) fn launch_r0(&self, context: &ProverContext) -> CudaResult<()> {
        launch_eq_high_low_pr(
            self.claim_point,
            PR_DR_WINDOW_COORDINATES as u32,
            (self.folding_steps - PR_DR_WINDOW_COORDINATES) as u32,
            self.r0_eq.high_0(),
            self.r0_eq.high_1(),
            self.r0_eq.low(),
            context,
        )?;
        let config = CudaLaunchConfig::basic(
            self.r0_row_tiles as u32,
            PR_DR_WINDOW_BLOCK_THREADS,
            context.get_exec_stream(),
        );
        PrDrWindowR0Function::default().launch(&config, &PrDrWindowR0Arguments::new(*self.r0))
    }

    pub(crate) fn r0_tail_state(&self, transcript: &DrLayerTranscriptPr) -> WindowTailStatePr {
        let (active_eq_slot_base, active_eq_size_before_fold) = resolve_active_eq_slot_pr(
            &self.r0_eq_sizes,
            self.r0_eq.low(),
            self.r0_eq.high_0(),
            self.r0_eq.high_1(),
        );
        WindowTailStatePr {
            partials: self.r0.partials,
            row_tiles: self.r0_row_tiles,
            reduced_tensor: unsafe {
                self.r0
                    .partials
                    .add(PR_WINDOW_TAIL_TENSOR_CELLS * self.r0_row_tiles)
            },
            prev_claim_coords: transcript.point_out,
            seed: transcript.seed,
            claim: transcript.claim,
            eq_prefactor: transcript.eq_prefactor,
            coeffs_out: transcript.coeffs_out,
            challenges_out: transcript.point_out,
            active_eq_slot_base,
            active_eq_size_before_fold,
        }
    }

    pub(crate) fn megakernel_source_pointers(
        &self,
        program: &DrWindowLayerProgram,
        storage: &GpuGKRStorage<PR, PR>,
    ) -> Result<Vec<*const PR>, DrWindowBindError> {
        let projection = program.input_projection();
        let canonical_count = projection.canonical_sources().len();
        let Some(last) = self.continuations.last() else {
            return self
                .raw_inputs
                .canonical_source_pointers(storage, projection);
        };
        let arena = self.arenas[last.geometry.destination().index()]
            .as_ref()
            .expect("Proth120 final DR continuation destination must remain owned");
        assert_eq!(arena.poly_count, canonical_count);
        let binding = arena.binding(last.geometry.log2_stride())?;
        let stride = 1usize << binding.log2_stride;
        Ok((0..canonical_count)
            .map(|poly_idx| unsafe { binding.base.cast::<PR>().add(poly_idx * stride) })
            .collect())
    }
}
