use crate::backward::window_dr::shared::{self, DrCompactSourceTable};
use crate::backward::window_dr::DrWindowBindError;
use crate::backward::window_dr::{dr_window_log_rows, dr_window_row_tiles};
use core::mem::{align_of, offset_of, size_of};

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_gkr_compiler::{DrWindowInputProjection, DrWindowProgram, KERNEL_ARGUMENT_CEILING_BYTES};
use gpu_prover_context::ProverContext;
use std::ffi::c_void;

use super::{plan_dr_window_continuations_pr, DrWindowPassGeometryPr, PR_DR_WINDOW_COORDINATES};
use crate::backward::window_dr::{dr_window_partials_len, validate_dr_window_folding_steps};
use crate::backward::{
    make_eq_sizes, FoldingArenaBinding, GkrEqSizes, GpuGKRDimensionReducingBatch,
    GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN, GKR_EQ_GROUP_TABLE_LEN,
};
use crate::proth120::backward::eq::{launch_eq_high_low_pr, resolve_active_eq_slot_pr};
use crate::proth120::backward::window::{WindowTailStatePr, PR_WINDOW_TAIL_TENSOR_CELLS};
use crate::upstream::{GKRAddress, PR};
use crate::{DrWindowLayerProgram, GpuGKRStorage};

const PR_DR_WINDOW_BLOCK_THREADS: u32 = 288;
const PR_DR_EQ_TABLE_SLOTS: usize = 3;

const _: () = assert!(PR_WINDOW_TAIL_TENSOR_CELLS == 27);

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct DrWindowLaunchBindingPr {
    pub(crate) batch: GpuGKRDimensionReducingBatch<PR>,
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
    assert!(offset_of!(DrWindowLaunchBindingPr, eq_high_0) == 288);
    assert!(offset_of!(DrWindowLaunchBindingPr, eq_high_1) == 296);
    assert!(offset_of!(DrWindowLaunchBindingPr, partials) == 304);
    assert!(offset_of!(DrWindowLaunchBindingPr, claim_point) == 312);
    assert!(offset_of!(DrWindowLaunchBindingPr, log_rows) == 320);
    assert!(offset_of!(DrWindowLaunchBindingPr, start_round) == 324);
};

cuda_kernel!(
    pub(crate) PrDrWindowR0,
    ab_pr_gkr_bwd_dr_window_r0_kernel(desc: DrWindowLaunchBindingPr)
);

cuda_kernel!(
    pub(crate) PrDrWindowContinuation,
    ab_pr_gkr_bwd_dr_window_continuation_kernel(desc: DrWindowLaunchBindingPr)
);

cuda_struct_and_stub! {
    static ab_pr_gkr_dim_reducing_batch_challenge_table:
        [PR; GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN];
}

pub(crate) fn schedule_dr_batch_challenge_table_pr(
    batching: *const PR,
    context: &ProverContext,
) -> CudaResult<*const PR> {
    assert!(
        !batching.is_null(),
        "Proth120 DR batch challenge base is null"
    );
    let mut address: *mut c_void = std::ptr::null_mut();
    // SAFETY: the CUDA definition and Rust stub name the same ten-element symbol.
    unsafe {
        cudaGetSymbolAddress(
            &mut address,
            &ab_pr_gkr_dim_reducing_batch_challenge_table as *const _ as *const c_void,
        )
    }
    .wrap()?;
    // SAFETY: symbol storage spans exactly this table and lives for the CUDA context.
    // The exec-stream prelude precedes its readers, as for the BabyBear table.
    let table = unsafe {
        DeviceSlice::from_raw_parts_mut(
            address.cast::<PR>(),
            GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN,
        )
    };
    // SAFETY: the layer keeps its device-resident batching scalar alive through the prelude.
    let base = unsafe { DeviceVariable::from_raw_parts(batching) };
    gpu_ops::powers::get_powers_by_ref::<PR>(base, 0, table, context.get_exec_stream())?;
    Ok(table.as_ptr())
}

pub(crate) type DrWindowRawInputKeepalivePr = shared::DrRawInputKeepalive<PR>;

pub(in crate::proth120::backward) fn assert_binding<T>(result: Result<T, DrWindowBindError>) -> T {
    result.unwrap_or_else(|error| panic!("Proth120 binding {error}"))
}

struct DrEqCellsPr {
    cells: DeviceAllocation<PR>,
}

impl DrEqCellsPr {
    fn allocate(context: &ProverContext) -> CudaResult<Self> {
        let cells = context.alloc(
            PR_DR_EQ_TABLE_SLOTS * GKR_EQ_GROUP_TABLE_LEN,
            AllocationPlacement::Top,
        )?;

        Ok(Self { cells })
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
    fn allocate(context: &ProverContext, log2_stride: u32, poly_count: usize) -> CudaResult<Self> {
        let required = 1usize
            .checked_shl(log2_stride)
            .and_then(|len| len.checked_mul(poly_count))
            .unwrap_or_else(|| {
                panic!(
                    "Proth120 binding ArenaGeometryOverflow: log2_stride={:?}, poly_count={:?}",
                    log2_stride, poly_count
                )
            });
        Ok(Self {
            allocation: context
                .alloc_with_extra_alignment::<PR, 1>(required, AllocationPlacement::Top)?,
            log2_stride,
            poly_count,
        })
    }

    fn binding(&self, log2_stride: u32) -> FoldingArenaBinding {
        assert!(log2_stride <= self.log2_stride,
            "Proth120 binding FinalPublicationStrideMismatch: owner_log2_stride={:?}, planned_log2_stride={:?}", self.log2_stride, log2_stride
        );
        FoldingArenaBinding::new(self.allocation.as_ptr().cast(), log2_stride)
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
) -> GpuGKRDimensionReducingBatch<PR> {
    assert_binding(shared::assemble_r0_batch(
        program,
        eq_low,
        eq_sizes,
        |table, address| table.intern_storage(storage, address),
    ))
}

fn assemble_continuation_batch(
    program: &DrWindowProgram,
    projection: &DrWindowInputProjection,
    eq_low: *const PR,
    eq_sizes: GkrEqSizes,
    destination: FoldingArenaBinding,
    intern_source: impl FnMut(
        &mut DrCompactSourceTable,
        GKRAddress,
        u16,
    ) -> Result<u16, DrWindowBindError>,
) -> GpuGKRDimensionReducingBatch<PR> {
    assert_binding(shared::assemble_continuation_batch(
        program,
        projection,
        eq_low,
        eq_sizes,
        destination,
        intern_source,
    ))
}

fn validate_continuation_table_bases(batch: &GpuGKRDimensionReducingBatch<PR>) {
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
                assert!(!batch.tables.bases[table_slot].is_null(),
                    "Proth120 binding NullContinuationTableBase: slot={:?}, input_operand={:?}, table_slot={:?}, destination={:?}", slot, input_operand, table_slot, destination
                );
            }
        }
    }
}

fn validate_continuation_eq(
    geometry: DrWindowPassGeometryPr,
    eq_sizes: GkrEqSizes,
    pointers: [(&'static str, *const PR); 3],
) {
    assert!(
        eq_sizes == geometry.eq_entry_sizes(),
        "Proth120 binding EqSizeMismatch"
    );
    for (name, pointer) in pointers {
        assert!(
            !pointer.is_null(),
            "Proth120 binding NullContinuationPointer: pointer={:?}",
            name
        );
    }
    for (first, second) in [(0, 1), (0, 2), (1, 2)] {
        assert!(
            pointers[first].1 != pointers[second].1,
            "Proth120 binding ContinuationEqAliasedPointers: first={:?}, second={:?}",
            pointers[first].0,
            pointers[second].0
        );
    }
}

impl DrWindowLayerHookPr {
    pub(crate) fn bind(
        program: &DrWindowLayerProgram,
        storage: &GpuGKRStorage<PR, PR>,
        entry_round: usize,
        claim_point_out: *const PR,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let folding_steps = program.folding_steps();
        validate_dr_window_folding_steps(folding_steps)
            .expect("Proth120 DR folding steps must be supported");
        let geometries = plan_dr_window_continuations_pr(folding_steps, entry_round);
        assert!(
            !claim_point_out.is_null(),
            "Proth120 DR continuation claim point is null"
        );

        let projection = program.input_projection();
        let poly_count = projection.canonical_sources().len();
        let raw_inputs = assert_binding(DrWindowRawInputKeepalivePr::from_projection(
            storage, projection,
        ));

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
        let r0_batch = build_r0_batch(program.program(), storage, r0_eq.low(), r0_eq_sizes);
        let r0 = Box::new(DrWindowLaunchBindingPr {
            batch: r0_batch,
            eq_high_0: r0_eq.high_0(),
            eq_high_1: r0_eq.high_1(),
            partials: partials_ptr,
            claim_point: core::ptr::null(),
            log_rows: dr_window_log_rows(folding_steps),
            start_round: 0,
        });

        let mut hook = Self {
            folding_steps,
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
            assert!(
                destination_arena.poly_count >= poly_count,
                "Proth120 binding ArenaCapacity: required={:?}, capacity={:?}",
                poly_count,
                destination_arena.poly_count
            );
            let destination = destination_arena.binding(geometry.log2_stride());
            let batch = if geometry.reads_raw_storage() {
                assemble_continuation_batch(
                    program.program(),
                    projection,
                    continuation_eq.low(),
                    eq_sizes,
                    destination,
                    |table, address, _| table.intern_storage(storage, address),
                )
            } else {
                let previous = previous.expect("Proth120 DR arena source follows a prior pass");
                debug_assert_eq!(previous.destination(), geometry.destination().opposite());
                let source = hook.arenas[previous.destination().index()]
                    .as_ref()
                    .expect("Proth120 DR source arena was allocated")
                    .binding(previous.log2_stride());
                assemble_continuation_batch(
                    program.program(),
                    projection,
                    continuation_eq.low(),
                    eq_sizes,
                    destination,
                    |table, _, publication_index| {
                        table.intern_arena(source, usize::from(publication_index))
                    },
                )
            };
            validate_continuation_eq(
                geometry,
                batch.eq_sizes,
                [
                    ("eq_high_0", continuation_eq.high_0().cast_const()),
                    ("eq_high_1", continuation_eq.high_1().cast_const()),
                    ("eq_low", batch.eq_low),
                ],
            );
            validate_continuation_table_bases(&batch);
            let row_tiles = dr_window_row_tiles(geometry.suffix_folding_steps());
            let required = PR_WINDOW_TAIL_TENSOR_CELLS * (row_tiles * slot_count + 1);
            assert!(
                hook.partials.len() >= required,
                "Proth120 binding ScratchCapacity: required={:?}, capacity={:?}",
                required,
                hook.partials.len()
            );
            hook.continuations.push(DrWindowContinuationPassPr {
                geometry,
                binding: Box::new(DrWindowLaunchBindingPr {
                    batch,
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
    ) -> Vec<*const PR> {
        let projection = program.input_projection();
        let canonical_count = projection.canonical_sources().len();
        let Some(last) = self.continuations.last() else {
            return assert_binding(
                self.raw_inputs
                    .canonical_source_pointers(storage, projection),
            );
        };
        let arena = self.arenas[last.geometry.destination().index()]
            .as_ref()
            .expect("Proth120 final DR continuation destination must remain owned");
        assert_eq!(arena.poly_count, canonical_count);
        let binding = arena.binding(last.geometry.log2_stride());
        let stride = 1usize << binding.log2_stride;
        shared::source_column_pointers(binding.base.cast::<PR>(), stride, canonical_count)
    }
}
