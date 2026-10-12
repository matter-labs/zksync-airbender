use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_prover_context::ProverContext;

use super::eq::launch_eq_high_low_pr;
use crate::backward::{make_eq_sizes, GkrEqSizes};
use crate::upstream::{GKRAddress, PR};
use crate::{GpuBaseFieldPoly, GpuGKRStorage};

pub(crate) const PR_EXTRAS_MAX_COLUMNS: usize = 64;
pub(crate) const PR_EXTRAS_BLOCKS: u32 = 128;
pub(crate) const PR_EXTRAS_THREADS: u32 = 256;

#[repr(C, align(8))]
#[derive(Clone, Copy)]
pub(crate) struct PrExtrasColumns {
    pub(crate) values: [*const PR; PR_EXTRAS_MAX_COLUMNS],
}

#[repr(C)]
struct PrExtrasArgumentLayout {
    columns: PrExtrasColumns,
    eq_high_0: *const PR,
    eq_high_1: *const PR,
    eq_low: *const PR,
    sizes: GkrEqSizes,
    rows: u32,
    column_count: u32,
    out: *mut PR,
}

pub(crate) const PR_EXTRAS_ARGUMENT_BYTES: usize = size_of::<PrExtrasArgumentLayout>();

const _: () = {
    assert!(size_of::<PrExtrasColumns>() == 512);
    assert!(align_of::<PrExtrasColumns>() == 8);
    assert!(std::mem::offset_of!(PrExtrasArgumentLayout, eq_high_0) == 512);
    assert!(std::mem::offset_of!(PrExtrasArgumentLayout, eq_low) == 528);
    assert!(std::mem::offset_of!(PrExtrasArgumentLayout, sizes) == 536);
    assert!(std::mem::offset_of!(PrExtrasArgumentLayout, rows) == 548);
    assert!(std::mem::offset_of!(PrExtrasArgumentLayout, column_count) == 552);
    assert!(std::mem::offset_of!(PrExtrasArgumentLayout, out) == 560);
    assert!(PR_EXTRAS_ARGUMENT_BYTES == 568);
};

cuda_kernel!(
    PrLayerExtras,
    ab_pr_gkr_layer0_extras_kernel(
        columns: PrExtrasColumns,
        eq_high_0: *const PR,
        eq_high_1: *const PR,
        eq_low: *const PR,
        sizes: GkrEqSizes,
        rows: u32,
        column_count: u32,
        out: *mut PR,
    )
);

pub(crate) struct LayerExtrasKeepalivePr {
    _partials: DeviceAllocation<PR>,
    _views: Vec<GpuBaseFieldPoly<PR>>,
}

pub(crate) struct LayerExtrasEqPr {
    pub(crate) eq_high_0: *mut PR,
    pub(crate) eq_high_1: *mut PR,
    pub(crate) eq_low: *mut PR,
}

fn launch_extras(
    columns: &[*const PR],
    eq: Option<&LayerExtrasEqPr>,
    sizes: GkrEqSizes,
    rows: usize,
    blocks: u32,
    out: *mut PR,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(
        (1..=PR_EXTRAS_MAX_COLUMNS).contains(&columns.len()),
        "Proth120 layer extras exceed the column cap"
    );
    let mut table = PrExtrasColumns {
        values: [std::ptr::null(); PR_EXTRAS_MAX_COLUMNS],
    };
    table.values[..columns.len()].copy_from_slice(columns);
    let rows = u32::try_from(rows).expect("Proth120 layer extras rows exceed u32");
    let config = CudaLaunchConfig::basic(
        Dim3::new(blocks, columns.len() as u32, 1),
        PR_EXTRAS_THREADS,
        context.get_exec_stream(),
    );
    let (eq_high_0, eq_high_1, eq_low) = eq.map_or(
        (std::ptr::null(), std::ptr::null(), std::ptr::null()),
        |eq| {
            (
                eq.eq_high_0.cast_const(),
                eq.eq_high_1.cast_const(),
                eq.eq_low.cast_const(),
            )
        },
    );
    PrLayerExtrasFunction::default().launch(
        &config,
        &PrLayerExtrasArguments::new(
            table,
            eq_high_0,
            eq_high_1,
            eq_low,
            sizes,
            rows,
            columns.len() as u32,
            out,
        ),
    )
}

pub(crate) fn schedule_layer_extras_pr(
    addresses: &[GKRAddress],
    storage: &GpuGKRStorage<PR, PR>,
    point: *const PR,
    folding_steps: usize,
    eq: &LayerExtrasEqPr,
    claims_tail: &mut DeviceSlice<PR>,
    slab_extras: &mut DeviceSlice<PR>,
    context: &ProverContext,
) -> CudaResult<LayerExtrasKeepalivePr> {
    let count = addresses.len();
    assert!(
        (1..=PR_EXTRAS_MAX_COLUMNS).contains(&count),
        "Proth120 layer extras exceed the column cap"
    );
    assert_eq!(
        claims_tail.len(),
        count,
        "Proth120 layer extras claim tail length mismatch"
    );
    assert_eq!(
        slab_extras.len(),
        count,
        "Proth120 layer extras slab length mismatch"
    );
    let rows = 1usize << folding_steps;
    let views: Vec<GpuBaseFieldPoly<PR>> = addresses
        .iter()
        .map(|address| {
            let view = storage.resolve_base_view_or_panic(*address);
            assert_eq!(
                view.len(),
                rows,
                "Proth120 layer extra {address:?} length mismatch"
            );
            view
        })
        .collect();
    launch_eq_high_low_pr(
        point,
        0,
        folding_steps as u32,
        eq.eq_high_0,
        eq.eq_high_1,
        eq.eq_low,
        context,
    )?;
    let sizes = make_eq_sizes(folding_steps);
    let mut partials =
        context.alloc(count * PR_EXTRAS_BLOCKS as usize, AllocationPlacement::Top)?;
    let columns: Vec<*const PR> = views.iter().map(|view| view.as_ptr()).collect();
    launch_extras(
        &columns,
        Some(eq),
        sizes,
        rows,
        PR_EXTRAS_BLOCKS,
        partials.as_mut_ptr(),
        context,
    )?;
    let partial_rows: Vec<*const PR> = (0..count)
        .map(|column| unsafe { partials.as_ptr().add(column * PR_EXTRAS_BLOCKS as usize) })
        .collect();
    launch_extras(
        &partial_rows,
        None,
        GkrEqSizes::zeroed(),
        PR_EXTRAS_BLOCKS as usize,
        1,
        claims_tail.as_mut_ptr(),
        context,
    )?;
    memory_copy_async(slab_extras, &*claims_tail, context.get_exec_stream())?;
    Ok(LayerExtrasKeepalivePr {
        _partials: partials,
        _views: views,
    })
}
