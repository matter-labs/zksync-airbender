//! Probe for the multi-coset fused LDE boundary: one kernel produces the
//! monomial writeback plus ALL cosets' initial outputs (per-coset hot re-read
//! of the block's own just-written monomial window), replacing the separate
//! per-coset initial launches. Parity must be byte-exact against the shipped
//! sequence; the A/B times both PRODUCTION per-column launch sequences over
//! two consecutive columns. Run with `--ignored --nocapture` on a GPU.

use era_cudart::cuda_kernel;
use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;

use super::make_context;
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixChunkMut, DeviceMatrixChunkMutImpl,
    MutPtrAndStride, PtrAndStride,
};
use gpu_core::primitives::field::BaseField;

type BF = BaseField;

cuda_kernel!(
    Fused,
    fused,
    scratch_matrix: MutPtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    log_n: i32,
    coset_index_base: i32,
    coset_factor_shift: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
);

fused!(ab_lde_fused_boundary_writeback_8_stages_kernel);

cuda_kernel!(
    FusedMc,
    fused_mc,
    scratch_matrix: MutPtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    outputs_matrix_cs: MutPtrAndStride<BF>,
    log_n: i32,
    coset_index_base: i32,
    coset_factor_shift: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
);

fused_mc!(ab_lde_fused_boundary_writeback_2_cosets_8_stages_kernel);

cuda_kernel!(
    Initial,
    initial,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    transposed_monomials: bool,
    log_n: i32,
    coset_index_base: i32,
    coset_factor_shift: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
);

initial!(ab_monomials_to_evals_initial_8_stages_kernel);
initial!(ab_monomials_to_evals_initial_8_stages_reversed_kernel);

cuda_kernel!(
    Noninitial,
    noninitial,
    inputs_matrix: PtrAndStride<BF>,
    outputs_matrix: MutPtrAndStride<BF>,
    log_n: i32,
    start_stage: i32,
    num_cols_per_coset: i32,
    log_cosets_in_tile: i32,
);

noninitial!(ab_monomials_to_evals_noninitial_8_stages_kernel);
noninitial!(ab_monomials_to_evals_noninitial_8_stages_evict_kernel);

const LOG_N: usize = 24;
const N: usize = 1 << LOG_N;
const K: usize = 2;
const COSET_FACTOR_SHIFT: i32 = 2; // OMEGA_LOG_ORDER(27) - 24 - log_lde_factor(1)
const COLS: usize = 2;
const WARMUP: usize = 5;
const TIMED: usize = 50;

fn slab_views(
    buf: &mut DeviceAllocation<BF>,
    slab: usize,
) -> (PtrAndStride<BF>, MutPtrAndStride<BF>) {
    let range = slab * N..(slab + 1) * N;
    let const_slice =
        unsafe { era_cudart::slice::DeviceSlice::from_raw_parts(buf.as_ptr().add(slab * N), N) };
    let getter = DeviceMatrixChunk::new(const_slice, N, 0, N).as_ptr_and_stride();
    let setter = DeviceMatrixChunkMut::new(&mut buf[range], N, 0, N).as_mut_ptr_and_stride();
    (getter, setter)
}

fn time_launches(
    stream: &CudaStream,
    mut launch: impl FnMut(&CudaStream) -> CudaResult<()>,
) -> f32 {
    for _ in 0..WARMUP {
        launch(stream).unwrap();
    }
    let start = CudaEvent::create().unwrap();
    let end = CudaEvent::create().unwrap();
    start.record(stream).unwrap();
    for _ in 0..TIMED {
        launch(stream).unwrap();
    }
    end.record(stream).unwrap();
    end.synchronize().unwrap();
    elapsed_time(&start, &end).unwrap() * 1000.0 / TIMED as f32
}

#[test]
#[ignore]
fn probe_multicoset_boundary_ab() {
    let ctx = make_context();
    let stream = ctx.get_exec_stream();

    let num_vblocks = (N / 8192) as u32;
    let grid: Dim3 = num_vblocks.into();

    // Per column: hypercube input (host), scratch (device, re-seeded before
    // every fused launch since the kernel transforms it in place), K-slab out.
    let mut inputs = Vec::new();
    let mut d_scratch = Vec::new();
    let mut d_out_cur = Vec::new();
    let mut d_out_new = Vec::new();
    for col in 0..COLS {
        let input = (0..N)
            .map(|idx| BF::new(43 + col as u32 * 6007 + (idx as u32).wrapping_mul(2654435761)))
            .collect::<Vec<_>>();
        let mut scratch = DeviceAllocation::<BF>::alloc(N).unwrap();
        memory_copy_async(&mut scratch, &input[..], stream).unwrap();
        inputs.push(input);
        d_scratch.push(scratch);
        d_out_cur.push(DeviceAllocation::<BF>::alloc(K * N).unwrap());
        d_out_new.push(DeviceAllocation::<BF>::alloc(K * N).unwrap());
    }

    let scratch_views: Vec<_> = d_scratch.iter_mut().map(|s| slab_views(s, 0)).collect();
    let out_cur_views: Vec<Vec<_>> = d_out_cur
        .iter_mut()
        .map(|o| (0..K).map(|k| slab_views(o, k)).collect())
        .collect();
    let out_new_views: Vec<Vec<_>> = d_out_new
        .iter_mut()
        .map(|o| (0..K).map(|k| slab_views(o, k)).collect())
        .collect();

    let fused_fn = FusedFunction(ab_lde_fused_boundary_writeback_8_stages_kernel);
    let initial_rev_fn = InitialFunction(ab_monomials_to_evals_initial_8_stages_reversed_kernel);
    let fused_mc_fn = FusedMcFunction(ab_lde_fused_boundary_writeback_2_cosets_8_stages_kernel);
    let initial_fn = InitialFunction(ab_monomials_to_evals_initial_8_stages_kernel);
    let mid_fn = NoninitialFunction(ab_monomials_to_evals_noninitial_8_stages_kernel);
    let evict_fn = NoninitialFunction(ab_monomials_to_evals_noninitial_8_stages_evict_kernel);

    let noninit_pair = |stream: &CudaStream,
                        getter: PtrAndStride<BF>,
                        setter: MutPtrAndStride<BF>|
     -> CudaResult<()> {
        let config = CudaLaunchConfig::basic(grid, 256, stream);
        let args =
            NoninitialArguments::new(getter, setter, LOG_N as i32, (LOG_N - 16) as i32, 1, 0);
        mid_fn.launch(&config, &args)?;
        let config = CudaLaunchConfig::basic(grid, 256, stream);
        let args = NoninitialArguments::new(getter, setter, LOG_N as i32, (LOG_N - 8) as i32, 1, 0);
        evict_fn.launch(&config, &args)
    };

    // Shipped per-column sequence: fused(c0) + noninit pair(c0) + standalone
    // initial(c1) + noninit pair(c1). 6 launches per column.
    let launch_current = |stream: &CudaStream| -> CudaResult<()> {
        for col in 0..COLS {
            let (scratch_getter, scratch_setter) = scratch_views[col];
            let config = CudaLaunchConfig::basic(grid, 256, stream);
            let args = FusedArguments::new(
                scratch_setter,
                out_cur_views[col][0].1,
                LOG_N as i32,
                0,
                COSET_FACTOR_SHIFT,
                1,
                0,
            );
            fused_fn.launch(&config, &args)?;
            noninit_pair(stream, out_cur_views[col][0].0, out_cur_views[col][0].1)?;
            let config = CudaLaunchConfig::basic(grid, 256, stream);
            let args = InitialArguments::new(
                scratch_getter,
                out_cur_views[col][1].1,
                true,
                LOG_N as i32,
                1,
                COSET_FACTOR_SHIFT,
                1,
                0,
            );
            initial_fn.launch(&config, &args)?;
            noninit_pair(stream, out_cur_views[col][1].0, out_cur_views[col][1].1)?;
        }
        Ok(())
    };

    // Multi-coset per-column sequence: fused(c0 + c1) + noninit pairs.
    // 5 launches per column. The fused kernel's outputs matrix spans both
    // slabs (per-coset col offset = num_cols_per_coset applied in-kernel).
    let launch_new = |stream: &CudaStream| -> CudaResult<()> {
        for col in 0..COLS {
            let (_, scratch_setter) = scratch_views[col];
            let config = CudaLaunchConfig::basic(grid, 256, stream);
            let args = FusedMcArguments::new(
                scratch_setter,
                out_new_views[col][0].1,
                out_new_views[col][0].1,
                LOG_N as i32,
                0,
                COSET_FACTOR_SHIFT,
                1,
                0,
            );
            fused_mc_fn.launch(&config, &args)?;
            for k in 0..K {
                noninit_pair(stream, out_new_views[col][k].0, out_new_views[col][k].1)?;
            }
        }
        Ok(())
    };

    let launch_reversed = |stream: &CudaStream| -> CudaResult<()> {
        for col in 0..COLS {
            let (scratch_getter, scratch_setter) = scratch_views[col];
            let config = CudaLaunchConfig::basic(grid, 256, stream);
            let args = FusedArguments::new(
                scratch_setter,
                out_new_views[col][0].1,
                LOG_N as i32,
                0,
                COSET_FACTOR_SHIFT,
                1,
                0,
            );
            fused_fn.launch(&config, &args)?;
            noninit_pair(stream, out_new_views[col][0].0, out_new_views[col][0].1)?;
            let config = CudaLaunchConfig::basic(grid, 256, stream);
            let args = InitialArguments::new(
                scratch_getter,
                out_new_views[col][1].1,
                true,
                LOG_N as i32,
                1,
                COSET_FACTOR_SHIFT,
                1,
                0,
            );
            initial_rev_fn.launch(&config, &args)?;
            noninit_pair(stream, out_new_views[col][1].0, out_new_views[col][1].1)?;
        }
        Ok(())
    };

    // The fused kernels transform scratch in place; re-seed before each pass.
    let reseed = |stream: &CudaStream,
                  d_scratch: &mut [DeviceAllocation<BF>],
                  inputs: &[Vec<BF>]|
     -> CudaResult<()> {
        for (scratch, input) in d_scratch.iter_mut().zip(inputs) {
            memory_copy_async(scratch, &input[..], stream)?;
        }
        Ok(())
    };

    // Parity: run current, capture; reseed; run new; compare outputs AND the
    // materialized monomial scratch.
    launch_current(stream).unwrap();
    let mut h_scratch_cur = vec![vec![BF::new(0); N]; COLS];
    for col in 0..COLS {
        memory_copy_async(&mut h_scratch_cur[col][..], &d_scratch[col], stream).unwrap();
    }
    reseed(stream, &mut d_scratch, &inputs).unwrap();
    launch_new(stream).unwrap();
    for col in 0..COLS {
        let mut h_cur = vec![BF::new(0); K * N];
        let mut h_new = vec![BF::new(0); K * N];
        let mut h_scratch_new = vec![BF::new(0); N];
        memory_copy_async(&mut h_cur[..], &d_out_cur[col], stream).unwrap();
        memory_copy_async(&mut h_new[..], &d_out_new[col], stream).unwrap();
        memory_copy_async(&mut h_scratch_new[..], &d_scratch[col], stream).unwrap();
        stream.synchronize().unwrap();
        assert_ne!(
            h_cur,
            vec![BF::new(0); K * N],
            "column {col} reference is zero"
        );
        assert_eq!(h_cur, h_new, "column {col} coset outputs mismatch");
        assert_eq!(
            h_scratch_cur[col], h_scratch_new,
            "column {col} materialized monomials mismatch"
        );
    }

    // Reversed-initial parity (order-only change, outputs must be identical).
    reseed(stream, &mut d_scratch, &inputs).unwrap();
    launch_reversed(stream).unwrap();
    for col in 0..COLS {
        let mut h_cur = vec![BF::new(0); K * N];
        let mut h_new = vec![BF::new(0); K * N];
        memory_copy_async(&mut h_cur[..], &d_out_cur[col], stream).unwrap();
        memory_copy_async(&mut h_new[..], &d_out_new[col], stream).unwrap();
        stream.synchronize().unwrap();
        assert_eq!(h_cur, h_new, "column {col} reversed-initial mismatch");
    }

    // Timing: repeated launches re-transform scratch in place — same
    // instruction stream and traffic, values just churn (still field
    // elements), so timings stay representative.
    let us_current = time_launches(stream, launch_current);
    let us_new = time_launches(stream, launch_new);
    let us_reversed = time_launches(stream, launch_reversed);
    println!(
        "{COLS} columns x K={K} boundary: current 6-launch {us_current:.1} us | \
         multi-coset 5-launch {us_new:.1} us (ratio {:.3}) | \
         reversed-c1-initial {us_reversed:.1} us (ratio {:.3})",
        us_new / us_current,
        us_reversed / us_current
    );
}
