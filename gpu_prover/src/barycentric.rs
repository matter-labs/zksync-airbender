use std::cmp;
use std::mem::size_of;

use cs::one_row_compiler::{ColumnAddress, CompiledCircuitArtifact};
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, Dim3, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use fft::field_utils::domain_generator_for_size;
use field::Field;
use prover::prover_stages::cached_data::ProverCachedData;

use crate::device_structures::{
    DeviceMatrixChunk, DeviceMatrixChunkImpl, DeviceMatrixMut, DeviceMatrixMutImpl,
    DeviceVectorMutImpl, MutPtrAndStride, PtrAndStride,
};
use crate::field::{BaseField, Ext2Field, Ext4Field};
use crate::ops_complex::BatchInv;
use crate::ops_cub::device_reduce::{
    batch_reduce, get_batch_reduce_temp_storage_bytes, ReduceOperation,
};
use crate::prover::arg_utils::get_grand_product_col;
use crate::utils::{GetChunksCount, WARP_SIZE};

type BF = BaseField;
type E2 = Ext2Field;
type E4 = Ext4Field;

cuda_kernel!(
    PrecomputeCommonFactor,
    precompute_common_factor,
    z: *const E4,
    common_factor: *mut E4,
    coset: E2,
    decompression_factor: E2,
    count: u32,
);

precompute_common_factor!(barycentric_precompute_common_factor_kernel);

cuda_kernel!(
    PrecomputeLagrangeCoeffs,
    precompute_lagrange_coeffs,
    z: *const E4,
    common_factor: *const E4,
    w_inv_step: E2,
    coset: E2,
    lagrange_coeffs: *mut E4,
    log_count: u32,
);

precompute_lagrange_coeffs!(barycentric_precompute_lagrange_coeffs_kernel);

pub fn precompute_lagrange_coeffs(
    z: &DeviceVariable<E4>,
    common_factor_storage: &mut DeviceVariable<E4>,
    coset: E2,
    decompression_factor: Option<E2>,
    lagrange_coeffs: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let inv_batch: u32 = <E4 as BatchInv>::BATCH_SIZE;
    assert!(lagrange_coeffs.len() <= u32::MAX as usize);
    assert!(lagrange_coeffs.len().is_power_of_two());
    let count = lagrange_coeffs.len() as u32;
    let common_factor = common_factor_storage.as_mut_ptr();
    let config = CudaLaunchConfig::basic(1, 1, stream);
    let decompression_factor = decompression_factor.unwrap_or(E2::ONE);
    let z = z.as_ptr();
    let args =
        PrecomputeCommonFactorArguments::new(z, common_factor, coset, decompression_factor, count);
    PrecomputeCommonFactorFunction(barycentric_precompute_common_factor_kernel)
        .launch(&config, &args)?;
    let log_count: u32 = count.trailing_zeros();
    let block_dim = WARP_SIZE * 4;
    let grid_dim = count.get_chunks_count(inv_batch * block_dim);
    let w = domain_generator_for_size::<E2>((1 << log_count) as u64);
    let w_inv = w.inverse().expect("inverse of omega must exist");
    let w_inv_step = w_inv.pow(block_dim * grid_dim);
    let common_factor = common_factor_storage.as_ptr();
    let dst = lagrange_coeffs.as_mut_ptr();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args =
        PrecomputeLagrangeCoeffsArguments::new(z, common_factor, w_inv_step, coset, dst, log_count);
    PrecomputeLagrangeCoeffsFunction(barycentric_precompute_lagrange_coeffs_kernel)
        .launch(&config, &args)?;
    Ok(())
}

const MAX_COLS: usize = 1344;
const DOES_NOT_NEED_Z_OMEGA: u32 = u32::MAX;

// This is very wastefully sized, but well under 8 KB, so we might as well keep it simple.
#[derive(Clone)]
#[repr(C)]
struct ColIdxsToEvalAtZOmegaIdxsMap {
    pub map: [u32; MAX_COLS],
}

cuda_kernel!(
    BarycentricPartialReduce,
    barycentric_partial_reduce,
    setup_cols: PtrAndStride<BF>,
    witness_cols: PtrAndStride<BF>,
    memory_cols: PtrAndStride<BF>,
    stage_2_bf_cols: PtrAndStride<BF>,
    stage_2_e4_cols: PtrAndStride<BF>,
    composition_col: PtrAndStride<BF>,
    lagrange_coeffs: *const E4,
    partial_sums: MutPtrAndStride<E4>,
    map: ColIdxsToEvalAtZOmegaIdxsMap,
    decompression_factor_inv: E2,
    num_setup_cols: u32,
    num_witness_cols: u32,
    num_memory_cols: u32,
    num_stage_2_bf_cols: u32,
    num_stage_2_e4_cols: u32,
    row_chunk_size: u32,
    log_count: u32,
);

barycentric_partial_reduce!(barycentric_partial_reduce_kernel);

fn get_batch_partial_reduce_grid_block(domain_size: u32, row_chunk_size: u32) -> (Dim3, u32) {
    let block_dim_x = WARP_SIZE;
    let grid_dim_x = domain_size.get_chunks_count(row_chunk_size);
    let mut block_dim: Dim3 = block_dim_x.into();
    // Warning: warp-to-col mapping in the kernel is hardcoded to assume block_dim.y = 16
    block_dim.y = 16;
    (block_dim, grid_dim_x)
}

pub fn get_batch_eval_temp_storage_sizes(
    circuit: &CompiledCircuitArtifact<BF>,
    domain_size: u32,
    row_chunk_size: u32,
) -> CudaResult<(usize, usize)> {
    let num_evals = circuit.num_openings_at_z() + circuit.num_openings_at_z_omega();
    let (block_dim, grid_dim_x) = get_batch_partial_reduce_grid_block(domain_size, row_chunk_size);
    let output_rows_nonlast_block = cmp::min(row_chunk_size, block_dim.x);
    let output_rows_last_block = cmp::min(
        output_rows_nonlast_block,
        domain_size - (grid_dim_x - 1) * row_chunk_size,
    );
    let output_rows = output_rows_nonlast_block * (grid_dim_x - 1) + output_rows_last_block;
    let partial_reduce_temp_elems = num_evals * output_rows as usize;
    let final_cub_reduce_temp_bytes = get_batch_reduce_temp_storage_bytes::<E4>(
        ReduceOperation::Sum,
        num_evals as i32,
        output_rows as i32,
    )?;
    Ok((partial_reduce_temp_elems, final_cub_reduce_temp_bytes))
}

// On the coset domain, all evals EXCEPT the composition col were multiplied
// by the compression factor. Therefore, if we're using coset evals,
// I fold the decompression factor into the lagrange coeffs.
// But the composition col doesn't need it. Therefore, while accumulating I also
// multiply the composition col's intermediate results by the inverse of the
// decompression factor (== original compression factor)
// Computing decompression_factor_inv for this corner case (composition col on coset domain)
// is the only reason we need the decompression_factor arg below.
// If we decided to always use main domain evals for barycentric eval-at-z,
// we can get rid of it.
#[allow(clippy::too_many_arguments)]
pub fn batch_barycentric_eval(
    setup_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    witness_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    memory_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    stage_2_cols: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    composition_col: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    lagrange_coeffs: &DeviceSlice<E4>,
    temp_storage_partial_reduce: &mut DeviceSlice<E4>,
    temp_storage_final_cub_reduce: &mut DeviceSlice<u8>,
    evals: &mut (impl DeviceVectorMutImpl<E4> + ?Sized),
    decompression_factor: Option<E2>,
    cached_data: &ProverCachedData,
    circuit: &CompiledCircuitArtifact<BF>,
    row_chunk_size: u32,
    log_n: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let n = 1 << log_n;
    let num_setup_cols = circuit.setup_layout.total_width;
    let num_witness_cols = circuit.witness_layout.total_width;
    let num_memory_cols = circuit.memory_layout.total_width;
    let num_stage_2_cols = circuit.stage_2_layout.total_width;
    let num_stage_2_bf_cols = circuit.stage_2_layout.num_base_field_polys();
    let num_stage_2_e4_cols = circuit.stage_2_layout.num_ext4_field_polys();
    assert_eq!(setup_cols.rows(), n);
    assert_eq!(setup_cols.cols(), num_setup_cols);
    assert_eq!(witness_cols.rows(), n);
    assert_eq!(witness_cols.cols(), num_witness_cols,);
    assert_eq!(memory_cols.rows(), n);
    assert_eq!(memory_cols.cols(), num_memory_cols,);
    assert_eq!(stage_2_cols.rows(), n);
    assert_eq!(stage_2_cols.cols(), num_stage_2_cols);
    assert_eq!(composition_col.rows(), n);
    assert_eq!(composition_col.cols(), 4);
    assert_eq!(
        stage_2_cols.cols(),
        4 * (((num_stage_2_bf_cols + 3) / 4) + num_stage_2_e4_cols)
    );
    // for convenience, demarcate bf and vectorized e4 sections of stage_2_cols
    let e4_cols_offset = circuit.stage_2_layout.ext4_polys_offset;
    assert_eq!(e4_cols_offset % 4, 0);
    assert!(num_stage_2_bf_cols <= e4_cols_offset);
    assert!(e4_cols_offset - num_stage_2_bf_cols < 4);
    // the above should also suffice to show e4_cols_offset = 4 * ceil(num_stage_2_bf_cols / 4)
    // which implies stage_2_cols.cols() = e4_cols_offset + num_stage_2_e4_cols
    let (stage_2_bf_cols, stage_2_e4_cols) = {
        let stride = stage_2_cols.stride();
        let offset = stage_2_cols.offset();
        let slice = stage_2_cols.slice();
        let (bf_slice, e4_slice) = slice.split_at(e4_cols_offset * stride);
        (
            DeviceMatrixChunk::new(
                &bf_slice[0..num_stage_2_bf_cols * stride],
                stride,
                offset,
                n,
            ),
            DeviceMatrixChunk::new(e4_slice, stride, offset, n),
        )
    };
    let num_evals_at_z = circuit.num_openings_at_z();
    let mut num_evals_at_z_doublecheck = num_setup_cols;
    num_evals_at_z_doublecheck += num_witness_cols;
    num_evals_at_z_doublecheck += num_memory_cols;
    num_evals_at_z_doublecheck += num_stage_2_bf_cols;
    num_evals_at_z_doublecheck += num_stage_2_e4_cols;
    num_evals_at_z_doublecheck += 1; // composition quotient
    assert_eq!(num_evals_at_z, num_evals_at_z_doublecheck);
    let num_evals_at_z_omega = circuit.num_openings_at_z_omega();
    let num_evals_total = num_evals_at_z + num_evals_at_z_omega;
    assert_eq!(evals.slice().len(), num_evals_total);
    let mut map = [DOES_NOT_NEED_Z_OMEGA; MAX_COLS];
    let mut col_offset = num_setup_cols;
    let mut eval_at_z_omega_offset: usize = num_evals_at_z;
    for (_src, dst) in circuit.state_linkage_constraints.iter() {
        let ColumnAddress::WitnessSubtree(col_idx) = *dst else {
            panic!()
        };
        assert_eq!(map[col_idx], DOES_NOT_NEED_Z_OMEGA);
        map[col_offset + col_idx] = eval_at_z_omega_offset as u32;
        eval_at_z_omega_offset += 1;
    }
    col_offset += num_witness_cols;
    if let Some(shuffle_ram_inits_and_teardowns) =
        circuit.memory_layout.shuffle_ram_inits_and_teardowns
    {
        assert!(cached_data.process_shuffle_ram_init);
        let start = shuffle_ram_inits_and_teardowns
            .lazy_init_addresses_columns
            .start();
        map[col_offset + start] = eval_at_z_omega_offset as u32;
        eval_at_z_omega_offset += 1;
        map[col_offset + start + 1] = eval_at_z_omega_offset as u32;
        eval_at_z_omega_offset += 1;
    } else {
        assert!(!cached_data.process_shuffle_ram_init);
    };
    col_offset += num_memory_cols + num_stage_2_bf_cols;
    let memory_grand_product_offset = get_grand_product_col(circuit, cached_data);
    map[col_offset + memory_grand_product_offset] = eval_at_z_omega_offset as u32;
    assert_eq!(eval_at_z_omega_offset + 1, num_evals_total);
    let (block_dim, grid_dim) = get_batch_partial_reduce_grid_block(n as u32, row_chunk_size);
    // double-check
    let (partial_reduce_temp_elems, final_cub_reduce_temp_bytes) =
        get_batch_eval_temp_storage_sizes(circuit, n as u32, row_chunk_size)?;
    assert_eq!(temp_storage_partial_reduce.len(), partial_reduce_temp_elems);
    assert_eq!(
        temp_storage_final_cub_reduce.len(),
        final_cub_reduce_temp_bytes
    );
    let mut temp_storage_partial_reduce = DeviceMatrixMut::new(
        temp_storage_partial_reduce,
        partial_reduce_temp_elems / num_evals_total,
    );
    let setup_cols = setup_cols.as_ptr_and_stride();
    let witness_cols = witness_cols.as_ptr_and_stride();
    let memory_cols = memory_cols.as_ptr_and_stride();
    let stage_2_bf_cols = stage_2_bf_cols.as_ptr_and_stride();
    let stage_2_e4_cols = stage_2_e4_cols.as_ptr_and_stride();
    let composition_col = composition_col.as_ptr_and_stride();
    let lagrange_coeffs = lagrange_coeffs.as_ptr();
    let partial_sums = temp_storage_partial_reduce.as_mut_ptr_and_stride();
    let map = ColIdxsToEvalAtZOmegaIdxsMap { map };
    let decompression_factor_inv = if let Some(df) = decompression_factor {
        df.inverse().expect("must exist")
    } else {
        E2::ONE
    };
    let mut config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    config.dynamic_smem_bytes = (row_chunk_size + 1) as usize * size_of::<E4>();
    let args = BarycentricPartialReduceArguments::new(
        setup_cols,
        witness_cols,
        memory_cols,
        stage_2_bf_cols,
        stage_2_e4_cols,
        composition_col,
        lagrange_coeffs,
        partial_sums,
        map,
        decompression_factor_inv,
        num_setup_cols as u32,
        num_witness_cols as u32,
        num_memory_cols as u32,
        num_stage_2_bf_cols as u32,
        num_stage_2_e4_cols as u32,
        row_chunk_size,
        log_n,
    );
    BarycentricPartialReduceFunction(barycentric_partial_reduce_kernel).launch(&config, &args)?;
    batch_reduce::<E4>(
        ReduceOperation::Sum,
        temp_storage_final_cub_reduce,
        &temp_storage_partial_reduce,
        evals.slice_mut(),
        stream,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::context::Context;
    use crate::device_structures::DeviceMatrix;
    use crate::field::{BaseField, Ext2Field, Ext4Field};

    use era_cudart::memory::{memory_copy_async, DeviceAllocation};
    use era_cudart::stream::CudaStream;
    use field::FieldExtension;
    use prover::tests::{run_basic_delegation_test_impl, GpuComparisonArgs};
    use serial_test::serial;

    use crate::prover::arg_utils::print_size;

    type BF = BaseField;
    type E2 = Ext2Field;
    type E4 = Ext4Field;

    fn comparison_hook(gpu_comparison_args: &GpuComparisonArgs) {
        let GpuComparisonArgs {
            circuit,
            setup,
            external_values,
            public_inputs: _,
            twiddles: _,
            lde_precomputations,
            table_driver: _,
            lookup_mapping: _,
            log_n,
            circuit_sequence,
            delegation_processing_type,
            prover_data,
        } = gpu_comparison_args;
        let log_n = *log_n;
        let circuit_sequence = *circuit_sequence;
        let delegation_processing_type = delegation_processing_type.unwrap_or(0);
        let domain_size = 1 << log_n;
        let tau = lde_precomputations.domain_bound_precomputations[1]
            .as_ref()
            .unwrap()
            .coset_offset;
        let decompression_factor = tau.pow((domain_size / 2) as u32);
        let cached_data = ProverCachedData::new(
            &circuit,
            &external_values,
            domain_size,
            circuit_sequence,
            delegation_processing_type,
        );
        let evals = &prover_data.deep_poly_result.values_at_z;
        let z = prover_data.deep_poly_result.z;

        print_size::<ColIdxsToEvalAtZOmegaIdxsMap>("ColIdxsToEvalAtZOmegaIdxsMap");

        // Try barycentric eval using the evals on the main domain and the evals on the coset.
        // Both cases should yield the same evals at z.
        for &(domain_index, coset, decompression_factor) in
            [(0, E2::ONE, None), (1, tau, Some(decompression_factor))].iter()
        {
            // Repackage row-major data as column-major for GPU
            let range = 0..domain_size;
            let mut trace_view = prover_data.stage_1_result.ldes[domain_index]
                .trace
                .row_view(range.clone());
            let mut stage_2_trace_view = prover_data.stage_2_result.ldes[domain_index]
                .trace
                .row_view(range.clone());
            let mut setup_trace_view = setup.ldes[domain_index].trace.row_view(range.clone());
            let mut quotient_trace_view = prover_data.quotient_commitment_result.ldes[domain_index]
                .trace
                .row_view(range.clone());
            let num_setup_cols = circuit.setup_layout.total_width;
            let num_witness_cols = circuit.witness_layout.total_width;
            let num_memory_cols = circuit.memory_layout.total_width;
            let num_trace_cols = num_witness_cols + num_memory_cols;
            let num_stage_2_cols = circuit.stage_2_layout.total_width;
            // let num_stage_2_bf_cols = circuit.stage_2_layout.num_base_field_polys();
            // let num_stage_2_e4_cols = circuit.stage_2_layout.num_ext4_field_polys();
            let mut h_setup_cols: Vec<BF> = vec![BF::ZERO; domain_size * num_setup_cols];
            let mut h_trace_cols: Vec<BF> = vec![BF::ZERO; domain_size * num_trace_cols];
            let mut h_stage_2_cols: Vec<BF> = vec![BF::ZERO; domain_size * num_stage_2_cols];
            let mut h_composition_col: Vec<BF> = vec![BF::ZERO; 4 * domain_size];
            // imitating access patterns in zksync_airbender's prover_stages/stage4.rs
            unsafe {
                for i in 0..domain_size {
                    let setup_trace_view_row = setup_trace_view.current_row_ref();
                    let trace_view_row = trace_view.current_row_ref();
                    let stage_2_trace_view_row = stage_2_trace_view.current_row_ref();
                    let quotient_trace_view_row = quotient_trace_view.current_row_ref();
                    {
                        let mut src = setup_trace_view_row.as_ptr();
                        for j in 0..num_setup_cols {
                            h_setup_cols[i + j * domain_size] = src.read();
                            src = src.add(1);
                        }
                    }
                    {
                        let mut src = trace_view_row.as_ptr();
                        for j in 0..num_trace_cols {
                            h_trace_cols[i + j * domain_size] = src.read();
                            src = src.add(1);
                        }
                    }
                    {
                        let mut src = stage_2_trace_view_row.as_ptr();
                        for j in 0..num_stage_2_cols {
                            h_stage_2_cols[i + j * domain_size] = src.read();
                            src = src.add(1);
                        }
                    }
                    {
                        let src = quotient_trace_view_row.as_ptr().cast::<E4>();
                        assert!(src.is_aligned());
                        let coeffs = src.read().into_coeffs_in_base();
                        for (j, coeff) in coeffs.iter().enumerate() {
                            h_composition_col[i + j * domain_size] = *coeff;
                        }
                    }
                    setup_trace_view.advance_row();
                    trace_view.advance_row();
                    stage_2_trace_view.advance_row();
                    quotient_trace_view.advance_row();
                }
            }
            // Allocate GPU args
            let stream = CudaStream::default();
            let num_evals_at_z = circuit.num_openings_at_z();
            let num_evals_at_z_omega = circuit.num_openings_at_z_omega();
            let num_evals = num_evals_at_z + num_evals_at_z_omega;
            let row_chunk_size = 2048; // tunable for performance, 2048 is decent
            let mut d_alloc_setup_cols =
                DeviceAllocation::<BF>::alloc(domain_size * num_setup_cols).unwrap();
            let mut d_alloc_trace_cols =
                DeviceAllocation::<BF>::alloc(domain_size * num_trace_cols).unwrap();
            let mut d_alloc_stage_2_cols =
                DeviceAllocation::<BF>::alloc(domain_size * num_stage_2_cols).unwrap();
            let mut d_alloc_composition_col =
                DeviceAllocation::<BF>::alloc(4 * domain_size).unwrap();
            let mut d_alloc_z = DeviceAllocation::<E4>::alloc(1).unwrap();
            let mut d_alloc_evals = DeviceAllocation::<E4>::alloc(num_evals).unwrap();
            let (partial_reduce_temp_elems, final_cub_reduce_temp_bytes) =
                super::get_batch_eval_temp_storage_sizes(
                    &circuit,
                    domain_size as u32,
                    row_chunk_size,
                )
                .unwrap();
            let mut d_alloc_temp_storage_partial_reduce =
                DeviceAllocation::<E4>::alloc(partial_reduce_temp_elems).unwrap();
            let mut d_alloc_temp_storage_final_cub_reduce =
                DeviceAllocation::<u8>::alloc(final_cub_reduce_temp_bytes).unwrap();
            let mut d_common_factor_storage = DeviceAllocation::<E4>::alloc(1).unwrap();
            let mut d_lagrange_coeffs = DeviceAllocation::<E4>::alloc(domain_size).unwrap();
            let mut h_evals_from_gpu = vec![E4::ZERO; num_evals];
            memory_copy_async(&mut d_alloc_setup_cols, &h_setup_cols, &stream).unwrap();
            memory_copy_async(&mut d_alloc_trace_cols, &h_trace_cols, &stream).unwrap();
            memory_copy_async(&mut d_alloc_stage_2_cols, &h_stage_2_cols, &stream).unwrap();
            memory_copy_async(&mut d_alloc_composition_col, &h_composition_col, &stream).unwrap();
            memory_copy_async(&mut d_alloc_z, &[z], &stream).unwrap();
            let d_setup_cols = DeviceMatrix::new(&d_alloc_setup_cols, domain_size);
            let d_trace_cols = DeviceMatrix::new(&d_alloc_trace_cols, domain_size);
            let slice = d_trace_cols.slice();
            let stride = d_trace_cols.stride();
            let offset = d_trace_cols.offset();
            let d_witness_cols = DeviceMatrixChunk::new(
                &slice[0..num_witness_cols * stride],
                stride,
                offset,
                domain_size,
            );
            let d_memory_cols = DeviceMatrixChunk::new(
                &slice[num_witness_cols * stride..],
                stride,
                offset,
                domain_size,
            );
            let d_stage_2_cols = DeviceMatrix::new(&d_alloc_stage_2_cols, domain_size);
            let d_composition_col = DeviceMatrix::new(&d_alloc_composition_col, domain_size);
            super::precompute_lagrange_coeffs(
                &d_alloc_z[0],
                &mut d_common_factor_storage[0],
                coset,
                decompression_factor,
                &mut d_lagrange_coeffs,
                &stream,
            )
            .unwrap();
            super::batch_barycentric_eval(
                &d_setup_cols,
                &d_witness_cols,
                &d_memory_cols,
                &d_stage_2_cols,
                &d_composition_col,
                &d_lagrange_coeffs,
                &mut d_alloc_temp_storage_partial_reduce,
                &mut d_alloc_temp_storage_final_cub_reduce,
                &mut d_alloc_evals,
                decompression_factor,
                &cached_data,
                circuit,
                row_chunk_size,
                log_n as u32,
                &stream,
            )
            .unwrap();
            memory_copy_async(&mut h_evals_from_gpu, &d_alloc_evals, &stream).unwrap();
            stream.synchronize().unwrap();
            for (i, (eval_from_cpu, eval_from_gpu)) in
                evals.iter().zip(h_evals_from_gpu.iter()).enumerate()
            {
                assert_eq!(
                    *eval_from_cpu, *eval_from_gpu,
                    " failed at for coset {}, eval {} with num evals at z and z omega {}, {}",
                    coset, i, num_evals_at_z, num_evals_at_z_omega
                );
            }
        }
    }

    // #[test]
    // #[serial]
    // fn test_barycentric_for_basic_circuit() {
    //     let ctx = Context::create(12).unwrap();
    //     run_basic_test_impl(Some(Box::new(comparison_hook)));
    //     ctx.destroy().unwrap();
    // }

    #[test]
    #[serial]
    fn test_barycentric_for_delegation_circuit() {
        let ctx = Context::create(12).unwrap();
        run_basic_delegation_test_impl(
            Some(Box::new(comparison_hook)),
            Some(Box::new(comparison_hook)),
        );
        ctx.destroy().unwrap();
    }
}
