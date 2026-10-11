use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, PtrAndStride,
};
use gpu_core::primitives::field::PR;

use super::hypercube::hypercube_evals_to_monomials_in_place;
use super::{validate_disjoint, validate_matrix};

cuda_kernel!(PackColumns, ab_pr_pack_columns_kernel(
    inputs: PtrAndStride<PR>, output: *mut PR, log_rows: u32, cols_in_group: u32, group_width: u32,
));

pub(crate) const PACK_BLOCK_THREADS: u32 = 256;

pub(crate) fn pack_grid_blocks(log_rows: u32, pack_log2: u32) -> u32 {
    (1u32 << (log_rows + pack_log2)).div_ceil(PACK_BLOCK_THREADS)
}

pub fn pack_hypercubes_to_monomials(
    inputs: &(impl DeviceMatrixChunkImpl<PR> + ?Sized),
    outputs: &mut (impl DeviceMatrixChunkMutImpl<PR> + ?Sized),
    pack_log2: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let (log_rows, input_range) = validate_matrix(inputs, 0, 26, "Proth120 pack input");
    let log_packed = log_rows
        .checked_add(pack_log2)
        .filter(|log| (8..=26).contains(log))
        .unwrap_or_else(|| {
            panic!("Proth120 pack: log_n {log_rows} + pack_log2 {pack_log2} outside 8..=26")
        });
    let (output_log, output_range) = validate_matrix(outputs, 8, 26, "Proth120 pack output");
    assert_eq!(
        output_log, log_packed,
        "Proth120 pack: output rows must equal input rows << pack_log2"
    );
    assert!(
        inputs.cols() >= 1,
        "Proth120 pack: at least one input column is required"
    );
    let group_width = 1usize << pack_log2;
    assert_eq!(
        outputs.cols(),
        inputs.cols().div_ceil(group_width),
        "Proth120 pack: output columns must equal input columns / 2^pack_log2 rounded up"
    );
    validate_disjoint(
        &input_range,
        &output_range,
        "Proth120 pack: input/output overlap",
    );
    let source = inputs.as_ptr_and_stride();
    let target = outputs.as_mut_ptr_and_stride();
    let config = CudaLaunchConfig::basic(
        pack_grid_blocks(log_rows, pack_log2),
        PACK_BLOCK_THREADS,
        stream,
    );
    for group in 0..outputs.cols() {
        let first = group << pack_log2;
        let cols_in_group = (inputs.cols() - first).min(group_width);
        let input = PtrAndStride::new(
            unsafe {
                source.ptr.add(
                    first
                        .checked_mul(source.stride)
                        .expect("Proth120 pack: input column offset overflow"),
                )
            },
            source.stride,
        );
        let output = unsafe {
            target.ptr.add(
                group
                    .checked_mul(target.stride)
                    .expect("Proth120 pack: output column offset overflow"),
            )
        };
        PackColumnsFunction::default().launch(
            &config,
            &PackColumnsArguments::new(
                input,
                output,
                log_rows,
                cols_in_group as u32,
                group_width as u32,
            ),
        )?;
    }
    hypercube_evals_to_monomials_in_place(outputs, stream)
}
