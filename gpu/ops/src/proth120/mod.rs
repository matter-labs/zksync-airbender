use core::mem::{align_of, offset_of, size_of};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::primitives::device_structures::{MutPtrAndStride, PtrAndStride};
use gpu_core::primitives::field::PR;
use gpu_core::primitives::utils::get_grid_block_dims_for_threads_count;

#[doc(hidden)]
#[repr(C, align(16))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PrProbeInput {
    pub a: PR,
    pub b: PR,
    pub c: PR,
    pub exp_u32: u32,
    pub exp_le: [u32; 4],
    pub natural_le: [u32; 4],
    pub extract_offset: u32,
    pub extract_count: u32,
    pub _pad: u32,
}

const _: () = {
    assert!(size_of::<PrProbeInput>() == 96);
    assert!(align_of::<PrProbeInput>() == 16);
    assert!(offset_of!(PrProbeInput, a) == 0);
    assert!(offset_of!(PrProbeInput, b) == 16);
    assert!(offset_of!(PrProbeInput, c) == 32);
    assert!(offset_of!(PrProbeInput, exp_u32) == 48);
    assert!(offset_of!(PrProbeInput, exp_le) == 52);
    assert!(offset_of!(PrProbeInput, natural_le) == 68);
    assert!(offset_of!(PrProbeInput, extract_offset) == 84);
    assert!(offset_of!(PrProbeInput, extract_count) == 88);
    assert!(offset_of!(PrProbeInput, _pad) == 92);
};

#[doc(hidden)]
#[repr(C, align(16))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PrProbeOutput {
    pub add: PR,
    pub sub: PR,
    pub mul: PR,
    pub sqr: PR,
    pub neg: PR,
    pub dbl: PR,
    pub inv: PR,
    pub pow_u32: PR,
    pub pow_u128: PR,
    pub fma: PR,
    pub fms: PR,
    pub from_natural: PR,
    pub pow_log2_8: PR,
    pub scalar_mul: PR,
    pub half: PR,
    pub zero: PR,
    pub one: PR,
    pub two: PR,
    pub be_bytes: [u8; 16],
    pub eq: u32,
    pub is_zero: u32,
    pub extract: u32,
    pub operator_mismatch: u32,
}

const _: () = {
    assert!(size_of::<PrProbeOutput>() == 320);
    assert!(align_of::<PrProbeOutput>() == 16);
    assert!(offset_of!(PrProbeOutput, add) == 0);
    assert!(offset_of!(PrProbeOutput, sub) == 16);
    assert!(offset_of!(PrProbeOutput, mul) == 32);
    assert!(offset_of!(PrProbeOutput, sqr) == 48);
    assert!(offset_of!(PrProbeOutput, neg) == 64);
    assert!(offset_of!(PrProbeOutput, dbl) == 80);
    assert!(offset_of!(PrProbeOutput, inv) == 96);
    assert!(offset_of!(PrProbeOutput, pow_u32) == 112);
    assert!(offset_of!(PrProbeOutput, pow_u128) == 128);
    assert!(offset_of!(PrProbeOutput, fma) == 144);
    assert!(offset_of!(PrProbeOutput, fms) == 160);
    assert!(offset_of!(PrProbeOutput, from_natural) == 176);
    assert!(offset_of!(PrProbeOutput, pow_log2_8) == 192);
    assert!(offset_of!(PrProbeOutput, scalar_mul) == 208);
    assert!(offset_of!(PrProbeOutput, half) == 224);
    assert!(offset_of!(PrProbeOutput, zero) == 240);
    assert!(offset_of!(PrProbeOutput, one) == 256);
    assert!(offset_of!(PrProbeOutput, two) == 272);
    assert!(offset_of!(PrProbeOutput, be_bytes) == 288);
    assert!(offset_of!(PrProbeOutput, eq) == 304);
    assert!(offset_of!(PrProbeOutput, is_zero) == 308);
    assert!(offset_of!(PrProbeOutput, extract) == 312);
    assert!(offset_of!(PrProbeOutput, operator_mismatch) == 316);
};

#[doc(hidden)]
#[repr(C, align(16))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PrRawProbeInput {
    pub a: [u32; 8],
    pub b: [u32; 8],
    pub op: u32,
    pub n: u32,
    pub width: u32,
    pub flags: u32,
}

const _: () = {
    assert!(size_of::<PrRawProbeInput>() == 80);
    assert!(align_of::<PrRawProbeInput>() == 16);
    assert!(offset_of!(PrRawProbeInput, a) == 0);
    assert!(offset_of!(PrRawProbeInput, b) == 32);
    assert!(offset_of!(PrRawProbeInput, op) == 64);
    assert!(offset_of!(PrRawProbeInput, n) == 68);
    assert!(offset_of!(PrRawProbeInput, width) == 72);
    assert!(offset_of!(PrRawProbeInput, flags) == 76);
};

#[doc(hidden)]
#[repr(C, align(16))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PrRawProbeOutput {
    pub r: [u32; 8],
    pub carry: u32,
    pub status: u32,
    pub _pad: [u32; 2],
}

const _: () = {
    assert!(size_of::<PrRawProbeOutput>() == 48);
    assert!(align_of::<PrRawProbeOutput>() == 16);
    assert!(offset_of!(PrRawProbeOutput, r) == 0);
    assert!(offset_of!(PrRawProbeOutput, carry) == 32);
    assert!(offset_of!(PrRawProbeOutput, status) == 36);
    assert!(offset_of!(PrRawProbeOutput, _pad) == 40);
};

cuda_kernel_signature_arguments_and_function!(
    InvPR,
    values: *const PR,
    result: *mut PR,
    count: u32,
);
cuda_kernel_declaration!(
    ab_inv_pr_kernel(values: *const PR, result: *mut PR, count: u32,)
);

cuda_kernel_signature_arguments_and_function!(
    BatchInversePR,
    input: *const PR,
    output: *mut PR,
    prefix: *mut PR,
    count: u32,
);
cuda_kernel_declaration!(
    ab_batch_inverse_pr_kernel(input: *const PR, output: *mut PR, prefix: *mut PR, count: u32,)
);

cuda_kernel_signature_arguments_and_function!(
    PrFieldProbe,
    input: *const PrProbeInput,
    output: *mut PrProbeOutput,
    count: u32,
);
cuda_kernel_declaration!(
    ab_pr_field_probe_kernel(input: *const PrProbeInput, output: *mut PrProbeOutput, count: u32,)
);

cuda_kernel_signature_arguments_and_function!(
    PrRawProbe,
    input: *const PrRawProbeInput,
    output: *mut PrRawProbeOutput,
    count: u32,
);
cuda_kernel_declaration!(
    ab_pr_raw_probe_kernel(input: *const PrRawProbeInput, output: *mut PrRawProbeOutput, count: u32,)
);

cuda_kernel_signature_arguments_and_function!(
    PrAccessProbe,
    src: *const PR,
    dst: *mut PR,
    src_matrix: PtrAndStride<PR>,
    dst_matrix_setter: MutPtrAndStride<PR>,
    dst_matrix_getter_setter: MutPtrAndStride<PR>,
    rows: u32,
);
cuda_kernel_declaration!(
    ab_pr_access_probe_kernel(
        src: *const PR,
        dst: *mut PR,
        src_matrix: PtrAndStride<PR>,
        dst_matrix_setter: MutPtrAndStride<PR>,
        dst_matrix_getter_setter: MutPtrAndStride<PR>,
        rows: u32,
    )
);

const _: () = {
    assert!(size_of::<PtrAndStride<PR>>() == 16 && align_of::<PtrAndStride<PR>>() == 8);
    assert!(offset_of!(PtrAndStride<PR>, ptr) == 0);
    assert!(offset_of!(PtrAndStride<PR>, stride) == 8);
    assert!(size_of::<MutPtrAndStride<PR>>() == 16 && align_of::<MutPtrAndStride<PR>>() == 8);
    assert!(offset_of!(MutPtrAndStride<PR>, ptr) == 0);
    assert!(offset_of!(MutPtrAndStride<PR>, stride) == 8);
};

pub fn inv_pr(
    values: &DeviceSlice<PR>,
    result: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        values.len() == result.len(),
        "Proth120 inverse length mismatch"
    );
    assert!(
        values.len() <= u32::MAX as usize,
        "Proth120 inverse count exceeds u32::MAX"
    );
    let count = values.len() as u32;
    if count == 0 {
        return Ok(());
    }
    let (grid, block) = get_grid_block_dims_for_threads_count(128, count);
    let config = CudaLaunchConfig::basic(grid, block, stream);
    let args = InvPRArguments::new(values.as_ptr(), result.as_mut_ptr(), count);
    InvPRFunction(ab_inv_pr_kernel).launch(&config, &args)
}

fn check_batch_lengths(input: usize, output: usize, prefix: usize) {
    assert!(
        input <= u32::MAX as usize,
        "Proth120 batch inverse count exceeds u32::MAX"
    );
    assert!(
        input == output && input == prefix,
        "Proth120 batch inverse length mismatch"
    );
}

fn check_spans(
    input: (usize, usize),
    output: (usize, usize),
    prefix: (usize, usize),
    in_place: bool,
) -> u32 {
    let count = input.1 / size_of::<PR>();
    assert!(
        count <= u32::MAX as usize,
        "Proth120 batch inverse count exceeds u32::MAX"
    );
    assert!(
        input.1 == output.1 && input.1 == prefix.1,
        "Proth120 batch inverse length mismatch"
    );
    if input.1 == 0 {
        return 0;
    }
    let end = |span: (usize, usize)| {
        span.0
            .checked_add(span.1)
            .expect("Proth120 batch inverse address range overflow")
    };
    let input_end = end(input);
    let output_end = end(output);
    let prefix_end = end(prefix);
    let overlaps = |a: usize, a_end: usize, b: usize, b_end: usize| a < b_end && b < a_end;
    assert!(
        in_place || !overlaps(input.0, input_end, output.0, output_end),
        "Proth120 batch inverse input/output overlap: use in-place API"
    );
    assert!(
        !overlaps(prefix.0, prefix_end, input.0, input_end),
        "Proth120 batch inverse prefix overlaps input"
    );
    assert!(
        !overlaps(prefix.0, prefix_end, output.0, output_end),
        "Proth120 batch inverse prefix overlaps output"
    );
    count as u32
}

fn byte_span(ptr: *const PR, len: usize) -> (usize, usize) {
    (
        ptr as usize,
        len.checked_mul(size_of::<PR>())
            .expect("Proth120 batch inverse address range overflow"),
    )
}

fn launch_batch(
    input: *const PR,
    output: *mut PR,
    prefix: *mut PR,
    count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    if count == 0 {
        return Ok(());
    }
    let chunks = count.div_ceil(256);
    let config = CudaLaunchConfig::basic(chunks.div_ceil(128), 128, stream);
    let args = BatchInversePRArguments::new(input, output, prefix, count);
    BatchInversePRFunction(ab_batch_inverse_pr_kernel).launch(&config, &args)
}

pub fn batch_inverse_pr(
    input: &DeviceSlice<PR>,
    output: &mut DeviceSlice<PR>,
    prefix: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    check_batch_lengths(input.len(), output.len(), prefix.len());
    let count = check_spans(
        byte_span(input.as_ptr(), input.len()),
        byte_span(output.as_ptr(), output.len()),
        byte_span(prefix.as_ptr(), prefix.len()),
        false,
    );
    launch_batch(
        input.as_ptr(),
        output.as_mut_ptr(),
        prefix.as_mut_ptr(),
        count,
        stream,
    )
}

pub fn batch_inverse_pr_in_place(
    values: &mut DeviceSlice<PR>,
    prefix: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    check_batch_lengths(values.len(), values.len(), prefix.len());
    let ptr = values.as_mut_ptr();
    let span = byte_span(ptr, values.len());
    let count = check_spans(span, span, byte_span(prefix.as_ptr(), prefix.len()), true);
    launch_batch(ptr, ptr, prefix.as_mut_ptr(), count, stream)
}

#[doc(hidden)]
pub fn pr_field_probe(
    input: &DeviceSlice<PrProbeInput>,
    output: &mut DeviceSlice<PrProbeOutput>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        input.len() <= u32::MAX as usize,
        "Proth120 field probe count exceeds u32::MAX"
    );
    assert!(
        input.len() == output.len(),
        "Proth120 field probe length mismatch"
    );
    let count = input.len() as u32;
    if count == 0 {
        return Ok(());
    }
    let (grid, block) = get_grid_block_dims_for_threads_count(128, count);
    let config = CudaLaunchConfig::basic(grid, block, stream);
    let args = PrFieldProbeArguments::new(input.as_ptr(), output.as_mut_ptr(), count);
    PrFieldProbeFunction(ab_pr_field_probe_kernel).launch(&config, &args)
}

#[doc(hidden)]
pub fn pr_raw_probe(
    input: &DeviceSlice<PrRawProbeInput>,
    output: &mut DeviceSlice<PrRawProbeOutput>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        input.len() <= u32::MAX as usize,
        "Proth120 raw probe count exceeds u32::MAX"
    );
    assert!(
        input.len() == output.len(),
        "Proth120 raw probe length mismatch"
    );
    let count = input.len() as u32;
    if count == 0 {
        return Ok(());
    }
    let (grid, block) = get_grid_block_dims_for_threads_count(128, count);
    let config = CudaLaunchConfig::basic(grid, block, stream);
    let args = PrRawProbeArguments::new(input.as_ptr(), output.as_mut_ptr(), count);
    PrRawProbeFunction(ab_pr_raw_probe_kernel).launch(&config, &args)
}

#[doc(hidden)]
pub fn pr_access_probe(
    src: &DeviceSlice<PR>,
    dst: &mut DeviceSlice<PR>,
    rows: u32,
    stride: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        rows.is_multiple_of(32),
        "Proth120 access probe rows must be a multiple of 32"
    );
    assert!(rows <= stride, "Proth120 access probe rows exceed stride");
    let stride = stride as usize;
    assert!(
        src.len() >= 2 * stride,
        "Proth120 access probe source length mismatch"
    );
    assert!(
        dst.len() >= 9 * stride,
        "Proth120 access probe destination length mismatch"
    );
    if rows == 0 {
        return Ok(());
    }
    let (grid, block) = get_grid_block_dims_for_threads_count(128, rows);
    let config = CudaLaunchConfig::basic(grid, block, stream);
    let src_matrix = PtrAndStride::new(src.as_ptr(), stride);
    let ptr = dst.as_mut_ptr();
    let dst_matrix = MutPtrAndStride::new(ptr, stride);
    let args =
        PrAccessProbeArguments::new(src.as_ptr(), ptr, src_matrix, dst_matrix, dst_matrix, rows);
    PrAccessProbeFunction(ab_pr_access_probe_kernel).launch(&config, &args)
}
