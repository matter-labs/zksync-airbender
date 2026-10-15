use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{
    cuda_kernel, cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function,
};
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use gpu_core::primitives::field::PR;

use super::lde::{launch_transform, TransformPass, TransformPolicy};
use super::{validate_disjoint, validate_matrix, validate_slice};

cuda_kernel_signature_arguments_and_function!(
    pub(crate) Mobius,
    inputs: PtrAndStride<PR>, outputs: MutPtrAndStride<PR>, log_n: u32, start_stage: u32,
);
macro_rules! mobius_kernel {
    ($name:ident) => {
        cuda_kernel_declaration!($name(
            inputs: PtrAndStride<PR>, outputs: MutPtrAndStride<PR>, log_n: u32, start_stage: u32,
        ));
    };
}
mobius_kernel!(ab_pr_mobius_nonfinal_5_stages_kernel);
mobius_kernel!(ab_pr_mobius_nonfinal_6_stages_kernel);
mobius_kernel!(ab_pr_mobius_nonfinal_7_stages_kernel);
mobius_kernel!(ab_pr_mobius_nonfinal_8_stages_kernel);
mobius_kernel!(ab_pr_mobius_final_8_stages_kernel);
mobius_kernel!(ab_pr_mobius_final_10_stages_kernel);
mobius_kernel!(ab_pr_mobius_final_12_stages_kernel);
mobius_kernel!(ab_pr_mobius_small_kernel);

pub(crate) struct MobiusPolicy;
impl TransformPolicy for MobiusPolicy {
    type Function = MobiusFunction;
    type Arguments = MobiusArguments;
    fn function(&self, pass: TransformPass) -> MobiusFunction {
        MobiusFunction(match pass {
            TransformPass::Small => ab_pr_mobius_small_kernel,
            TransformPass::Nonfinal(5) => ab_pr_mobius_nonfinal_5_stages_kernel,
            TransformPass::Nonfinal(6) => ab_pr_mobius_nonfinal_6_stages_kernel,
            TransformPass::Nonfinal(7) => ab_pr_mobius_nonfinal_7_stages_kernel,
            TransformPass::Nonfinal(8) => ab_pr_mobius_nonfinal_8_stages_kernel,
            TransformPass::Final(8) => ab_pr_mobius_final_8_stages_kernel,
            TransformPass::Final(10) => ab_pr_mobius_final_10_stages_kernel,
            TransformPass::Final(12) => ab_pr_mobius_final_12_stages_kernel,
            _ => panic!("Proth120 hypercube transform: unsupported transform pass {pass:?}"),
        })
    }
    fn arguments(
        &self,
        source: PtrAndStride<PR>,
        target: MutPtrAndStride<PR>,
        log_n: u32,
        start_stage: u32,
    ) -> MobiusArguments {
        MobiusArguments::new(source, target, log_n, start_stage)
    }
}

pub fn hypercube_evals_to_monomials(
    inputs: &(impl DeviceMatrixChunkImpl<PR> + ?Sized),
    outputs: &mut (impl DeviceMatrixChunkMutImpl<PR> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
    let (log_n, input_range) = validate_matrix(inputs, 0, 26, "Proth120 hypercube input");
    let (_, output_range) = validate_matrix(outputs, 0, 26, "Proth120 hypercube output");
    assert_eq!(
        inputs.rows(),
        outputs.rows(),
        "Proth120 hypercube transform: input/output rows differ"
    );
    assert_eq!(
        inputs.cols(),
        outputs.cols(),
        "Proth120 hypercube transform: input/output columns differ"
    );
    validate_disjoint(
        &input_range,
        &output_range,
        "Proth120 hypercube transform: input/output overlap",
    );
    launch_transform(
        &MobiusPolicy,
        inputs.as_ptr_and_stride(),
        outputs.as_mut_ptr_and_stride(),
        log_n,
        outputs.cols(),
        stream,
    )
}

pub(crate) fn hypercube_evals_to_monomials_in_place(
    values: &mut (impl DeviceMatrixChunkMutImpl<PR> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
    let (log_n, _) = validate_matrix(values, 0, 26, "Proth120 hypercube values");
    let cols = values.cols();
    let target = values.as_mut_ptr_and_stride();
    let source = PtrAndStride::new(target.ptr as *const PR, target.stride);
    launch_transform(&MobiusPolicy, source, target, log_n, cols, stream)
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct EqSample {
    pub point: PR,
    pub weight: PR,
}

const _: () = {
    assert!(size_of::<EqSample>() == 32);
    assert!(align_of::<EqSample>() == 16);
    assert!(std::mem::offset_of!(EqSample, point) == 0);
    assert!(std::mem::offset_of!(EqSample, weight) == 16);
};

cuda_kernel!(UpdateEq, ab_pr_update_eq_poly_kernel(
    eq: *mut PR, log_n: u32, samples: *const EqSample, count: u32,
));

pub fn update_eq_poly(
    eq: &mut DeviceSlice<PR>,
    ood: &DeviceSlice<EqSample>,
    in_domain: &DeviceSlice<EqSample>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        eq.len().is_power_of_two(),
        "Proth120 eq update: length must be a power of two"
    );
    let log_n = eq.len().trailing_zeros();
    assert!(
        log_n <= 26,
        "Proth120 eq update: log_n {log_n} outside 0..=26"
    );
    let eq_range = validate_slice(eq, "Proth120 eq update values");
    for samples in [ood, in_domain] {
        let sample_range = validate_slice(samples, "Proth120 eq update samples");
        validate_disjoint(
            &eq_range,
            &sample_range,
            "Proth120 eq update: values/samples overlap",
        );
        let count =
            u32::try_from(samples.len()).expect("Proth120 eq update: sample count exceeds u32");
        if count == 0 {
            continue;
        }
        let config = CudaLaunchConfig::basic((eq.len() as u32).div_ceil(4096), 256, stream);
        UpdateEqFunction::default().launch(
            &config,
            &UpdateEqArguments::new(eq.as_mut_ptr(), log_n, samples.as_ptr(), count),
        )?;
    }
    Ok(())
}
