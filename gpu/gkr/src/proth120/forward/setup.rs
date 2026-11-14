use std::ptr::null_mut;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_prover_context::ProverContext;

use super::challenge_banks::ForwardChallengeBanks;
use crate::setup::PackedSetupSource;
use crate::upstream::{GKRCircuitArtifact, PR};

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct ForwardSetupLookupBatchPr {
    pub column_count: u32,
    pub decoder_table_id: u32,
    pub output: *mut PR,
    pub decoder_fill_value_out: *mut PR,
    pub alpha_powers: *const PR,
    pub inputs: [*const PR; 11],
}

const _: () = {
    assert!(size_of::<ForwardSetupLookupBatchPr>() == 120);
    assert!(align_of::<ForwardSetupLookupBatchPr>() == 8);
    assert!(core::mem::offset_of!(ForwardSetupLookupBatchPr, inputs) == 32);
    assert!(size_of::<ForwardSetupLookupBatchPr>() + size_of::<u32>() <= 32_764);
};

cuda_kernel_signature_arguments_and_function!(pub(crate) PrSetupLookup, batch: ForwardSetupLookupBatchPr, rows: u32);
cuda_kernel_declaration!(pub(crate) ab_pr_gkr_forward_setup_generic_lookup_batch_kernel(batch: ForwardSetupLookupBatchPr, rows: u32));

pub(crate) struct GpuGKRForwardSetupPr {
    pub generic_lookup: DeviceAllocation<PR>,
}

pub(crate) fn schedule_setup(
    setup: &PackedSetupSource<'_>,
    circuit: &GKRCircuitArtifact<PR>,
    banks: &ForwardChallengeBanks,
    context: &ProverContext,
) -> CudaResult<GpuGKRForwardSetupPr> {
    let width = circuit.generic_lookup_tables_width;
    assert!(
        width <= 11,
        "Proth120 generic lookup table width exceeds 11"
    );
    let raw = setup.raw();
    assert_eq!(raw.columns_count, width, "Proth120 setup columns mismatch");
    assert_eq!(
        1usize << raw.log_domain_size,
        circuit.trace_len,
        "Proth120 setup rows mismatch"
    );
    assert!(
        circuit.total_tables_size <= circuit.trace_len,
        "Proth120 setup tables exceed trace length"
    );
    let mut generic_lookup =
        context.alloc(circuit.total_tables_size, AllocationPlacement::BestFit)?;
    let mut inputs = [std::ptr::null(); 11];
    for (column, input) in inputs.iter_mut().take(width).enumerate() {
        *input = unsafe {
            raw.get_hypercube_evals()
                .as_ptr()
                .add(column * circuit.trace_len)
        };
    }
    if circuit.total_tables_size != 0 {
        let batch = ForwardSetupLookupBatchPr {
            column_count: width as u32,
            decoder_table_id: 0,
            output: generic_lookup.as_mut_ptr(),
            decoder_fill_value_out: null_mut(),
            alpha_powers: banks.lookup_alpha_powers.as_ptr(),
            inputs,
        };
        let config = CudaLaunchConfig::basic(
            (circuit.total_tables_size as u32).div_ceil(128),
            128,
            context.get_exec_stream(),
        );
        PrSetupLookupFunction(ab_pr_gkr_forward_setup_generic_lookup_batch_kernel).launch(
            &config,
            &PrSetupLookupArguments::new(batch, circuit.total_tables_size as u32),
        )?;
    }
    Ok(GpuGKRForwardSetupPr { generic_lookup })
}
