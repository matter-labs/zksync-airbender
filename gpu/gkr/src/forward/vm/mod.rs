//! Production forward VM.

pub(crate) mod desc;
pub(crate) mod lower;
mod output;
pub(crate) mod production_bind;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cuda_struct_and_stub;

use self::desc::{FwdVmDesc, CONST_DERIVED_E4_CAP};
use self::lower::{top_bits_const, FwdVmRequestSlot, LoweredFwdVm};
use self::production_bind::arg_derived_e4_value;
use crate::replay::GkrReplayValues;
use gpu_core::primitives::field::E4;
use gpu_prover_context::replay::register_kernel_patch;
use gpu_prover_context::ProverContext;
use gpu_trace::witness::circuit_type::{
    CircuitType, DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};

pub(crate) const FWD_VM_THREADS_PER_BLOCK: u32 = 128;

cuda_struct_and_stub! { static ab_gkr_fwd_vm_const_derived_e4: [E4; CONST_DERIVED_E4_CAP]; }

cuda_kernel_signature_arguments_and_function!(
    pub(crate) GkrFwdVmRelease,
    desc: FwdVmDesc,
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_fwd_vm_kernel(desc: FwdVmDesc)
);

cuda_kernel_declaration!(pub(crate)
    ab_gkr_fwd_vm_b8_kernel(desc: FwdVmDesc)
);

const fn production_fwd_vm_kernel(circuit_type: CircuitType) -> GkrFwdVmReleaseSignature {
    match circuit_type {
        CircuitType::Delegation(circuit_type) => match circuit_type {
            DelegationCircuitType::BigIntWithControl => ab_gkr_fwd_vm_b8_kernel,
            DelegationCircuitType::Blake2GFunction => ab_gkr_fwd_vm_b8_kernel,
            DelegationCircuitType::Blake2WithCompression => ab_gkr_fwd_vm_b8_kernel,
            DelegationCircuitType::KeccakChi5 => ab_gkr_fwd_vm_b8_kernel,
            DelegationCircuitType::KeccakColumnParity => ab_gkr_fwd_vm_b8_kernel,
            DelegationCircuitType::KeccakSpecial5 => ab_gkr_fwd_vm_b8_kernel,
            DelegationCircuitType::KeccakThetaRho => ab_gkr_fwd_vm_b8_kernel,
        },
        CircuitType::Unrolled(circuit_type) => match circuit_type {
            UnrolledCircuitType::InitsAndTeardowns => ab_gkr_fwd_vm_kernel,
            UnrolledCircuitType::Memory(circuit_type) => match circuit_type {
                UnrolledMemoryCircuitType::LoadStoreSubwordOnly => ab_gkr_fwd_vm_b8_kernel,
                UnrolledMemoryCircuitType::LoadStoreWordOnly => ab_gkr_fwd_vm_b8_kernel,
            },
            UnrolledCircuitType::NonMemory(circuit_type) => match circuit_type {
                UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop => ab_gkr_fwd_vm_b8_kernel,
                UnrolledNonMemoryCircuitType::JumpBranchSlt => ab_gkr_fwd_vm_b8_kernel,
                UnrolledNonMemoryCircuitType::MulDivUnsigned => ab_gkr_fwd_vm_b8_kernel,
                UnrolledNonMemoryCircuitType::ShiftBinary => ab_gkr_fwd_vm_b8_kernel,
            },
            UnrolledCircuitType::Unified => ab_gkr_fwd_vm_b8_kernel,
        },
    }
}

pub(crate) fn launch_fwd_vm(
    lowered: &LoweredFwdVm,
    circuit_type: CircuitType,
    context: &ProverContext,
) -> CudaResult<()> {
    let desc = &lowered.desc;
    assert!(
        desc.layer_count > 0,
        "forward VM must have at least one layer"
    );
    let grid = desc.count.max(1).div_ceil(FWD_VM_THREADS_PER_BLOCK);
    let config = CudaLaunchConfig::builder()
        .grid_dim(grid)
        .block_dim(FWD_VM_THREADS_PER_BLOCK)
        .stream(context.get_exec_stream())
        .build();
    let args = GkrFwdVmReleaseArguments::new(*desc);
    let kernel = production_fwd_vm_kernel(circuit_type);
    GkrFwdVmReleaseFunction(kernel).launch(&config, &args)?;
    register_fwd_vm_patch(kernel, grid, lowered, context)
}

/// Lets a replayed graph refill the descriptor slots that hold per-request
/// external challenges and top bits.
fn register_fwd_vm_patch(
    kernel: GkrFwdVmReleaseSignature,
    grid: u32,
    lowered: &LoweredFwdVm,
    context: &ProverContext,
) -> CudaResult<()> {
    if lowered.request_slots.is_empty() {
        return Ok(());
    }
    let desc = Box::new(lowered.desc);
    let slots = lowered.request_slots.clone();
    register_kernel_patch(context.get_exec_stream(), move |exec, node, inputs| {
        let values = inputs.get::<GkrReplayValues>();
        let mut desc = desc.clone();
        for slot in &slots {
            match *slot {
                FwdVmRequestSlot::ArgDerived { slot, reference } => {
                    desc.arg_derived_e4[slot] =
                        arg_derived_e4_value(&values.external_challenges, &reference)
                            .unwrap_or_else(|error| panic!("{error}"));
                }
                FwdVmRequestSlot::TopBits { slot, reference } => {
                    desc.consts[slot] =
                        top_bits_const(&values.inits_and_teardowns_top_bits, reference)
                            .expect("replayed request lacks a referenced top-bits set");
                }
            }
        }
        let config = CudaLaunchConfig {
            grid_dim: grid.into(),
            block_dim: FWD_VM_THREADS_PER_BLOCK.into(),
            ..Default::default()
        };
        exec.set_kernel_node(
            node,
            &GkrFwdVmReleaseFunction(kernel),
            &config,
            &GkrFwdVmReleaseArguments::new(*desc),
        )
    })
}

cuda_kernel_declaration!(pub(crate)
    ab_gkr_fwd_vm_streaming_kernel(desc: FwdVmDesc)
);

pub(crate) fn launch_fwd_vm_streaming(
    lowered: &LoweredFwdVm,
    blocks: u32,
    context: &ProverContext,
) -> CudaResult<()> {
    let desc = &lowered.desc;
    assert!(
        blocks > 0 && desc.layer_count > 0,
        "streaming forward needs blocks and layers"
    );
    let config = CudaLaunchConfig::builder()
        .grid_dim(blocks)
        .block_dim(FWD_VM_THREADS_PER_BLOCK)
        .stream(context.get_exec_stream())
        .build();
    let args = GkrFwdVmReleaseArguments::new(*desc);
    GkrFwdVmReleaseFunction(ab_gkr_fwd_vm_streaming_kernel).launch(&config, &args)?;
    register_fwd_vm_patch(ab_gkr_fwd_vm_streaming_kernel, blocks, lowered, context)
}
