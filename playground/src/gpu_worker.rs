use gpu_prover::cudart::device::set_device;
use gpu_prover::cudart::result::CudaResult;
use gpu_prover::prover::context::{MemPoolProverContext, ProverContextConfig};

pub fn get_gpu_worker(
    device_id: i32,
    prover_context_config: ProverContextConfig,
) -> impl FnOnce() + Send + 'static {
    move || inner(device_id, prover_context_config).unwrap()
}

fn inner(device_id: i32, prover_context_config: ProverContextConfig) -> CudaResult<()> {
    set_device(device_id)?;
    let context = MemPoolProverContext::new(&prover_context_config)?;

    Ok(())
}

