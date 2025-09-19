use super::context::{ProverContext, UnsafeMutAccessor};
use super::trace_holder::{get_tree_caps, TraceHolder, TreesCacheMode};
use super::tracing_data::{TracingDataDevice, TracingDataTransfer};
use super::{device_tracing, BF};
use crate::device_structures::DeviceMatrixMut;
use crate::prover::callbacks::Callbacks;
use crate::witness::memory_delegation::generate_memory_values_delegation;
use crate::witness::memory_main::generate_memory_values_main;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::result::CudaResult;
use fft::GoodAllocator;
use prover::merkle_trees::MerkleTreeCapVarLength;

pub struct MemoryCommitmentJob<'a> {
    is_finished_event: CudaEvent,
    callbacks: Callbacks<'a>,
    tree_caps: Box<Option<Vec<MerkleTreeCapVarLength>>>,
    range: device_tracing::Range<'a>,
}

impl<'a> MemoryCommitmentJob<'a> {
    pub fn is_finished(&self) -> CudaResult<bool> {
        self.is_finished_event.query()
    }

    pub fn finish(self) -> CudaResult<(Vec<MerkleTreeCapVarLength>, f32)> {
        let Self {
            is_finished_event,
            callbacks,
            tree_caps,
            range,
        } = self;
        is_finished_event.synchronize()?;
        drop(callbacks);
        let tree_caps = tree_caps.unwrap();
        let commitment_time_ms = range.elapsed()?;
        Ok((tree_caps, commitment_time_ms))
    }
}

pub fn commit_memory<'a>(
    tracing_data_transfer: TracingDataTransfer<'a, impl GoodAllocator>,
    circuit: &CompiledCircuitArtifact<BF>,
    log_lde_factor: u32,
    log_tree_cap_size: u32,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    let trace_len = circuit.trace_len;
    assert!(trace_len.is_power_of_two());
    let log_domain_size = trace_len.trailing_zeros();
    let memory_subtree = &circuit.memory_layout;
    let memory_columns_count = memory_subtree.total_width;
    let mut memory_holder = TraceHolder::new(
        log_domain_size,
        log_lde_factor,
        0,
        log_tree_cap_size,
        memory_columns_count,
        true,
        true,
        false,
        TreesCacheMode::CacheFull,
        context,
    )?;
    let TracingDataTransfer {
        circuit_type: _,
        data_host: _,
        data_device,
        transfer,
    } = tracing_data_transfer;
    transfer.ensure_transferred(context)?;
    let range = device_tracing::Range::new("commit_memory")?;
    let stream = context.get_exec_stream();
    range.start(stream)?;
    let mut evaluations = memory_holder.get_uninit_evaluations_mut();
    let memory = &mut DeviceMatrixMut::new(&mut evaluations, trace_len);
    match data_device {
        TracingDataDevice::Main {
            setup_and_teardown,
            trace,
        } => {
            generate_memory_values_main(
                memory_subtree,
                &setup_and_teardown,
                &trace,
                memory,
                stream,
            )?;
        }
        TracingDataDevice::Delegation(trace) => {
            generate_memory_values_delegation(memory_subtree, &trace, memory, stream)?;
        }
    };
    memory_holder.make_evaluations_sum_to_zero_extend_and_commit(context)?;
    let src_tree_cap_accessors = memory_holder.get_tree_caps_accessors();
    let mut tree_caps = Box::new(None);
    let dst_tree_caps_accessor = UnsafeMutAccessor::new(tree_caps.as_mut());
    let transform_tree_caps_fn = move || unsafe {
        let tree_caps = get_tree_caps(&src_tree_cap_accessors);
        assert!(dst_tree_caps_accessor
            .get_mut()
            .replace(tree_caps)
            .is_none());
    };
    let mut callbacks = transfer.callbacks;
    callbacks.schedule(transform_tree_caps_fn, stream)?;
    range.end(stream)?;
    let is_finished_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    is_finished_event.record(stream)?;
    let job = MemoryCommitmentJob {
        is_finished_event,
        callbacks,
        tree_caps,
        range,
    };
    Ok(job)
}
