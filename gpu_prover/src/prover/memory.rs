use super::context::ProverContext;
use super::trace_holder::{transform_tree_caps, TraceHolder};
use super::tracing_data::{TracingDataDevice, TracingDataTransfer};
use super::{device_tracing, BF};
use crate::blake2s::Digest;
use crate::device_structures::DeviceMatrixMut;
use crate::prover::callbacks::Callbacks;
use crate::witness::memory_delegation::generate_memory_values_delegation;
use crate::witness::memory_main::generate_memory_values_main;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::result::CudaResult;
use prover::merkle_trees::MerkleTreeCapVarLength;
use std::sync::Arc;

pub struct MemoryCommitmentJob<'a, C: ProverContext> {
    range: device_tracing::Range<'a>,
    is_finished_event: CudaEvent,
    callbacks: Callbacks<'a>,
    tree_caps: Arc<Vec<Vec<Digest, C::HostAllocator>>>,
}

impl<'a, C: ProverContext> MemoryCommitmentJob<'a, C> {
    pub fn is_finished(&self) -> CudaResult<bool> {
        self.is_finished_event.query()
    }

    pub fn finish(self) -> CudaResult<(Vec<MerkleTreeCapVarLength>, f32)> {
        let Self {
            range,
            is_finished_event,
            callbacks,
            tree_caps,
        } = self;
        is_finished_event.synchronize()?;
        drop(callbacks);
        let commitment_time_ms = range.elapsed()?;
        let tree_caps = transform_tree_caps(&tree_caps);
        Ok((tree_caps, commitment_time_ms))
    }
}

pub fn commit_memory<'a, C: ProverContext>(
    tracing_data_transfer: TracingDataTransfer<'a, C>,
    circuit: &CompiledCircuitArtifact<BF>,
    log_lde_factor: u32,
    log_tree_cap_size: u32,
    context: &C,
) -> CudaResult<MemoryCommitmentJob<'a, C>> {
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
    match data_device {
        TracingDataDevice::Main {
            setup_and_teardown,
            trace,
        } => {
            generate_memory_values_main(
                memory_subtree,
                &setup_and_teardown,
                &trace,
                &mut DeviceMatrixMut::new(memory_holder.get_evaluations_mut(), trace_len),
                stream,
            )?;
        }
        TracingDataDevice::Delegation(trace) => {
            generate_memory_values_delegation(
                memory_subtree,
                &trace,
                &mut DeviceMatrixMut::new(memory_holder.get_evaluations_mut(), trace_len),
                stream,
            )?;
        }
    };
    memory_holder.make_evaluations_sum_to_zero_extend_and_commit(context)?;
    memory_holder.produce_tree_caps(context)?;
    range.end(stream)?;
    let tree_caps = memory_holder.get_tree_caps();
    let callbacks = transfer.callbacks;
    let is_finished_event = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING)?;
    is_finished_event.record(stream)?;
    let job = MemoryCommitmentJob {
        range,
        is_finished_event,
        callbacks,
        tree_caps,
    };
    Ok(job)
}
