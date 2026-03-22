use crate::primitives::callbacks::Callbacks;
use crate::primitives::circuit_type::{CircuitType, UnrolledCircuitType};
use crate::primitives::context::{ProverContext, UnsafeMutAccessor};
use crate::primitives::device_structures::DeviceMatrixMut;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::BF;
use crate::prover::trace_holder::{get_tree_caps_for_accessors, TraceHolder, TreesCacheMode};
use crate::prover::tracing_data::{TracingDataDevice, UnrolledTracingDataDevice};
use crate::witness::memory_unrolled::{
    generate_memory_values_unrolled_memory, generate_memory_values_unrolled_non_memory,
};
use crate::witness::trace_unrolled::ExecutorFamilyDecoderData;
use cs::gkr_compiler::GKRCircuitArtifact;
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use prover::merkle_trees::MerkleTreeCapVarLength;

pub(crate) struct MemoryCommitmentJob<'a> {
    is_finished_event: CudaEvent,
    callbacks: Callbacks<'a>,
    tree_caps: Box<Option<Vec<MerkleTreeCapVarLength>>>,
    range: Range,
}

impl<'a> MemoryCommitmentJob<'a> {
    pub(crate) fn is_finished(&self) -> CudaResult<bool> {
        self.is_finished_event.query()
    }

    pub(crate) fn finish(self) -> CudaResult<(Vec<MerkleTreeCapVarLength>, f32)> {
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

#[allow(clippy::too_many_arguments)]
pub(crate) fn commit_memory<'a>(
    circuit_type: CircuitType,
    compiled_circuit: &GKRCircuitArtifact<BF>,
    decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
    tracing_data: &TracingDataDevice,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_tree_cap_size: u32,
    context: &ProverContext,
) -> CudaResult<MemoryCommitmentJob<'a>> {
    let trace_len = compiled_circuit.trace_len;
    assert!(trace_len.is_power_of_two());
    let log_domain_size = trace_len.trailing_zeros();
    let memory_columns_count = compiled_circuit.memory_layout.total_width;
    let mut memory_holder = TraceHolder::new(
        log_domain_size,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
        memory_columns_count,
        TreesCacheMode::CachePartial,
        context,
    )?;
    let mut callbacks = Callbacks::new();
    let range = Range::new("commit_memory")?;
    let stream = context.get_exec_stream();
    range.start(stream)?;
    let mut evaluations = memory_holder.get_uninit_hypercube_evals_mut();
    let memory = &mut DeviceMatrixMut::new(&mut evaluations, trace_len);
    match (circuit_type, tracing_data) {
        (
            CircuitType::Unrolled(UnrolledCircuitType::NonMemory(circuit_type)),
            TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(trace)),
        ) => {
            generate_memory_values_unrolled_non_memory(
                circuit_type,
                &compiled_circuit.memory_layout,
                decoder_table.expect("non-memory circuits require a decoder table"),
                trace,
                memory,
                stream,
            )?;
        }
        (
            CircuitType::Unrolled(UnrolledCircuitType::Memory(circuit_type)),
            TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Memory(trace)),
        ) => {
            generate_memory_values_unrolled_memory(
                circuit_type,
                &compiled_circuit.memory_layout,
                decoder_table.expect("memory circuits require a decoder table"),
                trace,
                memory,
                stream,
            )?;
        }
        _ => unimplemented!(
            "commit_memory currently supports only unrolled non-memory and memory traces"
        ),
    }
    let _ = evaluations;
    memory_holder.commit_all(context)?;
    let src_tree_cap_accessors = memory_holder.get_tree_caps_accessors();
    let log_lde = memory_holder.log_lde_factor;
    let mut tree_caps = Box::new(None);
    let dst_tree_caps_accessor = UnsafeMutAccessor::new(tree_caps.as_mut());
    let transform_tree_caps_fn = move || unsafe {
        let tree_caps = get_tree_caps_for_accessors(&src_tree_cap_accessors, log_lde);
        assert!(dst_tree_caps_accessor
            .get_mut()
            .replace(tree_caps)
            .is_none());
    };
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
