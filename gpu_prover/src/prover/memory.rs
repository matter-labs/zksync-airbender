use super::callbacks::Callbacks;
use super::context::{ProverContext, UnsafeMutAccessor};
use super::trace_holder::{get_tree_caps, TraceHolder, TreesCacheMode};
use super::tracing_data::{
    DelegationTracingDataDevice, InitsAndTeardownsTransfer, TracingDataDevice, TracingDataTransfer,
    UnrolledTracingDataDevice,
};
use super::{device_tracing, BF};
use crate::circuit_type::{CircuitType, DelegationCircuitType, UnrolledCircuitType};
use crate::device_structures::DeviceMatrixMut;
use crate::witness::memory_delegation::generate_memory_values_delegation;
use crate::witness::memory_unrolled::{
    generate_memory_values_unrolled_inits_and_teardowns, generate_memory_values_unrolled_memory,
    generate_memory_values_unrolled_non_memory, generate_memory_values_unrolled_unified,
};
use crate::witness::trace_unrolled::ExecutorFamilyDecoderData;
use cs::one_row_compiler::CompiledCircuitArtifact;
use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use fft::GoodAllocator;
use prover::merkle_trees::MerkleTreeCapVarLength;
use std::assert_matches::assert_matches;

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

pub(crate) fn commit_memory<'a, A: GoodAllocator>(
    circuit_type: CircuitType,
    circuit: &CompiledCircuitArtifact<BF>,
    decoder_table: Option<&DeviceSlice<ExecutorFamilyDecoderData>>,
    inits_and_teardowns_transfer: Option<InitsAndTeardownsTransfer<'a, A>>,
    tracing_data_transfer: Option<TracingDataTransfer<'a, A>>,
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
    let mut callbacks = Callbacks::new();
    let inits_and_teardowns =
        if let Some(inits_and_teardowns_transfer) = inits_and_teardowns_transfer {
            assert_matches!(
                circuit_type,
                CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns)
                    | CircuitType::Unrolled(UnrolledCircuitType::Unified)
            );
            let InitsAndTeardownsTransfer {
                data_host: _,
                data_device,
                transfer,
            } = inits_and_teardowns_transfer;
            transfer.ensure_transferred(context)?;
            callbacks.extend(transfer.callbacks);
            Some(data_device)
        } else {
            assert_ne!(
                circuit_type,
                CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns)
            );
            None
        };
    let trace = if let Some(tracing_data_transfer) = tracing_data_transfer {
        assert_ne!(
            circuit_type,
            CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns)
        );
        let TracingDataTransfer {
            data_host: _,
            data_device,
            transfer,
        } = tracing_data_transfer;
        transfer.ensure_transferred(context)?;
        callbacks.extend(transfer.callbacks);
        Some(data_device)
    } else {
        assert_eq!(
            circuit_type,
            CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns)
        );
        None
    };
    let range = device_tracing::Range::new("commit_memory")?;
    let stream = context.get_exec_stream();
    range.start(stream)?;
    let mut evaluations = memory_holder.get_uninit_evaluations_mut();
    let memory = &mut DeviceMatrixMut::new(&mut evaluations, trace_len);
    match circuit_type {
        CircuitType::Delegation(circuit_type) => {
            match trace.unwrap() {
                TracingDataDevice::Delegation(delegation) => match delegation {
                    DelegationTracingDataDevice::BigIntWithControl(trace) => {
                        assert_eq!(circuit_type, DelegationCircuitType::BigIntWithControl);
                        generate_memory_values_delegation(memory_subtree, &trace, memory, stream)?;
                    }
                    DelegationTracingDataDevice::Blake2WithCompression(trace) => {
                        assert_eq!(circuit_type, DelegationCircuitType::Blake2WithCompression);
                        generate_memory_values_delegation(memory_subtree, &trace, memory, stream)?;
                    }
                    DelegationTracingDataDevice::KeccakSpecial5(trace) => {
                        assert_eq!(circuit_type, DelegationCircuitType::KeccakSpecial5);
                        generate_memory_values_delegation(memory_subtree, &trace, memory, stream)?;
                    }
                },
                _ => panic!("expected delegation tracing data"),
            };
        }
        CircuitType::Unrolled(circuit_type) => match circuit_type {
            UnrolledCircuitType::InitsAndTeardowns => {
                let inits_and_teardowns = inits_and_teardowns.unwrap();
                generate_memory_values_unrolled_inits_and_teardowns(
                    memory_subtree,
                    &inits_and_teardowns,
                    memory,
                    stream,
                )?;
            }
            _ => {
                match trace.unwrap() {
                    TracingDataDevice::Unrolled(unrolled) => match unrolled {
                        UnrolledTracingDataDevice::Memory(trace) => {
                            let circuit_type = circuit_type.as_memory().unwrap();
                            generate_memory_values_unrolled_memory(
                                circuit_type,
                                memory_subtree,
                                decoder_table.unwrap(),
                                &trace,
                                memory,
                                stream,
                            )?;
                        }
                        UnrolledTracingDataDevice::NonMemory(trace) => {
                            let circuit_type = circuit_type.as_non_memory().unwrap();
                            generate_memory_values_unrolled_non_memory(
                                circuit_type,
                                memory_subtree,
                                decoder_table.unwrap(),
                                &trace,
                                memory,
                                stream,
                            )?;
                        }
                        UnrolledTracingDataDevice::Unified(trace) => {
                            assert_eq!(circuit_type, UnrolledCircuitType::Unified);
                            generate_memory_values_unrolled_unified(
                                memory_subtree,
                                decoder_table.unwrap(),
                                &inits_and_teardowns,
                                &trace,
                                memory,
                                stream,
                            )?;
                        }
                    },
                    _ => panic!("expected unrolled tracing data"),
                };
            }
        },
    }
    drop(evaluations);
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
