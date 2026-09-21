use super::*;
use crate::messages::{
    MemoryCommitmentRequest, SetupInitializationRequest, WorkRequest, WorkResult, WorkerResult,
};
use crate::setup::build_inits_and_teardowns_setup;
use crate::test_support::{FakeBackend, FakeBackendConfiguration, FakeTraceAllocator};
use crate::upstream::SecurityLevel;
use execution_prover_model::circuit_type::UnrolledCircuitType;
use execution_prover_model::trace::{ChunkedTraceHolder, TracingDataHost, UnrolledTracingDataHost};
use riscv_transpiler::witness::NonMemoryOpcodeTracingDataWithTimestamp;

fn backend() -> FakeBackend {
    let config = ExecutionProverConfiguration::<FakeBackendConfiguration>::default();
    config.validate().unwrap();
    FakeBackend::initialize(&config, Arc::new(Worker::new_with_num_threads(1))).unwrap()
}

/// One trace holder with `chunks` blocks, plus the address of each chunk.
///
/// The addresses are read with `Arc::as_ptr`, which does not take a strong
/// reference, so the uniqueness `into_allocators` requires still holds. They
/// let completion be checked for the *same* buffers: comparing counts alone
/// would accept a backend that dropped the inputs and returned fresh ones.
fn tracing_data(chunks: usize) -> (TracingDataHost<FakeTraceAllocator>, Vec<usize>) {
    let chunks: Vec<_> = (0..chunks)
        .map(|_| {
            Arc::new(Vec::<NonMemoryOpcodeTracingDataWithTimestamp, _>::new_in(
                FakeTraceAllocator,
            ))
        })
        .collect();
    let addresses = chunks.iter().map(|c| Arc::as_ptr(c) as usize).collect();
    let holder =
        TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(ChunkedTraceHolder {
            chunks,
        }));
    (holder, addresses)
}

/// Chunk addresses of a returned holder, read the same way.
fn chunk_addresses(data: &TracingDataHost<FakeTraceAllocator>) -> Vec<usize> {
    match data {
        TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(holder)) => holder
            .chunks
            .iter()
            .map(|c| Arc::as_ptr(c) as usize)
            .collect(),
        _ => panic!("expected an unrolled non-memory trace"),
    }
}

#[test]
fn cpu_submitted_work_completes_with_the_same_identity() {
    let backend = backend();
    let circuit_type = CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns);
    let batch_id = 7;
    let (submitted_trace, submitted_addresses) = tracing_data(2);
    let (request_sender, request_receiver) = crossbeam_channel::unbounded();
    let (result_sender, result_receiver) = crossbeam_channel::unbounded();

    request_sender
        .send(WorkRequest::SetupInitialization(
            SetupInitializationRequest {
                batch_id,
                circuit_type,
                sequence_id: 3,
                precomputations: backend
                    .prepare(
                        circuit_type,
                        build_inits_and_teardowns_setup(&Worker::new_with_num_threads(1)),
                        SecurityLevel::Sec100,
                    )
                    .unwrap(),
                security_level: SecurityLevel::Sec100,
            },
        ))
        .unwrap();
    request_sender
        .send(WorkRequest::MemoryCommitment(MemoryCommitmentRequest {
            batch_id,
            circuit_type,
            sequence_id: 11,
            precomputations: backend
                .prepare(
                    circuit_type,
                    build_inits_and_teardowns_setup(&Worker::new_with_num_threads(1)),
                    SecurityLevel::Sec100,
                )
                .unwrap(),
            inits_and_teardowns: None,
            tracing_data: Some(submitted_trace),
            security_level: SecurityLevel::Sec100,
        }))
        .unwrap();
    // Closing the request channel is what retires the batch.
    drop(request_sender);

    backend.submit(WorkBatch {
        batch_id,
        receiver: request_receiver,
        sender: result_sender,
    });

    let results: Vec<_> = result_receiver.iter().collect();
    assert_eq!(results.len(), 2);

    let mut seen = Vec::new();
    for result in results {
        let WorkerResult::BackendWorkResult(result) = result else {
            panic!("expected backend work results only");
        };
        assert_eq!(result.batch_id(), batch_id);
        assert_eq!(result.circuit_type(), circuit_type);
        seen.push(result.sequence_id());

        if let WorkResult::MemoryCommitment(commitment) = result {
            // Trace ownership must come back in the completion, or the blocks
            // it holds can never return to the producer pool. The same buffers
            // must come back, not merely the same number of them.
            let returned = commitment
                .tracing_data
                .expect("memory commitment must return the trace it was given");
            assert_eq!(chunk_addresses(&returned), submitted_addresses);

            // And they must still be uniquely owned, or recycling panics.
            let allocators = returned.into_allocators();
            assert_eq!(allocators.len(), submitted_addresses.len());
        }
    }
    seen.sort();
    assert_eq!(seen, vec![3, 11]);
}

#[test]
fn cpu_initialization_error_keeps_the_backend_name_and_source() {
    let mut config = ExecutionProverConfiguration::<FakeBackendConfiguration>::default();
    config.backend.fail_initialization_with = Some("no device available");

    // Shared validation still passes; this is a backend resource failure.
    config.validate().unwrap();
    let error = FakeBackend::initialize(&config, Arc::new(Worker::new_with_num_threads(1)))
        .err()
        .expect("initialization must fail");

    match &error {
        crate::error::ExecutionProverError::BackendInitialization { backend, source } => {
            assert_eq!(*backend, FakeBackendConfiguration::BACKEND_NAME);
            assert_eq!(source.to_string(), "no device available");
        }
        other => panic!("expected a backend initialization error, got {other:?}"),
    }
    // The chain is reachable through `Error::source`, not only through Display.
    assert!(std::error::Error::source(&error).is_some());
    assert!(error.to_string().contains("fake"));
    assert!(error.to_string().contains("no device available"));
}

#[test]
fn cpu_backend_allocates_its_declared_storage_types() {
    let backend = backend();
    let config = ExecutionProverConfiguration::<FakeBackendConfiguration>::default();

    let allocator = backend
        .allocate_trace_block(config.host_allocator_backing_allocation_size)
        .unwrap();
    assert_eq!(
        HostTraceAllocator::capacity(&allocator),
        config.host_allocator_backing_allocation_size
    );

    let memory = backend.allocate_memory(config.ram_config).unwrap();
    assert_eq!(memory.ram_size(), config.ram_config.ram_size());

    let snapshot = backend.allocate_snapshot().unwrap();
    assert_eq!(snapshot.len, 0);

    assert_eq!(backend.extra_trace_blocks(), 0);
}
