use super::PtrRange;
use crate::messages::{TracingData, WorkerResult};
use crate::workers::cancellation::{CancellationToken, Pool};
use crossbeam_channel::{Receiver, Sender};
use execution_prover_model::allocator::HostTraceAllocator;
use execution_prover_model::circuit_type::CircuitType;
use execution_prover_model::trace::ChunkedTraceHolder;
use execution_prover_model::trace::{
    DelegationTracingDataHostSource, TracingDataHost, UnrolledTracingDataHost,
};
use itertools::Itertools;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};
use std::cmp::min;
use std::collections::{BTreeSet, VecDeque};
use std::mem::take;
use std::sync::Arc;

pub(crate) trait TracingDataProducerType: Sized {
    fn produce_tracing_data<A: HostTraceAllocator>(
        holder: ChunkedTraceHolder<Self, A>,
    ) -> TracingDataHost<A>;
}

// `DelegationTracingDataHostSource` is foreign (defined in
// `execution_prover_model`), so a blanket `impl<T: DelegationTracingDataHostSource>`
// is not coherent here — the compiler cannot prove the unrolled types below
// don't also implement it. Enumerate the four delegation witness types instead
// (the trait has exactly these four impls upstream).
macro_rules! impl_delegation_tracing_data_producer {
    ($($ty:ty),+ $(,)?) => {$(
        impl TracingDataProducerType for $ty {
            fn produce_tracing_data<A: HostTraceAllocator>(
                holder: ChunkedTraceHolder<Self, A>,
            ) -> TracingDataHost<A> {
                TracingDataHost::Delegation(<Self as DelegationTracingDataHostSource>::get(holder))
            }
        }
    )+};
}
impl_delegation_tracing_data_producer!(
    BigintDelegationWitness,
    Blake2sRoundFunctionDelegationWitness,
    Blake2sGFunctionDelegationWitness,
    KeccakSpecial5DelegationWitness,
);

impl TracingDataProducerType for MemoryOpcodeTracingDataWithTimestamp {
    fn produce_tracing_data<A: HostTraceAllocator>(
        holder: ChunkedTraceHolder<Self, A>,
    ) -> TracingDataHost<A> {
        TracingDataHost::Unrolled(UnrolledTracingDataHost::Memory(holder))
    }
}

impl TracingDataProducerType for NonMemoryOpcodeTracingDataWithTimestamp {
    fn produce_tracing_data<A: HostTraceAllocator>(
        holder: ChunkedTraceHolder<Self, A>,
    ) -> TracingDataHost<A> {
        TracingDataHost::Unrolled(UnrolledTracingDataHost::NonMemory(holder))
    }
}

impl TracingDataProducerType for UnifiedOpcodeTracingDataWithTimestamp {
    fn produce_tracing_data<A: HostTraceAllocator>(
        holder: ChunkedTraceHolder<Self, A>,
    ) -> TracingDataHost<A> {
        TracingDataHost::Unrolled(UnrolledTracingDataHost::Unified(holder))
    }
}

/// Per-circuit trace-row count used to slice cycle counters into circuit-sized
/// partitions. The full `2^N` rows are usable (no reserved padding row).
fn cycles_per_circuit_for(circuit_type: CircuitType) -> usize {
    circuit_type.get_domain_size()
}

pub(crate) struct TracingDataProducer<T: TracingDataProducerType, A: HostTraceAllocator> {
    circuit_type: CircuitType,
    cycles_per_circuit: usize,
    free_allocators: Receiver<A>,
    results: Sender<WorkerResult<A>>,
    cancellation: CancellationToken,
    current_circuit_index: usize,
    chunks: VecDeque<Arc<Vec<T, A>>>,
    participating_snapshot_indexes: BTreeSet<usize>,
}

impl<T: TracingDataProducerType, A: HostTraceAllocator> TracingDataProducer<T, A> {
    pub fn new(
        circuit_type: CircuitType,
        free_allocators: Receiver<A>,
        results: Sender<WorkerResult<A>>,
        cancellation: CancellationToken,
    ) -> Self {
        Self {
            circuit_type,
            cycles_per_circuit: cycles_per_circuit_for(circuit_type),
            free_allocators,
            results,
            cancellation,
            current_circuit_index: 0,
            chunks: VecDeque::new(),
            participating_snapshot_indexes: BTreeSet::new(),
        }
    }

    /// `None` once cancellation (or a closed channel) has ended production.
    ///
    /// This runs underneath the JIT's non-unwinding `receive_trace` callback,
    /// so giving up has to travel back out as a value: a panic here would abort
    /// the process instead of letting the orchestrator join its workers.
    pub fn process_snapshot(
        &mut self,
        snapshot_index: usize,
        mut start: usize,
        end: usize,
        trace_ranges: &mut VecDeque<PtrRange<T, A>>,
    ) -> Option<()> {
        while start != end {
            let cycles_per_circuit = self.cycles_per_circuit;
            let next_circuit_boundary = (start + 1).next_multiple_of(cycles_per_circuit);
            let next_circuit_index = next_circuit_boundary / cycles_per_circuit;
            assert_eq!(next_circuit_index, self.current_circuit_index + 1);
            if self.chunks.back().is_none_or(|v| v.len() == v.capacity()) {
                let allocator = self
                    .cancellation
                    .recv(Pool::TraceBlock, &self.free_allocators)?;
                let capacity = allocator.capacity() / size_of::<T>();
                let chunk = Arc::new(Vec::with_capacity_in(capacity, allocator));
                self.chunks.push_back(chunk)
            };
            let chunk = self.chunks.back_mut().unwrap();
            // SAFETY: prior `Arc::clone`s of `chunk` live inside `PtrRange`s
            // queued for the tracer/consumer threads, but those threads run
            // strictly after this producer finishes the snapshot, so no
            // concurrent access to the `Vec` exists right now.
            let chunk_mut = unsafe { Arc::get_mut_unchecked(chunk) };
            let spare_capacity = chunk_mut.spare_capacity_mut();
            let end = min(end, next_circuit_boundary);
            let diff = min(spare_capacity.len(), end - start);
            assert_ne!(diff, 0);
            // SAFETY: `start_ptr..end_ptr` is `diff` elements inside
            // `spare_capacity` (bounded by `diff <= spare_capacity.len()`).
            // `set_len` extends the Vec over memory the tracer fills via the
            // raw `PtrRange` before any reader sees the chunk via Vec
            // accessors; `T: Copy + 'static` so no `Drop` runs on slots that
            // remain unwritten until then.
            let ptr_range = unsafe {
                let start_ptr = spare_capacity.as_mut_ptr() as *mut T;
                let end_ptr = start_ptr.add(diff);
                chunk_mut.set_len(chunk_mut.len() + diff);
                PtrRange {
                    start: start_ptr,
                    end: end_ptr,
                    _chunk: Some(chunk.clone()),
                }
            };
            trace_ranges.push_back(ptr_range);
            self.participating_snapshot_indexes.insert(snapshot_index);
            start += diff;
            if start.is_multiple_of(cycles_per_circuit) {
                assert_eq!(start / cycles_per_circuit, next_circuit_index);
                self.produce_and_send_result()?;
                self.current_circuit_index = next_circuit_index;
            }
        }
        Some(())
    }

    fn produce_and_send_result(&mut self) -> Option<()> {
        let chunks = self.chunks.drain(..).collect_vec();
        let holder = ChunkedTraceHolder { chunks };
        let tracing_data = T::produce_tracing_data(holder);
        let participating_snapshot_indexes = take(&mut self.participating_snapshot_indexes);
        let data = TracingData {
            circuit_type: self.circuit_type,
            sequence_id: self.current_circuit_index,
            tracing_data,
            participating_snapshot_indexes,
        };
        let result = WorkerResult::TracingData(data);
        self.results.send(result).ok()
    }

    pub fn finalize(mut self) {
        if !self.chunks.is_empty() {
            let _ = self.produce_and_send_result();
        }
    }
}
