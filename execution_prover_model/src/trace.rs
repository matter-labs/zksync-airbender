//! Host-side trace containers: the shapes a circuit's witness rows take
//! between the replayer that fills them and the backend that consumes them.
//! Rows are the upstream `riscv_transpiler::witness` types unchanged; this
//! module owns the chunked, allocator-parameterised container around them and
//! the per-circuit-kind enum the orchestrator routes on. The matching device
//! allocations and transfers stay in `gpu_trace`.

use crate::upstream::TimestampScalar;
use fft::GoodAllocator;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;
use riscv_transpiler::witness::{
    MemoryOpcodeTracingDataWithTimestamp, NonMemoryOpcodeTracingDataWithTimestamp,
    UnifiedOpcodeTracingDataWithTimestamp,
};
use std::sync::Arc;

/// Page size for the inits-and-teardowns trace, in `log2(words)`.
///
/// Each touched page carries `1 << PAGE_SIZE_LOG2` `u32` values plus
/// `1 << PAGE_SIZE_LOG2` timestamps. Producer and consumer both rely on this
/// value as the contract.
pub const PAGE_SIZE_LOG2: u32 = 10;

/// One circuit's rows, held as a sequence of allocator-backed chunks.
///
/// A chunk is exactly one finite trace block, so the chunk list doubles as the
/// credit list: [`ChunkedTraceHolder::into_allocators`] is how blocks are
/// returned to the producer pool once the consumer is done, and it requires
/// unique `Arc` ownership precisely so a reader that outlived the trace is a
/// loud panic rather than a silently leaked credit.
#[derive(Clone)]
pub struct ChunkedTraceHolder<T, A: GoodAllocator> {
    pub chunks: Vec<Arc<Vec<T, A>>>,
}

impl<T, A: GoodAllocator> ChunkedTraceHolder<T, A> {
    pub fn len(&self) -> usize {
        self.chunks.iter().map(|chunk| chunk.len()).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Trace blocks this holder owns: what `into_allocators` would return,
    /// without consuming the holder or asserting unique ownership. Charges a
    /// live cache entry against a pool quota.
    pub fn block_count(&self) -> usize {
        self.chunks.len()
    }

    pub fn into_allocators(self) -> Vec<A> {
        self.chunks
            .into_iter()
            .map(|c| {
                Arc::into_inner(c)
                    .expect(
                        "ChunkedTraceHolder::into_allocators requires unique Arc ownership per chunk",
                    )
                    .allocator()
                    .clone()
            })
            .collect()
    }
}

pub type DelegationTraceHost<T, A> = ChunkedTraceHolder<T, A>;
pub type UnrolledMemoryTraceHost<A> = ChunkedTraceHolder<MemoryOpcodeTracingDataWithTimestamp, A>;
pub type UnrolledNonMemoryTraceHost<A> =
    ChunkedTraceHolder<NonMemoryOpcodeTracingDataWithTimestamp, A>;
pub type UnrolledUnifiedTraceHost<A> = ChunkedTraceHolder<UnifiedOpcodeTracingDataWithTimestamp, A>;

/// Chunked, sparse inits-and-teardowns trace.
///
/// The three series stay in lockstep at page granularity: chunks of
/// `values_packed` and `timestamps_packed` are page-aligned (length is a
/// multiple of `1 << PAGE_SIZE_LOG2`); chunks of `page_indices` carry one entry
/// per page. Per-field chunk lengths sum to the same total page count.
///
/// `page_indices` are **local** to this instance: the high `log2(num_sets)` bits
/// select the set, the low bits the page within that set's window. `top_bits`
/// maps each set back to the global window it holds — set `i` covers global
/// words `[top_bits[i] << trace_len_log2, (top_bits[i] + 1) << trace_len_log2)`.
#[derive(Clone)]
pub struct InitsAndTeardownsTraceHost<A: GoodAllocator> {
    pub page_indices: ChunkedTraceHolder<u32, A>,
    pub values_packed: ChunkedTraceHolder<u32, A>,
    pub timestamps_packed: ChunkedTraceHolder<TimestampScalar, A>,
    /// One global window index per set, ascending.
    pub top_bits: Vec<u32>,
}

impl<A: GoodAllocator> InitsAndTeardownsTraceHost<A> {
    /// Trace blocks this instance owns, across all three series.
    pub fn block_count(&self) -> usize {
        self.page_indices.block_count()
            + self.values_packed.block_count()
            + self.timestamps_packed.block_count()
    }

    pub fn into_allocators(self) -> Vec<A> {
        let Self {
            page_indices,
            values_packed,
            timestamps_packed,
            top_bits: _,
        } = self;
        let mut allocators = page_indices.into_allocators();
        allocators.extend(values_packed.into_allocators());
        allocators.extend(timestamps_packed.into_allocators());
        allocators
    }
}

#[derive(Clone)]
pub enum DelegationTracingDataHost<A: GoodAllocator> {
    BigIntWithControl(DelegationTraceHost<BigintDelegationWitness, A>),
    Blake2WithCompression(DelegationTraceHost<Blake2sRoundFunctionDelegationWitness, A>),
    Blake2GFunction(DelegationTraceHost<Blake2sGFunctionDelegationWitness, A>),
    KeccakSpecial5(DelegationTraceHost<KeccakSpecial5DelegationWitness, A>),
}

impl<A: GoodAllocator> DelegationTracingDataHost<A> {
    pub fn block_count(&self) -> usize {
        match self {
            DelegationTracingDataHost::BigIntWithControl(trace) => trace.block_count(),
            DelegationTracingDataHost::Blake2WithCompression(trace) => trace.block_count(),
            DelegationTracingDataHost::Blake2GFunction(trace) => trace.block_count(),
            DelegationTracingDataHost::KeccakSpecial5(trace) => trace.block_count(),
        }
    }

    pub fn into_allocators(self) -> Vec<A> {
        match self {
            DelegationTracingDataHost::BigIntWithControl(trace) => trace.into_allocators(),
            DelegationTracingDataHost::Blake2WithCompression(trace) => trace.into_allocators(),
            DelegationTracingDataHost::Blake2GFunction(trace) => trace.into_allocators(),
            DelegationTracingDataHost::KeccakSpecial5(trace) => trace.into_allocators(),
        }
    }
}

pub trait DelegationTracingDataHostSource: Sized {
    fn get<A: GoodAllocator>(trace: DelegationTraceHost<Self, A>) -> DelegationTracingDataHost<A>;
}

impl DelegationTracingDataHostSource for BigintDelegationWitness {
    fn get<A: GoodAllocator>(trace: DelegationTraceHost<Self, A>) -> DelegationTracingDataHost<A> {
        DelegationTracingDataHost::BigIntWithControl(trace)
    }
}

impl DelegationTracingDataHostSource for Blake2sRoundFunctionDelegationWitness {
    fn get<A: GoodAllocator>(trace: DelegationTraceHost<Self, A>) -> DelegationTracingDataHost<A> {
        DelegationTracingDataHost::Blake2WithCompression(trace)
    }
}

impl DelegationTracingDataHostSource for Blake2sGFunctionDelegationWitness {
    fn get<A: GoodAllocator>(trace: DelegationTraceHost<Self, A>) -> DelegationTracingDataHost<A> {
        DelegationTracingDataHost::Blake2GFunction(trace)
    }
}

impl DelegationTracingDataHostSource for KeccakSpecial5DelegationWitness {
    fn get<A: GoodAllocator>(trace: DelegationTraceHost<Self, A>) -> DelegationTracingDataHost<A> {
        DelegationTracingDataHost::KeccakSpecial5(trace)
    }
}

#[derive(Clone)]
pub enum UnrolledTracingDataHost<A: GoodAllocator> {
    Memory(UnrolledMemoryTraceHost<A>),
    NonMemory(UnrolledNonMemoryTraceHost<A>),
    Unified(UnrolledUnifiedTraceHost<A>),
}

impl<A: GoodAllocator> UnrolledTracingDataHost<A> {
    pub fn block_count(&self) -> usize {
        match self {
            UnrolledTracingDataHost::Memory(trace) => trace.block_count(),
            UnrolledTracingDataHost::NonMemory(trace) => trace.block_count(),
            UnrolledTracingDataHost::Unified(trace) => trace.block_count(),
        }
    }

    pub fn into_allocators(self) -> Vec<A> {
        match self {
            UnrolledTracingDataHost::Memory(trace) => trace.into_allocators(),
            UnrolledTracingDataHost::NonMemory(trace) => trace.into_allocators(),
            UnrolledTracingDataHost::Unified(trace) => trace.into_allocators(),
        }
    }
}

#[derive(Clone)]
pub enum TracingDataHost<A: GoodAllocator> {
    Delegation(DelegationTracingDataHost<A>),
    Unrolled(UnrolledTracingDataHost<A>),
}

impl<A: GoodAllocator> TracingDataHost<A> {
    pub fn block_count(&self) -> usize {
        match self {
            TracingDataHost::Delegation(trace) => trace.block_count(),
            TracingDataHost::Unrolled(trace) => trace.block_count(),
        }
    }

    pub fn into_allocators(self) -> Vec<A> {
        match self {
            TracingDataHost::Delegation(trace) => trace.into_allocators(),
            TracingDataHost::Unrolled(trace) => trace.into_allocators(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::Global;

    #[test]
    #[should_panic(
        expected = "ChunkedTraceHolder::into_allocators requires unique Arc ownership per chunk"
    )]
    fn into_allocators_names_arc_uniqueness_invariant() {
        let chunk = Arc::new(Vec::<u8, Global>::new_in(Global));
        let holder = ChunkedTraceHolder {
            chunks: vec![Arc::clone(&chunk), chunk],
        };

        let _ = holder.into_allocators();
    }
}

/// Layout facts about one host trace series that a finite block must hold.
/// Producers carve a block into whole rows, and the inits-and-teardowns series
/// additionally into whole pages, so a block smaller than one aligned unit
/// cannot make progress at all; configuration validation walks
/// [`host_trace_row_layouts`] to reject one up front.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HostTraceRowLayout {
    /// Series name, used in configuration error messages.
    pub name: &'static str,
    /// `size_of` one element of the series.
    pub row_size: usize,
    /// Elements the producer rounds a chunk length down to. One for series with
    /// no page structure; `1 << PAGE_SIZE_LOG2` for the packed I&T series.
    pub alignment_in_items: usize,
}

impl HostTraceRowLayout {
    /// Smallest block, in bytes, that can hold one aligned unit of this series.
    pub const fn minimum_block_bytes(&self) -> usize {
        self.row_size * self.alignment_in_items
    }
}

/// Every host trace series a block may have to hold, with the sizes taken from
/// the types themselves rather than restated as literals.
pub fn host_trace_row_layouts() -> Vec<HostTraceRowLayout> {
    let page = 1usize << PAGE_SIZE_LOG2;
    vec![
        HostTraceRowLayout {
            name: "unrolled memory rows",
            row_size: size_of::<MemoryOpcodeTracingDataWithTimestamp>(),
            alignment_in_items: 1,
        },
        HostTraceRowLayout {
            name: "unrolled non-memory rows",
            row_size: size_of::<NonMemoryOpcodeTracingDataWithTimestamp>(),
            alignment_in_items: 1,
        },
        HostTraceRowLayout {
            name: "unified rows",
            row_size: size_of::<UnifiedOpcodeTracingDataWithTimestamp>(),
            alignment_in_items: 1,
        },
        HostTraceRowLayout {
            name: "bigint delegation rows",
            row_size: size_of::<BigintDelegationWitness>(),
            alignment_in_items: 1,
        },
        HostTraceRowLayout {
            name: "blake2 round-function delegation rows",
            row_size: size_of::<Blake2sRoundFunctionDelegationWitness>(),
            alignment_in_items: 1,
        },
        HostTraceRowLayout {
            name: "blake2 g-function delegation rows",
            row_size: size_of::<Blake2sGFunctionDelegationWitness>(),
            alignment_in_items: 1,
        },
        HostTraceRowLayout {
            name: "keccak special5 delegation rows",
            row_size: size_of::<KeccakSpecial5DelegationWitness>(),
            alignment_in_items: 1,
        },
        HostTraceRowLayout {
            name: "inits-and-teardowns page indices",
            row_size: size_of::<u32>(),
            alignment_in_items: 1,
        },
        HostTraceRowLayout {
            name: "inits-and-teardowns packed values",
            row_size: size_of::<u32>(),
            alignment_in_items: page,
        },
        HostTraceRowLayout {
            name: "inits-and-teardowns packed timestamps",
            row_size: size_of::<TimestampScalar>(),
            alignment_in_items: page,
        },
    ]
}
