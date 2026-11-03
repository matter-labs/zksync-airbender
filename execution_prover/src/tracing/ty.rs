use super::{
    DataTraceRanges, SplitDataTraceRanges, SplitTracer, SplitTracingDataProducers, Tracer,
    TracingDataProducers, UnifiedDataTraceRanges, UnifiedTracer, UnifiedTracingDataProducers,
};
use execution_prover_model::allocator::HostTraceAllocator;
use riscv_transpiler::jit::MachineCounters;
use riscv_transpiler::vm::{
    Counters, DelegationsAndFamiliesCounters, DelegationsAndUnifiedCounters,
};

pub(crate) trait TracingType<A: HostTraceAllocator> {
    const IS_SPLIT: bool;
    type Ranges: DataTraceRanges;
    type Producers: TracingDataProducers<A, Ranges = Self::Ranges>;
    type Tracer: Tracer<A, Ranges = Self::Ranges>;
    type Counters: Counters + From<MachineCounters>;
}

pub(crate) struct SplitTracingType;

impl<A: HostTraceAllocator> TracingType<A> for SplitTracingType {
    const IS_SPLIT: bool = true;
    type Ranges = SplitDataTraceRanges<A>;
    type Producers = SplitTracingDataProducers<A>;
    type Tracer = SplitTracer<A>;
    type Counters = DelegationsAndFamiliesCounters;
}

pub(crate) struct UnifiedTracingType;

impl<A: HostTraceAllocator> TracingType<A> for UnifiedTracingType {
    const IS_SPLIT: bool = false;
    type Ranges = UnifiedDataTraceRanges<A>;
    type Producers = UnifiedTracingDataProducers<A>;
    type Tracer = UnifiedTracer<A>;
    type Counters = DelegationsAndUnifiedCounters;
}
