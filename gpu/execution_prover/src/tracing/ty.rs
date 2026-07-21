use super::{
    DataTraceRanges, SplitDataTraceRanges, SplitTracer, SplitTracingDataProducers, Tracer,
    TracingDataProducers, UnifiedDataTraceRanges, UnifiedTracer, UnifiedTracingDataProducers,
};
use riscv_transpiler::jit::MachineCounters;
use riscv_transpiler::vm::{
    Counters, DelegationsAndFamiliesCounters, DelegationsAndUnifiedCounters,
};

pub(crate) trait TracingType {
    const IS_SPLIT: bool;
    type Ranges: DataTraceRanges;
    type Producers: TracingDataProducers<Ranges = Self::Ranges>;
    type Tracer: Tracer<Ranges = Self::Ranges>;
    type Counters: Counters + From<MachineCounters>;
}

pub(crate) struct SplitTracingType;

impl TracingType for SplitTracingType {
    const IS_SPLIT: bool = true;
    type Ranges = SplitDataTraceRanges;
    type Producers = SplitTracingDataProducers;
    type Tracer = SplitTracer;
    type Counters = DelegationsAndFamiliesCounters;
}

pub(crate) struct UnifiedTracingType;

impl TracingType for UnifiedTracingType {
    const IS_SPLIT: bool = false;
    type Ranges = UnifiedDataTraceRanges;
    type Producers = UnifiedTracingDataProducers;
    type Tracer = UnifiedTracer;
    type Counters = DelegationsAndUnifiedCounters;
}
