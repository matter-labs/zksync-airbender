use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::ProverContext;
use crate::primitives::transfer::Transfer;
use crate::witness::trace_delegation::{DelegationTraceDevice, DelegationTraceHost};
use crate::witness::trace_unrolled::{
    InitsAndTeardownsTraceDevice, InitsAndTeardownsTraceHost, UnrolledMemoryTraceDevice,
    UnrolledMemoryTraceHost, UnrolledNonMemoryTraceDevice, UnrolledNonMemoryTraceHost,
    UnrolledUnifiedTraceDevice, UnrolledUnifiedTraceHost,
};
use era_cudart::result::CudaResult;
use fft::GoodAllocator;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;

pub(crate) enum DelegationTracingDataDevice {
    BigIntWithControl(DelegationTraceDevice<BigintDelegationWitness>),
    Blake2WithCompression(DelegationTraceDevice<Blake2sRoundFunctionDelegationWitness>),
    KeccakSpecial5(DelegationTraceDevice<KeccakSpecial5DelegationWitness>),
}

pub(crate) enum UnrolledTracingDataDevice {
    Memory(UnrolledMemoryTraceDevice),
    NonMemory(UnrolledNonMemoryTraceDevice),
    Unified(UnrolledUnifiedTraceDevice),
}

pub(crate) enum TracingDataDevice {
    Delegation(DelegationTracingDataDevice),
    Unrolled(UnrolledTracingDataDevice),
}

#[derive(Clone)]
pub(crate) enum DelegationTracingDataHost<A: GoodAllocator> {
    BigIntWithControl(DelegationTraceHost<BigintDelegationWitness, A>),
    Blake2WithCompression(DelegationTraceHost<Blake2sRoundFunctionDelegationWitness, A>),
    KeccakSpecial5(DelegationTraceHost<KeccakSpecial5DelegationWitness, A>),
}

impl<A: GoodAllocator> DelegationTracingDataHost<A> {
    pub fn into_allocators(self) -> Vec<A> {
        match self {
            DelegationTracingDataHost::BigIntWithControl(trace) => trace.into_allocators(),
            DelegationTracingDataHost::Blake2WithCompression(trace) => trace.into_allocators(),
            DelegationTracingDataHost::KeccakSpecial5(trace) => trace.into_allocators(),
        }
    }
}

pub(crate) trait DelegationTracingDataHostSource: Sized {
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

impl DelegationTracingDataHostSource for KeccakSpecial5DelegationWitness {
    fn get<A: GoodAllocator>(trace: DelegationTraceHost<Self, A>) -> DelegationTracingDataHost<A> {
        DelegationTracingDataHost::KeccakSpecial5(trace)
    }
}

#[derive(Clone)]
pub(crate) enum UnrolledTracingDataHost<A: GoodAllocator> {
    Memory(UnrolledMemoryTraceHost<A>),
    NonMemory(UnrolledNonMemoryTraceHost<A>),
    Unified(UnrolledUnifiedTraceHost<A>),
}

impl<A: GoodAllocator> UnrolledTracingDataHost<A> {
    pub fn into_allocators(self) -> Vec<A> {
        match self {
            UnrolledTracingDataHost::Memory(trace) => trace.into_allocators(),
            UnrolledTracingDataHost::NonMemory(trace) => trace.into_allocators(),
            UnrolledTracingDataHost::Unified(trace) => trace.into_allocators(),
        }
    }
}

#[derive(Clone)]
pub(crate) enum TracingDataHost<A: GoodAllocator> {
    Delegation(DelegationTracingDataHost<A>),
    Unrolled(UnrolledTracingDataHost<A>),
}

impl<A: GoodAllocator> TracingDataHost<A> {
    pub fn into_allocators(self) -> Vec<A> {
        match self {
            TracingDataHost::Delegation(trace) => trace.into_allocators(),
            TracingDataHost::Unrolled(trace) => trace.into_allocators(),
        }
    }
}

pub(crate) struct TracingDataTransfer<'a, A: GoodAllocator> {
    pub data_host: TracingDataHost<A>,
    pub data_device: TracingDataDevice,
    pub transfer: Transfer<'a>,
}

impl<'a, A: GoodAllocator + 'a> TracingDataTransfer<'a, A> {
    pub fn new(data_host: TracingDataHost<A>, context: &ProverContext) -> CudaResult<Self> {
        let data_device = match &data_host {
            TracingDataHost::Delegation(delegation) => {
                let data = match delegation {
                    DelegationTracingDataHost::BigIntWithControl(data) => {
                        let tracing_data = context.alloc(data.len(), AllocationPlacement::Top)?;
                        let trace = DelegationTraceDevice { tracing_data };
                        DelegationTracingDataDevice::BigIntWithControl(trace)
                    }
                    DelegationTracingDataHost::Blake2WithCompression(data) => {
                        let tracing_data = context.alloc(data.len(), AllocationPlacement::Top)?;
                        let trace = DelegationTraceDevice { tracing_data };
                        DelegationTracingDataDevice::Blake2WithCompression(trace)
                    }
                    DelegationTracingDataHost::KeccakSpecial5(data) => {
                        let tracing_data = context.alloc(data.len(), AllocationPlacement::Top)?;
                        let trace = DelegationTraceDevice { tracing_data };
                        DelegationTracingDataDevice::KeccakSpecial5(trace)
                    }
                };
                TracingDataDevice::Delegation(data)
            }
            TracingDataHost::Unrolled(unrolled) => match unrolled {
                UnrolledTracingDataHost::Memory(trace) => {
                    let tracing_data = context.alloc(trace.len(), AllocationPlacement::Top)?;
                    let data = UnrolledMemoryTraceDevice { tracing_data };
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Memory(data))
                }
                UnrolledTracingDataHost::NonMemory(trace) => {
                    let tracing_data = context.alloc(trace.len(), AllocationPlacement::Top)?;
                    let data = UnrolledNonMemoryTraceDevice { tracing_data };
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(data))
                }
                UnrolledTracingDataHost::Unified(trace) => {
                    let tracing_data = context.alloc(trace.len(), AllocationPlacement::Top)?;
                    let trace = UnrolledUnifiedTraceDevice { tracing_data };
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Unified(trace))
                }
            },
        };
        let transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        Ok(Self {
            data_host,
            data_device,
            transfer,
        })
    }

    pub fn schedule_transfer(&mut self, context: &ProverContext) -> CudaResult<()> {
        match &self.data_host {
            TracingDataHost::Delegation(delegation) => match delegation {
                DelegationTracingDataHost::BigIntWithControl(h_trace) => {
                    match &mut self.data_device {
                        TracingDataDevice::Delegation(
                            DelegationTracingDataDevice::BigIntWithControl(d_trace),
                        ) => self.transfer.schedule_multiple(
                            &h_trace.chunks,
                            &mut d_trace.tracing_data,
                            context,
                        )?,
                        _ => panic!("expected bigint with control trace"),
                    }
                }
                DelegationTracingDataHost::Blake2WithCompression(h_trace) => {
                    match &mut self.data_device {
                        TracingDataDevice::Delegation(
                            DelegationTracingDataDevice::Blake2WithCompression(d_trace),
                        ) => self.transfer.schedule_multiple(
                            &h_trace.chunks,
                            &mut d_trace.tracing_data,
                            context,
                        )?,
                        _ => panic!("expected blake2 with compression trace"),
                    }
                }
                DelegationTracingDataHost::KeccakSpecial5(h_trace) => match &mut self.data_device {
                    TracingDataDevice::Delegation(DelegationTracingDataDevice::KeccakSpecial5(
                        d_trace,
                    )) => self.transfer.schedule_multiple(
                        &h_trace.chunks,
                        &mut d_trace.tracing_data,
                        context,
                    )?,
                    _ => panic!("expected keccak special 5 trace"),
                },
            },
            TracingDataHost::Unrolled(unrolled) => match unrolled {
                UnrolledTracingDataHost::Memory(h_trace) => match &mut self.data_device {
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Memory(d_trace)) => self
                        .transfer
                        .schedule_multiple(&h_trace.chunks, &mut d_trace.tracing_data, context)?,
                    _ => panic!("expected unrolled memory trace"),
                },
                UnrolledTracingDataHost::NonMemory(h_trace) => match &mut self.data_device {
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(d_trace)) => {
                        self.transfer.schedule_multiple(
                            &h_trace.chunks,
                            &mut d_trace.tracing_data,
                            context,
                        )?
                    }
                    _ => panic!("expected unrolled non-memory trace"),
                },
                UnrolledTracingDataHost::Unified(h_trace) => match &mut self.data_device {
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Unified(d_trace)) => {
                        self.transfer.schedule_multiple(
                            &h_trace.chunks,
                            &mut d_trace.tracing_data,
                            context,
                        )?;
                    }
                    _ => panic!("expected unrolled unified trace"),
                },
            },
        }
        self.transfer.record_transferred(context)
    }

    pub(crate) fn into_host_keepalive(self) -> crate::primitives::callbacks::Callbacks<'a> {
        let Self {
            data_host: _,
            data_device: _,
            transfer,
        } = self;
        transfer.into_callbacks()
    }
}

pub(crate) struct InitsAndTeardownsTransfer<'a> {
    pub data_host: InitsAndTeardownsTraceHost,
    pub data_device: InitsAndTeardownsTraceDevice,
    pub transfer: Transfer<'a>,
}

impl<'a> InitsAndTeardownsTransfer<'a> {
    pub fn new(data_host: InitsAndTeardownsTraceHost, context: &ProverContext) -> CudaResult<Self> {
        let page_indices = context.alloc(data_host.page_indices.len(), AllocationPlacement::Top)?;
        let values_packed =
            context.alloc(data_host.values_packed.len(), AllocationPlacement::Top)?;
        let timestamps_packed =
            context.alloc(data_host.timestamps_packed.len(), AllocationPlacement::Top)?;
        let data_device = InitsAndTeardownsTraceDevice {
            page_indices,
            values_packed,
            timestamps_packed,
        };
        let transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        Ok(Self {
            data_host,
            data_device,
            transfer,
        })
    }

    pub fn schedule_transfer(&mut self, context: &ProverContext) -> CudaResult<()> {
        self.transfer.schedule_multiple(
            &self.data_host.page_indices.chunks,
            &mut self.data_device.page_indices,
            context,
        )?;
        self.transfer.schedule_multiple(
            &self.data_host.values_packed.chunks,
            &mut self.data_device.values_packed,
            context,
        )?;
        self.transfer.schedule_multiple(
            &self.data_host.timestamps_packed.chunks,
            &mut self.data_device.timestamps_packed,
            context,
        )?;
        self.transfer.record_transferred(context)
    }

    pub(crate) fn into_host_keepalive(self) -> crate::primitives::callbacks::Callbacks<'a> {
        let Self {
            data_host: _,
            data_device: _,
            transfer,
        } = self;
        transfer.into_callbacks()
    }
}
