use crate::witness::trace_delegation::DelegationTraceDevice;
use crate::witness::trace_unrolled::{
    InitsAndTeardownsTraceDevice, InitsAndTeardownsTraceHost, UnrolledMemoryTraceDevice,
    UnrolledNonMemoryTraceDevice, UnrolledUnifiedTraceDevice, PAGE_SIZE_LOG2,
};
use era_cudart::result::CudaResult;
use fft::GoodAllocator;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_prover_context::transfer::Transfer;
use gpu_prover_context::ProverContext;
use riscv_transpiler::witness::delegation::bigint::BigintDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_g_function::Blake2sGFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;
use riscv_transpiler::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;

pub use execution_prover_model::trace::{
    DelegationTracingDataHost, DelegationTracingDataHostSource, TracingDataHost,
    UnrolledTracingDataHost,
};

// test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
#[doc(hidden)]
pub enum DelegationTracingDataDevice {
    BigIntWithControl(DelegationTraceDevice<BigintDelegationWitness>),
    Blake2WithCompression(DelegationTraceDevice<Blake2sRoundFunctionDelegationWitness>),
    Blake2GFunction(DelegationTraceDevice<Blake2sGFunctionDelegationWitness>),
    KeccakSpecial5(DelegationTraceDevice<KeccakSpecial5DelegationWitness>),
}

// test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
#[doc(hidden)]
pub enum UnrolledTracingDataDevice {
    Memory(UnrolledMemoryTraceDevice),
    NonMemory(UnrolledNonMemoryTraceDevice),
    Unified(UnrolledUnifiedTraceDevice),
}

// test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
#[doc(hidden)]
pub enum TracingDataDevice {
    Delegation(DelegationTracingDataDevice),
    Unrolled(UnrolledTracingDataDevice),
}

pub struct TracingDataTransfer<'a, A: GoodAllocator> {
    pub data_host: TracingDataHost<A>,
    // pub: apex production (`prover::gkr::stage1`) reads the device trace across the split.
    pub data_device: TracingDataDevice,
    _marker: std::marker::PhantomData<&'a ()>,
}

impl<'a, A: GoodAllocator + 'a> TracingDataTransfer<'a, A> {
    /// Allocates the circuit's full `capacity`, not the host length, so every
    /// instance of a circuit allocates alike.
    pub fn new(
        data_host: TracingDataHost<A>,
        capacity: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let data_device = match &data_host {
            TracingDataHost::Delegation(delegation) => {
                let data = match delegation {
                    DelegationTracingDataHost::BigIntWithControl(data) => {
                        let tracing_data = alloc_input(data.len(), capacity, context)?;
                        let trace = DelegationTraceDevice { tracing_data };
                        DelegationTracingDataDevice::BigIntWithControl(trace)
                    }
                    DelegationTracingDataHost::Blake2WithCompression(data) => {
                        let tracing_data = alloc_input(data.len(), capacity, context)?;
                        let trace = DelegationTraceDevice { tracing_data };
                        DelegationTracingDataDevice::Blake2WithCompression(trace)
                    }
                    DelegationTracingDataHost::Blake2GFunction(data) => {
                        let tracing_data = alloc_input(data.len(), capacity, context)?;
                        let trace = DelegationTraceDevice { tracing_data };
                        DelegationTracingDataDevice::Blake2GFunction(trace)
                    }
                    DelegationTracingDataHost::KeccakSpecial5(data) => {
                        let tracing_data = alloc_input(data.len(), capacity, context)?;
                        let trace = DelegationTraceDevice { tracing_data };
                        DelegationTracingDataDevice::KeccakSpecial5(trace)
                    }
                };
                TracingDataDevice::Delegation(data)
            }
            TracingDataHost::Unrolled(unrolled) => match unrolled {
                UnrolledTracingDataHost::Memory(trace) => {
                    let tracing_data = alloc_input(trace.len(), capacity, context)?;
                    let data = UnrolledMemoryTraceDevice { tracing_data };
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Memory(data))
                }
                UnrolledTracingDataHost::NonMemory(trace) => {
                    let tracing_data = alloc_input(trace.len(), capacity, context)?;
                    let data = UnrolledNonMemoryTraceDevice { tracing_data };
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(data))
                }
                UnrolledTracingDataHost::Unified(trace) => {
                    let tracing_data = alloc_input(trace.len(), capacity, context)?;
                    let trace = UnrolledUnifiedTraceDevice { tracing_data };
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Unified(trace))
                }
            },
        };
        Ok(Self {
            data_host,
            data_device,
            _marker: std::marker::PhantomData,
        })
    }

    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn schedule_transfer(
        &mut self,
        transfer: &mut Transfer<'a>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        match &self.data_host {
            TracingDataHost::Delegation(delegation) => match delegation {
                DelegationTracingDataHost::BigIntWithControl(h_trace) => {
                    match &mut self.data_device {
                        TracingDataDevice::Delegation(
                            DelegationTracingDataDevice::BigIntWithControl(d_trace),
                        ) => transfer.schedule_multiple(
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
                        ) => transfer.schedule_multiple(
                            &h_trace.chunks,
                            &mut d_trace.tracing_data,
                            context,
                        )?,
                        _ => panic!("expected blake2 with compression trace"),
                    }
                }
                DelegationTracingDataHost::Blake2GFunction(h_trace) => {
                    match &mut self.data_device {
                        TracingDataDevice::Delegation(
                            DelegationTracingDataDevice::Blake2GFunction(d_trace),
                        ) => transfer.schedule_multiple(
                            &h_trace.chunks,
                            &mut d_trace.tracing_data,
                            context,
                        )?,
                        _ => panic!("expected blake2 g function trace"),
                    }
                }
                DelegationTracingDataHost::KeccakSpecial5(h_trace) => match &mut self.data_device {
                    TracingDataDevice::Delegation(DelegationTracingDataDevice::KeccakSpecial5(
                        d_trace,
                    )) => transfer.schedule_multiple(
                        &h_trace.chunks,
                        &mut d_trace.tracing_data,
                        context,
                    )?,
                    _ => panic!("expected keccak special 5 trace"),
                },
            },
            TracingDataHost::Unrolled(unrolled) => match unrolled {
                UnrolledTracingDataHost::Memory(h_trace) => match &mut self.data_device {
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Memory(d_trace)) => {
                        transfer.schedule_multiple(
                            &h_trace.chunks,
                            &mut d_trace.tracing_data,
                            context,
                        )?
                    }
                    _ => panic!("expected unrolled memory trace"),
                },
                UnrolledTracingDataHost::NonMemory(h_trace) => match &mut self.data_device {
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(d_trace)) => {
                        transfer.schedule_multiple(
                            &h_trace.chunks,
                            &mut d_trace.tracing_data,
                            context,
                        )?
                    }
                    _ => panic!("expected unrolled non-memory trace"),
                },
                UnrolledTracingDataHost::Unified(h_trace) => match &mut self.data_device {
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Unified(d_trace)) => {
                        transfer.schedule_multiple(
                            &h_trace.chunks,
                            &mut d_trace.tracing_data,
                            context,
                        )?;
                    }
                    _ => panic!("expected unrolled unified trace"),
                },
            },
        }
        Ok(())
    }
}

pub struct InitsAndTeardownsTransfer<'a, A: GoodAllocator> {
    pub data_host: InitsAndTeardownsTraceHost<A>,
    // pub: apex production (`prover::gkr::stage1`) reads the device trace across the split.
    pub data_device: InitsAndTeardownsTraceDevice,
    _marker: std::marker::PhantomData<&'a ()>,
}

impl<'a, A: GoodAllocator + 'a> InitsAndTeardownsTransfer<'a, A> {
    pub fn new(
        data_host: InitsAndTeardownsTraceHost<A>,
        capacity_pages: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let data_device = alloc_inits_and_teardowns(
            [
                data_host.page_indices.len(),
                data_host.values_packed.len(),
                data_host.timestamps_packed.len(),
            ],
            capacity_pages,
            context,
        )?;
        Ok(Self {
            data_host,
            data_device,
            _marker: std::marker::PhantomData,
        })
    }

    // test-reference readers: gpu_circuit_prover's test suites reach this across the crate boundary.
    #[doc(hidden)]
    pub fn schedule_transfer(
        &mut self,
        transfer: &mut Transfer<'a>,
        context: &ProverContext,
    ) -> CudaResult<()> {
        transfer.schedule_multiple(
            &self.data_host.page_indices.chunks,
            &mut self.data_device.page_indices,
            context,
        )?;
        transfer.schedule_multiple(
            &self.data_host.values_packed.chunks,
            &mut self.data_device.values_packed,
            context,
        )?;
        transfer.schedule_multiple(
            &self.data_host.timestamps_packed.chunks,
            &mut self.data_device.timestamps_packed,
            context,
        )?;
        Ok(())
    }
}

/// Device buffers of an absent inits-and-teardowns input (a TRIVIAL leading
/// unified chunk), allocated like a present one and released at the same point.
pub struct InitsAndTeardownsReservation {
    _device: InitsAndTeardownsTraceDevice,
}

impl InitsAndTeardownsReservation {
    pub fn new(capacity_pages: usize, context: &ProverContext) -> CudaResult<Self> {
        let _device = alloc_inits_and_teardowns([0; 3], capacity_pages, context)?;
        Ok(Self { _device })
    }
}

pub fn inits_and_teardowns_capacity_pages(num_sets: usize, domain_size_log2: u32) -> usize {
    assert!(domain_size_log2 >= PAGE_SIZE_LOG2);
    num_sets << (domain_size_log2 - PAGE_SIZE_LOG2)
}

fn alloc_input<T>(
    len: usize,
    capacity: usize,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<T>> {
    assert!(
        len <= capacity,
        "input of {len} elements exceeds its capacity of {capacity}"
    );
    let mut allocation = context.alloc(capacity, AllocationPlacement::Top)?;
    allocation.shrink_len_to(len);
    Ok(allocation)
}

fn alloc_inits_and_teardowns(
    [pages, values, timestamps]: [usize; 3],
    capacity_pages: usize,
    context: &ProverContext,
) -> CudaResult<InitsAndTeardownsTraceDevice> {
    let capacity_values = capacity_pages << PAGE_SIZE_LOG2;
    Ok(InitsAndTeardownsTraceDevice {
        page_indices: alloc_input(pages, capacity_pages, context)?,
        values_packed: alloc_input(values, capacity_values, context)?,
        timestamps_packed: alloc_input(timestamps, capacity_values, context)?,
    })
}
