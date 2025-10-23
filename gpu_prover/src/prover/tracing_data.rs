use super::context::ProverContext;
use super::transfer::Transfer;
use crate::allocator::tracker::AllocationPlacement;
use crate::circuit_type::CircuitType;
use crate::ops_simple::set_to_zero;
use crate::witness::trace::{ShuffleRamInitsAndTeardownsDevice, ShuffleRamInitsAndTeardownsHost};
use crate::witness::trace_delegation::{DelegationTraceDevice, DelegationTraceHost};
use crate::witness::trace_main::{MainTraceDevice, MainTraceHost};
use crate::witness::trace_unrolled::{
    UnrolledMemoryTraceDevice, UnrolledMemoryTraceHost, UnrolledNonMemoryTraceDevice,
    UnrolledNonMemoryTraceHost,
};
use era_cudart::result::CudaResult;
use fft::GoodAllocator;

pub enum UnrolledTracingDataDevice {
    Memory(UnrolledMemoryTraceDevice),
    NonMemory(UnrolledNonMemoryTraceDevice),
    InitsAndTeardowns(ShuffleRamInitsAndTeardownsDevice),
}

pub enum TracingDataDevice {
    Main {
        inits_and_teardowns: ShuffleRamInitsAndTeardownsDevice,
        trace: MainTraceDevice,
    },
    Delegation(DelegationTraceDevice),
    Unrolled(UnrolledTracingDataDevice),
}

#[derive(Clone)]
pub enum UnrolledTracingDataHost<A: GoodAllocator> {
    Memory(UnrolledMemoryTraceHost<A>),
    NonMemory(UnrolledNonMemoryTraceHost<A>),
    InitsAndTeardowns(ShuffleRamInitsAndTeardownsHost<A>),
}

#[derive(Clone)]
pub enum TracingDataHost<A: GoodAllocator> {
    Main {
        inits_and_teardowns: Option<ShuffleRamInitsAndTeardownsHost<A>>,
        trace: MainTraceHost<A>,
    },
    Delegation(DelegationTraceHost<A>),
    Unrolled(UnrolledTracingDataHost<A>),
}

pub struct TracingDataTransfer<'a, A: GoodAllocator> {
    pub circuit_type: CircuitType,
    pub data_host: TracingDataHost<A>,
    pub data_device: TracingDataDevice,
    pub transfer: Transfer<'a>,
}

impl<'a, A: GoodAllocator + 'a> TracingDataTransfer<'a, A> {
    pub fn new(
        circuit_type: CircuitType,
        data_host: TracingDataHost<A>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let data_device = match &data_host {
            TracingDataHost::Main {
                inits_and_teardowns,
                trace,
            } => {
                let len = trace.cycle_data.len();
                if let Some(inits_and_teardowns) = inits_and_teardowns {
                    assert_eq!(inits_and_teardowns.inits_and_teardowns.len(), len);
                };
                let inits_and_teardowns = ShuffleRamInitsAndTeardownsDevice {
                    inits_and_teardowns: context.alloc(len, AllocationPlacement::Top)?,
                };
                let cycle_data = context.alloc(len, AllocationPlacement::Top)?;
                let trace = MainTraceDevice { cycle_data };
                TracingDataDevice::Main {
                    inits_and_teardowns,
                    trace,
                }
            }
            TracingDataHost::Delegation(trace) => {
                let d_write_timestamp =
                    context.alloc(trace.write_timestamp.len(), AllocationPlacement::Top)?;
                let d_register_accesses =
                    context.alloc(trace.register_accesses.len(), AllocationPlacement::Top)?;
                let d_indirect_reads =
                    context.alloc(trace.indirect_reads.len(), AllocationPlacement::Top)?;
                let d_indirect_writes =
                    context.alloc(trace.indirect_writes.len(), AllocationPlacement::Top)?;
                let d_indirect_offset_variables = context.alloc(
                    trace.indirect_offset_variables.len(),
                    AllocationPlacement::Top,
                )?;
                let trace = DelegationTraceDevice {
                    num_requests: trace.num_requests,
                    num_register_accesses_per_delegation: trace
                        .num_register_accesses_per_delegation,
                    num_indirect_reads_per_delegation: trace.num_indirect_reads_per_delegation,
                    num_indirect_writes_per_delegation: trace.num_indirect_writes_per_delegation,
                    num_indirect_access_variable_offsets_per_delegation: trace
                        .num_indirect_access_variable_offsets_per_delegation,
                    base_register_index: trace.base_register_index,
                    delegation_type: trace.delegation_type,
                    indirect_accesses_properties: trace.indirect_accesses_properties.clone(),
                    write_timestamp: d_write_timestamp,
                    register_accesses: d_register_accesses,
                    indirect_reads: d_indirect_reads,
                    indirect_writes: d_indirect_writes,
                    indirect_offset_variables: d_indirect_offset_variables,
                };
                TracingDataDevice::Delegation(trace)
            }
            TracingDataHost::Unrolled(unrolled) => match unrolled {
                UnrolledTracingDataHost::Memory(trace) => {
                    let tracing_data =
                        context.alloc(trace.tracing_data.len(), AllocationPlacement::Top)?;
                    let trace = UnrolledMemoryTraceDevice {
                        cycles_count: trace.cycles_count,
                        tracing_data,
                    };
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Memory(trace))
                }
                UnrolledTracingDataHost::NonMemory(trace) => {
                    let tracing_data =
                        context.alloc(trace.tracing_data.len(), AllocationPlacement::Top)?;
                    let trace = UnrolledNonMemoryTraceDevice {
                        cycles_count: trace.cycles_count,
                        tracing_data,
                    };
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(trace))
                }
                UnrolledTracingDataHost::InitsAndTeardowns(trace) => {
                    let len = trace.inits_and_teardowns.len();
                    let inits_and_teardowns = context.alloc(len, AllocationPlacement::Top)?;
                    let trace = ShuffleRamInitsAndTeardownsDevice {
                        inits_and_teardowns,
                    };
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::InitsAndTeardowns(trace))
                }
            },
        };
        let transfer = Transfer::new()?;
        transfer.record_allocated(context)?;
        Ok(Self {
            circuit_type,
            data_host,
            data_device,
            transfer,
        })
    }

    pub fn schedule_transfer(&mut self, context: &ProverContext) -> CudaResult<()> {
        match &self.data_host {
            TracingDataHost::Main {
                inits_and_teardowns: h_inits_and_teardowns,
                trace: h_trace,
            } => match &mut self.data_device {
                TracingDataDevice::Main {
                    inits_and_teardowns: d_inits_and_teardowns,
                    trace: d_trace,
                } => {
                    if let Some(h_inits_and_teardowns) = h_inits_and_teardowns {
                        self.transfer.schedule(
                            h_inits_and_teardowns.inits_and_teardowns.clone(),
                            &mut d_inits_and_teardowns.inits_and_teardowns,
                            context,
                        )?;
                    } else {
                        self.transfer.ensure_allocated(context)?;
                        set_to_zero(
                            &mut d_inits_and_teardowns.inits_and_teardowns,
                            context.get_h2d_stream(),
                        )?;
                    }
                    self.transfer.schedule(
                        h_trace.cycle_data.clone(),
                        &mut d_trace.cycle_data,
                        context,
                    )?;
                }
                _ => panic!("expected main trace"),
            },
            TracingDataHost::Delegation(h_witness) => match &mut self.data_device {
                TracingDataDevice::Delegation(d_trace) => {
                    self.transfer.schedule(
                        h_witness.write_timestamp.clone(),
                        &mut d_trace.write_timestamp,
                        context,
                    )?;
                    self.transfer.schedule(
                        h_witness.register_accesses.clone(),
                        &mut d_trace.register_accesses,
                        context,
                    )?;
                    self.transfer.schedule(
                        h_witness.indirect_reads.clone(),
                        &mut d_trace.indirect_reads,
                        context,
                    )?;
                    self.transfer.schedule(
                        h_witness.indirect_writes.clone(),
                        &mut d_trace.indirect_writes,
                        context,
                    )?;
                    self.transfer.schedule(
                        h_witness.indirect_offset_variables.clone(),
                        &mut d_trace.indirect_offset_variables,
                        context,
                    )?;
                }
                _ => panic!("expected delegation trace"),
            },
            TracingDataHost::Unrolled(unrolled) => match unrolled {
                UnrolledTracingDataHost::Memory(h_trace) => match &mut self.data_device {
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::Memory(d_trace)) => {
                        self.transfer.schedule(
                            h_trace.tracing_data.clone(),
                            &mut d_trace.tracing_data,
                            context,
                        )?
                    }
                    _ => panic!("expected unrolled memory trace"),
                },
                UnrolledTracingDataHost::NonMemory(h_trace) => match &mut self.data_device {
                    TracingDataDevice::Unrolled(UnrolledTracingDataDevice::NonMemory(d_trace)) => {
                        self.transfer.schedule(
                            h_trace.tracing_data.clone(),
                            &mut d_trace.tracing_data,
                            context,
                        )?
                    }
                    _ => panic!("expected unrolled non-memory trace"),
                },
                UnrolledTracingDataHost::InitsAndTeardowns(h_trace) => {
                    match &mut self.data_device {
                        TracingDataDevice::Unrolled(
                            UnrolledTracingDataDevice::InitsAndTeardowns(d_trace),
                        ) => self.transfer.schedule(
                            h_trace.inits_and_teardowns.clone(),
                            &mut d_trace.inits_and_teardowns,
                            context,
                        )?,
                        _ => panic!("expected unrolled inits and teardowns trace"),
                    }
                }
            },
        }
        self.transfer.record_transferred(context)
    }
}
