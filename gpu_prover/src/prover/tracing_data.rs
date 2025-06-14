use crate::circuit_type::CircuitType;
use crate::ops_simple::set_to_zero;
use crate::prover::context::ProverContext;
use crate::prover::transfer::Transfer;
use crate::witness::trace_delegation::{DelegationTraceDevice, DelegationTraceHost};
use crate::witness::trace_main::{
    MainTraceDevice, MainTraceHost, ShuffleRamSetupAndTeardownDevice,
    ShuffleRamSetupAndTeardownHost,
};
use era_cudart::result::CudaResult;
use fft::GoodAllocator;

pub enum TracingDataDevice<C: ProverContext> {
    Main {
        setup_and_teardown: ShuffleRamSetupAndTeardownDevice<C>,
        trace: MainTraceDevice<C>,
    },
    Delegation(DelegationTraceDevice<C>),
}

#[derive(Clone)]
pub enum TracingDataHost<A: GoodAllocator> {
    Main {
        setup_and_teardown: Option<ShuffleRamSetupAndTeardownHost<A>>,
        trace: MainTraceHost<A>,
    },
    Delegation(DelegationTraceHost<A>),
}

pub struct TracingDataTransfer<'a, C: ProverContext> {
    pub circuit_type: CircuitType,
    pub data_host: TracingDataHost<C::HostAllocator>,
    pub data_device: TracingDataDevice<C>,
    pub transfer: Transfer<'a, C>,
}

impl<'a, C: ProverContext> TracingDataTransfer<'a, C> {
    pub fn new(
        circuit_type: CircuitType,
        data_host: TracingDataHost<C::HostAllocator>,
        context: &C,
    ) -> CudaResult<Self> {
        let data_device = match &data_host {
            TracingDataHost::Main {
                setup_and_teardown,
                trace,
            } => {
                let len = trace.cycle_data.len();
                if let Some(setup_and_teardown) = setup_and_teardown {
                    assert_eq!(setup_and_teardown.lazy_init_data.len(), len);
                };
                let lazy_init_data = context.alloc(len)?;
                let setup_and_teardown = ShuffleRamSetupAndTeardownDevice { lazy_init_data };
                let cycle_data = context.alloc(len)?;
                let trace = MainTraceDevice { cycle_data };
                TracingDataDevice::Main {
                    setup_and_teardown,
                    trace,
                }
            }
            TracingDataHost::Delegation(trace) => {
                let d_write_timestamp = context.alloc(trace.write_timestamp.len())?;
                let d_register_accesses = context.alloc(trace.register_accesses.len())?;
                let d_indirect_reads = context.alloc(trace.indirect_reads.len())?;
                let d_indirect_writes = context.alloc(trace.indirect_writes.len())?;
                let trace = DelegationTraceDevice::<C> {
                    num_requests: trace.num_requests,
                    num_register_accesses_per_delegation: trace
                        .num_register_accesses_per_delegation,
                    num_indirect_reads_per_delegation: trace.num_indirect_reads_per_delegation,
                    num_indirect_writes_per_delegation: trace.num_indirect_writes_per_delegation,
                    base_register_index: trace.base_register_index,
                    delegation_type: trace.delegation_type,
                    indirect_accesses_properties: trace.indirect_accesses_properties.clone(),
                    write_timestamp: d_write_timestamp,
                    register_accesses: d_register_accesses,
                    indirect_reads: d_indirect_reads,
                    indirect_writes: d_indirect_writes,
                };
                TracingDataDevice::Delegation(trace)
            }
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

    pub fn schedule_transfer(&mut self, context: &C) -> CudaResult<()>
    where
        C::HostAllocator: 'a,
    {
        match &self.data_host {
            TracingDataHost::Main {
                setup_and_teardown: h_setup_and_teardown,
                trace: h_trace,
            } => match &mut self.data_device {
                TracingDataDevice::Main {
                    setup_and_teardown: d_setup_and_teardown,
                    trace: d_trace,
                } => {
                    if let Some(h_setup_and_teardown) = h_setup_and_teardown {
                        self.transfer.schedule(
                            h_setup_and_teardown.lazy_init_data.clone(),
                            &mut d_setup_and_teardown.lazy_init_data,
                            context,
                        )?;
                    } else {
                        set_to_zero(
                            &mut d_setup_and_teardown.lazy_init_data,
                            context.get_h2d_stream(),
                        )?;
                    }
                    self.transfer.schedule(
                        h_trace.cycle_data.clone(),
                        &mut d_trace.cycle_data,
                        context,
                    )?;
                }
                TracingDataDevice::Delegation(_) => panic!("expected main trace"),
            },
            TracingDataHost::Delegation(h_witness) => match &mut self.data_device {
                TracingDataDevice::Main { .. } => panic!("expected delegation trace"),
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
                }
            },
        }
        self.transfer.record_transferred(context)
    }
}
