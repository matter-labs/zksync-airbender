use crate::prover::context::ProverContext;
use crate::witness::BF;
use cs::utils::{split_timestamp, split_u32_into_pair_u16};
use era_cudart::slice::CudaSlice;
use fft::GoodAllocator;
use prover::definitions::{AuxArgumentsBoundaryValues, LazyInitAndTeardown};
use prover::risc_v_simulator::cycle::MachineConfig;
use prover::tracers::main_cycle_optimized::{CycleData, SingleCycleTracingData};
use prover::ShuffleRamSetupAndTeardown;
use std::sync::Arc;

pub struct MainTraceDevice<C: ProverContext> {
    pub(crate) cycle_data: C::Allocation<SingleCycleTracingData>,
}

#[repr(C)]
pub(crate) struct MainTraceRaw {
    cycle_data: *const SingleCycleTracingData,
}

impl<C: ProverContext> From<&MainTraceDevice<C>> for MainTraceRaw {
    fn from(value: &MainTraceDevice<C>) -> Self {
        Self {
            cycle_data: value.cycle_data.as_ptr(),
        }
    }
}

#[derive(Clone)]
pub struct MainTraceHost<A: GoodAllocator> {
    pub cycles_traced: usize,
    pub cycle_data: Arc<Vec<SingleCycleTracingData, A>>,
    pub num_cycles_chunk_size: usize,
}

impl<M: MachineConfig, A: GoodAllocator> From<CycleData<M, A>> for MainTraceHost<A> {
    fn from(value: CycleData<M, A>) -> Self {
        Self {
            cycles_traced: value.cycles_traced,
            cycle_data: Arc::new(value.per_cycle_data),
            num_cycles_chunk_size: value.num_cycles_chunk_size,
        }
    }
}

pub struct ShuffleRamSetupAndTeardownDevice<C: ProverContext> {
    pub lazy_init_data: C::Allocation<LazyInitAndTeardown>,
}

#[repr(C)]
pub(crate) struct ShuffleRamSetupAndTeardownRaw {
    pub lazy_init_data: *const LazyInitAndTeardown,
}

impl<C: ProverContext> From<&ShuffleRamSetupAndTeardownDevice<C>>
    for ShuffleRamSetupAndTeardownRaw
{
    fn from(value: &ShuffleRamSetupAndTeardownDevice<C>) -> Self {
        Self {
            lazy_init_data: value.lazy_init_data.as_ptr(),
        }
    }
}

#[derive(Clone)]
pub struct ShuffleRamSetupAndTeardownHost<A: GoodAllocator> {
    pub lazy_init_data: Arc<Vec<LazyInitAndTeardown, A>>,
}

impl<A: GoodAllocator> From<ShuffleRamSetupAndTeardown<A>> for ShuffleRamSetupAndTeardownHost<A> {
    fn from(value: ShuffleRamSetupAndTeardown<A>) -> Self {
        Self {
            lazy_init_data: Arc::new(value.lazy_init_data),
        }
    }
}

pub fn get_aux_arguments_boundary_values(
    lazy_init_data: &[LazyInitAndTeardown],
    cycles_count: usize,
) -> AuxArgumentsBoundaryValues {
    let LazyInitAndTeardown {
        address: lazy_init_address_first_row,
        teardown_value: lazy_teardown_value_first_row,
        teardown_timestamp: lazy_teardown_timestamp_first_row,
    } = lazy_init_data[0];

    let LazyInitAndTeardown {
        address: lazy_init_address_one_before_last_row,
        teardown_value: lazy_teardown_value_one_before_last_row,
        teardown_timestamp: lazy_teardown_timestamp_one_before_last_row,
    } = lazy_init_data[cycles_count - 1];

    let (lazy_init_address_first_row_low, lazy_init_address_first_row_high) =
        split_u32_into_pair_u16(lazy_init_address_first_row);
    let (teardown_value_first_row_low, teardown_value_first_row_high) =
        split_u32_into_pair_u16(lazy_teardown_value_first_row);
    let (teardown_timestamp_first_row_low, teardown_timestamp_first_row_high) =
        split_timestamp(lazy_teardown_timestamp_first_row.as_scalar());

    let (lazy_init_address_one_before_last_row_low, lazy_init_address_one_before_last_row_high) =
        split_u32_into_pair_u16(lazy_init_address_one_before_last_row);
    let (teardown_value_one_before_last_row_low, teardown_value_one_before_last_row_high) =
        split_u32_into_pair_u16(lazy_teardown_value_one_before_last_row);
    let (teardown_timestamp_one_before_last_row_low, teardown_timestamp_one_before_last_row_high) =
        split_timestamp(lazy_teardown_timestamp_one_before_last_row.as_scalar());

    let lazy_init_first_row = [
        BF::new(lazy_init_address_first_row_low as u32),
        BF::new(lazy_init_address_first_row_high as u32),
    ];
    let teardown_value_first_row = [
        BF::new(teardown_value_first_row_low as u32),
        BF::new(teardown_value_first_row_high as u32),
    ];
    let teardown_timestamp_first_row = [
        BF::new(teardown_timestamp_first_row_low),
        BF::new(teardown_timestamp_first_row_high),
    ];

    let lazy_init_one_before_last_row = [
        BF::new(lazy_init_address_one_before_last_row_low as u32),
        BF::new(lazy_init_address_one_before_last_row_high as u32),
    ];
    let teardown_value_one_before_last_row = [
        BF::new(teardown_value_one_before_last_row_low as u32),
        BF::new(teardown_value_one_before_last_row_high as u32),
    ];
    let teardown_timestamp_one_before_last_row = [
        BF::new(teardown_timestamp_one_before_last_row_low),
        BF::new(teardown_timestamp_one_before_last_row_high),
    ];

    AuxArgumentsBoundaryValues {
        lazy_init_first_row,
        teardown_value_first_row,
        teardown_timestamp_first_row,
        lazy_init_one_before_last_row,
        teardown_value_one_before_last_row,
        teardown_timestamp_one_before_last_row,
    }
}
