use crate::prover::context::DeviceAllocation;
use crate::witness::BF;
use cs::definitions::split_timestamp;
use cs::one_row_compiler::CompiledCircuitArtifact;
use cs::utils::split_u32_into_pair_u16;
use era_cudart::slice::CudaSlice;
use fft::GoodAllocator;
use prover::definitions::{AuxArgumentsBoundaryValues, LazyInitAndTeardown};
use prover::ShuffleRamSetupAndTeardown;
use std::sync::Arc;

pub struct ShuffleRamInitsAndTeardownsDevice {
    pub inits_and_teardowns: DeviceAllocation<LazyInitAndTeardown>,
}

#[repr(C)]
pub(crate) struct ShuffleRamInitsAndTeardownsRaw {
    // pub count: u32,
    pub inits_and_teardowns: *const LazyInitAndTeardown,
}

impl From<&ShuffleRamInitsAndTeardownsDevice> for ShuffleRamInitsAndTeardownsRaw {
    fn from(value: &ShuffleRamInitsAndTeardownsDevice) -> Self {
        Self {
            // count: value.inits_and_teardowns.len() as u32,
            inits_and_teardowns: value.inits_and_teardowns.as_ptr(),
        }
    }
}

#[derive(Clone)]
pub struct ShuffleRamInitsAndTeardownsHost<A: GoodAllocator> {
    pub inits_and_teardowns: Arc<Vec<LazyInitAndTeardown, A>>,
}

impl<A: GoodAllocator> From<ShuffleRamSetupAndTeardown<A>> for ShuffleRamInitsAndTeardownsHost<A> {
    fn from(value: ShuffleRamSetupAndTeardown<A>) -> Self {
        Self {
            inits_and_teardowns: Arc::new(value.lazy_init_data),
        }
    }
}

pub fn get_aux_arguments_boundary_values(
    compiled_circuit: &CompiledCircuitArtifact<BF>,
    cycles: usize,
    lazy_init_data: &[LazyInitAndTeardown],
) -> Vec<AuxArgumentsBoundaryValues> {
    assert_eq!(
        compiled_circuit
            .memory_layout
            .shuffle_ram_inits_and_teardowns
            .len(),
        compiled_circuit.lazy_init_address_aux_vars.len()
    );

    if compiled_circuit
        .memory_layout
        .shuffle_ram_inits_and_teardowns
        .is_empty()
        == false
    {
        assert_eq!(
            lazy_init_data.len(),
            cycles
                * compiled_circuit
                    .memory_layout
                    .shuffle_ram_inits_and_teardowns
                    .len()
        );
    }

    // now get aux variables
    let mut values = Vec::with_capacity(lazy_init_data.len());
    let len = compiled_circuit
        .memory_layout
        .shuffle_ram_inits_and_teardowns
        .len();

    for i in 0..len {
        let LazyInitAndTeardown {
            address: lazy_init_address_first_row,
            teardown_value: lazy_teardown_value_first_row,
            teardown_timestamp: lazy_teardown_timestamp_first_row,
        } = lazy_init_data[(cycles - 1) * i];

        let LazyInitAndTeardown {
            address: lazy_init_address_one_before_last_row,
            teardown_value: lazy_teardown_value_one_before_last_row,
            teardown_timestamp: lazy_teardown_timestamp_one_before_last_row,
        } = lazy_init_data[(cycles * (i + 1)) - 1];

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
        let (
            teardown_timestamp_one_before_last_row_low,
            teardown_timestamp_one_before_last_row_high,
        ) = split_timestamp(lazy_teardown_timestamp_one_before_last_row.as_scalar());

        let aux_value = AuxArgumentsBoundaryValues {
            lazy_init_first_row: [
                BF::new(lazy_init_address_first_row_low as u32),
                BF::new(lazy_init_address_first_row_high as u32),
            ],
            teardown_value_first_row: [
                BF::new(teardown_value_first_row_low as u32),
                BF::new(teardown_value_first_row_high as u32),
            ],
            teardown_timestamp_first_row: [
                BF::new(teardown_timestamp_first_row_low),
                BF::new(teardown_timestamp_first_row_high),
            ],
            lazy_init_one_before_last_row: [
                BF::new(lazy_init_address_one_before_last_row_low as u32),
                BF::new(lazy_init_address_one_before_last_row_high as u32),
            ],
            teardown_value_one_before_last_row: [
                BF::new(teardown_value_one_before_last_row_low as u32),
                BF::new(teardown_value_one_before_last_row_high as u32),
            ],
            teardown_timestamp_one_before_last_row: [
                BF::new(teardown_timestamp_one_before_last_row_low),
                BF::new(teardown_timestamp_one_before_last_row_high),
            ],
        };
        values.push(aux_value);
    }

    values
}
