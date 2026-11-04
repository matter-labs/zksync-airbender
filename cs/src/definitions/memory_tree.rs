use super::*;

#[derive(Clone, Copy, Hash, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct ShuffleRamInitAndTeardownLayout {
    pub lazy_init_addresses_columns: ColumnSet<REGISTER_SIZE>,
    pub lazy_teardown_values_columns: ColumnSet<REGISTER_SIZE>,
    pub lazy_teardown_timestamps_columns: ColumnSet<NUM_TIMESTAMP_COLUMNS_FOR_RAM>,
}

impl ShuffleRamInitAndTeardownLayout {
    pub const fn empty() -> Self {
        Self {
            lazy_init_addresses_columns: ColumnSet::empty(),
            lazy_teardown_values_columns: ColumnSet::empty(),
            lazy_teardown_timestamps_columns: ColumnSet::empty(),
        }
    }
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct MemorySubtree {
    pub shuffle_ram_inits_and_teardowns: Vec<ShuffleRamInitAndTeardownLayout>,
    pub shuffle_ram_access_sets: Vec<ShuffleRamQueryColumns>,
    pub delegation_request_layout: Option<DelegationRequestLayout>,
    pub delegation_processor_layout: Option<DelegationProcessingLayout>,
    pub machine_state_layout: Option<MachineStatePermutationVariables>,
    pub intermediate_state_layout: Option<IntermediateStatePermutationVariables>,
    pub batched_ram_accesses: Vec<BatchedRamAccessColumns>,
    pub register_and_indirect_accesses: Vec<RegisterAndIndirectAccessDescription>,
    pub total_width: usize,
}

impl MemorySubtree {
    pub fn as_compiled<'a>(
        &'a self,
        buffer: &'a mut Vec<CompiledRegisterAndIndirectAccessDescription<'a>>,
    ) -> CompiledMemorySubtree<'a> {
        assert!(buffer.is_empty());
        for el in self.register_and_indirect_accesses.iter() {
            buffer.push(el.as_compiled());
        }

        CompiledMemorySubtree {
            shuffle_ram_inits_and_teardowns: &self.shuffle_ram_inits_and_teardowns,
            shuffle_ram_access_sets: &self.shuffle_ram_access_sets,
            delegation_request_layout: self.delegation_request_layout,
            delegation_processor_layout: self.delegation_processor_layout,
            machine_state_layout: self.machine_state_layout,
            intermediate_state_layout: self.intermediate_state_layout,
            batched_ram_accesses: &self.batched_ram_accesses,
            register_and_indirect_accesses: &*buffer,
            total_width: self.total_width,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct CompiledMemorySubtree<'a> {
    pub shuffle_ram_inits_and_teardowns: &'a [ShuffleRamInitAndTeardownLayout],
    pub shuffle_ram_access_sets: &'a [ShuffleRamQueryColumns],
    pub delegation_request_layout: Option<DelegationRequestLayout>,
    pub delegation_processor_layout: Option<DelegationProcessingLayout>,
    pub machine_state_layout: Option<MachineStatePermutationVariables>,
    pub intermediate_state_layout: Option<IntermediateStatePermutationVariables>,
    pub batched_ram_accesses: &'a [BatchedRamAccessColumns],
    pub register_and_indirect_accesses: &'a [CompiledRegisterAndIndirectAccessDescription<'a>],
    pub total_width: usize,
}
