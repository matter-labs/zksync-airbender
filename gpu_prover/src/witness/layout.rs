use crate::upstream::{GKRMemoryLayout, NUM_TIMESTAMP_COLUMNS_FOR_RAM};
#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct DelegationProcessingLayout {
    pub execute: u32,
    pub invocation_timestamp: [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM],
}

impl From<&GKRMemoryLayout> for DelegationProcessingLayout {
    fn from(value: &GKRMemoryLayout) -> Self {
        let delegation_state = value
            .delegation_state
            .as_ref()
            .expect("delegation circuits require delegation_state");

        Self {
            execute: delegation_state.execute as u32,
            invocation_timestamp: delegation_state.invocation_timestamp.map(|el| el as u32),
        }
    }
}
