use era_cudart::slice::DeviceSlice;
use gpu_core::primitives::device_structures::DeviceMatrixMut;
use gpu_core::primitives::field::PR;

mod fused;
mod inits_and_teardowns;
mod multiplicities;
mod relations;

#[cfg(test)]
mod tests;

pub use fused::generate_fused_values;
pub use inits_and_teardowns::generate_inits_and_teardowns;
pub use multiplicities::generate_lookup_multiplicities;
pub use relations::{
    prepare_lookup_relations, Proth120LookupRelations, Proth120LookupRelationsHost,
};

pub struct Proth120WitnessBuffers<'a> {
    pub memory: DeviceMatrixMut<'a, PR>,
    pub witness: DeviceMatrixMut<'a, PR>,
    pub scratch: DeviceMatrixMut<'a, PR>,
    pub generic_lookup_mapping: DeviceMatrixMut<'a, u32>,
    pub range_check_16_lookup_mapping: DeviceMatrixMut<'a, u32>,
    pub range_check_timestamp_lookup_mapping: DeviceMatrixMut<'a, u32>,
    pub decoder_lookup_mapping: &'a mut DeviceSlice<u32>,
}
