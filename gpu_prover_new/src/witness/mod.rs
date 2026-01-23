use cs::definitions::{GKRAddress, NUM_TIMESTAMP_COLUMNS_FOR_RAM, REGISTER_SIZE};
use cs::definitions::gkr::RamQuery;

// pub mod memory_delegation;
pub mod memory_unrolled;
mod option;
mod placeholder;
mod ram_access;
pub mod trace;
// pub mod trace_delegation;
pub mod trace_unrolled;
// pub mod witness_delegation;
pub mod witness_unrolled;


#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub enum Address {
    BaseLayerWitness(u32),
    BaseLayerMemory(u32),
    InnerLayer { offset: u32, layer: u32 },
    Setup(u32),
    OptimizedOut(u32),
    Cached { offset: u32, layer: u32 },
}

impl Default for Address {
    fn default() -> Self {
        Self::BaseLayerWitness(0)
    }
}

impl From<GKRAddress> for Address {
    fn from(value: GKRAddress) -> Self {
        match value {
            GKRAddress::BaseLayerWitness(x) => Self::BaseLayerWitness(x as u32),
            GKRAddress::BaseLayerMemory(x) => Self::BaseLayerMemory(x as u32),
            GKRAddress::InnerLayer { layer, offset } => Self::InnerLayer {
                offset: offset as u32,
                layer: layer as u32,
            },
            GKRAddress::Setup(x) => Self::Setup(x as u32),
            GKRAddress::OptimizedOut(x) => Self::OptimizedOut(x as u32),
            GKRAddress::Cached { layer, offset } => Self::Cached {
                offset: offset as u32,
                layer: layer as u32,
            },
        }
    }
}
