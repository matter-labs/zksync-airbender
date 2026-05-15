use crate::upstream::GKRAddress;

// pub mod arg_utils;
pub(crate) mod layout;
pub(crate) mod memory_delegation;
pub(crate) mod memory_unrolled;
pub(crate) mod multiplicities;
mod option;
mod ram_access;
pub(crate) mod trace;
pub(crate) mod trace_delegation;
pub(crate) mod trace_unrolled;
pub(crate) mod witness_delegation;
pub(crate) mod witness_unrolled;

#[repr(C, u32)]
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub(crate) enum Address {
    BaseLayerWitness(u32),
    BaseLayerMemory(u32),
    InnerLayer { offset: u32, layer: u32 },
    Setup(u32),
    ScratchSpace(u32),
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
            GKRAddress::VirtualSetup(_) => {
                unreachable!(
                    "GPU witness serialization does not materialize virtual setup addresses"
                )
            }
            GKRAddress::ScratchSpace(x) => Self::ScratchSpace(x as u32),
            GKRAddress::Cached { layer, offset } => Self::Cached {
                offset: offset as u32,
                layer: layer as u32,
            },
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct NoFieldLinearTerm {
    coefficient: u32,
    address: Address,
}

pub(crate) const MAX_LINEAR_TERMS_COUNT: usize = 4;

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct NoFieldLinearRelation {
    linear_terms_count: u32,
    linear_terms: [NoFieldLinearTerm; MAX_LINEAR_TERMS_COUNT],
    constant: u32,
}

impl From<&cs::definitions::gkr::NoFieldLinearRelation> for NoFieldLinearRelation {
    fn from(value: &cs::definitions::gkr::NoFieldLinearRelation) -> Self {
        let terms = &value.linear_terms;
        let len = terms.len();
        assert!(len <= MAX_LINEAR_TERMS_COUNT);
        let mut linear_terms = [NoFieldLinearTerm::default(); MAX_LINEAR_TERMS_COUNT];
        for (&src, dst) in terms.iter().zip(linear_terms.iter_mut()) {
            *dst = NoFieldLinearTerm {
                coefficient: src.0,
                address: src.1.into(),
            };
        }
        Self {
            linear_terms_count: len as u32,
            linear_terms,
            constant: value.constant,
        }
    }
}
