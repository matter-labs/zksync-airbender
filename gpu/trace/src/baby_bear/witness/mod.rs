// Production consumers launch BabyBear witness generation through these modules.
pub mod memory_delegation;
pub mod memory_unrolled;
pub mod multiplicities;
pub mod witness_delegation;
pub mod witness_unrolled;

use crate::witness::{Address, MAX_LINEAR_TERMS_COUNT};

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct LinearTerm {
    coefficient: u32,
    address: Address,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct LinearRelation {
    linear_terms_count: u32,
    linear_terms: [LinearTerm; MAX_LINEAR_TERMS_COUNT],
    constant: u32,
}

impl From<&crate::upstream::LinearRelation> for LinearRelation {
    fn from(value: &crate::upstream::LinearRelation) -> Self {
        let terms = &value.linear_terms;
        let len = terms.len();
        assert!(len <= MAX_LINEAR_TERMS_COUNT);
        let mut linear_terms = [LinearTerm::default(); MAX_LINEAR_TERMS_COUNT];
        for (&src, dst) in terms.iter().zip(linear_terms.iter_mut()) {
            *dst = LinearTerm {
                coefficient: src.0.to_u32(),
                address: src.1.into(),
            };
        }
        Self {
            linear_terms_count: len as u32,
            linear_terms,
            constant: value.constant.to_u32(),
        }
    }
}
