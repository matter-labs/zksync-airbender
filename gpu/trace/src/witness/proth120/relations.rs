use crate::upstream::{GKRAddress, GKRCircuitArtifact, PRLinearRelation};
use crate::witness::{Address, MAX_LINEAR_TERMS_COUNT};
use gpu_core::primitives::field::PR;
use std::mem::{align_of, offset_of, size_of};

#[repr(C, align(16))]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Proth120LinearTerm {
    coefficient: PR,
    address: Address,
    padding: u32,
}

#[repr(C, align(16))]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Proth120LinearRelation {
    constant: PR,
    terms: [Proth120LinearTerm; MAX_LINEAR_TERMS_COUNT],
    terms_count: u32,
    padding: [u32; 3],
}

pub(crate) const RANGE_CHECK_16_RELATIONS: usize = 15;
pub(crate) const TIMESTAMP_RELATIONS: usize = 8;

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct Proth120LookupExpressions<const N: usize> {
    relations: [Proth120LinearRelation; N],
}

/// Immutable launch arguments for the unified Proth120 circuit.
#[derive(Clone, Copy, Debug)]
pub struct LookupRelationsPr {
    pub(crate) range_check_16: Proth120LookupExpressions<RANGE_CHECK_16_RELATIONS>,
    pub(crate) timestamp: Proth120LookupExpressions<TIMESTAMP_RELATIONS>,
}

impl LookupRelationsPr {
    pub fn new(circuit: &GKRCircuitArtifact<PR>) -> Self {
        fn expressions<const N: usize>(
            relations: &[crate::upstream::PRSingleColumnLookupRelation],
        ) -> Proth120LookupExpressions<N> {
            assert_eq!(relations.len(), N, "Proth120 unified lookup relation count");
            Proth120LookupExpressions {
                relations: std::array::from_fn(|i| (&relations[i].input).into()),
            }
        }
        Self {
            range_check_16: expressions(&circuit.range_check_16_lookup_expressions),
            timestamp: expressions(&circuit.timestamp_range_check_lookup_expressions),
        }
    }
}

const _: () = {
    assert!(size_of::<Address>() == 12);
    assert!(align_of::<Address>() == 4);
    assert!(offset_of!(Proth120LinearTerm, coefficient) == 0);
    assert!(offset_of!(Proth120LinearTerm, address) == 16);
    assert!(offset_of!(Proth120LinearTerm, padding) == 28);
    assert!(size_of::<Proth120LinearTerm>() == 32);
    assert!(align_of::<Proth120LinearTerm>() == 16);
    assert!(offset_of!(Proth120LinearRelation, constant) == 0);
    assert!(offset_of!(Proth120LinearRelation, terms) == 16);
    assert!(offset_of!(Proth120LinearRelation, terms_count) == 144);
    assert!(offset_of!(Proth120LinearRelation, padding) == 148);
    assert!(size_of::<Proth120LinearRelation>() == 160);
    assert!(align_of::<Proth120LinearRelation>() == 16);
    assert!(size_of::<Proth120LookupExpressions<15>>() == 2400);
    assert!(size_of::<Proth120LookupExpressions<8>>() == 1280);
    assert!(align_of::<Proth120LookupExpressions<15>>() == 16);
    assert!(size_of::<LookupRelationsPr>() == 3680);
};

impl From<&PRLinearRelation> for Proth120LinearRelation {
    fn from(value: &PRLinearRelation) -> Self {
        let len = value.linear_terms.len();
        assert!(
            len <= MAX_LINEAR_TERMS_COUNT,
            "Proth120 lookup relation has {len} terms, at most {MAX_LINEAR_TERMS_COUNT} are supported"
        );
        let mut terms = [Proth120LinearTerm::default(); MAX_LINEAR_TERMS_COUNT];
        for (&(coefficient, address), dst) in value.linear_terms.iter().zip(terms.iter_mut()) {
            let address = match address {
                GKRAddress::BaseLayerMemory(_)
                | GKRAddress::BaseLayerWitness(_)
                | GKRAddress::ScratchSpace(_) => Address::from(address),
                address => {
                    panic!("Proth120 lookup relation term reads unsupported address {address:?}")
                }
            };
            *dst = Proth120LinearTerm {
                coefficient,
                address,
                padding: 0,
            };
        }
        Self {
            constant: value.constant,
            terms,
            terms_count: len as u32,
            padding: [0; 3],
        }
    }
}
