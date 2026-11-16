use field::Proth120;
use gpu_core::primitives::device_structures::DeviceMatrixMut;
use gpu_prover_context::ProverContext;
use std::mem::{align_of, size_of};

use super::relations::{Proth120LinearRelation, Proth120LinearTerm, Proth120LookupExpressions};
use crate::witness::tests::MultiplicityField;
use crate::witness::Address;

#[test]
fn cpu_relations_abi_pins() {
    let circuit = serde_json::from_slice(include_bytes!(
        "../../../../../circuit_defs/unrolled_circuits/unified_reduced_machine_proth120/generated/layout.json"
    ))
    .unwrap();
    let _relations = super::LookupRelationsPr::new(&circuit);
    assert_eq!((size_of::<Address>(), align_of::<Address>()), (12, 4));
    assert_eq!(
        (
            size_of::<crate::baby_bear::witness::LinearTerm>(),
            align_of::<crate::baby_bear::witness::LinearTerm>()
        ),
        (16, 4)
    );
    assert_eq!(
        (
            size_of::<crate::baby_bear::witness::LinearRelation>(),
            align_of::<crate::baby_bear::witness::LinearRelation>()
        ),
        (72, 4)
    );
    assert_eq!(
        (
            size_of::<Proth120LinearTerm>(),
            align_of::<Proth120LinearTerm>()
        ),
        (32, 16)
    );
    assert_eq!(
        (
            size_of::<Proth120LinearRelation>(),
            align_of::<Proth120LinearRelation>()
        ),
        (160, 16)
    );
    assert_eq!(
        (
            size_of::<Proth120LookupExpressions<15>>(),
            align_of::<Proth120LookupExpressions<15>>()
        ),
        (2400, 16)
    );
    assert_eq!(size_of::<Proth120LookupExpressions<8>>(), 1280);
    assert_eq!(size_of::<super::LookupRelationsPr>(), 3680);
    let address = Address::InnerLayer {
        offset: 0x12345678,
        layer: 0x87654321,
    };
    let words =
        unsafe { std::slice::from_raw_parts((&address as *const Address).cast::<u32>(), 3) };
    assert_eq!(
        words,
        &[2, 0x12345678, 0x87654321],
        "Proth120 Address tag/offset/layer at 0/4/8"
    );
    for (address, tag) in [
        (Address::BaseLayerWitness(0), 0),
        (Address::BaseLayerMemory(0), 1),
        (
            Address::InnerLayer {
                offset: 0,
                layer: 0,
            },
            2,
        ),
        (Address::Setup(0), 3),
        (Address::ScratchSpace(0), 4),
        (
            Address::Cached {
                offset: 0,
                layer: 0,
            },
            5,
        ),
    ] {
        assert_eq!(
            unsafe { *(&address as *const Address).cast::<u32>() },
            tag,
            "Proth120 Address discriminant"
        );
    }
}

impl MultiplicityField for Proth120 {
    fn count(value: u32) -> Self {
        Proth120::new(value as u128)
    }
    fn generate(
        mapping: &mut DeviceMatrixMut<'_, u32>,
        counts: &mut DeviceMatrixMut<'_, Self>,
        active: usize,
        context: &ProverContext,
    ) {
        super::generate_lookup_multiplicities(mapping, counts, active, context).unwrap();
    }
}
