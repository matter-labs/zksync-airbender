use crate::primitives::field::{BF, E4};
use cs::definitions::GKRAddress;
use field::{Field, FieldExtension, PrimeField};

use super::{
    build_lookup_from_vector_input_with_setup_inputs_and_metadata,
    build_lookup_with_dens_and_setup_expressions_inputs_and_metadata,
};

#[test]
fn lookup_with_dens_and_setup_expression_metadata_uses_tail_relative_indices() {
    let input = (
        GKRAddress::BaseLayerWitness(10),
        cs::definitions::gkr::NoFieldVectorLookupRelation {
            columns: vec![
                cs::definitions::gkr::NoFieldLinearRelation::from_single_input(
                    GKRAddress::BaseLayerWitness(20),
                ),
                cs::definitions::gkr::NoFieldLinearRelation::from_single_input(
                    GKRAddress::BaseLayerWitness(21),
                ),
            ]
            .into_boxed_slice(),
            lookup_set_index: 0,
        },
    );
    let setup = (
        GKRAddress::BaseLayerWitness(11),
        vec![
            GKRAddress::BaseLayerWitness(30),
            GKRAddress::BaseLayerWitness(31),
        ]
        .into_boxed_slice(),
    );

    let (inputs, metadata) = build_lookup_with_dens_and_setup_expressions_inputs_and_metadata::<E4>(
        &input,
        &setup,
        [GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        }; 2],
        E4::from_base(BF::from_u32_unchecked(5)),
        E4::ZERO,
    );

    assert_eq!(
        inputs.inputs_in_base,
        vec![
            GKRAddress::BaseLayerWitness(10),
            GKRAddress::BaseLayerWitness(11),
            GKRAddress::BaseLayerWitness(20),
            GKRAddress::BaseLayerWitness(21),
            GKRAddress::BaseLayerWitness(30),
            GKRAddress::BaseLayerWitness(31),
        ],
    );
    assert_eq!(
        metadata
            .quadratic_terms
            .iter()
            .map(|term| term.lhs)
            .collect::<Vec<_>>(),
        vec![0, 1],
    );
    assert_eq!(
        metadata
            .linear_terms
            .iter()
            .map(|term| term.input)
            .collect::<Vec<_>>(),
        vec![2, 3],
    );
}

#[test]
fn lookup_from_vector_input_with_setup_metadata_uses_tail_relative_indices() {
    let input = cs::definitions::gkr::NoFieldVectorLookupRelation {
        columns: vec![
            cs::definitions::gkr::NoFieldLinearRelation::from_single_input(
                GKRAddress::BaseLayerWitness(20),
            ),
            cs::definitions::gkr::NoFieldLinearRelation::from_single_input(
                GKRAddress::BaseLayerWitness(21),
            ),
        ]
        .into_boxed_slice(),
        lookup_set_index: 0,
    };
    let setup = (
        GKRAddress::BaseLayerWitness(11),
        vec![
            GKRAddress::BaseLayerWitness(30),
            GKRAddress::BaseLayerWitness(31),
        ]
        .into_boxed_slice(),
    );

    let (inputs, metadata) = build_lookup_from_vector_input_with_setup_inputs_and_metadata::<E4>(
        &input,
        &setup,
        [GKRAddress::InnerLayer {
            layer: 1,
            offset: 0,
        }; 2],
        E4::from_base(BF::from_u32_unchecked(5)),
        E4::ZERO,
    );

    assert_eq!(
        inputs.inputs_in_base,
        vec![
            GKRAddress::BaseLayerWitness(11),
            GKRAddress::BaseLayerWitness(20),
            GKRAddress::BaseLayerWitness(21),
            GKRAddress::BaseLayerWitness(30),
            GKRAddress::BaseLayerWitness(31),
        ],
    );
    assert_eq!(
        metadata
            .quadratic_terms
            .iter()
            .map(|term| term.lhs)
            .collect::<Vec<_>>(),
        vec![0, 1],
    );
    assert_eq!(
        metadata
            .linear_terms
            .iter()
            .map(|term| term.input)
            .collect::<Vec<_>>(),
        vec![2, 3],
    );
}
