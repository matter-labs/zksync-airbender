use std::ptr::null;

use era_cudart::result::CudaResult;

use crate::upstream::{
    GKRAddress, RamWordRepresentation, VirtualSetupPoly, DECODER_LOOKUP_FORMAL_SET_INDEX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};

use super::super::setup::GpuGKRForwardSetup;
use super::super::stage1::GpuGKRStage1Output;
use super::super::{
    GpuBaseFieldPoly, GpuBaseFieldSourceKind, GpuExtensionFieldPoly, GpuGKRStorage,
};
use super::flat_plan::cache_relation_layer;
use super::kernels::*;
use crate::ops::simple::{Add, BinaryOp, Mul, SetByRef, SetByVal, Sub};
use crate::primitives::field::BF;
use crate::prover::ProverContext;
use crate::upstream::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp, Field,
    FieldExtension, GKRExternalChallenges, NoFieldGKRCacheRelation,
    NoFieldSpecialMemoryContributionRelation, PrimeField,
};

fn add_memory_tuple_linear_term<E: Field>(
    descriptor: &mut GpuGKRForwardCacheDescriptor<E>,
    term_idx: usize,
    input: *const BF,
    challenge: E,
) {
    descriptor.linear_inputs[term_idx] = input;
    descriptor.linear_challenges[term_idx] = challenge;
}

fn push_memory_tuple_linear_term<E: Field>(
    descriptor: &mut GpuGKRForwardCacheDescriptor<E>,
    input: *const BF,
    challenge: E,
) {
    let term_idx = descriptor
        .linear_inputs
        .iter()
        .position(|ptr| ptr.is_null())
        .expect("GPU memory tuple linear terms exceeded fixed descriptor capacity");
    add_memory_tuple_linear_term(descriptor, term_idx, input, challenge);
}

fn add_memory_expr_linear_term<E: Field>(
    expr: &mut GpuFlatFwdMemoryExpr<E>,
    term_idx: usize,
    input: *const BF,
    challenge: E,
) {
    expr.linear_inputs[term_idx] = input;
    expr.linear_challenges[term_idx] = challenge;
}

fn push_memory_expr_linear_term<E: Field>(
    expr: &mut GpuFlatFwdMemoryExpr<E>,
    input: *const BF,
    challenge: E,
) {
    let term_idx = expr
        .linear_inputs
        .iter()
        .position(|ptr| ptr.is_null())
        .expect("GPU memory tuple linear terms exceeded fixed descriptor capacity");
    add_memory_expr_linear_term(expr, term_idx, input, challenge);
}

pub(super) fn build_memory_expr<E>(
    rel: &NoFieldSpecialMemoryContributionRelation,
    storage: &GpuGKRStorage<BF, E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> GpuFlatFwdMemoryExpr<E>
where
    E: Field + FieldExtension<BF>,
{
    let mut expr = GpuFlatFwdMemoryExpr {
        constant_term: external_challenges.permutation_argument_additive_part,
        ..GpuFlatFwdMemoryExpr::default()
    };
    let mut deferred_low_dynamic_term: Option<(*const BF, E)> = None;

    match rel.address_space {
        CompiledAddressSpaceRelationStrict::Constant(c) => {
            expr.address_space_kind = GpuGKRForwardCacheAddressSpaceKind::Constant;
            expr.address_space_constant = BF::from_u32_unchecked(c);
        }
        CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
            expr.address_space_kind = GpuGKRForwardCacheAddressSpaceKind::Not;
            expr.address_space_ptr = storage
                .get_base_layer(GKRAddress::BaseLayerMemory(offset))
                .as_ptr();
        }
        CompiledAddressSpaceRelationStrict::IsRam(offset) => {
            expr.address_space_kind = GpuGKRForwardCacheAddressSpaceKind::Is;
            expr.address_space_ptr = storage
                .get_base_layer(GKRAddress::BaseLayerMemory(offset))
                .as_ptr();
        }
    }

    match &rel.address {
        CompiledAddressStrict::ConstantU16(c) => {
            let mut contribution = external_challenges
                .permutation_argument_linearization_challenges
                [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            contribution.mul_assign_by_base(&BF::from_u32_unchecked(*c as u32));
            expr.constant_term.add_assign(&contribution);
        }
        CompiledAddressStrict::Constant(c) => {
            let mut contribution = external_challenges
                .permutation_argument_linearization_challenges
                [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            contribution.mul_assign_by_base(&BF::from_u32_unchecked(*c));
            expr.constant_term.add_assign(&contribution);
        }
        CompiledAddressStrict::U16Space(offset) => {
            add_memory_expr_linear_term(
                &mut expr,
                MEMORY_TUPLE_ADDRESS_LOW_TERM,
                storage
                    .get_base_layer(GKRAddress::BaseLayerMemory(*offset))
                    .as_ptr(),
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
            );
        }
        CompiledAddressStrict::U32Space([low, high]) => {
            add_memory_expr_linear_term(
                &mut expr,
                MEMORY_TUPLE_ADDRESS_LOW_TERM,
                storage
                    .get_base_layer(GKRAddress::BaseLayerMemory(*low))
                    .as_ptr(),
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
            );
            add_memory_expr_linear_term(
                &mut expr,
                MEMORY_TUPLE_ADDRESS_HIGH_TERM,
                storage
                    .get_base_layer(GKRAddress::BaseLayerMemory(*high))
                    .as_ptr(),
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX],
            );
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect {
            low_base,
            low_dynamic_offset,
            low_offset,
            high,
        } => {
            let low_challenge = external_challenges.permutation_argument_linearization_challenges
                [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
            let high_challenge = external_challenges.permutation_argument_linearization_challenges
                [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
            if *low_offset != 0 {
                let mut contribution = low_challenge;
                contribution.mul_assign_by_base(&BF::from_u32_unchecked(*low_offset));
                expr.constant_term.add_assign(&contribution);
            }
            add_memory_expr_linear_term(
                &mut expr,
                MEMORY_TUPLE_ADDRESS_LOW_TERM,
                storage
                    .get_base_layer(GKRAddress::BaseLayerMemory(*low_base))
                    .as_ptr(),
                low_challenge,
            );
            if let Some((multiplier, dynamic_offset)) = *low_dynamic_offset {
                let mut challenge = low_challenge;
                challenge.mul_assign_by_base(&BF::from_u32_unchecked(multiplier as u32));
                deferred_low_dynamic_term = Some((
                    storage
                        .get_base_layer(GKRAddress::BaseLayerMemory(dynamic_offset))
                        .as_ptr(),
                    challenge,
                ));
            }
            add_memory_expr_linear_term(
                &mut expr,
                MEMORY_TUPLE_ADDRESS_HIGH_TERM,
                storage
                    .get_base_layer(GKRAddress::BaseLayerMemory(*high))
                    .as_ptr(),
                high_challenge,
            );
        }
        CompiledAddressStrict::U32SpaceGeneric(..) => {
            unimplemented!(
                "unsupported GPU memory tuple address relation: {:?}",
                rel.address
            )
        }
    }

    match &rel.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(timestamp) => {
            add_memory_expr_linear_term(
                &mut expr,
                MEMORY_TUPLE_TIMESTAMP_LOW_TERM,
                storage
                    .get_base_layer(GKRAddress::BaseLayerMemory(timestamp[0]))
                    .as_ptr(),
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX],
            );
            if rel.timestamp_offset != 0 {
                let mut contribution = external_challenges
                    .permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                contribution.mul_assign_by_base(&BF::from_u32_unchecked(rel.timestamp_offset));
                expr.constant_term.add_assign(&contribution);
            }
            add_memory_expr_linear_term(
                &mut expr,
                MEMORY_TUPLE_TIMESTAMP_HIGH_TERM,
                storage
                    .get_base_layer(GKRAddress::BaseLayerMemory(timestamp[1]))
                    .as_ptr(),
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX],
            );
        }
    }

    match rel.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(read_value) => {
            add_memory_expr_linear_term(
                &mut expr,
                MEMORY_TUPLE_VALUE_LOW_TERM,
                storage
                    .get_base_layer(GKRAddress::BaseLayerMemory(read_value[0]))
                    .as_ptr(),
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX],
            );
            add_memory_expr_linear_term(
                &mut expr,
                MEMORY_TUPLE_VALUE_HIGH_TERM,
                storage
                    .get_base_layer(GKRAddress::BaseLayerMemory(read_value[1]))
                    .as_ptr(),
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX],
            );
        }
        RamWordRepresentation::U8Limbs(read_value_bytes) => {
            let byte_shift = BF::from_u32_unchecked(1 << 8);
            for (challenge_idx, low_term_idx, high_term_idx, low_offset, high_offset) in [
                (
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                    MEMORY_TUPLE_VALUE_LOW_TERM,
                    MEMORY_TUPLE_VALUE_LOW_EXTRA_TERM,
                    read_value_bytes[0],
                    read_value_bytes[1],
                ),
                (
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                    MEMORY_TUPLE_VALUE_HIGH_TERM,
                    MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM,
                    read_value_bytes[2],
                    read_value_bytes[3],
                ),
            ] {
                let challenge = external_challenges.permutation_argument_linearization_challenges
                    [challenge_idx];
                add_memory_expr_linear_term(
                    &mut expr,
                    low_term_idx,
                    storage
                        .get_base_layer(GKRAddress::BaseLayerMemory(low_offset))
                        .as_ptr(),
                    challenge,
                );
                let mut shifted_challenge = challenge;
                shifted_challenge.mul_assign_by_base(&byte_shift);
                add_memory_expr_linear_term(
                    &mut expr,
                    high_term_idx,
                    storage
                        .get_base_layer(GKRAddress::BaseLayerMemory(high_offset))
                        .as_ptr(),
                    shifted_challenge,
                );
            }
        }
    }

    if let Some((input, challenge)) = deferred_low_dynamic_term {
        push_memory_expr_linear_term(&mut expr, input, challenge);
    }

    expr
}

pub(super) enum LoweredCacheRelationOutput<E> {
    Base(GpuBaseFieldPoly<BF>),
    Ext(GpuExtensionFieldPoly<E>),
}

pub(super) fn lower_cache_relation<E>(
    layer_idx: usize,
    address: GKRAddress,
    relation: &NoFieldGKRCacheRelation,
    storage: &mut GpuGKRStorage<BF, E>,
    stage1: &GpuGKRStage1Output,
    forward_setup: &GpuGKRForwardSetup<E>,
    external_challenges: &GKRExternalChallenges<BF, E>,
    decoder_predicate_address: Option<GKRAddress>,
    _trace_len: usize,
    context: &ProverContext,
) -> CudaResult<(
    GpuGKRForwardCacheDescriptor<E>,
    LoweredCacheRelationOutput<E>,
)>
where
    E: FieldExtension<BF> + Field + SetByRef + SetByVal,
    Add: BinaryOp<E, E, E>,
    Add: BinaryOp<BF, E, E>,
    Add: BinaryOp<E, BF, E>,
    Mul: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
    Mul: BinaryOp<E, BF, E>,
    Sub: BinaryOp<E, E, E>,
    Sub: BinaryOp<E, BF, E>,
    Sub: BinaryOp<BF, BF, BF>,
{
    cache_relation_layer(layer_idx, address);
    let generic_lookup = if forward_setup.generic_lookup_len() > 0 {
        forward_setup.generic_lookup().as_ptr()
    } else {
        null()
    };

    match relation {
        NoFieldGKRCacheRelation::SingleColumnLookup {
            relation,
            range_check_width,
        } => {
            let mapping = if *range_check_width == 16 {
                stage1
                    .lookup_mappings
                    .range_check_mapping(relation.lookup_set_index)
            } else {
                stage1
                    .lookup_mappings
                    .timestamp_mapping(relation.lookup_set_index)
            };
            let setup_address = if *range_check_width == 16 {
                GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits)
            } else {
                GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp)
            };
            let setup_source_kind = GpuBaseFieldSourceKind::from_address(setup_address)
                .expect("single-column lookup setup must be virtual");
            let dst_view = storage.allocate_base_view(layer_idx, address, context)?;
            let base_output = dst_view.as_mut_ptr();
            Ok((
                GpuGKRForwardCacheDescriptor {
                    kind: GpuGKRForwardCacheKind::SingleColumnLookup,
                    mapping: mapping.as_ptr(),
                    setup_values: null(),
                    setup_source_kind,
                    base_output,
                    ..GpuGKRForwardCacheDescriptor::default()
                },
                LoweredCacheRelationOutput::Base(dst_view),
            ))
        }
        NoFieldGKRCacheRelation::VectorizedLookup(rel) => {
            let is_decoder_lookup = rel.lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX;
            let mapping = if rel.lookup_set_index != DECODER_LOOKUP_FORMAL_SET_INDEX {
                stage1.lookup_mappings.generic_mapping(rel.lookup_set_index)
            } else {
                stage1
                    .lookup_mappings
                    .decoder_mapping()
                    .expect("decoder mapping must be present for decoder lookup relation")
            };
            let dst_view = storage.allocate_ext_view(layer_idx, address, context)?;
            let ext_output = dst_view.as_mut_ptr();
            let decoder_mask = if is_decoder_lookup {
                storage
                    .get_base_layer(
                        decoder_predicate_address
                            .expect("decoder lookup requires a decoder predicate column"),
                    )
                    .as_ptr()
            } else {
                null()
            };
            Ok((
                GpuGKRForwardCacheDescriptor {
                    kind: GpuGKRForwardCacheKind::VectorizedLookup,
                    mapping: mapping.as_ptr(),
                    generic_lookup,
                    decoder_mask,
                    decoder_fill_value: if is_decoder_lookup {
                        forward_setup.decoder_lookup_fill_value_device().as_ptr()
                    } else {
                        null()
                    },
                    ext_output,
                    ..GpuGKRForwardCacheDescriptor::default()
                },
                LoweredCacheRelationOutput::Ext(dst_view),
            ))
        }
        NoFieldGKRCacheRelation::VectorizedLookupSetup(_) => {
            let dst_view = storage.allocate_ext_view(layer_idx, address, context)?;
            let ext_output = dst_view.as_mut_ptr();
            Ok((
                GpuGKRForwardCacheDescriptor {
                    kind: GpuGKRForwardCacheKind::VectorizedLookupSetup,
                    generic_lookup,
                    ext_output,
                    generic_lookup_len: forward_setup.generic_lookup_len() as u32,
                    ..GpuGKRForwardCacheDescriptor::default()
                },
                LoweredCacheRelationOutput::Ext(dst_view),
            ))
        }
        NoFieldGKRCacheRelation::MemoryTuple(rel) => {
            let dst_view = storage.allocate_ext_view(layer_idx, address, context)?;
            let ext_output = dst_view.as_mut_ptr();
            let mut descriptor = GpuGKRForwardCacheDescriptor {
                kind: GpuGKRForwardCacheKind::MemoryTuple,
                ext_output,
                constant_term: external_challenges.permutation_argument_additive_part,
                ..GpuGKRForwardCacheDescriptor::default()
            };
            let mut deferred_low_dynamic_term: Option<(*const BF, E)> = None;
            match rel.address_space {
                CompiledAddressSpaceRelationStrict::Constant(c) => {
                    descriptor.address_space_kind = GpuGKRForwardCacheAddressSpaceKind::Constant;
                    descriptor.address_space_constant = BF::from_u32_unchecked(c);
                }
                CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
                    descriptor.address_space_kind = GpuGKRForwardCacheAddressSpaceKind::Not;
                    descriptor.address_space_ptr = storage
                        .get_base_layer(GKRAddress::BaseLayerMemory(offset))
                        .as_ptr();
                }
                CompiledAddressSpaceRelationStrict::IsRam(offset) => {
                    descriptor.address_space_kind = GpuGKRForwardCacheAddressSpaceKind::Is;
                    descriptor.address_space_ptr = storage
                        .get_base_layer(GKRAddress::BaseLayerMemory(offset))
                        .as_ptr();
                }
            }

            match &rel.address {
                CompiledAddressStrict::ConstantU16(c) => {
                    let mut contribution = external_challenges
                        .permutation_argument_linearization_challenges
                        [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                    contribution.mul_assign_by_base(&BF::from_u32_unchecked(*c as u32));
                    descriptor.constant_term.add_assign(&contribution);
                }
                CompiledAddressStrict::Constant(c) => {
                    let mut contribution = external_challenges
                        .permutation_argument_linearization_challenges
                        [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                    contribution.mul_assign_by_base(&BF::from_u32_unchecked(*c));
                    descriptor.constant_term.add_assign(&contribution);
                }
                CompiledAddressStrict::U16Space(offset) => {
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_ADDRESS_LOW_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(*offset))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
                    );
                }
                CompiledAddressStrict::U32Space([low, high]) => {
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_ADDRESS_LOW_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(*low))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
                    );
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_ADDRESS_HIGH_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(*high))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX],
                    );
                }
                CompiledAddressStrict::U32SpaceSpecialIndirect {
                    low_base,
                    low_dynamic_offset,
                    low_offset,
                    high,
                } => {
                    let low_challenge = external_challenges
                        .permutation_argument_linearization_challenges
                        [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
                    let high_challenge = external_challenges
                        .permutation_argument_linearization_challenges
                        [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
                    if *low_offset != 0 {
                        let mut contribution = low_challenge;
                        contribution.mul_assign_by_base(&BF::from_u32_unchecked(*low_offset));
                        descriptor.constant_term.add_assign(&contribution);
                    }
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_ADDRESS_LOW_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(*low_base))
                            .as_ptr(),
                        low_challenge,
                    );
                    if let Some((multiplier, dynamic_offset)) = *low_dynamic_offset {
                        let mut challenge = low_challenge;
                        challenge.mul_assign_by_base(&BF::from_u32_unchecked(multiplier as u32));
                        deferred_low_dynamic_term = Some((
                            storage
                                .get_base_layer(GKRAddress::BaseLayerMemory(dynamic_offset))
                                .as_ptr(),
                            challenge,
                        ));
                    }
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_ADDRESS_HIGH_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(*high))
                            .as_ptr(),
                        high_challenge,
                    );
                }
                CompiledAddressStrict::U32SpaceGeneric(..) => {
                    unimplemented!(
                        "unsupported GPU memory tuple address relation: {:?}",
                        rel.address
                    )
                }
            }

            match &rel.timestamp {
                CompiledMemoryTimestamp::Zero => {}
                CompiledMemoryTimestamp::Normal(timestamp) => {
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_TIMESTAMP_LOW_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(timestamp[0]))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX],
                    );
                    if rel.timestamp_offset != 0 {
                        let mut contribution = external_challenges
                            .permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX];
                        contribution
                            .mul_assign_by_base(&BF::from_u32_unchecked(rel.timestamp_offset));
                        descriptor.constant_term.add_assign(&contribution);
                    }
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_TIMESTAMP_HIGH_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(timestamp[1]))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX],
                    );
                }
            }

            match rel.value {
                RamWordRepresentation::Zero => {}
                RamWordRepresentation::U16Limbs(read_value) => {
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_VALUE_LOW_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(read_value[0]))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX],
                    );
                    add_memory_tuple_linear_term(
                        &mut descriptor,
                        MEMORY_TUPLE_VALUE_HIGH_TERM,
                        storage
                            .get_base_layer(GKRAddress::BaseLayerMemory(read_value[1]))
                            .as_ptr(),
                        external_challenges.permutation_argument_linearization_challenges
                            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX],
                    );
                }
                RamWordRepresentation::U8Limbs(read_value_bytes) => {
                    let byte_shift = BF::from_u32_unchecked(1 << 8);
                    for (challenge_idx, low_term_idx, high_term_idx, low_offset, high_offset) in [
                        (
                            PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                            MEMORY_TUPLE_VALUE_LOW_TERM,
                            MEMORY_TUPLE_VALUE_LOW_EXTRA_TERM,
                            read_value_bytes[0],
                            read_value_bytes[1],
                        ),
                        (
                            PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                            MEMORY_TUPLE_VALUE_HIGH_TERM,
                            MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM,
                            read_value_bytes[2],
                            read_value_bytes[3],
                        ),
                    ] {
                        let challenge = external_challenges
                            .permutation_argument_linearization_challenges[challenge_idx];
                        add_memory_tuple_linear_term(
                            &mut descriptor,
                            low_term_idx,
                            storage
                                .get_base_layer(GKRAddress::BaseLayerMemory(low_offset))
                                .as_ptr(),
                            challenge,
                        );
                        let mut shifted_challenge = challenge;
                        shifted_challenge.mul_assign_by_base(&byte_shift);
                        add_memory_tuple_linear_term(
                            &mut descriptor,
                            high_term_idx,
                            storage
                                .get_base_layer(GKRAddress::BaseLayerMemory(high_offset))
                                .as_ptr(),
                            shifted_challenge,
                        );
                    }
                }
            }

            if let Some((input, challenge)) = deferred_low_dynamic_term {
                push_memory_tuple_linear_term(&mut descriptor, input, challenge);
            }

            Ok((descriptor, LoweredCacheRelationOutput::Ext(dst_view)))
        }
    }
}
