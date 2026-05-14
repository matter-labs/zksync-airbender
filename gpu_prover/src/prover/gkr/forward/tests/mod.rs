use super::*;
use helpers::*;

use crate::allocator::tracker::AllocationPlacement;
use crate::ops::simple::set_by_val;
use crate::primitives::field::E4;
use crate::prover::test_utils::make_test_context;

use era_cudart::memory::memory_copy_async;

use crate::upstream::{
    materialize_virtual_inits_and_teardowns_base_address_setup_poly, GateArtifacts,
};
use serial_test::serial;
use std::alloc::Global;
use worker::Worker;

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn forward_cache_single_column_lookup_synthesizes_virtual_setup_values() {
    let context = make_test_context(256, 32);
    let mappings_range16 = [0u32, 1, 65_535, 65_536, 70_000, 42, 7, 2];
    let mappings_timestamp = [0u32, 1, (1 << 19) - 1, 1 << 19, (1 << 19) + 1, 42, 7, 2];
    let trace_len = mappings_range16.len();

    let mut range16_dev = context.alloc(trace_len, AllocationPlacement::Top).unwrap();
    memory_copy_async(
        &mut range16_dev,
        &mappings_range16,
        context.get_exec_stream(),
    )
    .unwrap();
    let mut timestamp_dev = context.alloc(trace_len, AllocationPlacement::Top).unwrap();
    memory_copy_async(
        &mut timestamp_dev,
        &mappings_timestamp,
        context.get_exec_stream(),
    )
    .unwrap();
    let mut out_range16 = context.alloc(trace_len, AllocationPlacement::Top).unwrap();
    let mut out_timestamp = context.alloc(trace_len, AllocationPlacement::Top).unwrap();

    let mut batch: GpuGKRForwardCacheBatch<E4> = GpuGKRForwardCacheBatch::default();
    batch.count = 2;
    batch.descriptors[0] = GpuGKRForwardCacheDescriptor {
        kind: GpuGKRForwardCacheKind::SingleColumnLookup,
        mapping: range16_dev.as_ptr(),
        setup_source_kind: GpuBaseFieldSourceKind::VirtualRangeCheck16Bits,
        base_output: out_range16.as_mut_ptr(),
        ..GpuGKRForwardCacheDescriptor::default()
    };
    batch.descriptors[1] = GpuGKRForwardCacheDescriptor {
        kind: GpuGKRForwardCacheKind::SingleColumnLookup,
        mapping: timestamp_dev.as_ptr(),
        setup_source_kind: GpuBaseFieldSourceKind::VirtualRangeCheckTimestamp,
        base_output: out_timestamp.as_mut_ptr(),
        ..GpuGKRForwardCacheDescriptor::default()
    };

    launch_forward_cache(batch, trace_len, &context).unwrap();

    let expected_range16 = mappings_range16
        .iter()
        .map(|&value| {
            if value < (1 << 16) {
                BF::new(value)
            } else {
                BF::ZERO
            }
        })
        .collect::<Vec<_>>();
    let expected_timestamp = mappings_timestamp
        .iter()
        .map(|&value| {
            if value < (1 << 19) {
                BF::new(value)
            } else {
                BF::ZERO
            }
        })
        .collect::<Vec<_>>();

    assert_eq!(
        read_base_allocation(&out_range16, &context),
        expected_range16
    );
    assert_eq!(
        read_base_allocation(&out_timestamp, &context),
        expected_timestamp
    );
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
fn materialize_inits_and_teardowns_initial_pair_matches_cpu_for_init_and_teardown() {
    let context = make_test_context(256, 32);
    let trace_len = 1usize << 14;
    let worker = Worker::new();
    let address_high_bits = [1u32, 5u32];
    let high_bits_shift = high_bits_offset_for_inits_and_teardowns::<2>(trace_len);
    let external_challenges = sample_external_challenges(300);
    let setup = [
        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
        GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
    ];

    let (address_low, address_high) =
        materialize_virtual_inits_and_teardowns_base_address_setup_poly::<BF, Global, 2>(
            trace_len.trailing_zeros(),
            &worker,
        );
    let timestamp_low = (0..trace_len)
        .map(|idx| BF::new((100 + idx) as u32))
        .collect::<Vec<_>>();
    let timestamp_high = (0..trace_len)
        .map(|idx| BF::new((200 + idx) as u32))
        .collect::<Vec<_>>();
    let value_low = (0..trace_len)
        .map(|idx| BF::new((300 + idx) as u32))
        .collect::<Vec<_>>();
    let value_high = (0..trace_len)
        .map(|idx| BF::new((400 + idx) as u32))
        .collect::<Vec<_>>();

    let mut storage = GpuGKRStorage::<BF, E4>::default();
    storage.insert_base_field_at_layer(
        0,
        GKRAddress::BaseLayerMemory(0),
        upload_base_poly(&timestamp_low, &context),
    );
    storage.insert_base_field_at_layer(
        0,
        GKRAddress::BaseLayerMemory(1),
        upload_base_poly(&timestamp_high, &context),
    );
    storage.insert_base_field_at_layer(
        0,
        GKRAddress::BaseLayerMemory(2),
        upload_base_poly(&value_low, &context),
    );
    storage.insert_base_field_at_layer(
        0,
        GKRAddress::BaseLayerMemory(3),
        upload_base_poly(&value_high, &context),
    );

    let init_output = GpuExtensionFieldPoly::<E4>::new(
        context
            .alloc(trace_len, AllocationPlacement::BestFit)
            .unwrap(),
    );
    materialize_inits_and_teardowns_initial_pair_into(
        &storage,
        &init_output,
        &InitsOrTeardownsTimestampAndValue::Init,
        setup,
        address_high_bits,
        high_bits_shift,
        &external_challenges,
        trace_len,
        &context,
    )
    .unwrap();
    let teardown_output = GpuExtensionFieldPoly::<E4>::new(
        context
            .alloc(trace_len, AllocationPlacement::BestFit)
            .unwrap(),
    );
    materialize_inits_and_teardowns_initial_pair_into(
        &storage,
        &teardown_output,
        &InitsOrTeardownsTimestampAndValue::Teardown {
            lhs_timestamp: [0, 1],
            lhs_value: [2, 3],
            rhs_timestamp: [1, 0],
            rhs_value: [3, 2],
        },
        setup,
        address_high_bits,
        high_bits_shift,
        &external_challenges,
        trace_len,
        &context,
    )
    .unwrap();

    let expected_init = (0..trace_len)
        .map(|row| {
            let lhs = expected_init_value(
                row,
                address_high_bits[0],
                high_bits_shift,
                address_low.as_ref(),
                address_high.as_ref(),
                &external_challenges,
            );
            let rhs = expected_init_value(
                row,
                address_high_bits[1],
                high_bits_shift,
                address_low.as_ref(),
                address_high.as_ref(),
                &external_challenges,
            );
            let mut value = lhs;
            value.mul_assign(&rhs);
            value
        })
        .collect::<Vec<_>>();
    let base_layer_memory_sources = [
        timestamp_low.as_slice(),
        timestamp_high.as_slice(),
        value_low.as_slice(),
        value_high.as_slice(),
    ];
    let expected_teardown = (0..trace_len)
        .map(|row| {
            let lhs = expected_teardown_value(
                row,
                address_high_bits[0],
                high_bits_shift,
                [0, 1],
                [2, 3],
                base_layer_memory_sources,
                address_low.as_ref(),
                address_high.as_ref(),
                &external_challenges,
            );
            let rhs = expected_teardown_value(
                row,
                address_high_bits[1],
                high_bits_shift,
                [1, 0],
                [3, 2],
                base_layer_memory_sources,
                address_low.as_ref(),
                address_high.as_ref(),
                &external_challenges,
            );
            let mut value = lhs;
            value.mul_assign(&rhs);
            value
        })
        .collect::<Vec<_>>();

    assert_eq!(read_ext_poly(&init_output, &context), expected_init);
    assert_eq!(read_ext_poly(&teardown_output, &context), expected_teardown);
}

#[test]
#[serial]
fn forward_layer_dispatch_and_launch_match_expected_outputs() {
    let context = make_test_context(256, 32);
    let trace_len = 8;
    let copy_input = GKRAddress::BaseLayerMemory(0);
    let lookup_lhs = GKRAddress::BaseLayerMemory(1);
    let lookup_rhs = GKRAddress::BaseLayerWitness(0);
    let product_lhs = GKRAddress::InnerLayer {
        layer: 0,
        offset: 0,
    };
    let product_rhs = GKRAddress::InnerLayer {
        layer: 0,
        offset: 1,
    };
    let copy_output = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };
    let product_output = GKRAddress::InnerLayer {
        layer: 1,
        offset: 1,
    };
    let lookup_num_output = GKRAddress::InnerLayer {
        layer: 1,
        offset: 2,
    };
    let lookup_den_output = GKRAddress::InnerLayer {
        layer: 1,
        offset: 3,
    };

    let copy_values = (0..trace_len)
        .map(|idx| BF::new((idx + 1) as u32))
        .collect::<Vec<_>>();
    let lookup_lhs_values = [2u32, 3, 5, 7, 11, 13, 17, 19].map(BF::new);
    let lookup_rhs_values = [23u32, 29, 31, 37, 41, 43, 47, 53].map(BF::new);
    let product_lhs_values = (0..trace_len)
        .map(|idx| sample_ext(10 + idx as u32))
        .collect::<Vec<_>>();
    let product_rhs_values = (0..trace_len)
        .map(|idx| sample_ext(30 + idx as u32))
        .collect::<Vec<_>>();
    let lookup_additive_challenge = sample_ext(90);

    let mut storage = GpuGKRStorage::<BF, E4>::default();
    storage.insert_base_field_at_layer(0, copy_input, upload_base_poly(&copy_values, &context));
    storage.insert_base_field_at_layer(
        0,
        lookup_lhs,
        upload_base_poly(&lookup_lhs_values, &context),
    );
    storage.insert_base_field_at_layer(
        0,
        lookup_rhs,
        upload_base_poly(&lookup_rhs_values, &context),
    );
    storage.insert_extension_at_layer(
        0,
        product_lhs,
        upload_ext_poly(&product_lhs_values, &context),
    );
    storage.insert_extension_at_layer(
        0,
        product_rhs,
        upload_ext_poly(&product_rhs_values, &context),
    );
    attach_test_ext_output_layout(
        &mut storage,
        trace_len,
        1,
        &[product_output, lookup_num_output, lookup_den_output],
    );

    let mut lookup_additive_device = context.alloc(1, AllocationPlacement::BestFit).unwrap();
    set_by_val(
        lookup_additive_challenge,
        lookup_additive_device.deref_mut(),
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let layer = GKRLayerDescription {
        layer: 0,
        gates_with_external_connections: Vec::new(),
        cached_relations: BTreeMap::new(),
        intermediate_layer_width: None,
        gates: vec![
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::CopyInExtensionField {
                    input: copy_input,
                    output: copy_output,
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::TrivialProduct {
                    input: [product_lhs, product_rhs],
                    output: product_output,
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs {
                    input: [lookup_lhs, lookup_rhs],
                    output: [lookup_num_output, lookup_den_output],
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::EnforceConstraintsMaxQuadratic {
                    input: empty_constraints(),
                },
            },
        ],
    };
    let external_challenges = sample_external_challenges(200);
    let stage1 = GpuGKRStage1Output::empty_for_tests(&context).unwrap();
    let forward_setup = make_empty_forward_setup(trace_len, lookup_additive_challenge, &context);

    assert_forward_layer_invariants(0, 2, &layer);
    let plan = build_flat_forward_plan::<E4>(
        0,
        &layer.gates,
        &layer.gates_with_external_connections,
        &stage1,
        &forward_setup,
        None,
        &BTreeMap::new(),
        &mut storage,
        &external_challenges,
        trace_len,
        &context,
    )
    .unwrap();
    for desc in plan.descs.iter() {
        super::kernels::launch_flat_forward_layer::<E4>(desc, trace_len, &context).unwrap();
    }
    commit_flat_forward_plan(1, &mut storage, plan);
    context.get_exec_stream().synchronize().unwrap();

    let copied = storage
        .try_get_base_poly(copy_output)
        .expect("copy output must remain in base storage");
    assert!(storage
        .get_base_layer(copy_input)
        .shares_backing_with(copied));

    let expected_product = product_lhs_values
        .iter()
        .zip(product_rhs_values.iter())
        .map(|(lhs, rhs)| {
            let mut value = *lhs;
            value.mul_assign(rhs);
            value
        })
        .collect::<Vec<_>>();
    assert_eq!(
        read_ext_poly(storage.get_ext_poly(product_output), &context),
        expected_product
    );

    let mut expected_lookup_num = Vec::with_capacity(trace_len);
    let mut expected_lookup_den = Vec::with_capacity(trace_len);
    for (&lhs, &rhs) in lookup_lhs_values.iter().zip(lookup_rhs_values.iter()) {
        let mut shifted_lhs = ext_from_base::<E4>(lhs);
        shifted_lhs.add_assign(&lookup_additive_challenge);
        let mut shifted_rhs = ext_from_base::<E4>(rhs);
        shifted_rhs.add_assign(&lookup_additive_challenge);

        let mut num = shifted_lhs;
        num.add_assign(&shifted_rhs);
        let mut den = shifted_lhs;
        den.mul_assign(&shifted_rhs);

        expected_lookup_num.push(num);
        expected_lookup_den.push(den);
    }

    assert_eq!(
        read_ext_poly(storage.get_ext_poly(lookup_num_output), &context),
        expected_lookup_num
    );
    assert_eq!(
        read_ext_poly(storage.get_ext_poly(lookup_den_output), &context),
        expected_lookup_den
    );
}

#[test]
#[serial]
fn direct_no_cache_flat_forward_variants_match_expected_outputs() {
    let context = make_test_context(512, 64);
    let trace_len = 8;
    let gamma = sample_ext(700);
    let decoder_fill = sample_ext(800);
    let generic_lookup = (0..trace_len)
        .map(|idx| sample_ext(100 + idx as u32))
        .collect::<Vec<_>>();
    let mapping_0 = [0, 1, 2, 3, 4, 5, 6, 7];
    let mapping_1 = [7, 6, 5, 4, 3, 2, 1, 0];
    let mapping_2 = [1, 3, 5, 7, 0, 2, 4, 6];
    let mapping_3 = [2, 2, 3, 3, 4, 4, 5, 5];
    let decoder_mapping = [0, 1, 2, 3, 4, 5, 6, 7];
    let stage1 = GpuGKRStage1Output::with_lookup_mappings_for_tests(
        &context,
        trace_len,
        &[&mapping_0, &mapping_1, &mapping_2, &mapping_3],
        Some(&decoder_mapping),
        &[],
        &[],
    )
    .unwrap();
    let forward_setup =
        GpuGKRForwardSetup::for_test_generic_lookup(&context, gamma, &generic_lookup, decoder_fill)
            .unwrap();

    let mut storage = GpuGKRStorage::<BF, E4>::default();
    let memory_columns = (0..8)
        .map(|column| {
            (0..trace_len)
                .map(|row| BF::new((column * 17 + row + 1) as u32))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    for (column_idx, values) in memory_columns.iter().enumerate() {
        storage.insert_base_field_at_layer(
            0,
            GKRAddress::BaseLayerMemory(column_idx),
            upload_base_poly(values, &context),
        );
    }

    let decoder_predicate = GKRAddress::BaseLayerMemory(8);
    let decoder_predicate_values = [1, 0, 1, 0, 1, 0, 1, 0].map(BF::new);
    storage.insert_base_field_at_layer(
        0,
        decoder_predicate,
        upload_base_poly(&decoder_predicate_values, &context),
    );

    let dense_setup_multiplicity = GKRAddress::BaseLayerMemory(6);
    let vector_setup_multiplicity = GKRAddress::BaseLayerMemory(7);
    let unbalanced_a = GKRAddress::InnerLayer {
        layer: 0,
        offset: 0,
    };
    let unbalanced_b = GKRAddress::InnerLayer {
        layer: 0,
        offset: 1,
    };
    let unbalanced_a_values = (0..trace_len)
        .map(|idx| sample_ext(300 + idx as u32))
        .collect::<Vec<_>>();
    let unbalanced_b_values = (0..trace_len)
        .map(|idx| sample_ext(400 + idx as u32))
        .collect::<Vec<_>>();
    storage.insert_extension_at_layer(
        0,
        unbalanced_a,
        upload_ext_poly(&unbalanced_a_values, &context),
    );
    storage.insert_extension_at_layer(
        0,
        unbalanced_b,
        upload_ext_poly(&unbalanced_b_values, &context),
    );

    let out = |offset| GKRAddress::InnerLayer { layer: 1, offset };
    let pair_num = out(0);
    let pair_den = out(1);
    let dense_num = out(2);
    let dense_den = out(3);
    let minus_num = out(4);
    let minus_den = out(5);
    let unbalanced_num = out(6);
    let unbalanced_den = out(7);
    let memory_product_output = out(8);
    let memory_materialize_output = out(9);
    attach_test_ext_output_layout(
        &mut storage,
        trace_len,
        1,
        &[
            pair_num,
            pair_den,
            dense_num,
            dense_den,
            minus_num,
            minus_den,
            unbalanced_num,
            unbalanced_den,
            memory_product_output,
            memory_materialize_output,
        ],
    );

    let rel_a = NoFieldSpecialMemoryContributionRelation {
        address_space: CompiledAddressSpaceRelationStrict::Constant(7),
        address: CompiledAddressStrict::U16Space(0),
        timestamp: CompiledMemoryTimestamp::Normal([1, 2]),
        value: RamWordRepresentation::U16Limbs([3, 4]),
        timestamp_offset: 5,
    };
    let rel_b = NoFieldSpecialMemoryContributionRelation {
        address_space: CompiledAddressSpaceRelationStrict::IsRam(5),
        address: CompiledAddressStrict::U32Space([0, 1]),
        timestamp: CompiledMemoryTimestamp::Zero,
        value: RamWordRepresentation::U8Limbs([0, 1, 2, 3]),
        timestamp_offset: 0,
    };

    let layer = GKRLayerDescription {
        layer: 0,
        gates_with_external_connections: Vec::new(),
        cached_relations: BTreeMap::new(),
        intermediate_layer_width: None,
        gates: vec![
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::LookupPairFromVectorInputs {
                    input: [vector_lookup_relation(0), vector_lookup_relation(1)],
                    output: [pair_num, pair_den],
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
                    input: (
                        decoder_predicate,
                        vector_lookup_relation(DECODER_LOOKUP_FORMAL_SET_INDEX),
                    ),
                    setup: (
                        dense_setup_multiplicity,
                        Box::new([GKRAddress::placeholder()]),
                    ),
                    output: [dense_num, dense_den],
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::LookupFromVectorInputWithSetup {
                    input: vector_lookup_relation(2),
                    setup: (
                        vector_setup_multiplicity,
                        Box::new([GKRAddress::placeholder()]),
                    ),
                    output: [minus_num, minus_den],
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
                    input: [unbalanced_a, unbalanced_b],
                    remainder: vector_lookup_relation(3),
                    output: [unbalanced_num, unbalanced_den],
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::InitialGrandProductWithoutCaches {
                    input: [rel_a.clone(), rel_b.clone()],
                    output: memory_product_output,
                },
            },
            GateArtifacts {
                output_layer: 1,
                enforced_relation: NoFieldGKRRelation::MaterializeGrandProductTermExpression {
                    input: rel_a.clone(),
                    output: memory_materialize_output,
                },
            },
        ],
    };
    let external_challenges = sample_external_challenges(900);

    let plan = build_flat_forward_plan::<E4>(
        0,
        &layer.gates,
        &layer.gates_with_external_connections,
        &stage1,
        &forward_setup,
        Some(decoder_predicate),
        &BTreeMap::new(),
        &mut storage,
        &external_challenges,
        trace_len,
        &context,
    )
    .unwrap();
    assert_eq!(plan.descs.len(), 1);
    let desc = &plan.descs[0];
    assert_eq!(desc.num_mapped_e4_pairs, 1);
    assert_eq!(desc.num_mapped_cached_denses, 1);
    assert_eq!(desc.num_mapped_e4_minus_mults, 1);
    assert_eq!(desc.num_mapped_e4_unbalanceds, 1);
    assert_eq!(desc.num_memory_products, 1);
    assert_eq!(desc.num_memory_materializes, 1);

    for desc in plan.descs.iter() {
        super::kernels::launch_flat_forward_layer::<E4>(desc, trace_len, &context).unwrap();
    }
    commit_flat_forward_plan(1, &mut storage, plan);
    context.get_exec_stream().synchronize().unwrap();

    let mut expected_pair_num = Vec::with_capacity(trace_len);
    let mut expected_pair_den = Vec::with_capacity(trace_len);
    let mut expected_dense_num = Vec::with_capacity(trace_len);
    let mut expected_dense_den = Vec::with_capacity(trace_len);
    let mut expected_minus_num = Vec::with_capacity(trace_len);
    let mut expected_minus_den = Vec::with_capacity(trace_len);
    let mut expected_unbalanced_num = Vec::with_capacity(trace_len);
    let mut expected_unbalanced_den = Vec::with_capacity(trace_len);
    let mut expected_memory_product = Vec::with_capacity(trace_len);
    let mut expected_memory_materialize = Vec::with_capacity(trace_len);

    for row in 0..trace_len {
        let (num, den) = expected_lookup_ext_pair(
            generic_lookup[mapping_0[row] as usize],
            generic_lookup[mapping_1[row] as usize],
            gamma,
        );
        expected_pair_num.push(num);
        expected_pair_den.push(den);

        let decoder_value = if decoder_predicate_values[row] == BF::ZERO {
            decoder_fill
        } else {
            generic_lookup[decoder_mapping[row] as usize]
        };
        let (num, den) = expected_lookup_cached_dens_and_setup(
            decoder_predicate_values[row],
            decoder_value,
            memory_columns[dense_setup_multiplicity.offset()][row],
            generic_lookup[row],
            gamma,
        );
        expected_dense_num.push(num);
        expected_dense_den.push(den);

        let (num, den) = expected_lookup_minus_multiplicity(
            generic_lookup[mapping_2[row] as usize],
            memory_columns[vector_setup_multiplicity.offset()][row],
            generic_lookup[row],
            gamma,
        );
        expected_minus_num.push(num);
        expected_minus_den.push(den);

        let (num, den) = expected_lookup_unbalanced(
            generic_lookup[mapping_3[row] as usize],
            unbalanced_a_values[row],
            unbalanced_b_values[row],
            gamma,
        );
        expected_unbalanced_num.push(num);
        expected_unbalanced_den.push(den);

        let lhs = expected_memory_expr(&rel_a, &memory_columns, row, &external_challenges);
        let rhs = expected_memory_expr(&rel_b, &memory_columns, row, &external_challenges);
        let mut product = lhs;
        product.mul_assign(&rhs);
        expected_memory_product.push(product);
        expected_memory_materialize.push(lhs);
    }

    assert_eq!(
        read_ext_poly(storage.get_ext_poly(pair_num), &context),
        expected_pair_num
    );
    assert_eq!(
        read_ext_poly(storage.get_ext_poly(pair_den), &context),
        expected_pair_den
    );
    assert_eq!(
        read_ext_poly(storage.get_ext_poly(dense_num), &context),
        expected_dense_num
    );
    assert_eq!(
        read_ext_poly(storage.get_ext_poly(dense_den), &context),
        expected_dense_den
    );
    assert_eq!(
        read_ext_poly(storage.get_ext_poly(minus_num), &context),
        expected_minus_num
    );
    assert_eq!(
        read_ext_poly(storage.get_ext_poly(minus_den), &context),
        expected_minus_den
    );
    assert_eq!(
        read_ext_poly(storage.get_ext_poly(unbalanced_num), &context),
        expected_unbalanced_num
    );
    assert_eq!(
        read_ext_poly(storage.get_ext_poly(unbalanced_den), &context),
        expected_unbalanced_den
    );
    assert_eq!(
        read_ext_poly(storage.get_ext_poly(memory_product_output), &context),
        expected_memory_product
    );
    assert_eq!(
        read_ext_poly(storage.get_ext_poly(memory_materialize_output), &context),
        expected_memory_materialize
    );
}

#[test]
#[serial]
fn dimension_reducing_forward_tower_matches_reference() {
    let context = make_test_context(1024, 32);
    // initial_trace_log_2 = 11, final_trace_log_2 = 0 → 11 rounds total.
    // With log_block = 8: one 8-round body launch (grid 2^3 = 8) + one 3-round tail launch
    // (grid 1, parallel streams). Exercises both body and tail code paths.
    let initial_trace_log_2 = 11usize;
    let final_trace_log_2 = 0usize;
    let initial_trace_len = 1usize << initial_trace_log_2;
    let current_layer_idx = 3usize;

    let read_set = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 0,
    };
    let write_set = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 1,
    };
    let lookup16_num = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 2,
    };
    let lookup16_den = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 3,
    };
    let timestamp_num = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 4,
    };
    let timestamp_den = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 5,
    };
    let generic_num = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 6,
    };
    let generic_den = GKRAddress::InnerLayer {
        layer: current_layer_idx,
        offset: 7,
    };

    let read_values = (0..initial_trace_len)
        .map(|idx| sample_ext(100 + idx as u32))
        .collect::<Vec<_>>();
    let write_values = (0..initial_trace_len)
        .map(|idx| sample_ext(200 + idx as u32))
        .collect::<Vec<_>>();
    let lookup16_num_values = (0..initial_trace_len)
        .map(|idx| sample_ext(300 + idx as u32))
        .collect::<Vec<_>>();
    let lookup16_den_values = (0..initial_trace_len)
        .map(|idx| sample_ext(400 + idx as u32))
        .collect::<Vec<_>>();
    let timestamp_num_values = (0..initial_trace_len)
        .map(|idx| sample_ext(500 + idx as u32))
        .collect::<Vec<_>>();
    let timestamp_den_values = (0..initial_trace_len)
        .map(|idx| sample_ext(600 + idx as u32))
        .collect::<Vec<_>>();
    let generic_num_values = (0..initial_trace_len)
        .map(|idx| sample_ext(700 + idx as u32))
        .collect::<Vec<_>>();
    let generic_den_values = (0..initial_trace_len)
        .map(|idx| sample_ext(800 + idx as u32))
        .collect::<Vec<_>>();

    let mut storage = GpuGKRStorage::<BF, E4>::default();
    for (address, values) in [
        (read_set, &read_values),
        (write_set, &write_values),
        (lookup16_num, &lookup16_num_values),
        (lookup16_den, &lookup16_den_values),
        (timestamp_num, &timestamp_num_values),
        (timestamp_den, &timestamp_den_values),
        (generic_num, &generic_num_values),
        (generic_den, &generic_den_values),
    ] {
        storage.insert_extension_at_layer(
            current_layer_idx,
            address,
            upload_ext_poly(values, &context),
        );
    }

    let initial_output_map = BTreeMap::from([
        (OutputType::PermutationProduct, vec![read_set, write_set]),
        (OutputType::Lookup16Bits, vec![lookup16_num, lookup16_den]),
        (
            OutputType::LookupTimestamps,
            vec![timestamp_num, timestamp_den],
        ),
        (OutputType::GenericLookup, vec![generic_num, generic_den]),
    ]);

    let mut tracing_ranges = Vec::new();
    let (final_layer_idx, dim_reducing_inputs) = schedule_dimension_reduction_forward::<E4>(
        &mut storage,
        current_layer_idx,
        initial_output_map,
        initial_trace_log_2,
        final_trace_log_2,
        None,
        &mut tracing_ranges,
        &context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let total_rounds = initial_trace_log_2 - final_trace_log_2;
    assert_eq!(final_layer_idx, current_layer_idx + total_rounds - 1);

    // Walk every intermediate layer and compare against a fresh CPU reduction.
    let mut expected_read = read_values.clone();
    let mut expected_write = write_values.clone();
    let mut expected_lookup16 = (lookup16_num_values.clone(), lookup16_den_values.clone());
    let mut expected_timestamp = (timestamp_num_values.clone(), timestamp_den_values.clone());
    let mut expected_generic = (generic_num_values.clone(), generic_den_values.clone());

    for round_idx in 0..total_rounds {
        expected_read = expected_pairwise_reduction(&expected_read);
        expected_write = expected_pairwise_reduction(&expected_write);
        expected_lookup16 =
            expected_lookup_pair_reduction(&expected_lookup16.0, &expected_lookup16.1);
        expected_timestamp =
            expected_lookup_pair_reduction(&expected_timestamp.0, &expected_timestamp.1);
        expected_generic = expected_lookup_pair_reduction(&expected_generic.0, &expected_generic.1);

        let layer_description = dim_reducing_inputs
            .get(&(current_layer_idx + round_idx))
            .expect("dim reducing description present for round");

        let permutation_outputs = &layer_description[&OutputType::PermutationProduct].output;
        assert_eq!(
            read_ext_poly(storage.get_ext_poly(permutation_outputs[0]), &context),
            expected_read,
            "read chain mismatch at round {}",
            round_idx
        );
        assert_eq!(
            read_ext_poly(storage.get_ext_poly(permutation_outputs[1]), &context),
            expected_write,
            "write chain mismatch at round {}",
            round_idx
        );

        for (arg, expected) in [
            (OutputType::Lookup16Bits, &expected_lookup16),
            (OutputType::LookupTimestamps, &expected_timestamp),
            (OutputType::GenericLookup, &expected_generic),
        ] {
            let lookup_outputs = &layer_description[&arg].output;
            assert_eq!(
                read_ext_poly(storage.get_ext_poly(lookup_outputs[0]), &context),
                expected.0,
                "{:?} num chain mismatch at round {}",
                arg,
                round_idx
            );
            assert_eq!(
                read_ext_poly(storage.get_ext_poly(lookup_outputs[1]), &context),
                expected.1,
                "{:?} den chain mismatch at round {}",
                arg,
                round_idx
            );
        }
    }
}

mod helpers;
