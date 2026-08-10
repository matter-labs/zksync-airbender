use crate::upstream::{
    CSRamAddress, CSRamQuery, CSRamWordRepresentation, Field, GKRAddress, GKRAuxLayoutData,
    GKRCircuitArtifact, GKRMemoryLayout, NoFieldSingleColumnLookupRelation, PrimeField,
};
use crate::witness::circuit_type::UnrolledNonMemoryCircuitType;
use crate::witness::memory_unrolled::{AuxLayoutData, UnrolledMemoryLayout};
use crate::witness::trace_unrolled::{
    ExecutorFamilyDecoderData, UnrolledNonMemoryOracle, UnrolledNonMemoryTraceDevice,
};
use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::device_structures::{
    DeviceMatrixImpl, DeviceMatrixMutImpl, MutPtrAndStride, PtrAndStride,
};
use gpu_core::primitives::field::BF;
use gpu_core::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

cuda_kernel!(GenerateAddSubFixedWithMappings,
    ab_generate_memory_and_witness_values_add_sub_with_mappings_kernel(
        layout: UnrolledMemoryLayout,
        aux_layout_data: AuxLayoutData,
        oracle: UnrolledNonMemoryOracle,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        decoder_lookup_mapping: MutPtrAndStride<u32>,
        range16_mapping: MutPtrAndStride<u32>,
        timestamp_mapping: MutPtrAndStride<u32>,
        count: u32,
    )
);

cuda_kernel!(GenerateAddSubWitnessWithMappings,
    ab_generate_witness_values_add_sub_with_mappings_kernel(
        oracle: UnrolledNonMemoryOracle,
        generic_lookup_tables: PtrAndStride<BF>,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        scratch: MutPtrAndStride<BF>,
        generic_lookup_mapping: MutPtrAndStride<u32>,
        range16_mapping: MutPtrAndStride<u32>,
        timestamp_mapping: MutPtrAndStride<u32>,
        count: u32,
    )
);

cuda_kernel!(GenerateAddSubFused,
    ab_generate_memory_and_witness_values_add_sub_fused_kernel(
        layout: UnrolledMemoryLayout,
        aux_layout_data: AuxLayoutData,
        oracle: UnrolledNonMemoryOracle,
        generic_lookup_tables: PtrAndStride<BF>,
        memory: MutPtrAndStride<BF>,
        witness: MutPtrAndStride<BF>,
        scratch: MutPtrAndStride<BF>,
        generic_lookup_mapping: MutPtrAndStride<u32>,
        decoder_lookup_mapping: MutPtrAndStride<u32>,
        range16_mapping: MutPtrAndStride<u32>,
        timestamp_mapping: MutPtrAndStride<u32>,
        count: u32,
    )
);

fn relation_matches(
    relation: &NoFieldSingleColumnLookupRelation,
    lookup_set_index: usize,
    linear_terms: &[(BF, GKRAddress)],
    constant: BF,
) -> bool {
    relation.lookup_set_index == lookup_set_index
        && relation.input.linear_terms.as_ref() == linear_terms
        && relation.input.constant == constant
}

fn ram_layout_matches(circuit: &GKRCircuitArtifact<BF>) -> bool {
    let sets = &circuit.memory_layout.ram_access_sets;
    if sets.len() != 3 {
        return false;
    }

    let expected = [
        (0, 4, [0, 1], [2, 3], None),
        (1, 9, [5, 6], [7, 8], None),
        (2, 14, [10, 11], [12, 13], Some([15, 16])),
    ];

    for (query, (cycle_index, register_index, read_timestamp, read_value, write_value)) in
        sets.iter().zip(expected)
    {
        let (actual_cycle_index, address, actual_read_timestamp, actual_read_value, actual_write) =
            match query {
                CSRamQuery::Readonly(query) => (
                    query.in_cycle_write_index,
                    query.address,
                    query.read_timestamp,
                    query.read_value,
                    None,
                ),
                CSRamQuery::Write(query) => (
                    query.in_cycle_write_index,
                    query.address,
                    query.read_timestamp,
                    query.read_value,
                    Some(query.write_value),
                ),
            };
        if actual_cycle_index != cycle_index
            || address
                != CSRamAddress::RegisterOnly(crate::upstream::CSRegisterOnlyAccessAddress {
                    register_index,
                })
            || actual_read_timestamp != read_timestamp
            || actual_read_value != CSRamWordRepresentation::U16Limbs(read_value)
            || actual_write != write_value.map(CSRamWordRepresentation::U16Limbs)
        {
            return false;
        }
    }

    true
}

fn range_relations_match(circuit: &GKRCircuitArtifact<BF>) -> bool {
    let one = BF::ONE;
    let expected_addresses = [
        GKRAddress::BaseLayerWitness(11),
        GKRAddress::BaseLayerWitness(12),
        GKRAddress::BaseLayerMemory(15),
        GKRAddress::BaseLayerMemory(16),
        GKRAddress::BaseLayerMemory(22),
        GKRAddress::BaseLayerMemory(23),
    ];
    circuit.range_check_16_lookup_expressions.len() == expected_addresses.len()
        && circuit
            .range_check_16_lookup_expressions
            .iter()
            .zip(expected_addresses)
            .enumerate()
            .all(|(index, (relation, address))| {
                relation_matches(relation, index, &[(one, address)], BF::ZERO)
            })
}

fn timestamp_relations_match(circuit: &GKRCircuitArtifact<BF>) -> bool {
    let relations = &circuit.timestamp_range_check_lookup_expressions;
    if relations.len() != 8 {
        return false;
    }

    let one = BF::ONE;
    let mut minus_one = one;
    minus_one.negate();
    let two19 = BF::from_u32_unchecked(1 << 19);
    if !relation_matches(
        &relations[0],
        0,
        &[(one, GKRAddress::BaseLayerMemory(24))],
        BF::ZERO,
    ) || !relation_matches(
        &relations[1],
        1,
        &[(one, GKRAddress::BaseLayerMemory(25))],
        BF::ZERO,
    ) {
        return false;
    }

    for index in 0..3 {
        let read_timestamp = [0, 1].map(|limb| limb + index * 5);
        let borrow = GKRAddress::BaseLayerWitness(16 + index);
        let low_terms = [
            (minus_one, GKRAddress::BaseLayerMemory(20)),
            (one, GKRAddress::BaseLayerMemory(read_timestamp[0])),
            (two19, borrow),
        ];
        let high_terms = [
            (minus_one, GKRAddress::BaseLayerMemory(21)),
            (one, GKRAddress::BaseLayerMemory(read_timestamp[1])),
            (minus_one, borrow),
        ];
        let mut low_constant = BF::from_u32_unchecked(index as u32);
        low_constant.negate();
        if !relation_matches(
            &relations[2 + 2 * index],
            2 + 2 * index,
            &low_terms,
            low_constant,
        ) || !relation_matches(&relations[3 + 2 * index], 3 + 2 * index, &high_terms, two19)
        {
            return false;
        }
    }

    true
}

/// Returns true only for the committed add/sub layout whose range-check
/// mappings are emitted directly by the specialized row producers.
pub fn add_sub_layout_is_compatible(circuit: &GKRCircuitArtifact<BF>) -> bool {
    if circuit.trace_len != UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop.get_domain_size()
        || circuit.memory_layout.total_width != 26
        || circuit.witness_layout.total_width != 22
        || circuit
            .witness_layout
            .multiplicities_columns_for_range_check_16
            != (19..20)
        || circuit
            .witness_layout
            .multiplicities_columns_for_timestamp_range_check
            != (20..21)
        || circuit
            .witness_layout
            .multiplicities_columns_for_generic_lookup
            != (21..22)
        || !circuit.generic_lookups.is_empty()
        || circuit.num_generic_lookups != 1
        || !circuit.has_decoder_lookup
        || circuit.offset_for_decoder_table != 0
        || circuit.memory_layout.delegation_state.is_some()
        || !circuit
            .memory_layout
            .indirect_access_variable_offsets
            .is_empty()
        || !circuit.memory_layout.teardown_sets.is_empty()
    {
        return false;
    }

    let Some(machine_state) = circuit.memory_layout.machine_state else {
        return false;
    };
    if machine_state.execute != 17
        || machine_state.initial_state.pc != [18, 19]
        || machine_state.initial_state.timestamp != [20, 21]
        || machine_state.final_state.pc != [22, 23]
        || machine_state.final_state.timestamp != [24, 25]
    {
        return false;
    }

    let Some(decoder) = circuit.memory_layout.decoder_input.as_ref() else {
        return false;
    };
    let expected_family_bits: Box<[GKRAddress]> = (2..=10)
        .map(GKRAddress::BaseLayerWitness)
        .collect::<Vec<_>>()
        .into_boxed_slice();
    if decoder.rs1_index != 4
        || decoder.rs2_index != GKRAddress::BaseLayerMemory(9)
        || decoder.rd_index != GKRAddress::BaseLayerMemory(14)
        || decoder.circuit_family_mask_bits != expected_family_bits
        || decoder.decoder_witness_is_in_memory
        || decoder.imm != [0, 1]
        || decoder.funct3.is_some()
    {
        return false;
    }

    if !ram_layout_matches(circuit) {
        return false;
    }
    let aux = &circuit
        .aux_layout_data
        .shuffle_ram_timestamp_comparison_aux_vars;
    if aux.len() != 3
        || aux
            .iter()
            .enumerate()
            .any(|(index, set)| set.intermediate_borrow != GKRAddress::BaseLayerWitness(16 + index))
    {
        return false;
    }

    range_relations_match(circuit) && timestamp_relations_match(circuit)
}

#[allow(clippy::too_many_arguments)]
pub fn generate_add_sub_values_and_mappings_two_kernel(
    layout: &GKRMemoryLayout,
    aux_layout_data: &GKRAuxLayoutData,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    decoder_lookup_offset: u32,
    trace: &UnrolledNonMemoryTraceDevice,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    scratch: &mut impl DeviceMatrixMutImpl<BF>,
    generic_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    decoder_lookup_mapping: &mut DeviceSlice<u32>,
    range16_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    timestamp_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop.get_domain_size();
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), layout.total_width);
    assert_eq!(witness.stride(), count);
    assert_eq!(witness.cols(), 22);
    assert_eq!(scratch.stride(), count);
    assert_eq!(generic_lookup_tables.stride(), count);
    assert_eq!(generic_lookup_mapping.stride(), count);
    assert_eq!(decoder_lookup_mapping.len(), count);
    assert_eq!(range16_mapping.stride(), count);
    assert_eq!(range16_mapping.cols(), 6);
    assert_eq!(timestamp_mapping.stride(), count);
    assert_eq!(timestamp_mapping.cols(), 8);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;

    let layout = UnrolledMemoryLayout::from_parts(layout, decoder_lookup_offset);
    let aux_layout_data = aux_layout_data.into();
    let oracle = UnrolledNonMemoryOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
        default_pc_value_in_padding: UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop
            .get_default_pc_value_in_padding(),
    };
    let memory_ptr = memory.as_mut_ptr_and_stride();
    let witness_ptr = witness.as_mut_ptr_and_stride();
    let decoder_lookup_mapping_ptr =
        MutPtrAndStride::new(decoder_lookup_mapping.as_mut_ptr(), count as usize);
    let range16_mapping_ptr = range16_mapping.as_mut_ptr_and_stride();
    let timestamp_mapping_ptr = timestamp_mapping.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateAddSubFixedWithMappingsArguments::new(
        layout,
        aux_layout_data,
        oracle,
        memory_ptr,
        witness_ptr,
        decoder_lookup_mapping_ptr,
        range16_mapping_ptr,
        timestamp_mapping_ptr,
        count,
    );
    GenerateAddSubFixedWithMappingsFunction::default().launch(&config, &args)?;

    let oracle = UnrolledNonMemoryOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
        default_pc_value_in_padding: UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop
            .get_default_pc_value_in_padding(),
    };
    let generic_lookup_tables = generic_lookup_tables.as_ptr_and_stride();
    let memory = memory.as_mut_ptr_and_stride();
    let witness = witness.as_mut_ptr_and_stride();
    let scratch = scratch.as_mut_ptr_and_stride();
    let generic_lookup_mapping = generic_lookup_mapping.as_mut_ptr_and_stride();
    let range16_mapping = range16_mapping.as_mut_ptr_and_stride();
    let timestamp_mapping = timestamp_mapping.as_mut_ptr_and_stride();
    let args = GenerateAddSubWitnessWithMappingsArguments::new(
        oracle,
        generic_lookup_tables,
        memory,
        witness,
        scratch,
        generic_lookup_mapping,
        range16_mapping,
        timestamp_mapping,
        count,
    );
    GenerateAddSubWitnessWithMappingsFunction::default().launch(&config, &args)
}

#[allow(clippy::too_many_arguments)]
pub fn generate_add_sub_values_and_mappings_fused(
    layout: &GKRMemoryLayout,
    aux_layout_data: &GKRAuxLayoutData,
    decoder_table: &DeviceSlice<ExecutorFamilyDecoderData>,
    decoder_lookup_offset: u32,
    trace: &UnrolledNonMemoryTraceDevice,
    generic_lookup_tables: &impl DeviceMatrixImpl<BF>,
    memory: &mut impl DeviceMatrixMutImpl<BF>,
    witness: &mut impl DeviceMatrixMutImpl<BF>,
    scratch: &mut impl DeviceMatrixMutImpl<BF>,
    generic_lookup_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    decoder_lookup_mapping: &mut DeviceSlice<u32>,
    range16_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    timestamp_mapping: &mut impl DeviceMatrixMutImpl<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let count = UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop.get_domain_size();
    assert_eq!(memory.stride(), count);
    assert_eq!(memory.cols(), layout.total_width);
    assert_eq!(witness.stride(), count);
    assert_eq!(witness.cols(), 22);
    assert_eq!(scratch.stride(), count);
    assert_eq!(generic_lookup_tables.stride(), count);
    assert_eq!(generic_lookup_mapping.stride(), count);
    assert_eq!(decoder_lookup_mapping.len(), count);
    assert_eq!(range16_mapping.stride(), count);
    assert_eq!(range16_mapping.cols(), 6);
    assert_eq!(timestamp_mapping.stride(), count);
    assert_eq!(timestamp_mapping.cols(), 8);
    assert!(count <= u32::MAX as usize);
    let count = count as u32;

    let layout = UnrolledMemoryLayout::from_parts(layout, decoder_lookup_offset);
    let aux_layout_data = aux_layout_data.into();
    let oracle = UnrolledNonMemoryOracle {
        trace: trace.into(),
        decoder_table: decoder_table.as_ptr(),
        default_pc_value_in_padding: UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop
            .get_default_pc_value_in_padding(),
    };
    let generic_lookup_tables = generic_lookup_tables.as_ptr_and_stride();
    let memory = memory.as_mut_ptr_and_stride();
    let witness = witness.as_mut_ptr_and_stride();
    let scratch = scratch.as_mut_ptr_and_stride();
    let generic_lookup_mapping = generic_lookup_mapping.as_mut_ptr_and_stride();
    let decoder_lookup_mapping =
        MutPtrAndStride::new(decoder_lookup_mapping.as_mut_ptr(), count as usize);
    let range16_mapping = range16_mapping.as_mut_ptr_and_stride();
    let timestamp_mapping = timestamp_mapping.as_mut_ptr_and_stride();
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GenerateAddSubFusedArguments::new(
        layout,
        aux_layout_data,
        oracle,
        generic_lookup_tables,
        memory,
        witness,
        scratch,
        generic_lookup_mapping,
        decoder_lookup_mapping,
        range16_mapping,
        timestamp_mapping,
        count,
    );
    GenerateAddSubFusedFunction::default().launch(&config, &args)
}
