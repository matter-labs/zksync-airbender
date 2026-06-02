use super::super::*;

pub(super) fn ext_from_base<E>(value: BF) -> E
where
    E: FieldExtension<BF> + Field,
{
    let mut result = E::ZERO;
    result.add_assign_base(&value);
    result
}

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::field::E4;

use crate::upstream::NoFieldMaxQuadraticConstraintsGKRRelation;
use era_cudart::memory::memory_copy_async;

pub(super) fn sample_ext(seed: u32) -> E4 {
    E4::from_array_of_base([
        BF::new(seed),
        BF::new(seed + 1),
        BF::new(seed + 2),
        BF::new(seed + 3),
    ])
}

pub(super) fn sample_external_challenges(seed: u32) -> GKRExternalChallenges<BF, E4> {
    GKRExternalChallenges {
        permutation_argument_linearization_challenges: std::array::from_fn(|idx| {
            sample_ext(seed + 10 + idx as u32)
        }),
        permutation_argument_additive_part: sample_ext(seed),
        _marker: std::marker::PhantomData,
    }
}

pub(super) fn upload_base_poly(values: &[BF], context: &ProverContext) -> GpuBaseFieldPoly<BF> {
    let mut device = context
        .alloc(values.len(), AllocationPlacement::Top)
        .unwrap();
    memory_copy_async(&mut device, values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    GpuBaseFieldPoly::new(device)
}

pub(super) fn upload_ext_poly(values: &[E4], context: &ProverContext) -> GpuExtensionFieldPoly<E4> {
    let mut device = context
        .alloc(values.len(), AllocationPlacement::Top)
        .unwrap();
    memory_copy_async(&mut device, values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    GpuExtensionFieldPoly::new(device)
}

pub(super) fn read_ext_poly(poly: &GpuExtensionFieldPoly<E4>, context: &ProverContext) -> Vec<E4> {
    let mut host = vec![E4::ZERO; poly.len()];
    memory_copy_async(&mut host, poly.as_device_slice(), context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

pub(super) fn read_base_allocation(
    values: &DeviceAllocation<BF>,
    context: &ProverContext,
) -> Vec<BF> {
    let mut host = vec![BF::ZERO; values.len()];
    memory_copy_async(&mut host, values, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

pub(super) fn attach_test_ext_output_layout(
    storage: &mut GpuGKRStorage<BF, E4>,
    trace_len: usize,
    output_layer: usize,
    outputs: &[GKRAddress],
) {
    use crate::prover::gkr::gkr_address_audit::AddressClass;
    use crate::prover::gkr::storage_layout::{
        FieldType, GpuGKRLayerLayout, GpuGKRStorageLayout, StorageSlot,
    };

    assert!(trace_len.is_power_of_two());
    let log2_stride = trace_len.trailing_zeros();
    let mut layers = vec![GpuGKRLayerLayout::default(); output_layer + 1];
    let mut index = BTreeMap::new();
    for (poly_idx, output) in outputs.iter().enumerate() {
        index.insert(
            *output,
            (
                AddressClass::ThisLayerInnerLayerWrite,
                FieldType::Ext,
                poly_idx as u32,
            ),
        );
    }
    let mut slot_poly_counts = BTreeMap::new();
    slot_poly_counts.insert(
        StorageSlot {
            class: AddressClass::ThisLayerInnerLayerWrite,
            field: FieldType::Ext,
        },
        outputs.len() as u32,
    );
    layers[output_layer] = GpuGKRLayerLayout {
        index,
        slot_poly_counts,
        log2_stride,
    };
    storage.set_layout(Arc::new(GpuGKRStorageLayout {
        trace_len,
        artifact_log2_stride: log2_stride,
        layers,
        aliases: BTreeMap::new(),
    }));
}

/// Install a storage layout that covers the input layer (`initial_layer_idx`)
/// plus every dim-reducing tower output layer. Mirrors
/// `gpu_gkr_model::storage_layout::append_tower_layers` so `schedule_dimension_reduction_forward`
/// can `allocate_ext_view` into each tower round.
pub(super) fn attach_test_dim_reducing_tower_layout(
    storage: &mut GpuGKRStorage<BF, E4>,
    initial_layer_idx: usize,
    initial_output_map: &BTreeMap<OutputType, Vec<GKRAddress>>,
    initial_trace_log_2: usize,
    final_trace_log_2: usize,
) {
    use crate::prover::gkr::gkr_address_audit::AddressClass;
    use crate::prover::gkr::storage_layout::{
        FieldType, GpuGKRLayerLayout, GpuGKRStorageLayout, StorageSlot,
    };

    let trace_len = 1usize << initial_trace_log_2;
    let total_rounds = initial_trace_log_2.saturating_sub(final_trace_log_2);
    let total_layers = initial_layer_idx + total_rounds + 1;
    let mut layers = vec![GpuGKRLayerLayout::default(); total_layers];

    // Register the test fixture inputs at `initial_layer_idx`. The test
    // inserts them into storage via `insert_extension_at_layer`; the layout
    // entry lets `allocate_ext_view` resolve them back when the dim-reducing
    // scheduler walks the input set.
    let mut initial_layer_layout = GpuGKRLayerLayout {
        log2_stride: initial_trace_log_2 as u32,
        ..GpuGKRLayerLayout::default()
    };
    let mut initial_poly_count = 0u32;
    for inputs in initial_output_map.values() {
        for input in inputs.iter() {
            initial_layer_layout.index.insert(
                *input,
                (
                    AddressClass::ThisLayerInnerLayerWrite,
                    FieldType::Ext,
                    initial_poly_count,
                ),
            );
            initial_poly_count += 1;
        }
    }
    if initial_poly_count > 0 {
        initial_layer_layout.slot_poly_counts.insert(
            StorageSlot {
                class: AddressClass::ThisLayerInnerLayerWrite,
                field: FieldType::Ext,
            },
            initial_poly_count,
        );
    }
    layers[initial_layer_idx] = initial_layer_layout;

    // Build per-tower-round layouts. Mirrors `append_tower_layers` exactly.
    let mut layer_inputs: BTreeMap<OutputType, Vec<GKRAddress>> = initial_output_map.clone();
    let mut current_layer_idx = initial_layer_idx;
    for round in 0..total_rounds {
        let output_layer = current_layer_idx + 1;
        let input_size_log_2 = initial_trace_log_2 - round;
        let output_log2_stride = (input_size_log_2 - 1) as u32;

        let mut new_layer_layout = GpuGKRLayerLayout {
            log2_stride: output_log2_stride,
            ..GpuGKRLayerLayout::default()
        };
        let mut output_idx: u32 = 0;
        let mut next_inputs: BTreeMap<OutputType, Vec<GKRAddress>> = BTreeMap::new();
        for (arg_type, inputs) in layer_inputs.iter() {
            assert_eq!(
                inputs.len(),
                2,
                "dim reduction tower expects 2 inputs per slot for {:?}",
                arg_type,
            );
            let out_a = GKRAddress::InnerLayer {
                layer: output_layer,
                offset: output_idx as usize,
            };
            let poly_idx_a = output_idx;
            output_idx += 1;
            let out_b = GKRAddress::InnerLayer {
                layer: output_layer,
                offset: output_idx as usize,
            };
            let poly_idx_b = output_idx;
            output_idx += 1;

            new_layer_layout.index.insert(
                out_a,
                (
                    AddressClass::ThisLayerInnerLayerWrite,
                    FieldType::Ext,
                    poly_idx_a,
                ),
            );
            new_layer_layout.index.insert(
                out_b,
                (
                    AddressClass::ThisLayerInnerLayerWrite,
                    FieldType::Ext,
                    poly_idx_b,
                ),
            );
            next_inputs.insert(*arg_type, vec![out_a, out_b]);
        }
        if output_idx > 0 {
            new_layer_layout.slot_poly_counts.insert(
                StorageSlot {
                    class: AddressClass::ThisLayerInnerLayerWrite,
                    field: FieldType::Ext,
                },
                output_idx,
            );
        }
        layers[output_layer] = new_layer_layout;
        layer_inputs = next_inputs;
        current_layer_idx += 1;
    }

    storage.set_layout(Arc::new(GpuGKRStorageLayout {
        trace_len,
        artifact_log2_stride: initial_trace_log_2 as u32,
        layers,
        aliases: BTreeMap::new(),
    }));
}

pub(super) fn empty_constraints() -> NoFieldMaxQuadraticConstraintsGKRRelation {
    NoFieldMaxQuadraticConstraintsGKRRelation {
        quadratic_terms: Vec::new().into_boxed_slice(),
        linear_terms: Vec::new().into_boxed_slice(),
        constants: Vec::new().into_boxed_slice(),
    }
}

pub(super) fn make_empty_forward_setup(
    trace_len: usize,
    lookup_additive_challenge: E4,
    context: &ProverContext,
) -> GpuGKRForwardSetup<E4> {
    let mut d_lookup_challenges: crate::primitives::context::DeviceAllocation<E4> = context
        .alloc(3, crate::allocator::tracker::AllocationPlacement::BestFit)
        .unwrap();
    era_cudart::memory::memory_copy_async(
        &mut d_lookup_challenges,
        &[E4::ONE, lookup_additive_challenge, E4::ZERO][..],
        context.get_exec_stream(),
    )
    .unwrap();
    crate::prover::gkr::forward::kernels::schedule_lookup_gamma_consts_prelude_e4(
        d_lookup_challenges[1..2].as_ptr(),
        context,
    )
    .unwrap();
    crate::prover::gkr::setup::schedule_forward_setup_for_shape::<E4>(
        None,
        trace_len,
        0,
        0,
        false,
        d_lookup_challenges,
        context,
    )
    .unwrap()
}

pub(super) fn expected_pairwise_reduction(values: &[E4]) -> Vec<E4> {
    values
        .chunks_exact(2)
        .map(|chunk| {
            let mut value = chunk[0];
            value.mul_assign(&chunk[1]);
            value
        })
        .collect()
}

pub(super) fn expected_lookup_pair_reduction(num: &[E4], den: &[E4]) -> (Vec<E4>, Vec<E4>) {
    let mut reduced_num = Vec::with_capacity(num.len() / 2);
    let mut reduced_den = Vec::with_capacity(den.len() / 2);

    for (num_pair, den_pair) in num.chunks_exact(2).zip(den.chunks_exact(2)) {
        let mut left_term = num_pair[0];
        left_term.mul_assign(&den_pair[1]);
        let mut right_term = num_pair[1];
        right_term.mul_assign(&den_pair[0]);
        left_term.add_assign(&right_term);
        reduced_num.push(left_term);

        let mut den_value = den_pair[0];
        den_value.mul_assign(&den_pair[1]);
        reduced_den.push(den_value);
    }

    (reduced_num, reduced_den)
}

pub(super) fn vector_lookup_relation(
    lookup_set_index: usize,
) -> cs::definitions::gkr::NoFieldVectorLookupRelation {
    cs::definitions::gkr::NoFieldVectorLookupRelation {
        columns: Box::new([]),
        lookup_set_index,
    }
}

pub(super) fn add_base(mut value: E4, base: BF) -> E4 {
    value.add_assign_base(&base);
    value
}

pub(super) fn add_scaled_base(mut value: E4, challenge: E4, base: BF) -> E4 {
    let mut contribution = challenge;
    contribution.mul_assign_by_base(&base);
    value.add_assign(&contribution);
    value
}

pub(super) fn shifted(value: E4, gamma: E4) -> E4 {
    let mut shifted = value;
    shifted.add_assign(&gamma);
    shifted
}

pub(super) fn expected_lookup_ext_pair(b: E4, d: E4, gamma: E4) -> (E4, E4) {
    let shifted_b = shifted(b, gamma);
    let shifted_d = shifted(d, gamma);
    let mut num = shifted_b;
    num.add_assign(&shifted_d);
    let mut den = shifted_b;
    den.mul_assign(&shifted_d);
    (num, den)
}

pub(super) fn expected_lookup_minus_multiplicity(b: E4, c: BF, d: E4, gamma: E4) -> (E4, E4) {
    let shifted_b = shifted(b, gamma);
    let shifted_d = shifted(d, gamma);
    let mut c_shifted_b = shifted_b;
    c_shifted_b.mul_assign_by_base(&c);
    let mut num = shifted_d;
    num.sub_assign(&c_shifted_b);
    let mut den = shifted_b;
    den.mul_assign(&shifted_d);
    (num, den)
}

pub(super) fn expected_lookup_cached_dens_and_setup(
    a: BF,
    b: E4,
    c: BF,
    d: E4,
    gamma: E4,
) -> (E4, E4) {
    let shifted_b = shifted(b, gamma);
    let shifted_d = shifted(d, gamma);
    let mut lhs = shifted_d;
    lhs.mul_assign_by_base(&a);
    let mut rhs = shifted_b;
    rhs.mul_assign_by_base(&c);
    lhs.sub_assign(&rhs);
    let mut den = shifted_b;
    den.mul_assign(&shifted_d);
    (lhs, den)
}

pub(super) fn expected_lookup_unbalanced(d: E4, a: E4, b: E4, gamma: E4) -> (E4, E4) {
    let shifted_d = shifted(d, gamma);
    let mut num = a;
    num.mul_assign(&shifted_d);
    num.add_assign(&b);
    let mut den = b;
    den.mul_assign(&shifted_d);
    (num, den)
}

pub(super) fn expected_memory_expr(
    rel: &NoFieldSpecialMemoryContributionRelation,
    memory_columns: &[Vec<BF>],
    row: usize,
    external_challenges: &GKRExternalChallenges<BF, E4>,
) -> E4 {
    let mut value = external_challenges.permutation_argument_additive_part;
    match rel.address_space {
        CompiledAddressSpaceRelationStrict::Constant(c) => {
            value = add_base(value, BF::from_u32_unchecked(c));
        }
        CompiledAddressSpaceRelationStrict::IsRam(offset) => {
            value = add_base(value, memory_columns[offset][row]);
        }
        CompiledAddressSpaceRelationStrict::IsRegister(offset) => {
            let mut is_register = BF::ONE;
            is_register.sub_assign(&memory_columns[offset][row]);
            value = add_base(value, is_register);
        }
    }

    match &rel.address {
        CompiledAddressStrict::ConstantU16(c) => {
            value = add_scaled_base(
                value,
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
                BF::from_u32_unchecked(*c as u32),
            );
        }
        CompiledAddressStrict::Constant(c) => {
            value = add_scaled_base(
                value,
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
                BF::from_u32_unchecked(*c),
            );
        }
        CompiledAddressStrict::U16Space(offset) => {
            value = add_scaled_base(
                value,
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
                memory_columns[*offset][row],
            );
        }
        CompiledAddressStrict::U32Space([low, high]) => {
            value = add_scaled_base(
                value,
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX],
                memory_columns[*low][row],
            );
            value = add_scaled_base(
                value,
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX],
                memory_columns[*high][row],
            );
        }
        CompiledAddressStrict::U32SpaceSpecialIndirect { .. }
        | CompiledAddressStrict::U32SpaceGeneric(..) => {
            unreachable!("not used by this flat-forward test")
        }
    }

    match rel.timestamp {
        CompiledMemoryTimestamp::Zero => {}
        CompiledMemoryTimestamp::Normal(timestamp) => {
            value = add_scaled_base(
                value,
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX],
                memory_columns[timestamp[0]][row],
            );
            if rel.timestamp_offset != 0 {
                value = add_scaled_base(
                    value,
                    external_challenges.permutation_argument_linearization_challenges
                        [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX],
                    BF::from_u32_unchecked(rel.timestamp_offset),
                );
            }
            value = add_scaled_base(
                value,
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX],
                memory_columns[timestamp[1]][row],
            );
        }
    }

    match rel.value {
        RamWordRepresentation::Zero => {}
        RamWordRepresentation::U16Limbs(limbs) => {
            value = add_scaled_base(
                value,
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX],
                memory_columns[limbs[0]][row],
            );
            value = add_scaled_base(
                value,
                external_challenges.permutation_argument_linearization_challenges
                    [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX],
                memory_columns[limbs[1]][row],
            );
        }
        RamWordRepresentation::U8Limbs(bytes) => {
            let byte_shift = BF::from_u32_unchecked(1 << 8);
            for (challenge_idx, low_offset, high_offset) in [
                (
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                    bytes[0],
                    bytes[1],
                ),
                (
                    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                    bytes[2],
                    bytes[3],
                ),
            ] {
                let challenge = external_challenges.permutation_argument_linearization_challenges
                    [challenge_idx];
                value = add_scaled_base(value, challenge, memory_columns[low_offset][row]);
                let mut shifted_challenge = challenge;
                shifted_challenge.mul_assign_by_base(&byte_shift);
                value = add_scaled_base(value, shifted_challenge, memory_columns[high_offset][row]);
            }
        }
    }

    value
}

pub(super) fn expected_init_value(
    row: usize,
    address_high_bits: u32,
    high_bits_shift: u32,
    address_low: &[BF],
    address_high: &[BF],
    external_challenges: &GKRExternalChallenges<BF, E4>,
) -> E4 {
    let mut result = external_challenges.permutation_argument_additive_part;
    result.add_assign_base(&BF::from_u32_unchecked(AddressSpaceType::RAM as u32));

    let mut address_low_term = external_challenges.permutation_argument_linearization_challenges
        [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
    address_low_term.mul_assign_by_base(&address_low[row]);
    result.add_assign(&address_low_term);

    let mut address_high_value = address_high[row];
    address_high_value.add_assign(&BF::from_u32_unchecked(
        address_high_bits << high_bits_shift,
    ));
    let mut address_high_term = external_challenges.permutation_argument_linearization_challenges
        [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
    address_high_term.mul_assign_by_base(&address_high_value);
    result.add_assign(&address_high_term);

    result
}

pub(super) fn expected_teardown_value(
    row: usize,
    address_high_bits: u32,
    high_bits_shift: u32,
    timestamp_offsets: [usize; 2],
    value_offsets: [usize; 2],
    base_layer_memory_sources: [&[BF]; 4],
    address_low: &[BF],
    address_high: &[BF],
    external_challenges: &GKRExternalChallenges<BF, E4>,
) -> E4 {
    let mut result = expected_init_value(
        row,
        address_high_bits,
        high_bits_shift,
        address_low,
        address_high,
        external_challenges,
    );

    for (idx, offset) in [
        (
            PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
            timestamp_offsets[0],
        ),
        (
            PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
            timestamp_offsets[1],
        ),
        (
            PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
            value_offsets[0],
        ),
        (
            PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
            value_offsets[1],
        ),
    ] {
        let mut term = external_challenges.permutation_argument_linearization_challenges[idx];
        term.mul_assign_by_base(&base_layer_memory_sources[offset][row]);
        result.add_assign(&term);
    }

    result
}
