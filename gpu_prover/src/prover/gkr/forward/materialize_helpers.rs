use super::*;

fn flatten_inits_or_teardowns_linear_combination<E: Field + FieldExtension<BF>>(
    timestamps_and_values: Option<([usize; 2], [usize; 2])>,
    setup: [GKRAddress; 2],
    address_high_bits: u32,
    address_high_bits_shift: u32,
    external_challenges: &GKRExternalChallenges<BF, E>,
) -> (BTreeMap<GKRAddress, E>, E) {
    let mut result = BTreeMap::new();
    let mut constant_term = external_challenges.permutation_argument_additive_part;
    constant_term.add_assign_base(&BF::from_u32_unchecked(AddressSpaceType::RAM as u32));

    {
        let challenge = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX];
        assert!(result.insert(setup[0], challenge).is_none());
    }
    {
        let mut challenge = external_challenges.permutation_argument_linearization_challenges
            [PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX];
        assert!(result.insert(setup[1], challenge).is_none());
        challenge.mul_assign_by_base(&BF::from_u32_unchecked(
            address_high_bits << address_high_bits_shift,
        ));
        constant_term.add_assign(&challenge);
    }

    if let Some((timestamps, values)) = timestamps_and_values {
        for (idx, address) in [
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
                GKRAddress::BaseLayerMemory(timestamps[0]),
            ),
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
                GKRAddress::BaseLayerMemory(timestamps[1]),
            ),
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
                GKRAddress::BaseLayerMemory(values[0]),
            ),
            (
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
                GKRAddress::BaseLayerMemory(values[1]),
            ),
        ] {
            let challenge = external_challenges.permutation_argument_linearization_challenges[idx];
            assert!(result.insert(address, challenge).is_none());
        }
    }

    (result, constant_term)
}

fn materialize_linear_base_combination<E>(
    storage: &GpuGKRStorage<BF, E>,
    terms: &BTreeMap<GKRAddress, E>,
    constant_term: E,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<DeviceAllocation<E>>
where
    E: Field + FieldExtension<BF> + GpuGKRVirtualBaseAccumKernelSet + SetByVal,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
{
    let mut dst = context.alloc(trace_len, AllocationPlacement::BestFit)?;
    set_by_val(constant_term, dst.deref_mut(), context.get_exec_stream())?;
    for (&address, &challenge) in terms.iter() {
        if let Some(source) = storage.try_get_base_poly(address) {
            scale_and_add_base_column(&mut dst, source, challenge, context)?;
        } else if let Some(source_kind) = GpuBaseFieldSourceKind::from_address(address) {
            launch_virtual_base_accum(
                source_kind,
                challenge,
                dst.as_mut_ptr(),
                trace_len,
                context,
            )?;
        } else {
            panic!(
                "base linear combination expects real or virtual base source, got {:?}",
                address
            );
        }
    }
    Ok(dst)
}

pub(super) fn materialize_inits_and_teardowns_initial_pair_into<E>(
    storage: &GpuGKRStorage<BF, E>,
    dst: &GpuExtensionFieldPoly<E>,
    timestamp_and_value: &InitsOrTeardownsTimestampAndValue,
    setup: [GKRAddress; 2],
    address_high_bits: [u32; 2],
    address_high_bits_shift: u32,
    external_challenges: &GKRExternalChallenges<BF, E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: Field + FieldExtension<BF> + GpuGKRVirtualBaseAccumKernelSet + SetByVal,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
    Mul: BinaryOp<E, E, E>,
{
    assert_eq!(
        dst.len(),
        trace_len,
        "InitsOrTeardownsInitialPair destination view must span trace_len"
    );
    let lhs_timestamps_and_values = match timestamp_and_value {
        InitsOrTeardownsTimestampAndValue::Init => None,
        InitsOrTeardownsTimestampAndValue::Teardown {
            lhs_timestamp,
            lhs_value,
            ..
        } => Some((*lhs_timestamp, *lhs_value)),
    };
    let rhs_timestamps_and_values = match timestamp_and_value {
        InitsOrTeardownsTimestampAndValue::Init => None,
        InitsOrTeardownsTimestampAndValue::Teardown {
            rhs_timestamp,
            rhs_value,
            ..
        } => Some((*rhs_timestamp, *rhs_value)),
    };

    let (lhs_terms, lhs_constant) = flatten_inits_or_teardowns_linear_combination(
        lhs_timestamps_and_values,
        setup,
        address_high_bits[0],
        address_high_bits_shift,
        external_challenges,
    );
    let (rhs_terms, rhs_constant) = flatten_inits_or_teardowns_linear_combination(
        rhs_timestamps_and_values,
        setup,
        address_high_bits[1],
        address_high_bits_shift,
        external_challenges,
    );
    let lhs =
        materialize_linear_base_combination(storage, &lhs_terms, lhs_constant, trace_len, context)?;
    let rhs =
        materialize_linear_base_combination(storage, &rhs_terms, rhs_constant, trace_len, context)?;
    // SAFETY: `dst` was just allocated for this consumer; no other clone of
    // this view is scheduled to write before the mul completes.
    let mut dst_chunk = unsafe { dst.as_mut_chunk_unchecked() };
    mul(
        &DeviceVectorChunk::new(&lhs, 0, trace_len),
        &DeviceVectorChunk::new(&rhs, 0, trace_len),
        &mut dst_chunk,
        context.get_exec_stream(),
    )
}

fn scale_and_add_base_column<E>(
    dst: &mut DeviceAllocation<E>,
    source: &GpuBaseFieldPoly<BF>,
    scalar: E,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: FieldExtension<BF> + Field + SetByVal,
    Add: BinaryOp<E, E, E>,
    Mul: BinaryOp<BF, E, E>,
{
    let mut weighted = context.alloc(source.len(), AllocationPlacement::BestFit)?;
    set_by_val(scalar, weighted.deref_mut(), context.get_exec_stream())?;
    mul_into_y(
        &source.as_device_chunk(),
        weighted.deref_mut(),
        context.get_exec_stream(),
    )?;
    add_into_y(
        &DeviceVectorChunk::new(&weighted, 0, source.len()),
        dst.deref_mut(),
        context.get_exec_stream(),
    )
}

pub(super) fn scale_and_add_base_column_in_place<D>(
    dst: &mut D,
    source: &GpuBaseFieldPoly<BF>,
    scalar: BF,
    context: &ProverContext,
) -> CudaResult<()>
where
    D: DeviceMatrixChunkMutImpl<BF> + ?Sized,
    Add: BinaryOp<BF, BF, BF>,
    Mul: BinaryOp<BF, BF, BF>,
{
    let mut weighted = context.alloc(source.len(), AllocationPlacement::BestFit)?;
    set_by_val(scalar, weighted.deref_mut(), context.get_exec_stream())?;
    mul_into_y(
        &source.as_device_chunk(),
        weighted.deref_mut(),
        context.get_exec_stream(),
    )?;
    add_into_y(
        &DeviceVectorChunk::new(&weighted, 0, source.len()),
        dst,
        context.get_exec_stream(),
    )
}
