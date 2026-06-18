use crate::gkr::sumcheck::evaluation_kernels::{
    lookup_base_minus_multiplicity_base, lookup_base_pair, lookup_rational_with_unbalanced_base,
    BatchedGKRKernel,
};
use cs::definitions::gkr::NoFieldSingleColumnLookupRelation;

use super::*;

pub fn forward_evaluate_lookup_from_base_inputs_with_setup<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    input: GKRAddress,
    setup: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    lookup_additive_challenge: E,
    worker: &Worker,
) {
    let kernel =
        lookup_base_minus_multiplicity_base::LookupBaseMinusMultiplicityByBaseGKRRelation {
            input,
            setup,
            outputs,
            lookup_additive_challenge,
            _marker: core::marker::PhantomData,
        };
    kernel.evaluate_forward_over_storage(gkr_storage, expected_output_layer, trace_len, worker);
}

pub fn forward_evaluate_lookup_base_inputs_pair<F: PrimeField, E: FieldExtension<F> + Field>(
    inputs: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    lookup_additive_challenge: E,
    worker: &Worker,
) {
    let kernel = lookup_base_pair::LookupBasePairGKRRelation {
        inputs,
        outputs,
        lookup_additive_challenge,
        _marker: core::marker::PhantomData,
    };
    kernel.evaluate_forward_over_storage(gkr_storage, expected_output_layer, trace_len, worker);
}

// 1/(b+gamma) + 1/(d + gamma) -> (b + d + 2*gamma), (b+gamma)*(d+gamma)
pub fn forward_evaluate_lookup_base_inputs_pair_range_check_16<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    inputs: &[NoFieldSingleColumnLookupRelation; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    lookup_additive_challenge: E,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    worker: &Worker,
) {
    let mut num_destination = Box::<[E], Global>::new_uninit_slice(trace_len);
    let mut den_destination = Box::<[E], Global>::new_uninit_slice(trace_len);

    let [lhs, rhs] = inputs;
    let lhs_source = std::mem::replace(
        &mut witness_trace.range_check_16_lookup_mapping[lhs.lookup_set_index],
        vec![],
    );
    let rhs_source = std::mem::replace(
        &mut witness_trace.range_check_16_lookup_mapping[rhs.lookup_set_index],
        vec![],
    );
    let lhs_source_ref = &lhs_source;
    let rhs_source_ref = &rhs_source;
    assert_eq!(lhs_source_ref.len(), trace_len);
    assert_eq!(rhs_source_ref.len(), trace_len);

    apply_row_wise::<F, _>(
        vec![],
        vec![&mut num_destination, &mut den_destination],
        trace_len,
        worker,
        |_, ext_dest, chunk_start, chunk_size| {
            assert_eq!(ext_dest.len(), 2);
            let [num_dest, den_dest] = ext_dest.try_into().unwrap();
            for i in 0..chunk_size {
                let row = chunk_start + i;
                let lhs_mapping_index = lhs_source_ref[row];
                let rhs_mapping_index = rhs_source_ref[row];

                #[cfg(feature = "gkr_self_checks")]
                {
                    for (rel, mapping_index) in [(lhs, lhs_mapping_index), (rhs, rhs_mapping_index)]
                    {
                        let value = evaluate_linear_relation_at_row(&rel.input, &*gkr_storage, row)
                            .as_u32_reduced();
                        assert!(
                            value < 1 << 16,
                            "range check 16 bits: value is {} at row {} for relation {:?}",
                            value,
                            row,
                            lhs
                        );
                        assert_eq!(value as u16, mapping_index);
                    }
                }

                let mut lhs = lookup_additive_challenge;
                lhs.add_assign_base(&F::from_u32_unchecked(lhs_mapping_index as u32));

                let mut rhs = lookup_additive_challenge;
                rhs.add_assign_base(&F::from_u32_unchecked(rhs_mapping_index as u32));

                let mut num = lhs;
                num.add_assign(&rhs);

                let mut den = lhs;
                den.mul_assign(&rhs);

                num_dest[i].write(num);
                den_dest[i].write(den);
            }
        },
    );

    for (output, destination) in outputs
        .into_iter()
        .zip([num_destination, den_destination].into_iter())
    {
        let destination = unsafe { destination.assume_init() };
        output.assert_as_layer(expected_output_layer);
        gkr_storage.insert_extension_at_layer(
            expected_output_layer,
            output,
            ExtensionFieldPoly::new(destination),
        );
    }
}

// 1/(b+gamma) + 1/(d + gamma) -> (b + d + 2*gamma), (b+gamma)*(d+gamma)
pub fn forward_evaluate_lookup_base_inputs_pair_timestamp_range_check<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    inputs: &[NoFieldSingleColumnLookupRelation; 2],
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    lookup_additive_challenge: E,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    worker: &Worker,
) {
    let mut num_destination = Box::<[E], Global>::new_uninit_slice(trace_len);
    let mut den_destination = Box::<[E], Global>::new_uninit_slice(trace_len);

    let [lhs, rhs] = inputs;
    let lhs_source = std::mem::replace(
        &mut witness_trace.timestamp_range_check_lookup_mapping[lhs.lookup_set_index],
        vec![],
    );
    let rhs_source = std::mem::replace(
        &mut witness_trace.timestamp_range_check_lookup_mapping[rhs.lookup_set_index],
        vec![],
    );
    let lhs_source_ref = &lhs_source;
    let rhs_source_ref = &rhs_source;
    assert_eq!(lhs_source_ref.len(), trace_len);
    assert_eq!(rhs_source_ref.len(), trace_len);

    apply_row_wise::<F, _>(
        vec![],
        vec![&mut num_destination, &mut den_destination],
        trace_len,
        worker,
        |_, ext_dest, chunk_start, chunk_size| {
            assert_eq!(ext_dest.len(), 2);
            let [num_dest, den_dest] = ext_dest.try_into().unwrap();
            for i in 0..chunk_size {
                let row = chunk_start + i;
                let lhs_mapping_index = lhs_source_ref[row];
                let rhs_mapping_index = rhs_source_ref[row];

                #[cfg(feature = "gkr_self_checks")]
                {
                    for (rel, mapping_index) in [(lhs, lhs_mapping_index), (rhs, rhs_mapping_index)]
                    {
                        let value = evaluate_linear_relation_at_row(&rel.input, &*gkr_storage, row)
                            .as_u32_reduced();
                        assert!(
                            value < 1 << TIMESTAMP_COLUMNS_NUM_BITS,
                            "timestamp range check: value is {} at row {} for relation {:?}",
                            value,
                            row,
                            lhs
                        );
                        assert_eq!(value, mapping_index);
                    }
                }

                let mut lhs = lookup_additive_challenge;
                lhs.add_assign_base(&F::from_u32_unchecked(lhs_mapping_index as u32));

                let mut rhs = lookup_additive_challenge;
                rhs.add_assign_base(&F::from_u32_unchecked(rhs_mapping_index as u32));

                let mut num = lhs;
                num.add_assign(&rhs);

                let mut den = lhs;
                den.mul_assign(&rhs);

                num_dest[i].write(num);
                den_dest[i].write(den);
            }
        },
    );

    for (output, destination) in outputs
        .into_iter()
        .zip([num_destination, den_destination].into_iter())
    {
        let destination = unsafe { destination.assume_init() };
        output.assert_as_layer(expected_output_layer);
        gkr_storage.insert_extension_at_layer(
            expected_output_layer,
            output,
            ExtensionFieldPoly::new(destination),
        );
    }
}

pub fn forward_evaluate_lookup_rational_with_base_remainder_input<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    inputs: [GKRAddress; 2],
    remainder: GKRAddress,
    outputs: [GKRAddress; 2],
    gkr_storage: &mut GKRStorage<F, E>,
    expected_output_layer: usize,
    trace_len: usize,
    lookup_additive_challenge: E,
    worker: &Worker,
) {
    let kernel =
        lookup_rational_with_unbalanced_base::LookupRationalPairWithUnbalancedBaseGKRRelation {
            inputs,
            remainder,
            outputs,
            lookup_additive_challenge,
            _marker: core::marker::PhantomData,
        };
    kernel.evaluate_forward_over_storage(gkr_storage, expected_output_layer, trace_len, worker);
}
