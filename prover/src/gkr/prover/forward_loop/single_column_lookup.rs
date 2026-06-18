use super::*;
use cs::definitions::gkr::NoFieldSingleColumnLookupRelation;

pub(crate) fn evaluate_single_column_lookup_relation<
    F: PrimeField,
    E: FieldExtension<F> + Field,
>(
    layer_idx: usize,
    output: GKRAddress,
    relation: &NoFieldSingleColumnLookupRelation,
    range_check_width: u32,
    gkr_storage: &mut GKRStorage<F, E>,
    witness_trace: &mut GKRFullWitnessTrace<F, Global, Global>,
    trace_len: usize,
    worker: &Worker,
) {
    let mut destination = Box::<[F], Global>::new_uninit_slice(trace_len);
    if range_check_width == 16 {
        let source = std::mem::replace(
            &mut witness_trace.range_check_16_lookup_mapping[relation.lookup_set_index],
            vec![],
        );
        let source_ref = &source;
        assert_eq!(source.len(), trace_len);
        apply_row_wise::<_, E>(
            vec![&mut destination],
            vec![],
            trace_len,
            worker,
            |dest, _, chunk_start, chunk_size| {
                assert_eq!(dest.len(), 1);
                let mut dest = dest;
                let dest = dest.pop().unwrap();
                for i in 0..chunk_size {
                    let row = chunk_start + i;
                    let mapping_index = source_ref[row];

                    #[cfg(feature = "gkr_self_checks")]
                    {
                        let value =
                            evaluate_linear_relation_at_row(&relation.input, &*gkr_storage, row)
                                .as_u32_reduced();
                        assert!(
                            value < 1 << 16,
                            "range check 16 bits: value is {} at row {} for relation {:?}",
                            value,
                            row,
                            relation
                        );
                        assert_eq!(value as u16, mapping_index);
                    }

                    let mapped_value = F::from_u32_unchecked(mapping_index as u32);
                    dest[i].write(mapped_value);
                }
            },
        );
    } else if range_check_width == TIMESTAMP_COLUMNS_NUM_BITS {
        let source = std::mem::replace(
            &mut witness_trace.timestamp_range_check_lookup_mapping[relation.lookup_set_index],
            vec![],
        );
        let source_ref = &source;
        assert_eq!(source.len(), trace_len);
        apply_row_wise::<_, E>(
            vec![&mut destination],
            vec![],
            trace_len,
            worker,
            |dest, _, chunk_start, chunk_size| {
                assert_eq!(dest.len(), 1);
                let mut dest = dest;
                let dest = dest.pop().unwrap();
                for i in 0..chunk_size {
                    let row = chunk_start + i;
                    let mapping_index = source_ref[row];

                    #[cfg(feature = "gkr_self_checks")]
                    {
                        let value =
                            evaluate_linear_relation_at_row(&relation.input, &*gkr_storage, row)
                                .as_u32_reduced();
                        assert!(
                            value < 1 << TIMESTAMP_COLUMNS_NUM_BITS,
                            "timestamp range check: value is {} at row {} for relation {:?}",
                            value,
                            row,
                            relation
                        );
                        assert_eq!(value, mapping_index);
                    }

                    let mapped_value = F::from_u32_unchecked(mapping_index);
                    dest[i].write(mapped_value);
                }
            },
        );
    } else {
        unreachable!(
            "unknown single column lookup range check of width {}",
            range_check_width
        );
    };

    let destination = unsafe { destination.assume_init() };
    output.assert_as_layer(layer_idx);
    gkr_storage.insert_base_field_at_layer(layer_idx, output, BaseFieldPoly::new(destination));
}
