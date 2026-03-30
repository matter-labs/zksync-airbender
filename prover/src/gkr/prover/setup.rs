use super::*;
use crate::gkr::sumcheck::access_and_fold::BaseFieldPoly;
use crate::utils::compute_aggregated_key_value_dyn;
use cs::definitions::GKRAddress;
use cs::gkr_circuits::materialize_flattened_decoder_table_with_bitmask;
use cs::gkr_circuits::DecoderTableEntry;
use cs::gkr_circuits::ExecutorFamilyDecoderData;
use cs::tables::{TableDriver, TableType};
use fft::{materialize_powers_serial_starting_with_one, GoodAllocator};
use std::sync::Arc;

pub struct GKRSetup<F: PrimeField + TwoAdicField> {
    pub hypercube_evals: Vec<Arc<Box<[F]>>>,
}

impl<F: PrimeField + TwoAdicField> GKRSetup<F> {
    pub fn construct(
        table_driver: &TableDriver<F>,
        decoder_table: &[Option<ExecutorFamilyDecoderData>],
        trace_len: usize,
        compiled_circuit: &GKRCircuitArtifact<F>,
    ) -> Self {
        // we always have range-check 16 bits and timestamp limbs
        let total_width = compiled_circuit.generic_lookup_tables_width;

        println!(
            "Creating setup with {} columns in total ({} generic lookup tables width)",
            total_width, compiled_circuit.generic_lookup_tables_width
        );

        let mut result = Vec::with_capacity(total_width);

        for _ in 0..compiled_circuit.generic_lookup_tables_width {
            result.push(vec![F::ZERO; trace_len].into_boxed_slice());
        }

        let table_encoding_capacity_per_tuple = trace_len;
        let total_tables_size = table_driver.total_tables_len + decoder_table.len();

        assert_eq!(total_tables_size, compiled_circuit.total_tables_size);

        let mut num_table_subsets = total_tables_size / table_encoding_capacity_per_tuple;
        if total_tables_size % table_encoding_capacity_per_tuple != 0 {
            num_table_subsets += 1;
        }
        assert_eq!(num_table_subsets, 1);

        // dump tables
        let all_generic_tables =
            table_driver.dump_tables(compiled_circuit.generic_lookup_tables_width);

        assert_eq!(
            all_generic_tables.len(),
            compiled_circuit.offset_for_decoder_table,
        );

        // no parallelism for now

        if compiled_circuit.tables_ids_in_generic_lookups == false {
            assert!(all_generic_tables.len() == 0 || decoder_table.len() == 0);
        }

        for row_idx in 0..all_generic_tables.len() {
            let row = &all_generic_tables[row_idx];
            assert_eq!(
                row.len(),
                compiled_circuit.generic_lookup_tables_width,
                "padded table row from the driver is {}, but setup has {} columns for it",
                row.len(),
                compiled_circuit.generic_lookup_tables_width
            );
            for column in 0..compiled_circuit.generic_lookup_tables_width {
                result[column][row_idx] = all_generic_tables[row_idx][column];
            }
        }
        let offset = compiled_circuit.offset_for_decoder_table;

        if decoder_table.len() > 0 {
            let table = materialize_flattened_decoder_table_with_bitmask(
                decoder_table,
                &compiled_circuit.decode_table_columns_mask,
            );
            let width = table[0].len();
            let padding_len = if compiled_circuit.tables_ids_in_generic_lookups {
                compiled_circuit.generic_lookup_tables_width - 1
            } else {
                compiled_circuit.generic_lookup_tables_width
            };
            for row_idx in 0..decoder_table.len() {
                let row = &table[row_idx];
                assert_eq!(row.len(), width);
                assert!(row.len() <= padding_len);

                for column in 0..width {
                    result[column][row_idx + offset] = table[row_idx][column];
                }
                for column in width..padding_len {
                    result[column][row_idx + offset] = F::ZERO;
                }
                if compiled_circuit.tables_ids_in_generic_lookups {
                    assert!(result.last().unwrap()[row_idx + offset].is_zero());
                    result.last_mut().unwrap()[row_idx + offset] =
                        F::from_u32_unchecked(TableType::Decoder as u32);
                }
            }
        }

        Self {
            hypercube_evals: result.into_iter().map(Arc::new).collect(),
        }
    }

    // NOTE: all(!) preprocessed lookups do NOT include additive constants,
    // and gates directly add it
    pub fn preprocess_generic_lookups<E: FieldExtension<F> + Field>(
        &self,
        compiled_circuit: &GKRCircuitArtifact<F>,
        lookup_alpha: E,
        trace_len: usize,
        gkr_storage: &mut GKRStorage<F, E>,
        worker: &Worker,
    ) -> (Box<[E]>, E) {
        // fill storage with all setup columns
        for (i, eval) in self.hypercube_evals.iter().enumerate() {
            gkr_storage.insert_base_field_at_layer(
                0,
                GKRAddress::Setup(i),
                BaseFieldPoly::from_arc(Arc::clone(eval)),
            );
        }

        self.preprocess_generic_lookup_tables::<E, Global>(
            compiled_circuit,
            lookup_alpha,
            trace_len,
            worker,
        )
    }

    pub(crate) fn preprocess_generic_lookup_tables<
        E: FieldExtension<F> + Field,
        A: GoodAllocator,
    >(
        &self,
        compiled_circuit: &GKRCircuitArtifact<F>,
        lookup_alpha: E,
        trace_len: usize,
        worker: &Worker,
    ) -> (Box<[E], A>, E) {
        let generic_lookup_tables_size = compiled_circuit.total_tables_size;
        assert!(trace_len >= generic_lookup_tables_size);

        if generic_lookup_tables_size > 0 {
            let challenge_powers = materialize_powers_serial_starting_with_one::<E, Global>(
                lookup_alpha,
                compiled_circuit.generic_lookup_tables_width,
            );
            assert_eq!(
                challenge_powers.len(),
                compiled_circuit.generic_lookup_tables_width
            );

            let mut generic_lookup_preprocessing = Vec::with_capacity_in(trace_len, A::default());
            let mut dst = &mut generic_lookup_preprocessing.spare_capacity_mut()
                [..generic_lookup_tables_size];

            worker.scope(generic_lookup_tables_size, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                    let (chunk, rest) = dst.split_at_mut(chunk_size);
                    dst = rest;
                    let challenge_powers_ref = &challenge_powers;

                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        let mut buffer = vec![F::ZERO; compiled_circuit.generic_lookup_tables_width];
                        for i in 0..chunk_size {
                            buffer.fill(F::ZERO);
                            let absolute_row_idx = chunk_start + i;

                            for column in 0..compiled_circuit.generic_lookup_tables_width {
                                buffer[column] = self.hypercube_evals[column][absolute_row_idx];
                            }

                            let denom = compute_aggregated_key_value_dyn(
                                buffer[0],
                                &buffer[1..],
                                &challenge_powers_ref[1..],
                                &E::ZERO,
                            );

                            chunk[i].write(denom);
                        }
                    });
                }

                assert!(dst.is_empty(), "expected to process all elements, but got {} remaining. Work size is {}, num cores = {}", dst.len(), generic_lookup_tables_size, worker.get_num_cores());
            });

            unsafe {
                generic_lookup_preprocessing.set_len(generic_lookup_tables_size);
            }

            let decoder_lookup_fill_value = if compiled_circuit.tables_ids_in_generic_lookups {
                assert!(DecoderTableEntry::<F>::from_executor_family_data(
                    0,
                    &ExecutorFamilyDecoderData::default()
                )
                .flatten()
                .iter()
                .all(|el| el.is_zero()));
                // no additive constant, modeled as all zeroes, just last column has table ID
                let mut t =
                    lookup_alpha.pow((compiled_circuit.generic_lookup_tables_width - 1) as u32);
                t.mul_assign_by_base(&F::from_u32_unchecked(TableType::Decoder as u32));

                t
            } else {
                E::ZERO
            };

            (
                generic_lookup_preprocessing.into_boxed_slice(),
                decoder_lookup_fill_value,
            )
        } else {
            (Vec::new_in(A::default()).into_boxed_slice(), E::ZERO)
        }
    }

    // pub(crate) fn preprocess_range_check_16_table<
    //     E: FieldExtension<F> + Field,
    //     A: GoodAllocator,
    // >(
    //     trace_len: usize,
    //     lookup_argument_gamma: E,
    //     worker: &Worker,
    // ) -> Box<[E], A> {
    //     assert!(trace_len >= 1 << 16);

    //     let mut range_check_16_preprocessing: Vec<E, A> =
    //         Vec::with_capacity_in(1 << 16, A::default());
    //     let mut dst = &mut range_check_16_preprocessing.spare_capacity_mut()[..(1 << 16)];

    //     unsafe {
    //         worker.scope(1 << 16, |scope, geometry| {
    //             for thread_idx in 0..geometry.len() {
    //                 let chunk_size = geometry.get_chunk_size(thread_idx);
    //                 let chunk_start = geometry.get_chunk_start_pos(thread_idx);

    //                 let (chunk, rest) = dst.split_at_mut(chunk_size);
    //                 dst = rest;

    //                 Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
    //                     let mut batch_inverse_buffer = vec![E::ZERO; chunk.len()];
    //                     for i in 0..chunk_size {
    //                         let absolute_table_idx = chunk_start + i;

    //                         // range check 16
    //                         let mut denom = lookup_argument_gamma;
    //                         denom.add_assign_base(&F::from_u32_unchecked(absolute_table_idx as u32));

    //                         chunk[i].write(denom);
    //                     }

    //                     // batch inverse
    //                     let buffer = chunk.assume_init_mut();
    //                     let all_nonzero = batch_inverse_checked(buffer, &mut batch_inverse_buffer);
    //                     assert!(all_nonzero);
    //                 });
    //             }

    //             assert!(dst.is_empty(), "expected to process all elements, but got {} remaining. Work size is {}, num cores = {}", dst.len(), 1 << 16, worker.get_num_cores());
    //         });
    //     }

    //     unsafe {
    //         range_check_16_preprocessing.set_len(1 << 16);
    //     }

    //     range_check_16_preprocessing.into_boxed_slice()
    // }

    // pub(crate) fn preprocess_timestamp_range_check_table<
    //     E: FieldExtension<F> + Field,
    //     A: GoodAllocator,
    // >(
    //     trace_len: usize,
    //     lookup_argument_gamma: E,
    //     worker: &Worker,
    // ) -> Box<[E], A> {
    //     // and timestamp range checks
    //     assert!(trace_len >= 1 << TIMESTAMP_COLUMNS_NUM_BITS);

    //     let mut timestamp_range_check_preprocessing: Vec<E, A> =
    //         Vec::with_capacity_in(1 << TIMESTAMP_COLUMNS_NUM_BITS, A::default());
    //     let mut dst = &mut timestamp_range_check_preprocessing.spare_capacity_mut()
    //         [..(1 << TIMESTAMP_COLUMNS_NUM_BITS)];

    //     unsafe {
    //         worker.scope(1 << TIMESTAMP_COLUMNS_NUM_BITS, |scope, geometry| {
    //             for thread_idx in 0..geometry.len() {
    //                 let chunk_size = geometry.get_chunk_size(thread_idx);
    //                 let chunk_start = geometry.get_chunk_start_pos(thread_idx);

    //                 let (chunk, rest) = dst.split_at_mut(chunk_size);
    //                 dst = rest;

    //                 Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
    //                     let mut batch_inverse_buffer = vec![E::ZERO; chunk.len()];
    //                     for i in 0..chunk_size {
    //                         let absolute_table_idx = chunk_start + i;

    //                         // range check
    //                         let mut denom = lookup_argument_gamma;
    //                         denom.add_assign_base(&F::from_u32_unchecked(absolute_table_idx as u32));

    //                         chunk[i].write(denom);
    //                     }

    //                     // batch inverse
    //                     let buffer = chunk.assume_init_mut();
    //                     let all_nonzero = batch_inverse_checked(buffer, &mut batch_inverse_buffer);
    //                     assert!(all_nonzero);
    //                 });
    //             }

    //             assert!(dst.is_empty(), "expected to process all elements, but got {} remaining. Work size is {}, num cores = {}", dst.len(), 1 << TIMESTAMP_COLUMNS_NUM_BITS, worker.get_num_cores());
    //         });
    //     }

    //     unsafe {
    //         timestamp_range_check_preprocessing.set_len(1 << TIMESTAMP_COLUMNS_NUM_BITS);
    //     }

    //     timestamp_range_check_preprocessing.into_boxed_slice()
    // }

    pub fn commit<T: ColumnMajorMerkleTreeConstructor<F>>(
        &self,
        twiddles: &Twiddles<F, Global>,
        lde_factor: usize,
        whir_first_fold_step_log2: usize,
        tree_cap_size: usize,
        trace_len_log2: usize,
        worker: &Worker,
    ) -> ColumnMajorBaseOracleForLDE<F, T>
    where
        [(); F::DEGREE]: Sized,
    {
        let inputs: Vec<_> = self.hypercube_evals.iter().map(|el| &el[..]).collect();
        use crate::gkr::prover::stage1::commit_trace_part;

        commit_trace_part(
            &inputs,
            twiddles,
            lde_factor,
            whir_first_fold_step_log2,
            tree_cap_size,
            trace_len_log2,
            worker,
        )
    }
}
