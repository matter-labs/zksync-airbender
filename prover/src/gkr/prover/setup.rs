use super::*;
use crate::gkr::sumcheck::access_and_fold::BaseFieldPoly;
use crate::prover_stages::compute_aggregated_key_value_dyn;
use common_constants::TIMESTAMP_COLUMNS_NUM_BITS;
use cs::definitions::GKRAddress;
use cs::machine::ops::unrolled::{
    materialize_flattened_decoder_table_with_bitmask, DecoderTableEntry,
};
use cs::tables::{TableDriver, TableType};
use fft::{materialize_powers_serial_starting_with_one, GoodAllocator};
use field::batch_inverse_checked;

pub struct GKRSetupPrecomputations<
    F: PrimeField + TwoAdicField,
    T: ColumnMajorMerkleTreeConstructor<F>,
> {
    pub ldes: Vec<BaseFieldCosetBoundTracePart<F>>,
    pub trees: Vec<T>,
}

impl<F: PrimeField + TwoAdicField, T: ColumnMajorMerkleTreeConstructor<F>>
    GKRSetupPrecomputations<F, T>
{
    pub fn from_tables_and_trace_len(
        table_driver: &TableDriver<F>,
        trace_len: usize,
        compiled_circuit: &GKRCircuitArtifact<F>,
        twiddles: &Twiddles<F, Global>,
        // lde_precomputations: &LdePrecomputations<A>,
        lde_factor: usize,
        tree_cap_size: usize,
        worker: &Worker,
    ) -> Self {
        Self::from_tables_and_trace_len_with_decoder_table(
            table_driver,
            &[],
            trace_len,
            compiled_circuit,
            twiddles,
            // lde_precomputations,
            lde_factor,
            tree_cap_size,
            worker,
        )
    }

    pub fn from_tables_and_trace_len_with_decoder_table(
        table_driver: &TableDriver<F>,
        decoder_table: &[Option<DecoderTableEntry<F>>],
        trace_len: usize,
        compiled_circuit: &GKRCircuitArtifact<F>,
        twiddles: &Twiddles<F, Global>,
        // lde_precomputations: &LdePrecomputations<A>,
        lde_factor: usize,
        tree_cap_size: usize,
        worker: &Worker,
    ) -> Self {
        assert!(trace_len.is_power_of_two());

        let optimal_folding =
            crate::definitions::OPTIMAL_FOLDING_PROPERTIES[trace_len.trailing_zeros() as usize];
        let subtree_cap_size = (1 << optimal_folding.total_caps_size_log2) / lde_factor;
        assert!(subtree_cap_size > 0);

        let main_domain_trace = Self::get_main_domain_trace(
            table_driver,
            decoder_table,
            trace_len,
            compiled_circuit,
            // worker,
        );

        Self {
            ldes: vec![main_domain_trace],
            trees: vec![],
        }

        // // NOTE: we do not use last row of the setup (and in general last of of circuit),
        // // and we must adjust it to be c0 == 0
        // adjust_to_zero_c0_var_length(&mut main_domain_trace, 0..setup_layout.total_width, worker);

        // // LDE them
        // let ldes = compute_wide_ldes(
        //     main_domain_trace,
        //     twiddles,
        //     lde_precomputations,
        //     0,
        //     lde_factor,
        //     worker,
        // );

        // assert_eq!(ldes.len(), lde_factor);

        // let mut trees = Vec::with_capacity(lde_factor);
        // for domain in ldes.iter() {
        //     let tree = T::construct_for_coset(&domain.trace, subtree_cap_size, true, worker);
        //     trees.push(tree);
        // }

        // Self { ldes, trees }
    }

    pub fn get_main_domain_trace(
        table_driver: &TableDriver<F>,
        decoder_table: &[Option<DecoderTableEntry<F>>],
        trace_len: usize,
        compiled_circuit: &GKRCircuitArtifact<F>,
        // worker: &Worker,
    ) -> BaseFieldCosetBoundTracePart<F> {
        // we always have range-check 16 bits and timestamp limbs
        let total_width = 2 + compiled_circuit.generic_lookup_tables_width;

        println!("Creating setup with {} columns in total", total_width);

        let mut trace = BaseFieldCosetBoundTracePart {
            columns: Vec::with_capacity(total_width),
            offset: F::ONE,
        };
        for _ in 0..(2 + compiled_circuit.generic_lookup_tables_width) {
            trace
                .columns
                .push(vec![F::ZERO; trace_len].into_boxed_slice());
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
        let all_generic_tables = table_driver.dump_tables();

        let range_check_16_table_content: Vec<_> = (0..(1 << 16))
            .map(|el| F::from_u32_unchecked(el as u32))
            .collect();

        let timestamp_range_check_table: Vec<_> = (0..(1 << TIMESTAMP_COLUMNS_NUM_BITS))
            .map(|el| F::from_u32_unchecked(el as u32))
            .collect();

        assert_eq!(
            all_generic_tables.len(),
            compiled_circuit.offset_for_decoder_table,
        );

        let range_check_16_table_content_len = range_check_16_table_content.len();
        let range_check_16_table_content_ref = &range_check_16_table_content;

        let timestamp_range_check_table_content_len = timestamp_range_check_table.len();
        let timestamp_range_check_table_content_ref = &timestamp_range_check_table;

        let all_generic_tables_ref = &all_generic_tables;

        // no parallelism for now

        trace.columns[0][..(1 << 16)].copy_from_slice(&range_check_16_table_content);
        trace.columns[1][..(1 << TIMESTAMP_COLUMNS_NUM_BITS)]
            .copy_from_slice(&timestamp_range_check_table);

        if compiled_circuit.tables_ids_in_generic_lookups == false {
            assert!(all_generic_tables.len() == 0 || decoder_table.len() == 0);
        }

        for row_idx in 0..all_generic_tables.len() {
            for column in 0..3 {
                trace.columns[2 + column][row_idx] = all_generic_tables[row_idx][column];
            }
            if compiled_circuit.tables_ids_in_generic_lookups {
                trace.columns.last_mut().unwrap()[row_idx] = all_generic_tables[row_idx][3];
            }
        }
        let offset = compiled_circuit.offset_for_decoder_table;

        if decoder_table.len() > 0 {
            let table = materialize_flattened_decoder_table_with_bitmask(
                decoder_table,
                &compiled_circuit.decode_table_columns_mask,
            );
            let width = table[0].len();
            assert_eq!(
                2 + width + (compiled_circuit.tables_ids_in_generic_lookups as usize),
                trace.columns.len()
            );
            for row_idx in 0..decoder_table.len() {
                for column in 0..width {
                    trace.columns[2 + column][row_idx + offset] = table[row_idx][column];
                }
                if compiled_circuit.tables_ids_in_generic_lookups {
                    trace.columns.last_mut().unwrap()[row_idx + offset] =
                        F::from_u32_unchecked(TableType::Decoder as u32);
                }
            }
        }

        trace
    }

    pub fn preprocess_lookups<E: FieldExtension<F> + Field>(
        &self,
        compiled_circuit: &GKRCircuitArtifact<F>,
        lookup_alpha: E,
        lookup_gamma: E,
        trace_len: usize,
        gkr_storage: &mut GKRStorage<F, E>,
        worker: &Worker,
    ) -> (Box<[E]>, Box<[E]>, Box<[E]>) {
        // fill storage
        {
            let mut range_check_16_poly = vec![F::ZERO; trace_len].into_boxed_slice();
            for (i, el) in range_check_16_poly[..(1 << 16)].iter_mut().enumerate() {
                *el = F::from_u32_unchecked(i as u32);
            }
            let mut timestamp_range_check_poly = vec![F::ZERO; trace_len].into_boxed_slice();
            for (i, el) in timestamp_range_check_poly[..(1 << TIMESTAMP_COLUMNS_NUM_BITS)].iter_mut().enumerate() {
                *el = F::from_u32_unchecked(i as u32);
            }

            gkr_storage.insert_base_field_at_layer(0, GKRAddress::Setup(0), BaseFieldPoly::new(range_check_16_poly));
            gkr_storage.insert_base_field_at_layer(0, GKRAddress::Setup(1), BaseFieldPoly::new(timestamp_range_check_poly));
        }

        (
            Self::preprocess_range_check_16_table::<E, Global>(trace_len, lookup_gamma, worker),
            Self::preprocess_timestamp_range_check_table::<E, Global>(
                trace_len,
                lookup_gamma,
                worker,
            ),
            self.preprocess_lookup_tables::<E, Global>(
                compiled_circuit,
                lookup_alpha,
                lookup_gamma,
                trace_len,
                worker,
            ),
        )
    }

    pub(crate) fn preprocess_lookup_tables<E: FieldExtension<F> + Field, A: GoodAllocator>(
        &self,
        compiled_circuit: &GKRCircuitArtifact<F>,
        lookup_alpha: E,
        lookup_gamma: E,
        trace_len: usize,
        worker: &Worker,
    ) -> Box<[E], A> {
        let generic_lookup_tables_size = compiled_circuit.total_tables_size;
        assert!(trace_len >= generic_lookup_tables_size);

        if generic_lookup_tables_size > 0 {
            assert!(self.ldes[0].columns.len() > 2);
            let challenge_powers = materialize_powers_serial_starting_with_one::<E, Global>(
                lookup_alpha,
                self.ldes[0].columns.len() - 2,
            );

            let mut generic_lookup_preprocessing = Vec::with_capacity_in(trace_len, A::default());
            let mut dst = &mut generic_lookup_preprocessing.spare_capacity_mut()
                [..generic_lookup_tables_size];

            unsafe {
                worker.scope(generic_lookup_tables_size, |scope, geometry| {
                    for thread_idx in 0..geometry.len() {
                        let chunk_size = geometry.get_chunk_size(thread_idx);
                        let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                        let (chunk, rest) = dst.split_at_mut(chunk_size);
                        dst = rest;
                        let challenge_powers_ref = &challenge_powers;

                        Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                            let mut batch_inverse_buffer = vec![E::ZERO; chunk.len()];
                            let mut buffer = vec![F::ZERO; compiled_circuit.generic_lookup_tables_width];
                            for i in 0..chunk_size {
                                buffer.fill(F::ZERO);
                                let absolute_row_idx = chunk_start + i;

                                for column in 0..compiled_circuit.generic_lookup_tables_width {
                                    buffer[column] = self.ldes[0].columns[2 + column][absolute_row_idx];
                                }

                                let denom = compute_aggregated_key_value_dyn(
                                    buffer[0],
                                    &buffer[1..],
                                    &challenge_powers_ref[1..],
                                    &lookup_gamma,
                                );

                                chunk[i].write(denom);
                            }

                            // batch inverse
                            let buffer = chunk.assume_init_mut();
                            let all_nonzero = batch_inverse_checked(buffer, &mut batch_inverse_buffer);
                            assert!(all_nonzero);
                        });
                    }

                    assert!(dst.is_empty(), "expected to process all elements, but got {} remaining. Work size is {}, num cores = {}", dst.len(), generic_lookup_tables_size, worker.get_num_cores());
                });
            }

            unsafe {
                generic_lookup_preprocessing.set_len(generic_lookup_tables_size);
            }

            generic_lookup_preprocessing.into_boxed_slice()
        } else {
            Vec::new_in(A::default()).into_boxed_slice()
        }
    }

    pub(crate) fn preprocess_range_check_16_table<
        E: FieldExtension<F> + Field,
        A: GoodAllocator,
    >(
        trace_len: usize,
        lookup_argument_gamma: E,
        worker: &Worker,
    ) -> Box<[E], A> {
        assert!(trace_len >= 1 << 16);

        let mut range_check_16_preprocessing: Vec<E, A> =
            Vec::with_capacity_in(1 << 16, A::default());
        let mut dst = &mut range_check_16_preprocessing.spare_capacity_mut()[..(1 << 16)];

        unsafe {
            worker.scope(1 << 16, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                    let (chunk, rest) = dst.split_at_mut(chunk_size);
                    dst = rest;

                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        let mut batch_inverse_buffer = vec![E::ZERO; chunk.len()];
                        for i in 0..chunk_size {
                            let absolute_table_idx = chunk_start + i;

                            // range check 16
                            let mut denom = lookup_argument_gamma;
                            denom.add_assign_base(&F::from_u32_unchecked(absolute_table_idx as u32));

                            chunk[i].write(denom);
                        }

                        // batch inverse
                        let buffer = chunk.assume_init_mut();
                        let all_nonzero = batch_inverse_checked(buffer, &mut batch_inverse_buffer);
                        assert!(all_nonzero);
                    });
                }

                assert!(dst.is_empty(), "expected to process all elements, but got {} remaining. Work size is {}, num cores = {}", dst.len(), 1 << 16, worker.get_num_cores());
            });
        }

        unsafe {
            range_check_16_preprocessing.set_len(1 << 16);
        }

        range_check_16_preprocessing.into_boxed_slice()
    }

    pub(crate) fn preprocess_timestamp_range_check_table<
        E: FieldExtension<F> + Field,
        A: GoodAllocator,
    >(
        trace_len: usize,
        lookup_argument_gamma: E,
        worker: &Worker,
    ) -> Box<[E], A> {
        // and timestamp range checks
        assert!(trace_len >= 1 << TIMESTAMP_COLUMNS_NUM_BITS);

        let mut timestamp_range_check_preprocessing: Vec<E, A> =
            Vec::with_capacity_in(1 << TIMESTAMP_COLUMNS_NUM_BITS, A::default());
        let mut dst = &mut timestamp_range_check_preprocessing.spare_capacity_mut()
            [..(1 << TIMESTAMP_COLUMNS_NUM_BITS)];

        unsafe {
            worker.scope(1 << TIMESTAMP_COLUMNS_NUM_BITS, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                    let (chunk, rest) = dst.split_at_mut(chunk_size);
                    dst = rest;

                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        let mut batch_inverse_buffer = vec![E::ZERO; chunk.len()];
                        for i in 0..chunk_size {
                            let absolute_table_idx = chunk_start + i;

                            // range check
                            let mut denom = lookup_argument_gamma;
                            denom.add_assign_base(&F::from_u32_unchecked(absolute_table_idx as u32));

                            chunk[i].write(denom);
                        }

                        // batch inverse
                        let buffer = chunk.assume_init_mut();
                        let all_nonzero = batch_inverse_checked(buffer, &mut batch_inverse_buffer);
                        assert!(all_nonzero);
                    });
                }

                assert!(dst.is_empty(), "expected to process all elements, but got {} remaining. Work size is {}, num cores = {}", dst.len(), 1 << TIMESTAMP_COLUMNS_NUM_BITS, worker.get_num_cores());
            });
        }

        unsafe {
            timestamp_range_check_preprocessing.set_len(1 << TIMESTAMP_COLUMNS_NUM_BITS);
        }

        timestamp_range_check_preprocessing.into_boxed_slice()
    }
}
