use super::*;
use crate::gkr::sumcheck::access_and_fold::BaseFieldPoly;
use crate::utils::compute_aggregated_key_value_dyn;
use cs::definitions::GKRAddress;
use cs::gkr_circuits::DecoderTableEntry;
use cs::gkr_circuits::ExecutorFamilyDecoderData;
use cs::tables::{LookupWrapper, TableDriver, TableType};
use fft::{materialize_powers_serial_starting_with_one, GoodAllocator};
use std::sync::Arc;
use worker::rayon::prelude::*;

pub struct GKRSetup<F: PrimeField + TwoAdicField> {
    pub hypercube_evals: Vec<Arc<crate::allocation_pool::AllocationType<F>>>,
}

impl<F: PrimeField + TwoAdicField> GKRSetup<F> {
    pub fn construct(
        table_driver: &TableDriver<F>,
        decoder_table: &[Option<ExecutorFamilyDecoderData>],
        trace_len: usize,
        compiled_circuit: &GKRCircuitArtifact<F>,
        worker: &Worker,
    ) -> Self {
        let total_width = compiled_circuit.generic_lookup_tables_width;
        let total_tables_size = table_driver.total_tables_len + decoder_table.len();
        assert_eq!(total_tables_size, compiled_circuit.total_tables_size);
        assert!(
            total_tables_size <= trace_len,
            "lookup tables must fit in the trace"
        );
        assert_eq!(
            table_driver.total_tables_len,
            compiled_circuit.offset_for_decoder_table
        );
        if !compiled_circuit.tables_ids_in_generic_lookups {
            assert!(table_driver.total_tables_len == 0 || decoder_table.is_empty());
        }
        let mut result: Vec<Box<[F]>> = worker.pool.install(|| {
            (0..total_width)
                .into_par_iter()
                .map(|_| vec![F::ZERO; trace_len].into_boxed_slice())
                .collect()
        });
        // Read the driver's existing rows directly into the columns. Table order,
        // zero padding and the final table-ID column match dump_tables exactly.
        if total_tables_size != 0 {
            assert!(table_driver.max_table_width() < total_width);
        }
        worker.pool.install(|| {
            result
                .par_iter_mut()
                .enumerate()
                .for_each(|(column_idx, column)| {
                    let mut offset = 0;
                    for table in &table_driver.tables {
                        let LookupWrapper::Initialized(table) = table else {
                            continue;
                        };
                        let width = table.width();
                        let id = F::from_u32_unchecked(table.id);
                        for (dst, row) in column[offset..offset + table.table_size()]
                            .iter_mut()
                            .zip(table.data.iter())
                        {
                            assert_eq!(row.len(), width);
                            *dst = if column_idx == total_width - 1 {
                                id
                            } else {
                                row.get(column_idx).copied().unwrap_or(F::ZERO)
                            };
                        }
                        offset += table.table_size();
                    }
                    assert_eq!(offset, table_driver.total_tables_len);
                });
        });
        if !decoder_table.is_empty() {
            assert!(decoder_table.len().is_power_of_two());
            let mask = &compiled_circuit.decode_table_columns_mask;
            assert_eq!(
                mask.len(),
                cs::definitions::EXECUTOR_FAMILY_CIRCUIT_DECODER_TABLE_WIDTH
            );
            assert!(mask[0] && mask[1]);
            let width = mask.iter().filter(|selected| **selected).count();
            let padding_width =
                total_width - usize::from(compiled_circuit.tables_ids_in_generic_lookups);
            assert!(width <= padding_width);
            let offset = table_driver.total_tables_len;
            let mut tails: Vec<_> = result
                .iter_mut()
                .map(|column| &mut column[offset..offset + decoder_table.len()])
                .collect();
            worker.scope(decoder_table.len(), |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let start = geometry.get_chunk_start_pos(thread_idx);
                    let len = geometry.get_chunk_size(thread_idx);
                    let mut columns: Vec<_> = tails
                        .iter_mut()
                        .map(|tail| {
                            let (chunk, rest) = std::mem::take(tail).split_at_mut(len);
                            *tail = rest;
                            chunk
                        })
                        .collect();
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        for (i, entry) in decoder_table[start..start + len].iter().enumerate() {
                            let row = entry.map(|entry| {
                                DecoderTableEntry::<F>::from_executor_family_data(
                                    ((start + i) * core::mem::size_of::<u32>()) as u32,
                                    &entry,
                                )
                                .flatten()
                            });
                            for (dst_idx, src_idx) in mask
                                .iter()
                                .enumerate()
                                .filter_map(|(i, selected)| selected.then_some(i))
                                .enumerate()
                            {
                                columns[dst_idx][i] =
                                    row.as_ref().map_or(F::MINUS_ONE, |row| row[src_idx]);
                            }
                            if compiled_circuit.tables_ids_in_generic_lookups {
                                columns.last_mut().unwrap()[i] =
                                    F::from_u32_unchecked(TableType::Decoder as u32);
                            }
                        }
                    });
                }
            });
        }
        if let Some(padding) = compiled_circuit.generic_lookup_padding {
            worker.pool.install(|| {
                result
                    .par_iter_mut()
                    .for_each(|column| column[total_tables_size..].fill(padding))
            });
        }

        Self {
            hypercube_evals: result
                .into_iter()
                .map(|b| Arc::new(crate::allocation_pool::AllocationType::from(b)))
                .collect(),
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

    /// Commit the setup polynomials in memory (RS codewords + Merkle tree) with the
    /// prover config's geometry — LDE factor, leaf size
    /// (`base_oracles_values_per_leaf`), cap, trace length and `pack_log2` (groups of
    /// `2^pack_log2` setup columns packed into `(trace_len_log2 + pack_log2)`-variate
    /// multilinears) — and wrap the resulting base oracle in an owned
    /// [`SetupCommitment::InMemory`]. The ONLY way to commit a setup, so a setup
    /// commitment cannot disagree with the proof's config. Runs on the naive
    /// backend; `twiddles` must cover the `2^(trace_len_log2 + pack_log2)` domain.
    pub fn commit_for_config<T: ColumnMajorMerkleTreeConstructor<F>>(
        &self,
        twiddles: &Twiddles<F, Global>,
        prover_config: &crate::gkr::prover_config::ProverConfig,
        worker: &Worker,
    ) -> SetupCommitment<F, T> {
        self.commit_for_config_with_backend::<T, F, _>(
            &crate::gkr::prover::backend::NaiveBackend,
            twiddles,
            prover_config,
            worker,
        )
    }

    /// [`Self::commit_for_config`] on a caller-chosen [`Backend`] (its twiddle set,
    /// its LDE schedule and kernels — including its fused packed commitment)
    /// instead of the naive one: the setup columns are few, so on wide machines
    /// the backend's under-filled-grid schedule matters here most. Values are
    /// identical across backends.
    pub fn commit_for_config_with_backend<
        T: ColumnMajorMerkleTreeConstructor<F>,
        E: FieldExtension<F> + Field,
        B: crate::gkr::prover::backend::Backend<F, E>,
    >(
        &self,
        backend: &B,
        twiddles: &B::TwiddleSet,
        prover_config: &crate::gkr::prover_config::ProverConfig,
        worker: &Worker,
    ) -> SetupCommitment<F, T> {
        let inputs: Vec<_> = self.hypercube_evals.iter().map(|el| &el[..]).collect();
        use crate::gkr::prover::commitment_utils::commit_trace_part_for_config;

        SetupCommitment::InMemory(commit_trace_part_for_config::<F, E, T, B>(
            backend,
            &inputs,
            twiddles,
            prover_config,
            &*crate::allocation_pool::default_proxy_pool_for(),
            worker,
        ))
    }
}
