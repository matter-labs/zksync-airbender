use cached_data::ProverCachedData;

use super::*;
use std::alloc::Global;

pub struct FourthStageOutput<const N: usize, A: GoodAllocator, T: MerkleTreeConstructor> {
    pub values_at_z: Vec<Mersenne31Quartic>,
    pub ldes: Vec<CosetBoundColumnMajorTracePart<A>>,
    pub trees: Vec<T>,
    // gpu comparison test needs z and alpha
    pub z: Mersenne31Quartic,
    pub alpha: Mersenne31Quartic,
}

fn comptute_barycentric_eval_coefficients_and_z_minus_x<A: GoodAllocator>(
    z: Mersenne31Quartic,
    omega: Mersenne31Complex,
    trace_len: usize,
    worker: &Worker,
) -> (
    RowMajorTrace<Mersenne31Field, 4, A>,
    RowMajorTrace<Mersenne31Field, 4, A>,
) {
    assert!(trace_len.is_power_of_two());
    assert_ne!(omega.pow((trace_len / 2) as u32), Mersenne31Complex::ONE);
    assert_eq!(omega.pow(trace_len as u32), Mersenne31Complex::ONE);

    let lagrange_polys_at_z =
        RowMajorTrace::<Mersenne31Field, 4, A>::new_zeroed_for_size(trace_len, 4, A::default());
    let z_minus_omega_powers_values =
        RowMajorTrace::<Mersenne31Field, 4, A>::new_zeroed_for_size(trace_len, 4, A::default());

    // L_i(X) = (omega^i / N) * (X^N - 1) / (X - omega^i)

    // (X^N - 1) / N
    let mut constant_factor = z.pow(trace_len as u32);
    constant_factor.sub_assign_base(&Mersenne31Field::ONE);
    constant_factor.mul_assign_by_base(
        &Mersenne31Field(trace_len as u32)
            .inverse()
            .expect("inverse of domain size must exist"),
    );

    // now we just compute
    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();

    unsafe {
        worker.scope(trace_len, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);

                let mut lagrange_view = lagrange_polys_at_z.row_view(range.clone());
                // check so that we can adjust pointer instead of moving over rows
                assert_eq!(lagrange_view.padded_width(), 4);

                let mut z_minus_omega_powers_view =
                    z_minus_omega_powers_values.row_view(range.clone());
                // check so that we can adjust pointer instead of moving over rows
                assert_eq!(z_minus_omega_powers_view.padded_width(), 4);

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut buffer = Vec::with_capacity(chunk_size);
                    let omega = omega;

                    let mut omega_pow = omega.pow(chunk_start as u32);
                    let mut prefactor = constant_factor;
                    prefactor.mul_assign_by_base(&omega_pow);

                    // compute z - omega^i, and then 1/(z - omega^i)
                    {
                        let mut z_minus_omega_powers_view_dst = z_minus_omega_powers_view
                            .current_row()
                            .as_mut_ptr()
                            .cast::<Mersenne31Quartic>();
                        assert!(z_minus_omega_powers_view_dst.is_aligned());

                        for _i in 0..chunk_size {
                            // X - omega^i, that will be handy for us in other places
                            let mut t = z;
                            t.sub_assign_base(&omega_pow);
                            z_minus_omega_powers_view_dst.write(t);

                            omega_pow.mul_assign(&omega);
                            z_minus_omega_powers_view_dst = z_minus_omega_powers_view_dst.add(1);
                        }
                        debug_assert_eq!(omega_pow, omega.pow((chunk_start + chunk_size) as u32));

                        // make them inverses
                        let start = z_minus_omega_powers_view
                            .current_row()
                            .as_mut_ptr()
                            .cast::<Mersenne31Quartic>();
                        let end = z_minus_omega_powers_view_dst;
                        let dst = core::slice::from_mut_ptr_range(start..end);

                        assert_eq!(dst.len(), chunk_size);
                        batch_inverse_with_buffer(dst, &mut buffer);
                    }

                    // now we can use 1 / (z - omega^i) terms to continue computing barycentric evaluation coefficients

                    let mut z_minus_omega_powers_view_src = z_minus_omega_powers_view
                        .current_row_ref()
                        .as_ptr()
                        .cast::<Mersenne31Quartic>();
                    assert!(z_minus_omega_powers_view_src.is_aligned());

                    let mut lagrange_view_dst = lagrange_view
                        .current_row()
                        .as_mut_ptr()
                        .cast::<Mersenne31Quartic>();
                    assert!(lagrange_view_dst.is_aligned());

                    for _ in 0..chunk_size {
                        // constant factor * omega^i / (X - omega^i)
                        let mut result = z_minus_omega_powers_view_src.read();
                        result.mul_assign(&prefactor);
                        lagrange_view_dst.write(result);

                        prefactor.mul_assign_by_base(&omega);
                        lagrange_view_dst = lagrange_view_dst.add(1);
                        z_minus_omega_powers_view_src = z_minus_omega_powers_view_src.add(1);
                    }
                });
            }
        });
    }

    #[cfg(feature = "timing_logs")]
    dbg!(now.elapsed());

    (lagrange_polys_at_z, z_minus_omega_powers_values)
}

pub fn prover_stage_4<const N: usize, A: GoodAllocator, T: MerkleTreeConstructor>(
    seed: &mut Seed,
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    cached_data: &ProverCachedData,
    stage_1_output: &FirstStageOutput<N, A, T>,
    stage_2_output: &SecondStageOutput<N, A, T>,
    stage_3_output: &ThirdStageOutput<N, A, T>,
    setup_precomputations: &SetupPrecomputations<N, A, T>,
    twiddles: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    lde_factor: usize,
    folding_description: &FoldingDescription,
    worker: &Worker,
) -> FourthStageOutput<N, A, T> {
    assert!(lde_factor.is_power_of_two());

    let ProverCachedData {
        offset_for_grand_product_accumulation_poly,
        trace_len,
        ..
    } = cached_data.clone();

    let mut transcript_challenges =
        [0u32; (1usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
    Transcript::draw_randomness(seed, &mut transcript_challenges);

    let mut it = transcript_challenges.as_chunks::<4>().0.iter();
    let z = Mersenne31Quartic::from_coeffs_in_base(
        &it.next()
            .unwrap()
            .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
    );

    #[cfg(feature = "debug_logs")]
    dbg!(z);

    // first we evaluate using barycentric formula,
    // and so we need lagrange poly's evaluated

    let (lagrange_polys_at_z, z_minus_omega_powers_values) =
        comptute_barycentric_eval_coefficients_and_z_minus_x::<A>(
            z,
            twiddles.omega,
            trace_len,
            worker,
        );

    let num_deep_poly_terms_at_z = compiled_circuit.num_openings_at_z();
    #[cfg(feature = "debug_logs")]
    dbg!(num_deep_poly_terms_at_z);

    let stage_2_num_base = compiled_circuit.stage_2_layout.num_base_field_polys();
    let stage_2_num_ext = compiled_circuit.stage_2_layout.num_ext4_field_polys();

    // now we count how many we open at z * omega
    let num_deep_poly_terms_at_z_omega = compiled_circuit.num_openings_at_z_omega();
    #[cfg(feature = "debug_logs")]
    dbg!(num_deep_poly_terms_at_z_omega);

    let mut columns_indexes_in_witness_trace = vec![];
    for (_src, dst) in compiled_circuit.state_linkage_constraints.iter() {
        let ColumnAddress::WitnessSubtree(index) = *dst else {
            panic!()
        };

        columns_indexes_in_witness_trace.push(index);
    }

    // then we open lazy init columns in memory
    let mut columns_indexes_in_memory_trace = vec![];
    if let Some(shuffle_ram_inits_and_teardowns) = compiled_circuit
        .memory_layout
        .shuffle_ram_inits_and_teardowns
    {
        columns_indexes_in_memory_trace.push(
            shuffle_ram_inits_and_teardowns
                .lazy_init_addresses_columns
                .start(),
        );
        columns_indexes_in_memory_trace.push(
            shuffle_ram_inits_and_teardowns
                .lazy_init_addresses_columns
                .start()
                + 1,
        );
    }

    // and accumulator for grand product in stage 2
    let offset_for_grand_product_poly = compiled_circuit
        .stage_2_layout
        .intermediate_polys_for_memory_argument
        .get_range(offset_for_grand_product_accumulation_poly)
        .start;

    assert_eq!(
        num_deep_poly_terms_at_z_omega,
        columns_indexes_in_witness_trace.len() + columns_indexes_in_memory_trace.len() + 1
    );

    // we open lazy init
    let total_num_evals = num_deep_poly_terms_at_z + num_deep_poly_terms_at_z_omega;

    // evaluate

    let geometry_chunks = worker.get_geometry(trace_len).len();
    let mut evaluations_at_z_and_z_omega =
        vec![vec![Mersenne31Quartic::ZERO; total_num_evals]; geometry_chunks];

    let columns_indexes_in_witness_trace_ref = &columns_indexes_in_witness_trace;
    let columns_indexes_in_memory_trace_ref = &columns_indexes_in_memory_trace;

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();

    // we compute on the main domain
    let domain_index = 0;

    unsafe {
        worker.scope(trace_len, |scope, geometry| {
            let mut it = evaluations_at_z_and_z_omega.chunks_mut(1);
            for thread_idx in 0..geometry.len() {
                let evaluations_at_z_and_z_omega_chunk = it.next().unwrap();
                assert_eq!(evaluations_at_z_and_z_omega_chunk.len(), 1);
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);

                let mut exec_trace_view = stage_1_output.ldes[domain_index]
                    .trace
                    .row_view(range.clone());
                let mut stage_2_trace_view = stage_2_output.ldes[domain_index]
                    .trace
                    .row_view(range.clone());
                let mut setup_trace_view = setup_precomputations.ldes[domain_index]
                    .trace
                    .row_view(range.clone());
                let mut quotient_trace_view = stage_3_output.ldes[domain_index]
                    .trace
                    .row_view(range.clone());
                let mut largange_evals_trace_view = lagrange_polys_at_z.row_view(range.clone());
                let mut z_minus_omega_powers_view = z_minus_omega_powers_values.row_view(range);

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    for _i in 0..chunk_size {
                        let _absolute_row_idx = chunk_start + _i;
                        let (exec_trace_view_row, exec_trace_view_next_row) =
                            exec_trace_view.current_and_next_row_ref();
                        let (witness_trace_view_row, memory_trace_view_row) = exec_trace_view_row
                            .split_at_unchecked(stage_1_output.num_witness_columns);
                        let (witness_trace_view_next_row, memory_trace_view_next_row) =
                            exec_trace_view_next_row
                                .split_at_unchecked(stage_1_output.num_witness_columns);

                        let (stage_2_trace_view_row, stage_2_trace_view_next_row) =
                            stage_2_trace_view.current_and_next_row_ref();
                        let setup_trace_view_row = setup_trace_view.current_row_ref();
                        let quotient_trace_view_row = quotient_trace_view.current_row_ref();
                        // we also need coeffs for barycentric eval and where to write
                        let lagrange_trace_view_row = largange_evals_trace_view.current_row_ref();

                        let mut values_at_z_ptr =
                            evaluations_at_z_and_z_omega_chunk[0].as_mut_ptr();
                        let lagrange_value_ptr =
                            lagrange_trace_view_row.as_ptr().cast::<Mersenne31Quartic>();
                        debug_assert!(lagrange_value_ptr.is_aligned());
                        let lagrange_value = lagrange_value_ptr.read();

                        // first at Z
                        // setup, then witness, then memory, then stage 2 base, then stage 2 ext, then quotient
                        {
                            let mut src = setup_trace_view_row.as_ptr();
                            let bound = compiled_circuit.setup_layout.total_width;
                            for _ in 0..bound {
                                // accumulate f(z) from this chunk
                                let mut value = lagrange_value;
                                let poly_value_at_row = src.read();
                                value.mul_assign_by_base(&poly_value_at_row);
                                // add term to accumulate f(z)
                                values_at_z_ptr.as_mut_unchecked().add_assign(&value);

                                src = src.add(1);
                                values_at_z_ptr = values_at_z_ptr.add(1);
                            }
                        }

                        {
                            let mut src = witness_trace_view_row.as_ptr();
                            let bound = compiled_circuit.witness_layout.total_width;
                            for _ in 0..bound {
                                let mut value = lagrange_value;
                                let poly_value_at_row = src.read();
                                value.mul_assign_by_base(&poly_value_at_row);
                                // add term to accumulate f(z)
                                values_at_z_ptr.as_mut_unchecked().add_assign(&value);

                                src = src.add(1);
                                values_at_z_ptr = values_at_z_ptr.add(1);
                            }
                        }

                        {
                            let mut src = memory_trace_view_row.as_ptr();
                            let bound = compiled_circuit.memory_layout.total_width;
                            for _ in 0..bound {
                                let mut value = lagrange_value;
                                let poly_value_at_row = src.read();
                                value.mul_assign_by_base(&poly_value_at_row);
                                // add term to accumulate f(z)
                                values_at_z_ptr.as_mut_unchecked().add_assign(&value);

                                src = src.add(1);
                                values_at_z_ptr = values_at_z_ptr.add(1);
                            }
                        }

                        {
                            let mut src = stage_2_trace_view_row.as_ptr();
                            let bound = stage_2_num_base;
                            for _ in 0..bound {
                                let mut value = lagrange_value;
                                let poly_value_at_row = src.read();
                                value.mul_assign_by_base(&poly_value_at_row);
                                // add term to accumulate f(z)
                                values_at_z_ptr.as_mut_unchecked().add_assign(&value);

                                src = src.add(1);
                                values_at_z_ptr = values_at_z_ptr.add(1);
                            }
                        }

                        {
                            let mut src = stage_2_trace_view_row
                                .as_ptr()
                                .add(compiled_circuit.stage_2_layout.ext4_polys_offset)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(src.is_aligned());
                            let bound = stage_2_num_ext;
                            for _ in 0..bound {
                                let mut value = lagrange_value;
                                let poly_value_at_row = src.read();
                                value.mul_assign_by_base(&poly_value_at_row);
                                // add term to accumulate f(z)
                                values_at_z_ptr.as_mut_unchecked().add_assign(&value);

                                src = src.add(1);
                                values_at_z_ptr = values_at_z_ptr.add(1);
                            }
                        }

                        // quotient
                        {
                            let src = quotient_trace_view_row.as_ptr().cast::<Mersenne31Quartic>();
                            debug_assert!(src.is_aligned());

                            let mut value = lagrange_value;
                            let poly_value_at_row = src.read();
                            value.mul_assign(&poly_value_at_row);
                            // add term to accumulate f(z)
                            values_at_z_ptr.as_mut_unchecked().add_assign(&value);

                            values_at_z_ptr = values_at_z_ptr.add(1);
                        }

                        // then at Z*omega
                        // witness, memory, stage 2
                        for offset in columns_indexes_in_witness_trace_ref.iter() {
                            let src = witness_trace_view_next_row.as_ptr().add(*offset);

                            let mut value = lagrange_value;
                            let poly_value_at_next_row = src.read();
                            value.mul_assign_by_base(&poly_value_at_next_row);
                            // add term to accumulate f(z*omega)
                            values_at_z_ptr.as_mut_unchecked().add_assign(&value);

                            values_at_z_ptr = values_at_z_ptr.add(1);
                        }

                        for offset in columns_indexes_in_memory_trace_ref.iter() {
                            let src = memory_trace_view_next_row.as_ptr().add(*offset);

                            let mut value = lagrange_value;
                            let poly_value_at_next_row = src.read();
                            value.mul_assign_by_base(&poly_value_at_next_row);
                            // add term to accumulate f(z*omega)
                            values_at_z_ptr.as_mut_unchecked().add_assign(&value);

                            values_at_z_ptr = values_at_z_ptr.add(1);
                        }

                        {
                            let src = stage_2_trace_view_next_row
                                .as_ptr()
                                .add(offset_for_grand_product_poly)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(src.is_aligned());

                            let mut value = lagrange_value;
                            let poly_value_at_next_row = src.read();
                            value.mul_assign(&poly_value_at_next_row);
                            // add term to accumulate f(z*omega)
                            values_at_z_ptr.as_mut_unchecked().add_assign(&value);

                            values_at_z_ptr = values_at_z_ptr.add(1);
                        }

                        assert_eq!(
                            values_at_z_ptr,
                            evaluations_at_z_and_z_omega_chunk[0].as_mut_ptr_range().end
                        );

                        exec_trace_view.advance_row();
                        setup_trace_view.advance_row();
                        stage_2_trace_view.advance_row();
                        quotient_trace_view.advance_row();
                        largange_evals_trace_view.advance_row();
                        z_minus_omega_powers_view.advance_row();
                    }
                });
            }
        });
    }
    #[cfg(feature = "timing_logs")]
    dbg!(now.elapsed());

    // now sum up all the values
    let mut values_at_z_and_z_omega = evaluations_at_z_and_z_omega.pop().unwrap();
    for set in evaluations_at_z_and_z_omega.into_iter() {
        for (dst, src) in values_at_z_and_z_omega.iter_mut().zip(set.into_iter()) {
            dst.add_assign(&src);
        }
    }

    assert_eq!(values_at_z_and_z_omega.len(), total_num_evals);

    // commit to all evaluations
    let mut transcript_input = vec![];
    transcript_input.extend(
        values_at_z_and_z_omega
            .iter()
            .map(|el| {
                el.into_coeffs_in_base()
                    .map(|el: Mersenne31Field| el.to_reduced_u32())
            })
            .flatten(),
    );
    Transcript::commit_with_seed(seed, &transcript_input);

    // now we can compute \sum alpha^i f_i(z)

    let mut transcript_challenges =
        [0u32; (1usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
    Transcript::draw_randomness(seed, &mut transcript_challenges);

    let mut it = transcript_challenges.as_chunks::<4>().0.iter();
    let deep_poly_alpha = Mersenne31Quartic::from_coeffs_in_base(
        &it.next()
            .unwrap()
            .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
    );

    #[cfg(feature = "debug_logs")]
    dbg!(deep_poly_alpha);
    let alphas =
        materialize_powers_serial_starting_with_one::<_, Global>(deep_poly_alpha, total_num_evals);

    let mut adjustment_at_z = Mersenne31Quartic::ZERO;
    let mut adjustment_at_z_omega = Mersenne31Quartic::ZERO;
    assert_eq!(alphas.len(), values_at_z_and_z_omega.len());

    unsafe {
        let mut value_ptr = values_at_z_and_z_omega.as_ptr();
        let mut challenge_ptr = alphas.as_ptr();

        for _ in 0..num_deep_poly_terms_at_z {
            let mut value = value_ptr.read();
            value.mul_assign(challenge_ptr.as_ref_unchecked());
            adjustment_at_z.add_assign(&value);

            value_ptr = value_ptr.add(1);
            challenge_ptr = challenge_ptr.add(1);
        }
        for _ in 0..num_deep_poly_terms_at_z_omega {
            let mut value = value_ptr.read();
            value.mul_assign(challenge_ptr.as_ref_unchecked());
            adjustment_at_z_omega.add_assign(&value);

            value_ptr = value_ptr.add(1);
            challenge_ptr = challenge_ptr.add(1);
        }

        assert_eq!(value_ptr, values_at_z_and_z_omega.as_ptr_range().end);
        assert_eq!(challenge_ptr, alphas.as_ptr_range().end);
    }

    let deep_poly_trace =
        RowMajorTrace::<Mersenne31Field, N, A>::new_zeroed_for_size(trace_len, 4, A::default());
    let (alphas_for_z, alphas_for_z_omega) = alphas.split_at(num_deep_poly_terms_at_z);

    // we precomputed \sum alpha^i * f_(z), now we need to compute at every row \sum alpha^i f_i(x), and then divide by (z - x)

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();

    unsafe {
        worker.scope(trace_len, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);

                let mut exec_trace_view = stage_1_output.ldes[domain_index]
                    .trace
                    .row_view(range.clone());
                let mut stage_2_trace_view = stage_2_output.ldes[domain_index]
                    .trace
                    .row_view(range.clone());
                let mut setup_trace_view = setup_precomputations.ldes[domain_index]
                    .trace
                    .row_view(range.clone());
                let mut quotient_trace_view = stage_3_output.ldes[domain_index]
                    .trace
                    .row_view(range.clone());
                let mut largange_evals_trace_view = lagrange_polys_at_z.row_view(range.clone());
                let mut deep_poly_trace_view = deep_poly_trace.row_view(range.clone());
                let mut z_minus_omega_powers_view = z_minus_omega_powers_values.row_view(range);
                let omega_inv = twiddles.omega_inv;

                Worker::smart_spawn(
                    scope,
                    thread_idx == geometry.len() - 1,
                    move |_| {
                    for _i in 0..chunk_size {
                        let (exec_trace_view_row, exec_trace_view_next_row) =
                            exec_trace_view.current_and_next_row_ref();
                        let (witness_trace_view_row, memory_trace_view_row)
                            = exec_trace_view_row.split_at_unchecked(stage_1_output.num_witness_columns);
                        let (witness_trace_view_next_row, memory_trace_view_next_row)
                            = exec_trace_view_next_row.split_at_unchecked(stage_1_output.num_witness_columns);

                        let (stage_2_trace_view_row, stage_2_trace_view_next_row) =
                            stage_2_trace_view.current_and_next_row_ref();
                        let setup_trace_view_row = setup_trace_view.current_row_ref();
                        let quotient_trace_view_row = quotient_trace_view.current_row_ref();

                        let deep_poly_trace_view_row = deep_poly_trace_view.current_row();
                        // we note that when we will be interested in value of  1/(z*omega - x), we can do it as
                        // omega^-1 * (z - x/omega), so effectively we need a previous row 
                        let (z_minus_omega_powers_view_row, z_minus_omega_powers_view_previous_row) = z_minus_omega_powers_view.current_and_previous_row_ref();

                        let deep_poly_trace_view_row_ptr = deep_poly_trace_view_row
                            .as_mut_ptr()
                            .cast::<Mersenne31Quartic>();
                        debug_assert!(deep_poly_trace_view_row_ptr.is_aligned());

                        let mut alphas_src = alphas_for_z.as_ptr();
                        let mut deep_poly_accumulator = Mersenne31Quartic::ZERO;

                        // first at Z
                        // setup, then witness, then memory, then stage 2 base, then stage 2 ext, then quotient
                        {
                            let mut src = setup_trace_view_row.as_ptr();
                            let bound = compiled_circuit.setup_layout.total_width;
                            for _ in 0..bound {
                                let poly_value_at_row = src.read();

                                // accumulate deep poly value at this row
                                let challenge_pow = alphas_src.read();
                                // and here we compute alpha^i * f_i(x) same time, and write into deep poly
                                let mut value = challenge_pow;
                                value.mul_assign_by_base(&poly_value_at_row);
                                deep_poly_accumulator.add_assign(&value);

                                src = src.add(1);
                                alphas_src = alphas_src.add(1);
                            }
                        }

                        {
                            let mut src = witness_trace_view_row.as_ptr();
                            let bound = compiled_circuit.witness_layout.total_width;
                            for _ in 0..bound {
                                let poly_value_at_row = src.read();

                                let challenge_pow = alphas_src.read();
                                // and here we compute alpha^i * f_i(x) same time, and write into deep poly
                                let mut value = challenge_pow;
                                value.mul_assign_by_base(&poly_value_at_row);
                                deep_poly_accumulator.add_assign(&value);

                                src = src.add(1);
                                alphas_src = alphas_src.add(1);
                            }
                        }

                        {
                            let mut src = memory_trace_view_row.as_ptr();
                            let bound = compiled_circuit.memory_layout.total_width;
                            for _ in 0..bound {
                                let poly_value_at_row = src.read();

                                let challenge_pow = alphas_src.read();
                                // and here we compute alpha^i * f_i(x) same time, and write into deep poly
                                let mut value = challenge_pow;
                                value.mul_assign_by_base(&poly_value_at_row);
                                deep_poly_accumulator.add_assign(&value);

                                src = src.add(1);
                                alphas_src = alphas_src.add(1);
                            }
                        }

                        {
                            let mut src = stage_2_trace_view_row.as_ptr();
                            let bound = stage_2_num_base;
                            for _ in 0..bound {
                                let poly_value_at_row = src.read();

                                let challenge_pow = alphas_src.read();
                                // and here we compute -alpha^i * f_i(x) same time, and write into deep poly
                                let mut value = challenge_pow;
                                value.mul_assign_by_base(&poly_value_at_row);
                                deep_poly_accumulator.add_assign(&value);

                                src = src.add(1);
                                alphas_src = alphas_src.add(1);
                            }
                        }

                        {
                            let mut src = stage_2_trace_view_row
                                .as_ptr()
                                .add(compiled_circuit.stage_2_layout.ext4_polys_offset)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(src.is_aligned());
                            let bound = stage_2_num_ext;
                            for _ in 0..bound {
                                let poly_value_at_row = src.read();

                                let challenge_pow = alphas_src.read();
                                // and here we compute -alpha^i * f_i(x) same time, and write into deep poly
                                let mut value = challenge_pow;
                                value.mul_assign(&poly_value_at_row);
                                deep_poly_accumulator.add_assign(&value);

                                src = src.add(1);
                                alphas_src = alphas_src.add(1);
                            }
                        }

                        // quotient
                        {
                            let src = quotient_trace_view_row.as_ptr().cast::<Mersenne31Quartic>();
                            debug_assert!(src.is_aligned());

                            let poly_value_at_row = src.read();

                            let challenge_pow = alphas_src.read();
                            // and here we compute -alpha^i * f_i(x) same time, and write into deep poly
                            let mut value = challenge_pow;
                            value.mul_assign(&poly_value_at_row);
                            deep_poly_accumulator.add_assign(&value);

                            alphas_src = alphas_src.add(1);
                        }

                        assert_eq!(alphas_src, alphas_for_z.as_ptr_range().end);

                        // now we can multiply it by 1/(z - omega^i)
                        let divisor = z_minus_omega_powers_view_row.as_ptr().cast::<Mersenne31Quartic>().read();
                        let mut contribution_at_z = adjustment_at_z;
                        contribution_at_z.sub_assign(&deep_poly_accumulator);
                        contribution_at_z.mul_assign(&divisor);

                        // and can continue the same for opening at z*omega
                        let mut deep_poly_accumulator = Mersenne31Quartic::ZERO;
                        let mut alphas_src = alphas_for_z_omega.as_ptr();

                        // even though we are computing terms related to z*omega, we still just need this row

                        // then at Z*omega
                        // witness, memory, stage 2
                        for offset in columns_indexes_in_witness_trace_ref.iter() {
                            let src = witness_trace_view_next_row.as_ptr().add(*offset);
                            debug_assert!(src.is_aligned());

                            let poly_value_at_row = witness_trace_view_row.as_ptr().add(*offset).read();
                            let challenge_pow = alphas_src.read();
                            // and here we compute -alpha^i * f_i(x) same time, and write into deep poly
                            let mut value = challenge_pow;
                            value.mul_assign_by_base(&poly_value_at_row);
                            deep_poly_accumulator.add_assign(&value);

                            alphas_src = alphas_src.add(1);
                        }

                        for offset in columns_indexes_in_memory_trace_ref.iter() {
                            let src = memory_trace_view_next_row.as_ptr().add(*offset);
                            debug_assert!(src.is_aligned());

                            let poly_value_at_row = memory_trace_view_row.as_ptr().add(*offset).read();
                            let challenge_pow = alphas_src.read();
                            // and here we compute -alpha^i * f_i(x) same time, and write into deep poly
                            let mut value = challenge_pow;
                            value.mul_assign_by_base(&poly_value_at_row);
                            deep_poly_accumulator.add_assign(&value);

                            alphas_src = alphas_src.add(1);
                        }

                        {
                            let src = stage_2_trace_view_next_row
                                .as_ptr()
                                .add(offset_for_grand_product_poly)
                                .cast::<Mersenne31Quartic>();
                            debug_assert!(src.is_aligned());

                            let poly_value_at_row = stage_2_trace_view_row
                                .as_ptr()
                                .add(offset_for_grand_product_poly)
                                .cast::<Mersenne31Quartic>().read();
                            let challenge_pow = alphas_src.read();
                            // and here we compute -alpha^i * f_i(x) same time, and write into deep poly
                            let mut value = challenge_pow;
                            value.mul_assign(&poly_value_at_row);
                            deep_poly_accumulator.add_assign(&value);

                            alphas_src = alphas_src.add(1);
                        }

                        assert_eq!(alphas_src, alphas_for_z_omega.as_ptr_range().end);

                        // now we can multiply it by 1/(z*omega - omega^i) = omega^-1 / (z - omega^(i-1))
                        let divisor = z_minus_omega_powers_view_previous_row.as_ptr().cast::<Mersenne31Quartic>().read();
                        let mut contribution_at_z_omega = adjustment_at_z_omega;
                        contribution_at_z_omega.sub_assign(&deep_poly_accumulator);
                        contribution_at_z_omega.mul_assign_by_base(&omega_inv);
                        contribution_at_z_omega.mul_assign(&divisor);

                        let mut accumulated = contribution_at_z;
                        accumulated.add_assign(&contribution_at_z_omega);

                        // write back accumulated value
                        deep_poly_trace_view_row_ptr.write(accumulated);

                        exec_trace_view.advance_row();
                        setup_trace_view.advance_row();
                        stage_2_trace_view.advance_row();
                        quotient_trace_view.advance_row();
                        largange_evals_trace_view.advance_row();
                        deep_poly_trace_view.advance_row();
                        z_minus_omega_powers_view.advance_row();
                    }
                });
            }
        });
    }
    #[cfg(feature = "timing_logs")]
    dbg!(now.elapsed());

    if DEBUG_QUOTIENT == true {
        // check that we have highest monomial coefficient 0
        let mut tmp = deep_poly_trace.clone();
        parallel_row_major_full_line_partial_ifft(&mut tmp, &twiddles.inverse_twiddles, worker);

        // NOTE: output is bitreversed, but we are interested at the highest monomial coefficient,
        // so it stays at the same place
        let row_view = tmp.row_view((trace_len - 1)..trace_len);
        let row = row_view.current_row_ref();
        for el in row {
            assert!(el.is_zero());
        }

        // let mut row_view = tmp.row_view((trace_len - 3)..trace_len);
        // for _ in 0..3 {
        //     let row = row_view.current_row_ref();
        //     dbg!(row);
        //     row_view.advance_row();
        // }
    }

    // now we can LDE and make oracles
    let ldes = compute_wide_ldes(
        deep_poly_trace,
        &twiddles,
        &lde_precomputations,
        0,
        lde_factor,
        worker,
    );
    assert_eq!(ldes.len(), lde_factor);

    let subtree_cap_size = (1 << folding_description.total_caps_size_log2) / lde_factor;
    assert!(subtree_cap_size > 0);

    // now we need to bitreverse elements of the trace, so we change a form of the trace and bitreverse
    let ldes: Vec<_> = ldes
        .into_iter()
        .map(|el| {
            let trace = bitreverse_and_change_trace_form(&el.trace, worker);

            CosetBoundColumnMajorTracePart { trace, tau: el.tau }
        })
        .collect();

    // // we got our LDEs in the bitreversed form, but as the result of FFTs above for all domains but main we have
    // // not the RS code word, but adjusted ones, so we will update them
    // for lde in ldes.iter_mut().skip(1) {
    //     let tau = lde.tau;
    //     let tau_in_domain_by_half = tau.pow(trace_len as u32 / 2);
    //     let source = lde.trace.columns_iter_mut().next().unwrap();
    //     unsafe {
    //         worker.scope(trace_len, |scope, geometry| {
    //             let mut dst = source;
    //             for i in 0..geometry.len() {
    //                 let chunk_size = geometry.get_chunk_size(i);
    //                 let _chunk_start = geometry.get_chunk_start_pos(i);

    //                 let (dst_chunk, rest) = dst.split_at_mut_unchecked(chunk_size);
    //                 dst = rest;

    //                 scope.spawn(move |_| {
    //                     let mut dst_ptr = dst_chunk.as_mut_ptr();
    //                     for _i in 0..chunk_size {
    //                         dst_ptr
    //                             .as_mut_unchecked()
    //                             .mul_assign_by_base(&tau_in_domain_by_half);
    //                         dst_ptr = dst_ptr.add(1);
    //                     }
    //                 });
    //             }

    //             assert!(dst.is_empty());
    //         });
    //     };
    // }

    let mut trees = Vec::with_capacity(lde_factor);
    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();
    let combine_by = 1 << folding_description.folding_sequence[0];
    for domain in ldes.iter() {
        let tree = T::construct_for_column_major_coset(
            &domain.trace,
            combine_by,
            subtree_cap_size,
            false,
            worker,
        );
        trees.push(tree);
    }
    #[cfg(feature = "timing_logs")]
    dbg!(now.elapsed());

    let output = FourthStageOutput {
        values_at_z: values_at_z_and_z_omega,
        ldes,
        trees,
        z,
        alpha: deep_poly_alpha,
    };

    output
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_barycentric_eval() {
        let trace_len = 1usize << 5;
        let num_cores = 1;

        let worker = Worker::new_with_num_threads(num_cores);
        let twiddles = Twiddles::<Mersenne31Complex, Global>::new(trace_len, &worker);
        let omega = twiddles.omega;
        let domain_size_inv = Mersenne31Field(trace_len as u32).inverse().unwrap();

        let z = Mersenne31Quartic {
            c0: Mersenne31Complex {
                c0: Mersenne31Field(1),
                c1: Mersenne31Field(2),
            },
            c1: Mersenne31Complex {
                c0: Mersenne31Field(3),
                c1: Mersenne31Field(4),
            },
        };

        let original_values = RowMajorTrace::<
            Mersenne31Field,
            DEFAULT_TRACE_PADDING_MULTIPLE,
            Global,
        >::new_zeroed_for_size(trace_len, 4, Global);
        let mut view = original_values.row_view(0..trace_len);
        for i in 0..trace_len {
            view.current_row()[0] = Mersenne31Field((i + 1) as u32);
            view.advance_row();
        }

        let from_monomial_naive = {
            let mut trace = original_values.clone();
            parallel_row_major_full_line_partial_ifft(
                &mut trace,
                &twiddles.inverse_twiddles,
                &worker,
            );
            let mut trace_dump = vec![];
            let mut view = trace.row_view(0..trace_len);
            for _ in 0..trace_len {
                unsafe {
                    let mut t = view
                        .current_row_ref()
                        .as_ptr()
                        .cast::<Mersenne31Complex>()
                        .read();
                    t.mul_assign_by_base(&domain_size_inv);
                    trace_dump.push(t);
                }

                view.advance_row();
            }

            bitreverse_enumeration_inplace(&mut trace_dump);
            let mut result = Mersenne31Quartic::ZERO;
            let mut p = Mersenne31Quartic::ONE;
            for coeff in trace_dump.iter() {
                let mut t = p;
                t.mul_assign_by_base(coeff);
                result.add_assign(&t);

                p.mul_assign(&z);
            }

            result
        };

        let (barycentric_coeffs, _) = comptute_barycentric_eval_coefficients_and_z_minus_x::<Global>(
            z, omega, trace_len, &worker,
        );

        let from_monomial = {
            let mut trace = original_values.clone();
            parallel_row_major_full_line_partial_ifft(
                &mut trace,
                &twiddles.inverse_twiddles,
                &worker,
            );

            let mut values_at_z_from_monimial = Mersenne31Quartic::ZERO;
            let domain_size_inv = Mersenne31Field(twiddles.domain_size as u32)
                .inverse()
                .unwrap();
            let mut z_powers =
                materialize_powers_parallel_starting_with_one::<_, Global>(z, trace_len, &worker);
            bitreverse_enumeration_inplace(&mut z_powers);

            let mut view = trace.row_view(0..trace_len);
            for z_power in z_powers.iter().copied() {
                let value = unsafe {
                    view.current_row_ref()
                        .as_ptr()
                        .cast::<Mersenne31Complex>()
                        .read()
                };
                let mut t = z_power;
                t.mul_assign_by_base(&value);
                t.mul_assign_by_base(&domain_size_inv);
                values_at_z_from_monimial.add_assign(&t);

                view.advance_row();
            }

            values_at_z_from_monimial
        };

        let mut from_barycentric = Mersenne31Quartic::ZERO;
        let mut coeffs_view = barycentric_coeffs.row_view(0..trace_len);
        let mut values_view = original_values.row_view(0..trace_len);
        for _ in 0..trace_len {
            unsafe {
                let value = values_view.current_row_ref()[0];
                let mut t = coeffs_view
                    .current_row_ref()
                    .as_ptr()
                    .cast::<Mersenne31Quartic>()
                    .read();
                t.mul_assign_by_base(&value);
                from_barycentric.add_assign(&t);
            }

            coeffs_view.advance_row();
            values_view.advance_row();
        }

        assert_eq!(from_monomial_naive, from_monomial);
        assert_eq!(from_barycentric, from_monomial);
    }
}
