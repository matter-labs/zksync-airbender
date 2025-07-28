use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;

use super::*;

pub struct FRIStep<A: GoodAllocator, T: MerkleTreeConstructor> {
    pub folding_challenge: Mersenne31Quartic,
    pub folding_degree_log2: u32,
    pub ldes: Vec<CosetBoundColumnMajorTracePart<A>>,
    pub trees: Vec<T>,
}

#[derive(Clone, Debug, Hash, serde::Serialize, serde::Deserialize)]
pub struct Query {
    pub query_index: u32,
    pub tree_index: u32,
    pub leaf_content: Vec<Mersenne31Field>,
    pub merkle_proof: Vec<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]>,
}

// in the fifth stage we output FRI oracles
pub struct FifthStageOutput<A: GoodAllocator, T: MerkleTreeConstructor> {
    pub fri_oracles: Vec<FRIStep<A, T>>,
    pub final_monomials: Vec<Mersenne31Quartic>,
    pub expose_all_leafs_at_last_step_instead: bool,
    pub last_fri_step_plain_leaf_values: Vec<Vec<Mersenne31Quartic>>,
}

pub fn prover_stage_5<const N: usize, A: GoodAllocator, T: MerkleTreeConstructor>(
    seed: &mut Seed,
    stage_4_output: &FourthStageOutput<N, A, T>,
    twiddles: &Twiddles<Mersenne31Complex, A>,
    lde_factor: usize,
    folding_description: &FoldingDescription,
    num_queries: usize,
    worker: &Worker,
) -> FifthStageOutput<A, T> {
    // we have our FRI initial oracles in the bitreversed form, so we can can just commit and start folding

    #[cfg(feature = "debug_logs")]
    dbg!(folding_description);

    let mut degree_log_2 = stage_4_output.ldes[0].trace.len().trailing_zeros();
    // under our assumptions about hash and field it's always beneficial to fold by 8

    let interpolate_fn = |coset: &CosetBoundColumnMajorTracePart<A>| {
        let trace_len = coset.trace.len();
        assert!(trace_len.is_power_of_two());

        let mut c0 = vec![];
        let mut c1 = vec![];

        // we need to adjust non-main domains if needed
        let tau = coset.tau;
        let tau_in_domain_by_half = tau.pow(trace_len as u32 / 2);

        for el in coset.trace.as_slice() {
            let mut c0_el = el.c0;
            let mut c1_el = el.c1;
            c0_el.mul_assign(&tau_in_domain_by_half);
            c1_el.mul_assign(&tau_in_domain_by_half);

            c0.push(c0_el);
            c1.push(c1_el);
        }

        // bitreverse them
        bitreverse_enumeration_inplace(&mut c0);
        bitreverse_enumeration_inplace(&mut c1);

        let twiddles = &twiddles.inverse_twiddles[..c0.len() / 2];
        partial_ifft_natural_to_natural(&mut c0, tau, twiddles);
        partial_ifft_natural_to_natural(&mut c1, tau, twiddles);

        if c0.len() > 1 {
            let n_inv = Mersenne31Field(c0.len() as u32).inverse().unwrap();
            let mut i = 0;
            let work_size = c0.len();
            while i < work_size {
                c0[i].mul_assign_by_base(&n_inv);
                c1[i].mul_assign_by_base(&n_inv);
                i += 1;
            }
        }

        // assert_eq!(*c0.last().unwrap(), Mersenne31Complex::ZERO);
        // assert_eq!(*c1.last().unwrap(), Mersenne31Complex::ZERO);

        (c0, c1)
    };

    if DEBUG_QUOTIENT == true {
        let monomials_from_main_domain = interpolate_fn(&stage_4_output.ldes[0]);
        let monomials_from_coset = interpolate_fn(&stage_4_output.ldes[1]);

        // assert_eq!(monomials_from_main_domain, monomials_from_coset);

        if monomials_from_main_domain != monomials_from_coset {
            panic!("DEEP quotient poly is most likely malformed, evaluations on main and other domains result in different monomials");
        }

        assert_eq!(
            *monomials_from_main_domain.0.last().unwrap(),
            Mersenne31Complex::ZERO
        );
        assert_eq!(
            *monomials_from_main_domain.1.last().unwrap(),
            Mersenne31Complex::ZERO
        );

        assert_eq!(
            *monomials_from_coset.0.last().unwrap(),
            Mersenne31Complex::ZERO
        );
        assert_eq!(
            *monomials_from_coset.1.last().unwrap(),
            Mersenne31Complex::ZERO
        );
    }

    // Now we should compute a schedule, assuming that we have rather large number of queries.
    // So we fold by 8 and always stop at cap size, so when we do queries we do less hashing to hash caps once
    // in transcript than to pay for merkle paths verification in queries

    let mut expose_all_leafs_at_last_step_instead = false;
    let mut intermediate_oracles: Vec<FRIStep<A, T>> = vec![];
    let mut last_fri_step_plain_leaf_values = vec![];
    let folding_with_merkle_tree_formations = folding_description.folding_sequence.len() - 1;

    // now we take our transcript, get challenge and fold
    for (i, folding_factor_log2) in folding_description
        .folding_sequence
        .iter()
        .take(folding_with_merkle_tree_formations)
        .enumerate()
    {
        let last_oraclization = i == folding_with_merkle_tree_formations - 1;
        let challenge = {
            let mut transcript_challenges =
                [0u32; (1usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
            Transcript::draw_randomness(seed, &mut transcript_challenges);

            let mut it = transcript_challenges.as_chunks::<4>().0.iter();
            let challenge = Mersenne31Quartic::from_coeffs_in_base(
                &it.next()
                    .unwrap()
                    .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
            );

            challenge
        };
        // fold
        let folding_input = if i == 0 {
            &stage_4_output.ldes
        } else {
            &intermediate_oracles.last().unwrap().ldes
        };

        let folded_cosets: Vec<_> = folding_input
            .iter()
            .map(|el| match *folding_factor_log2 {
                1 => {
                    fold_by_log_n::<A, false, 1>(el, &twiddles.inverse_twiddles, challenge, worker)
                }
                2 => {
                    fold_by_log_n::<A, false, 2>(el, &twiddles.inverse_twiddles, challenge, worker)
                }
                3 => {
                    fold_by_log_n::<A, false, 3>(el, &twiddles.inverse_twiddles, challenge, worker)
                }
                4 => {
                    fold_by_log_n::<A, false, 4>(el, &twiddles.inverse_twiddles, challenge, worker)
                }
                5 => {
                    fold_by_log_n::<A, false, 5>(el, &twiddles.inverse_twiddles, challenge, worker)
                }
                _ => {
                    unreachable!("too high folding degree")
                }
            })
            .collect();

        if DEBUG_QUOTIENT == true {
            let mut t = challenge;
            let mut input = folding_input[0].clone();
            for _ in 0..*folding_factor_log2 {
                let output = fold_by_2::<_, false>(&input, &twiddles.inverse_twiddles, t, worker);
                input = output;

                t.square();
            }

            for (j, (a, b)) in folded_cosets[0]
                .trace
                .as_slice()
                .iter()
                .zip(input.trace.as_slice().iter())
                .enumerate()
            {
                if a != b {
                    panic!("Diverged at index {} at folding step {}", j, i);
                }
            }
        }

        if DEBUG_QUOTIENT {
            let main_domain = interpolate_fn(&folded_cosets[0]);
            let other_domain = interpolate_fn(&folded_cosets[1]);

            assert_eq!(main_domain, other_domain);
        }

        if last_oraclization {
            // here we can decide what's more efficient for the verifier. If we have NUM_QUERIES ~= NUM LEAFS in the last oracle,
            // then we should instead just expose all leaf values in plain text and put them in transcript

            let combine_by = 1 << folding_description.folding_sequence[i + 1]; // account for next folding

            let bound = if num_queries.is_power_of_two() {
                num_queries
            } else {
                num_queries.next_power_of_two()
            };
            let domain_size = folded_cosets[0].trace.len();
            assert!(domain_size.is_power_of_two());
            let num_leafs = domain_size / combine_by;
            assert!(num_leafs > 0);

            if num_leafs * 2 / lde_factor <= bound {
                #[cfg(feature = "debug_logs")]
                println!("Final FRI folding will expose all leafs in plain text");

                // it means that on average we will access all of them
                // and there is no point to make merkle trees at all

                expose_all_leafs_at_last_step_instead = true;
            }
        }

        if !last_oraclization || !expose_all_leafs_at_last_step_instead {
            let subtree_cap_size = (1 << folding_description.total_caps_size_log2) / lde_factor;
            assert!(subtree_cap_size > 0);

            // and then commit. Note that we should put enough elements into the leaf so that NEXT
            // folding would take them all
            let mut trees = Vec::with_capacity(lde_factor);
            #[cfg(feature = "timing_logs")]
            let now = std::time::Instant::now();
            let combine_by = 1 << folding_description.folding_sequence[i + 1]; // account for next folding
            for domain in folded_cosets.iter() {
                let witness_tree = T::construct_for_column_major_coset(
                    &domain.trace,
                    combine_by,
                    subtree_cap_size,
                    false,
                    worker,
                );
                trees.push(witness_tree);
            }
            #[cfg(feature = "timing_logs")]
            dbg!(now.elapsed());

            let oracle = FRIStep {
                folding_challenge: challenge,
                folding_degree_log2: *folding_factor_log2 as u32,
                ldes: folded_cosets,
                trees,
            };

            let mut transcript_input = vec![];
            flatten_merkle_caps_into(&oracle.trees, &mut transcript_input);
            Transcript::commit_with_seed(seed, &transcript_input);

            intermediate_oracles.push(oracle);
        } else {
            assert!(last_oraclization);
            assert!(expose_all_leafs_at_last_step_instead);

            let mut transcript_input = vec![];
            for domain in folded_cosets.iter() {
                let domain = domain.trace.as_slice();
                let mut subvec = Vec::with_capacity(domain.len());
                for el in domain.iter() {
                    subvec.push(*el);
                    let el = el
                        .into_coeffs_in_base()
                        .map(|el: Mersenne31Field| el.to_reduced_u32());
                    transcript_input.extend(el);
                }

                last_fri_step_plain_leaf_values.push(subvec);
            }

            Transcript::commit_with_seed(seed, &transcript_input);

            let oracle = FRIStep {
                folding_challenge: challenge,
                folding_degree_log2: *folding_factor_log2 as u32,
                ldes: folded_cosets,
                trees: vec![],
            };

            intermediate_oracles.push(oracle);
        }

        degree_log_2 -= *folding_factor_log2 as u32;
    }

    assert_eq!(
        degree_log_2 as usize,
        folding_description.final_monomial_degree_log2
            + folding_description.folding_sequence.last().unwrap()
    );

    // fold one more time from the final oracle and make monomial form. Here we do not need to make another merkle tree
    let monomial_coefficients = {
        let final_folding_degree_log_2 = *folding_description.folding_sequence.last().unwrap();
        let final_folding_challenge = {
            let mut transcript_challenges =
                [0u32; (1usize * 4).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS)];
            Transcript::draw_randomness(seed, &mut transcript_challenges);

            let mut it = transcript_challenges.as_chunks::<4>().0.iter();
            let challenge = Mersenne31Quartic::from_coeffs_in_base(
                &it.next()
                    .unwrap()
                    .map(|el| Mersenne31Field::from_nonreduced_u32(el)),
            );

            challenge
        };
        // fold
        let folded_main_domain = match final_folding_degree_log_2 {
            1 => fold_by_log_n::<A, false, 1>(
                &intermediate_oracles.last().unwrap().ldes[0],
                &twiddles.inverse_twiddles,
                final_folding_challenge,
                worker,
            ),
            2 => fold_by_log_n::<A, false, 2>(
                &intermediate_oracles.last().unwrap().ldes[0],
                &twiddles.inverse_twiddles,
                final_folding_challenge,
                worker,
            ),
            3 => fold_by_log_n::<A, false, 3>(
                &intermediate_oracles.last().unwrap().ldes[0],
                &twiddles.inverse_twiddles,
                final_folding_challenge,
                worker,
            ),
            4 => fold_by_log_n::<A, false, 4>(
                &intermediate_oracles.last().unwrap().ldes[0],
                &twiddles.inverse_twiddles,
                final_folding_challenge,
                worker,
            ),
            5 => fold_by_log_n::<A, false, 5>(
                &intermediate_oracles.last().unwrap().ldes[0],
                &twiddles.inverse_twiddles,
                final_folding_challenge,
                worker,
            ),
            _ => {
                unreachable!("too high folding degree")
            }
        };

        degree_log_2 -= final_folding_degree_log_2 as u32;

        let mut c0 = Vec::with_capacity(1 << degree_log_2);
        let mut c1 = Vec::with_capacity(1 << degree_log_2);
        for el in folded_main_domain.trace.as_slice() {
            c0.push(el.c0);
            c1.push(el.c1);
        }

        assert_eq!(c0.len(), 1 << degree_log_2);
        assert_eq!(c1.len(), 1 << degree_log_2);

        // bitreverse them
        bitreverse_enumeration_inplace(&mut c0);
        bitreverse_enumeration_inplace(&mut c1);

        interpolate(&mut c0, &twiddles.inverse_twiddles);
        interpolate(&mut c1, &twiddles.inverse_twiddles);

        let mut output = Vec::with_capacity(1 << degree_log_2);
        for (c0, c1) in c0.into_iter().zip(c1.into_iter()) {
            let el = Mersenne31Quartic { c0, c1 };
            output.push(el);
        }

        assert_eq!(output.len(), 1 << degree_log_2);

        output
    };

    assert_eq!(
        degree_log_2 as usize,
        folding_description.final_monomial_degree_log2
    );

    // and commit monomial coefficients
    let mut transcript_input = vec![];
    transcript_input.extend(
        monomial_coefficients
            .iter()
            .map(|el| {
                el.into_coeffs_in_base()
                    .map(|el: Mersenne31Field| el.to_reduced_u32())
            })
            .flatten(),
    );
    Transcript::commit_with_seed(seed, &transcript_input);

    let output = FifthStageOutput {
        fri_oracles: intermediate_oracles,
        final_monomials: monomial_coefficients,
        expose_all_leafs_at_last_step_instead,
        last_fri_step_plain_leaf_values,
    };

    output
}

#[allow(dead_code)]
fn fold_by_8<A: GoodAllocator, const ADJUST_FIRST_VALUES: bool>(
    source: &CosetBoundColumnMajorTracePart<A>,
    inverse_twiddles: &[Mersenne31Complex],
    challenge: Mersenne31Quartic,
    worker: &Worker,
) -> CosetBoundColumnMajorTracePart<A> {
    assert_eq!(source.trace.width(), 1);
    let source_slice = source.trace.as_slice();
    let trace_len = source_slice.len();
    assert!(trace_len.is_power_of_two());
    let mut tau = source.tau;
    let mut tau_inv = tau.inverse().expect("must exist");

    // we should also understand that our evaluations need to be adjusted by tau^H/2
    let tau_in_domain_by_half = tau.pow((trace_len / 2) as u32);
    let expected_output_size = trace_len / 8;
    let mut result = ColumnMajorTrace::<Mersenne31Quartic, A>::new_uninit_for_size(
        expected_output_size,
        1,
        A::default(),
    );
    let used_twiddles = &inverse_twiddles[..(trace_len / 2)];

    let mut it = result.columns_iter_mut();
    let mut dst_column = it.next().unwrap();

    let mut challenge_powers = [Mersenne31Quartic::ZERO; 3];
    let mut challenge = challenge;
    challenge_powers[0] = challenge;
    challenge.square();
    challenge_powers[1] = challenge;
    challenge.square();
    challenge_powers[2] = challenge;

    let mut tau_inv_powers = [Mersenne31Complex::ZERO; 3];
    tau_inv_powers[0] = tau_inv;
    tau_inv.square();
    tau.square();
    tau_inv_powers[1] = tau_inv;
    tau_inv.square();
    tau.square();
    tau_inv_powers[2] = tau_inv;
    tau_inv.square();
    tau.square();

    unsafe {
        worker.scope(expected_output_size, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let _dst_range = chunk_start..(chunk_start + chunk_size);
                let src_range = chunk_start * 8..(chunk_start + chunk_size) * 8;

                let (dst_chunk, rest) = dst_column.split_at_mut(chunk_size);
                dst_column = rest;
                let src_chunk = &source_slice[src_range];

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut dst_ptr = dst_chunk.as_mut_ptr();
                    let mut source_chunks = src_chunk.as_chunks::<8>().0.iter();
                    for i in 0..chunk_size {
                        let t = chunk_start + i;
                        let absolute_set_idx = t * 4; // our twiddles are only half-size
                        let [a0, a1, b0, b1, c0, c1, d0, d1] =
                            source_chunks.next().unwrap_unchecked();

                        // we need to do (a0 + a1) + (a0 - a1)/root of unity, and do not forget to adjust by tau^H/2 at the end if needed
                        let (a0, a1, b0, b1) = {
                            let [a_root, b_root, c_root, d_root] = used_twiddles
                                [absolute_set_idx..]
                                .as_chunks::<4>()
                                .0
                                .iter()
                                .next()
                                .unwrap_unchecked();
                            let challenge = &challenge_powers[0];
                            let tau_inv = &tau_inv_powers[0];

                            let mut e0 = *a0;
                            e0.sub_assign(a1);
                            e0.mul_assign_by_base(a_root);
                            e0.mul_assign_by_base(tau_inv);
                            e0.mul_assign(&challenge);
                            e0.add_assign(a0);
                            e0.add_assign(a1);
                            if ADJUST_FIRST_VALUES {
                                e0.mul_assign_by_base(&tau_in_domain_by_half);
                            }

                            let mut e1 = *b0;
                            e1.sub_assign(b1);
                            e1.mul_assign_by_base(b_root);
                            e1.mul_assign_by_base(tau_inv);
                            e1.mul_assign(&challenge);
                            e1.add_assign(b0);
                            e1.add_assign(b1);
                            if ADJUST_FIRST_VALUES {
                                e1.mul_assign_by_base(&tau_in_domain_by_half);
                            }

                            let mut f0 = *c0;
                            f0.sub_assign(c1);
                            f0.mul_assign_by_base(c_root);
                            f0.mul_assign_by_base(tau_inv);
                            f0.mul_assign(&challenge);
                            f0.add_assign(c0);
                            f0.add_assign(c1);
                            if ADJUST_FIRST_VALUES {
                                f0.mul_assign_by_base(&tau_in_domain_by_half);
                            }

                            let mut f1 = *d0;
                            f1.sub_assign(d1);
                            f1.mul_assign_by_base(d_root);
                            f1.mul_assign_by_base(tau_inv);
                            f1.mul_assign(&challenge);
                            f1.add_assign(d0);
                            f1.add_assign(d1);
                            if ADJUST_FIRST_VALUES {
                                f1.mul_assign_by_base(&tau_in_domain_by_half);
                            }

                            (e0, e1, f0, f1)
                        };
                        let absolute_set_idx = absolute_set_idx / 2;

                        let (a0, a1) = {
                            let [a_root, b_root] = used_twiddles[absolute_set_idx..]
                                .as_chunks::<2>()
                                .0
                                .iter()
                                .next()
                                .unwrap_unchecked();
                            let challenge = &challenge_powers[1];
                            let tau_inv = &tau_inv_powers[1];

                            let mut e0 = a0;
                            e0.sub_assign(&a1);
                            e0.mul_assign_by_base(a_root);
                            e0.mul_assign_by_base(tau_inv);
                            e0.mul_assign(&challenge);
                            e0.add_assign(&a0);
                            e0.add_assign(&a1);

                            let mut e1 = b0;
                            e1.sub_assign(&b1);
                            e1.mul_assign_by_base(b_root);
                            e1.mul_assign_by_base(tau_inv);
                            e1.mul_assign(&challenge);
                            e1.add_assign(&b0);
                            e1.add_assign(&b1);

                            (e0, e1)
                        };

                        let absolute_set_idx = absolute_set_idx / 2;
                        let a_root = used_twiddles[absolute_set_idx];
                        let challenge = &challenge_powers[2];
                        let tau_inv = &tau_inv_powers[2];

                        let mut e0 = a0;
                        e0.sub_assign(&a1);
                        e0.mul_assign_by_base(&a_root);
                        e0.mul_assign_by_base(tau_inv);
                        e0.mul_assign(&challenge);
                        e0.add_assign(&a0);
                        e0.add_assign(&a1);

                        dst_ptr.write(e0);

                        dst_ptr = dst_ptr.add(1);
                    }
                });
            }
        });
    }
    drop(it);

    let result = CosetBoundColumnMajorTracePart { trace: result, tau };

    result
}

fn fold_by_log_n<A: GoodAllocator, const ADJUST_FIRST_VALUES: bool, const N: usize>(
    source: &CosetBoundColumnMajorTracePart<A>,
    inverse_twiddles: &[Mersenne31Complex],
    challenge: Mersenne31Quartic,
    worker: &Worker,
) -> CosetBoundColumnMajorTracePart<A> {
    assert!(N > 0);
    assert!(N <= 5);
    assert_eq!(source.trace.width(), 1);
    let source_slice = source.trace.as_slice();
    let trace_len = source_slice.len();
    assert!(trace_len.is_power_of_two());
    let mut tau = source.tau;
    let mut tau_inv = tau.inverse().expect("must exist");
    let fold_by = 1 << N;

    // we should also understand that our evaluations need to be adjusted by tau^H/2
    let tau_in_domain_by_half = tau.pow((trace_len / 2) as u32);
    let expected_output_size = trace_len / fold_by;
    let mut result = ColumnMajorTrace::<Mersenne31Quartic, A>::new_uninit_for_size(
        expected_output_size,
        1,
        A::default(),
    );
    let used_twiddles = &inverse_twiddles[..(trace_len / 2)];

    let mut it = result.columns_iter_mut();
    let mut dst_column = it.next().unwrap();

    let mut challenge_powers = [Mersenne31Quartic::ZERO; N];
    let mut challenge = challenge;
    challenge_powers[0] = challenge;
    for i in 1..N {
        challenge.square();
        challenge_powers[i] = challenge;
    }

    let mut tau_inv_powers = [Mersenne31Complex::ZERO; N];
    tau_inv_powers[0] = tau_inv;
    for i in 1..N {
        tau_inv.square();
        tau.square();
        tau_inv_powers[i] = tau_inv;
    }

    tau_inv.square();
    tau.square();

    unsafe {
        worker.scope(expected_output_size, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let _dst_range = chunk_start..(chunk_start + chunk_size);
                let src_range = chunk_start * fold_by..(chunk_start + chunk_size) * fold_by;

                let (dst_chunk, rest) = dst_column.split_at_mut(chunk_size);
                dst_column = rest;
                let src_chunk = &source_slice[src_range];

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut dst_ptr = dst_chunk.as_mut_ptr();
                    let mut buffer_0 = [Mersenne31Quartic::ZERO; 32]; // max size
                    let mut buffer_1 = [Mersenne31Quartic::ZERO; 32]; // max size
                    for i in 0..chunk_size {
                        let t = chunk_start + i;
                        let mut absolute_set_idx = t * fold_by / 2; // our twiddles are only half-size

                        for round in 0..N {
                            let chunk_size = 1 << (N - round);
                            let twiddles_chunk_size = chunk_size / 2;
                            let challenge = &challenge_powers[round];
                            let tau_inv = &tau_inv_powers[round];
                            let (input_buffer_ref, output_buffer_ref) = if round % 2 == 0 {
                                (&mut buffer_0, &mut buffer_1)
                            } else {
                                (&mut buffer_1, &mut buffer_0)
                            };

                            let input = if round == 0 {
                                &src_chunk[i * fold_by..][..fold_by]
                            } else {
                                &input_buffer_ref[..chunk_size]
                            };
                            let twiddles =
                                &used_twiddles[absolute_set_idx..][..twiddles_chunk_size];
                            assert_eq!(twiddles.len() * 2, input.len());
                            for (([a, b], twiddle), dst) in input
                                .as_chunks::<2>()
                                .0
                                .iter()
                                .zip(twiddles.iter())
                                .zip(output_buffer_ref.iter_mut())
                            {
                                *dst = *a;
                                dst.sub_assign(b);
                                dst.mul_assign_by_base(twiddle);
                                dst.mul_assign_by_base(tau_inv);
                                dst.mul_assign(&challenge);
                                dst.add_assign(a);
                                dst.add_assign(b);
                                if ADJUST_FIRST_VALUES && round == 0 {
                                    dst.mul_assign_by_base(&tau_in_domain_by_half);
                                }
                            }

                            // continue into next folding
                            absolute_set_idx /= 2;
                        }

                        let result = if N % 2 == 0 { buffer_0[0] } else { buffer_1[0] };

                        dst_ptr.write(result);

                        dst_ptr = dst_ptr.add(1);
                    }
                });
            }
        });
    }
    drop(it);

    let result = CosetBoundColumnMajorTracePart { trace: result, tau };

    result
}

fn fold_by_2<A: GoodAllocator, const ADJUST_FIRST_VALUES: bool>(
    source: &CosetBoundColumnMajorTracePart<A>,
    inverse_twiddles: &[Mersenne31Complex],
    challenge: Mersenne31Quartic,
    worker: &Worker,
) -> CosetBoundColumnMajorTracePart<A> {
    assert_eq!(source.trace.width(), 1);
    let source_slice = source.trace.as_slice();
    let trace_len = source_slice.len();
    assert!(trace_len.is_power_of_two());
    let mut tau = source.tau;
    let mut tau_inv = tau.inverse().expect("must exist");

    // we should also understand that our evaluations need to be adjusted by tau^H/2
    let tau_in_domain_by_half = tau.pow((trace_len / 2) as u32);
    let expected_output_size = trace_len / 2;
    let mut result = ColumnMajorTrace::<Mersenne31Quartic, A>::new_uninit_for_size(
        expected_output_size,
        1,
        A::default(),
    );
    let used_twiddles = &inverse_twiddles[..(trace_len / 2)];

    let mut it = result.columns_iter_mut();
    let mut dst_column = it.next().unwrap();

    let mut challenge_powers = [Mersenne31Quartic::ZERO; 3];
    let mut challenge = challenge;
    challenge_powers[0] = challenge;
    challenge.square();
    challenge_powers[1] = challenge;
    challenge.square();
    challenge_powers[2] = challenge;

    let mut tau_inv_powers = [Mersenne31Complex::ZERO; 3];
    tau_inv_powers[0] = tau_inv;
    tau_inv.square();
    tau.square();

    unsafe {
        worker.scope(expected_output_size, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let _dst_range = chunk_start..(chunk_start + chunk_size);
                let src_range = chunk_start * 2..(chunk_start + chunk_size) * 2;

                let (dst_chunk, rest) = dst_column.split_at_mut(chunk_size);
                dst_column = rest;
                let src_chunk = &source_slice[src_range];

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut dst_ptr = dst_chunk.as_mut_ptr();
                    let mut source_chunks = src_chunk.as_chunks::<2>().0.iter();
                    for i in 0..chunk_size {
                        let absolute_set_idx = chunk_start + i; // our twiddles are only half-size
                        let [a0, a1] = source_chunks.next().unwrap_unchecked();
                        let a_root = used_twiddles[absolute_set_idx];
                        let challenge = &challenge_powers[0];
                        let tau_inv = &tau_inv_powers[0];

                        let mut e0 = *a0;
                        e0.sub_assign(a1);
                        e0.mul_assign_by_base(&a_root);
                        e0.mul_assign_by_base(tau_inv);
                        e0.mul_assign(&challenge);
                        e0.add_assign(a0);
                        e0.add_assign(a1);
                        if ADJUST_FIRST_VALUES {
                            e0.mul_assign_by_base(&tau_in_domain_by_half);
                        }

                        dst_ptr.write(e0);

                        dst_ptr = dst_ptr.add(1);
                    }
                });
            }
        });
    }
    drop(it);

    let result = CosetBoundColumnMajorTracePart { trace: result, tau };

    result
}

fn interpolate(c0: &mut [Mersenne31Complex], twiddles: &[Mersenne31Complex]) {
    let twiddles = &twiddles[..c0.len() / 2];
    partial_ifft_natural_to_natural(c0, Mersenne31Complex::ONE, twiddles);

    if c0.len() > 1 {
        let n_inv = Mersenne31Field(c0.len() as u32).inverse().unwrap();
        let mut i = 0;
        let work_size = c0.len();
        while i < work_size {
            c0[i].mul_assign_by_base(&n_inv);
            i += 1;
        }
    }
}

#[allow(dead_code)]
fn fold_by_2_in_monomial_form(
    c0: &[Mersenne31Complex],
    c1: &[Mersenne31Complex],
    challenge: &Mersenne31Quartic,
) -> (Vec<Mersenne31Complex>, Vec<Mersenne31Complex>) {
    let mut output_c0 = vec![];
    let mut output_c1 = vec![];
    for ([a0, b0], [a1, b1]) in c0
        .as_chunks::<2>()
        .0
        .iter()
        .zip(c1.as_chunks::<2>().0.iter())
    {
        let a = Mersenne31Quartic { c0: *a0, c1: *a1 };
        let mut tmp = Mersenne31Quartic { c0: *b0, c1: *b1 };
        tmp.mul_assign(challenge);
        tmp.add_assign(&a);
        tmp.double();
        output_c0.push(tmp.c0);
        output_c1.push(tmp.c1);
    }

    (output_c0, output_c1)
}
