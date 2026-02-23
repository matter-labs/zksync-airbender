use super::*;

// this stage starts with public inputs, external challenges, witness and memory chunks of trace,
// and results in initialization of transcript and commitment to witness and memory traces

pub struct FirstStageOutput<const N: usize, A: GoodAllocator, T: MerkleTreeConstructor> {
    pub ldes: Vec<CosetBoundTracePart<N, A>>,
    pub num_witness_columns: usize,
    pub witness_tree: Vec<T>,
    pub memory_tree: Vec<T>,
}

pub fn compute_wide_ldes<const N: usize, A: GoodAllocator>(
    source_domain: RowMajorTrace<Mersenne31Field, N, A>,
    twiddles: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    source_domain_index: usize,
    lde_factor: usize,
    worker: &Worker,
) -> Vec<CosetBoundTracePart<N, A>> {
    compute_wide_ldes_row_major(
        source_domain,
        twiddles,
        lde_precomputations,
        source_domain_index,
        lde_factor,
        worker,
    )
    // compute_wide_ldes_grinded(
    //     source_domain,
    //     twiddles,
    //     lde_precomputations,
    //     source_domain_index,
    //     lde_factor,
    //     worker,
    // )
}

pub fn compute_wide_ldes_row_major<const N: usize, A: GoodAllocator>(
    source_domain: RowMajorTrace<Mersenne31Field, N, A>,
    twiddles: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    source_domain_index: usize,
    lde_factor: usize,
    worker: &Worker,
) -> Vec<CosetBoundTracePart<N, A>> {
    let mut ldes = Vec::with_capacity(lde_factor);

    assert!(
        source_domain_index != 0 || lde_factor != 1,
        "No reason to call this function"
    );

    let source_domain_is_used = source_domain_index < lde_factor;
    let mut source_domain_clone = None;
    if source_domain_is_used {
        source_domain_clone = Some(source_domain.clone());
    }

    let mut partial_ifft = source_domain;
    parallel_row_major_full_line_partial_ifft::<N, A>(
        &mut partial_ifft,
        &twiddles.inverse_twiddles,
        worker,
    );

    let mut partial_ifft = Some(partial_ifft);

    let precomputations = lde_precomputations.domain_bound_precomputations[source_domain_index]
        .as_ref()
        .unwrap();

    let mut num_other_cosets = if source_domain_is_used {
        lde_factor - 1
    } else {
        lde_factor
    };

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();
    for (coset_idx, (pows, tau)) in precomputations
        .bitreversed_powers
        .iter()
        .zip(precomputations.taus.iter())
        .enumerate()
    {
        if coset_idx == source_domain_index {
            let source_domain = source_domain_clone.take().unwrap();
            let coset_values = CosetBoundTracePart {
                trace: source_domain,
                tau: *tau,
            };
            ldes.push(coset_values);
        } else {
            // extrapolate
            let mut trace = if num_other_cosets == 1 {
                partial_ifft.take().unwrap()
            } else {
                partial_ifft.as_ref().unwrap().clone()
            };
            num_other_cosets -= 1;
            parallel_row_major_full_line_fft_dit::<N, A>(
                &mut trace,
                &twiddles.forward_twiddles_not_bitreversed,
                pows,
                worker,
            );

            // parallel_row_major_full_line_fft_dif::<N, A>(
            //     &mut trace,
            //     &twiddles.forward_twiddles,
            //     pows,
            //     worker,
            // );

            let coset_values = CosetBoundTracePart { trace, tau: *tau };

            ldes.push(coset_values);
        }
    }
    #[cfg(feature = "timing_logs")]
    dbg!(now.elapsed());

    assert!(partial_ifft.is_none());
    assert_eq!(ldes.len(), lde_factor);

    ldes
}

pub fn prover_stage_1<const N: usize, A: GoodAllocator, T: MerkleTreeConstructor>(
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    mut exec_trace: RowMajorTrace<Mersenne31Field, N, A>,
    num_witness_columns: usize,
    twiddles: &Twiddles<Mersenne31Complex, A>,
    lde_precomputations: &LdePrecomputations<A>,
    lde_factor: usize,
    folding_description: &FoldingDescription,
    worker: &Worker,
) -> FirstStageOutput<N, A, T> {
    assert!(lde_factor.is_power_of_two());

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();

    // adjust main domain
    let width = exec_trace.width();
    adjust_to_zero_c0_var_length(&mut exec_trace, 0..width, worker);

    let ldes = compute_wide_ldes(
        exec_trace,
        twiddles,
        lde_precomputations,
        0,
        lde_factor,
        worker,
    );

    #[cfg(feature = "timing_logs")]
    dbg!(now.elapsed());

    assert_eq!(ldes.len(), lde_factor);

    let subtree_cap_size = (1 << folding_description.total_caps_size_log2) / lde_factor;
    assert!(subtree_cap_size > 0);

    let mut witness_subtrees = Vec::with_capacity(lde_factor);
    let mut memory_subtrees = Vec::with_capacity(lde_factor);
    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();
    for domain in ldes.iter() {
        let mut trees = T::construct_separated_for_coset(
            &domain.trace,
            &vec![num_witness_columns, domain.trace.width()],
            subtree_cap_size,
            true,
            worker,
        );
        assert_eq!(trees.len(), 2);
        memory_subtrees.push(trees.pop().unwrap());
        witness_subtrees.push(trees.pop().unwrap());
    }

    #[cfg(feature = "timing_logs")]
    dbg!(now.elapsed());

    let output = FirstStageOutput {
        ldes,
        num_witness_columns,
        witness_tree: witness_subtrees,
        memory_tree: memory_subtrees,
    };

    if DEBUG_QUOTIENT {
        let trace_len = output.ldes[0].trace.len();
        let mut exec_trace_view = output.ldes[0].trace.row_view(0..(trace_len - 1));
        for _ in 0..trace_len - 1 {
            let row = unsafe {
                exec_trace_view
                    .current_row_ref()
                    .split_at_unchecked(num_witness_columns)
                    .1
            };
            for (_access_idx, mem_query) in compiled_circuit
                .memory_layout
                .batched_ram_accesses
                .iter()
                .enumerate()
            {
                let read_value_columns = mem_query.get_read_timestamp_columns();
                let read_timestamp_columns = mem_query.get_read_timestamp_columns();
                let address_low = read_value(
                    ColumnAddress::MemorySubtree(read_value_columns.start()),
                    &[],
                    row,
                );
                let address_high = read_value(
                    ColumnAddress::MemorySubtree(read_value_columns.start() + 1),
                    &[],
                    row,
                );

                assert!(address_low.to_reduced_u32() < (1 << 16));
                assert!(address_high.to_reduced_u32() < (1 << 16));

                let read_timestamp_low = read_value(
                    ColumnAddress::MemorySubtree(read_timestamp_columns.start()),
                    &[],
                    row,
                );
                let read_timestamp_high = read_value(
                    ColumnAddress::MemorySubtree(read_timestamp_columns.start() + 1),
                    &[],
                    row,
                );

                assert!(read_timestamp_low.to_reduced_u32() < (1 << 16));
                assert!(read_timestamp_high.to_reduced_u32() < (1 << 16));
            }
            exec_trace_view.advance_row();
        }
    }

    output
}
