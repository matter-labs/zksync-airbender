use super::*;
use blake2s_u32::*;
use fft::bitreverse_enumeration_inplace;

pub fn blake2s_leaf_hashes_for_coset<A: GoodAllocator, B: GoodAllocator, const N: usize>(
    trace: &RowMajorTrace<Mersenne31Field, N, A>,
    bitreverse: bool,
    worker: &Worker,
) -> Vec<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS], B> {
    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();

    let tree_size = trace.len();
    assert!(tree_size.is_power_of_two());

    #[cfg(feature = "timing_logs")]
    let elements_per_leaf = trace.width();

    // simplest job ever - compute by layers with parallelism
    // To prevent to complex parallelism we will work over each individual coset

    let mut leaf_hashes = Vec::with_capacity_in(tree_size, B::default());

    unsafe {
        worker.scope(tree_size, |scope, geometry| {
            let mut dst = &mut leaf_hashes.spare_capacity_mut()[..tree_size];
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);
                let mut trace_view = trace.row_view(range.clone());
                let (dst_chunk, rest) = dst.split_at_mut_unchecked(chunk_size);
                dst = rest;

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut dst_ptr = dst_chunk.as_mut_ptr();
                    let mut hasher = Blake2sState::new();
                    for _i in 0..chunk_size {
                        hasher.reset();
                        let trace_view_row = trace_view.current_row();
                        let only_full_rounds =
                            trace_view_row.len() % BLAKE2S_BLOCK_SIZE_U32_WORDS == 0;
                        let num_full_roudns = trace_view_row.len() / BLAKE2S_BLOCK_SIZE_U32_WORDS;
                        let (array_chunks, remainder) =
                            trace_view_row.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>();
                        let mut array_chunks = array_chunks.into_iter();

                        let write_into = (&mut *dst_ptr).assume_init_mut();
                        for i in 0..num_full_roudns {
                            let last_round = i == num_full_roudns - 1;
                            let chunk = array_chunks.next().unwrap_unchecked();

                            let block = chunk.map(|el| el.to_reduced_u32());

                            if last_round && only_full_rounds {
                                hasher.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
                                    &block,
                                    BLAKE2S_BLOCK_SIZE_U32_WORDS,
                                    write_into,
                                );
                            } else {
                                hasher.absorb::<USE_REDUCED_BLAKE2_ROUNDS>(&block);
                            }
                        }

                        if only_full_rounds == false {
                            let mut block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
                            let len = remainder.len();
                            for i in 0..len {
                                block[i] = remainder[i].to_reduced_u32();
                            }
                            hasher.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
                                &block, len, write_into,
                            );
                        }

                        dst_ptr = dst_ptr.add(1);
                        trace_view.advance_row();
                    }
                });
            }

            assert!(dst.is_empty());
        });

        leaf_hashes.set_len(tree_size)
    };

    #[cfg(feature = "timing_logs")]
    println!(
        "Merkle tree of size 2^{} leaf hashes taken {:?} for {} elements per leaf",
        tree_size.trailing_zeros(),
        now.elapsed(),
        elements_per_leaf,
    );

    if bitreverse {
        bitreverse_enumeration_inplace(&mut leaf_hashes);
    }

    leaf_hashes
}

pub fn blake2s_leaf_hashes_separated_for_coset<
    A: GoodAllocator,
    B: GoodAllocator,
    const N: usize,
>(
    trace: &RowMajorTrace<Mersenne31Field, N, A>,
    separators: &[usize],
    bitreverse: bool,
    worker: &Worker,
) -> Vec<Vec<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS], B>> {
    assert!(
        *separators
            .last()
            .expect("Should contain at least one separator")
            <= trace.width(),
        "Separator is out of bounds"
    );
    for idx in 0..separators.len() - 1 {
        assert!(
            separators[idx] < separators[idx + 1],
            "Separators are not sorted"
        );
    }

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();

    let tree_size = trace.len();
    assert!(tree_size.is_power_of_two());

    #[cfg(feature = "timing_logs")]
    let elements_per_leaf = trace.width();

    // simplest job ever - compute by layers with parallelism
    // To prevent to complex parallelism we will work over each individual coset

    let mut chunk_widths = vec![separators[0]];
    for i in 0..separators.len() - 1 {
        chunk_widths.push(separators[i + 1] - separators[i]);
    }

    let mut leaf_hashes: Vec<_> = (0..separators.len())
        .map(|_| Vec::with_capacity_in(tree_size, B::default()))
        .collect();

    unsafe {
        worker.scope(tree_size, |scope, geometry| {
            let mut dst: Vec<_> = leaf_hashes
                .iter_mut()
                .map(|lh| &mut lh.spare_capacity_mut()[..tree_size])
                .collect();
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let range = chunk_start..(chunk_start + chunk_size);
                let mut trace_view = trace.row_view(range.clone());
                let chunk_widths_clone = chunk_widths.clone();

                let mut rest_chunks = vec![];
                let mut dst_chunks = vec![];

                dst.into_iter().for_each(|dst| {
                    let (dst_chunk, rest) = dst.split_at_mut_unchecked(chunk_size);
                    dst_chunks.push(dst_chunk);
                    rest_chunks.push(rest);
                });
                dst = rest_chunks;

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut dst_ptrs: Vec<_> =
                        dst_chunks.iter_mut().map(|dst| dst.as_mut_ptr()).collect();
                    let mut hasher = Blake2sState::new();
                    for _i in 0..chunk_size {
                        let mut trace_view_row = trace_view.current_row();
                        for j in 0..dst_ptrs.len() {
                            hasher.reset();

                            let (cur_trace_view_row, rest) =
                                trace_view_row.split_at_mut_unchecked(chunk_widths_clone[j]);
                            trace_view_row = rest;

                            let only_full_rounds =
                                chunk_widths_clone[j] % BLAKE2S_BLOCK_SIZE_U32_WORDS == 0;
                            let num_full_roudns =
                                chunk_widths_clone[j] / BLAKE2S_BLOCK_SIZE_U32_WORDS;
                            let (array_chunks, remainder) =
                                cur_trace_view_row.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>();
                            let mut array_chunks = array_chunks.into_iter();

                            let write_into = (&mut *dst_ptrs[j]).assume_init_mut();
                            for i in 0..num_full_roudns {
                                let last_round = i == num_full_roudns - 1;
                                let chunk = array_chunks.next().unwrap_unchecked();

                                let block = chunk.map(|el| el.to_reduced_u32());

                                if last_round && only_full_rounds {
                                    hasher.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
                                        &block,
                                        BLAKE2S_BLOCK_SIZE_U32_WORDS,
                                        write_into,
                                    );
                                } else {
                                    hasher.absorb::<USE_REDUCED_BLAKE2_ROUNDS>(&block);
                                }
                            }

                            if only_full_rounds == false {
                                let mut block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
                                let len = remainder.len();
                                for i in 0..len {
                                    block[i] = remainder[i].to_reduced_u32();
                                }
                                hasher.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
                                    &block, len, write_into,
                                );
                            }
                        }

                        dst_ptrs
                            .iter_mut()
                            .for_each(|dst_ptr| *dst_ptr = dst_ptr.add(1));
                        trace_view.advance_row();
                    }
                });
            }

            assert!(dst.iter().all(|d| d.is_empty()));
        });

        leaf_hashes.iter_mut().for_each(|lh| lh.set_len(tree_size));
    };

    #[cfg(feature = "timing_logs")]
    println!(
        "Merkle tree of size 2^{} leaf hashes taken {:?} for {} elements per leaf",
        tree_size.trailing_zeros(),
        now.elapsed(),
        elements_per_leaf,
    );

    if bitreverse {
        for mut lh in leaf_hashes.iter_mut() {
            bitreverse_enumeration_inplace(&mut lh);
        }
    }

    leaf_hashes
}

pub fn blake2s_leaf_hashes_for_column_major_coset<A: GoodAllocator, B: GoodAllocator>(
    trace: &ColumnMajorTrace<Mersenne31Quartic, A>,
    combine_by: usize,
    bitreverse: bool,
    worker: &Worker,
) -> Vec<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS], B> {
    assert_eq!(
        trace.width(),
        1,
        "we only support it for narrow traces for now"
    );
    assert!(combine_by.is_power_of_two());
    assert_eq!(trace.len() % combine_by, 0);

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();

    let tree_size = trace.len() / combine_by;
    assert!(tree_size.is_power_of_two());

    #[cfg(feature = "timing_logs")]
    let elements_per_leaf = trace.width();

    let leaf_width_in_field_elements = combine_by * trace.width() * 4;

    let num_full_roudns = leaf_width_in_field_elements / BLAKE2S_BLOCK_SIZE_U32_WORDS;
    let remainder = leaf_width_in_field_elements % BLAKE2S_BLOCK_SIZE_U32_WORDS;
    let only_full_rounds = remainder == 0;

    // simplest job ever - compute by layers with parallelism
    // To prevent to complex parallelism we will work over each individual coset

    let mut leaf_hashes = Vec::with_capacity_in(tree_size, B::default());
    let source_column = trace.columns_iter().next().unwrap();

    unsafe {
        worker.scope(tree_size, |scope, geometry| {
            let mut dst = &mut leaf_hashes.spare_capacity_mut()[..tree_size];
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                let _dst_range = chunk_start..(chunk_start + chunk_size);
                let src_range = chunk_start * combine_by..(chunk_start + chunk_size) * combine_by;
                let (dst_chunk, rest) = dst.split_at_mut_unchecked(chunk_size);
                dst = rest;

                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut dst_ptr = dst_chunk.as_mut_ptr();
                    let source_chunk = &source_column[src_range];
                    assert_eq!(source_chunk.len(), chunk_size * combine_by);
                    let mut src_ptr = source_chunk.as_ptr();
                    let mut hasher = Blake2sState::new();
                    for _i in 0..chunk_size {
                        hasher.reset();
                        let src_chunk = core::slice::from_raw_parts(
                            src_ptr.cast::<Mersenne31Field>(),
                            combine_by * 4,
                        );
                        let (array_chunks, remainder) =
                            src_chunk.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>();
                        let mut array_chunks = array_chunks.into_iter();
                        debug_assert_eq!(src_chunk.len(), leaf_width_in_field_elements);

                        let write_into = (&mut *dst_ptr).assume_init_mut();
                        for i in 0..num_full_roudns {
                            let last_round = i == num_full_roudns - 1;
                            let chunk = array_chunks.next().unwrap_unchecked();

                            let block = chunk.map(|el| el.to_reduced_u32());

                            if last_round && only_full_rounds {
                                hasher.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
                                    &block,
                                    BLAKE2S_BLOCK_SIZE_U32_WORDS,
                                    write_into,
                                );
                            } else {
                                hasher.absorb::<USE_REDUCED_BLAKE2_ROUNDS>(&block);
                            }
                        }

                        if only_full_rounds == false {
                            let mut block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
                            let len = remainder.len();
                            for i in 0..len {
                                block[i] = remainder[i].to_reduced_u32();
                            }
                            hasher.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
                                &block, len, write_into,
                            );
                        }

                        dst_ptr = dst_ptr.add(1);
                        src_ptr = src_ptr.add(combine_by);
                    }
                });
            }

            assert!(dst.is_empty());
        });

        leaf_hashes.set_len(tree_size)
    };

    #[cfg(feature = "timing_logs")]
    println!(
        "Merkle tree of size 2^{} leaf hashes taken {:?} for {} elements per leaf",
        tree_size.trailing_zeros(),
        now.elapsed(),
        elements_per_leaf,
    );

    if bitreverse {
        bitreverse_enumeration_inplace(&mut leaf_hashes);
    }

    leaf_hashes
}
