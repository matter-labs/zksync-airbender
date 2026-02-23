use crate::gkr::whir::offsets_vec_for_leaf_construction;

use super::*;
use crate::utils::extension_field_into_base_coeffs;
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
                        let (chunks, remainder) =
                            trace_view_row.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>();
                        let mut chunks = chunks.iter();

                        let write_into = (&mut *dst_ptr).assume_init_mut();
                        for i in 0..num_full_roudns {
                            let last_round = i == num_full_roudns - 1;
                            let chunk = chunks.next().unwrap_unchecked();

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
                            let (chunks, remainder) =
                                cur_trace_view_row.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>();
                            let mut chunks = chunks.iter();

                            let write_into = (&mut *dst_ptrs[j]).assume_init_mut();
                            for i in 0..num_full_roudns {
                                let last_round = i == num_full_roudns - 1;
                                let chunk = chunks.next().unwrap_unchecked();

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
                        let (chunks, remainder) =
                            src_chunk.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>();
                        debug_assert_eq!(src_chunk.len(), leaf_width_in_field_elements);
                        let mut chunks = chunks.iter();

                        let write_into = (&mut *dst_ptr).assume_init_mut();
                        for i in 0..num_full_roudns {
                            let last_round = i == num_full_roudns - 1;
                            let chunk = chunks.next().unwrap_unchecked();

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

pub fn blake2s_leaf_hashes_from_columns<
    F: PrimeField,
    E: FieldExtension<F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    trace: &[&[E]],
    combine_by: usize,
    bitreverse_input: bool,
    bitreverse_output_leaf_hashes: bool,
    worker: &Worker,
) -> Vec<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS], B>
where
    [(); E::DEGREE]: Sized,
{
    let num_columns = trace.len();
    let trace_len = trace[0].len();
    assert!(combine_by.is_power_of_two());
    assert_eq!(trace_len % combine_by, 0);

    for el in trace.iter() {
        assert_eq!(el.len(), trace_len);
    }

    #[cfg(feature = "timing_logs")]
    println!("Constructing Merkle tree from {} columns of size 2^{}, and combining {} elements per poly per leaf", num_columns, trace_len.trailing_zeros(), combine_by);

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();

    let tree_size = trace_len / combine_by;
    assert!(tree_size.is_power_of_two());

    let leaf_width_in_field_elements = combine_by * num_columns * E::DEGREE;

    let num_full_roudns = leaf_width_in_field_elements / BLAKE2S_BLOCK_SIZE_U32_WORDS;
    let remainder = leaf_width_in_field_elements % BLAKE2S_BLOCK_SIZE_U32_WORDS;
    let only_full_rounds = remainder == 0;

    // simplest job ever - compute by layers with parallelism
    // To prevent to complex parallelism we will work over each individual coset

    let mut leaf_hashes = Vec::with_capacity_in(tree_size, B::default());

    if bitreverse_input {
        let offsets = offsets_vec_for_leaf_construction(trace_len, combine_by);
        let offsets_ref = &offsets[..];

        unsafe {
            worker.scope(tree_size, |scope, geometry| {
                let mut dst = &mut leaf_hashes.spare_capacity_mut()[..tree_size];
                for thread_idx in 0..geometry.len() {
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                    let src_range = chunk_start..(chunk_start + chunk_size);
                    let (dst_chunk, rest) = dst.split_at_mut_unchecked(chunk_size);
                    dst = rest;

                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        let mut dst_ptr = dst_chunk.as_mut_ptr();
                        let mut hasher = Blake2sState::new();
                        let mut buffer = Vec::with_capacity(leaf_width_in_field_elements);
                        for i in src_range {
                            hasher.reset();
                            buffer.clear();
                            for column in trace.iter() {
                                for offset in offsets_ref.iter() {
                                    let el = column[i + *offset];
                                    let as_base = extension_field_into_base_coeffs(el)
                                        .map(|el| el.as_u32_raw_repr_reduced());
                                    buffer.extend(as_base);
                                }
                            }
                            debug_assert_eq!(buffer.len(), leaf_width_in_field_elements);

                            let (chunks, remainder) =
                                buffer.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>();
                            let mut chunks = chunks.iter();

                            let write_into = (&mut *dst_ptr).assume_init_mut();
                            for i in 0..num_full_roudns {
                                let last_round = i == num_full_roudns - 1;
                                let block = chunks.next().unwrap_unchecked();

                                if last_round && only_full_rounds {
                                    hasher.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
                                        block,
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
                                block[..len].copy_from_slice(remainder);
                                hasher.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
                                    &block, len, write_into,
                                );
                            }

                            dst_ptr = dst_ptr.add(1);
                        }
                    });
                }

                assert!(dst.is_empty());
            });

            leaf_hashes.set_len(tree_size)
        };
    } else {
        // we just need continuous pieces

        todo!();
    }

    #[cfg(feature = "timing_logs")]
    println!(
        "Merkle tree of size 2^{} leaf hashes taken {:?} for {} elements per leaf",
        tree_size.trailing_zeros(),
        now.elapsed(),
        combine_by,
    );

    if bitreverse_output_leaf_hashes {
        bitreverse_enumeration_inplace(&mut leaf_hashes);
    }

    leaf_hashes
}

pub fn blake2s_leaf_hashes_from_cosets<
    F: PrimeField,
    E: FieldExtension<F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    trace: &[&[&[E]]],
    combine_by: usize,
    bitreverse_evaluations: bool,
    bitreverse_cosets: bool,
    bitreverse_leaf_hashes: bool,
    worker: &Worker,
) -> Vec<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS], B>
where
    [(); E::DEGREE]: Sized,
{
    let num_cosets = trace.len();
    let num_columns = trace[0].len();
    let trace_len = trace[0][0].len();
    assert!(combine_by.is_power_of_two());
    assert_eq!(trace_len % combine_by, 0);

    for el in trace.iter() {
        assert_eq!(el.len(), num_columns);
        for el in el.iter() {
            assert_eq!(el.len(), trace_len);
        }
    }

    #[cfg(feature = "timing_logs")]
    println!("Constructing Merkle tree from {} cosets {} columns of size 2^{}, and combining {} elements per poly per leaf", num_cosets, num_columns, trace_len.trailing_zeros(), combine_by);

    #[cfg(feature = "timing_logs")]
    let now = std::time::Instant::now();

    let coset_tree_size = trace_len / combine_by;
    assert!(coset_tree_size.is_power_of_two());
    let tree_size = num_cosets * coset_tree_size;
    assert!(tree_size.is_power_of_two());

    let leaf_width_in_field_elements = combine_by * num_columns * E::DEGREE;

    let num_full_roudns = leaf_width_in_field_elements / BLAKE2S_BLOCK_SIZE_U32_WORDS;
    let remainder = leaf_width_in_field_elements % BLAKE2S_BLOCK_SIZE_U32_WORDS;
    let only_full_rounds = remainder == 0;

    // simplest job ever - compute by layers with parallelism
    // To prevent to complex parallelism we will work over each individual coset

    let mut leaf_hashes = Vec::with_capacity_in(tree_size, B::default());

    let mut coset_indexes: Vec<usize> = (0..num_cosets).collect();
    if bitreverse_cosets {
        bitreverse_enumeration_inplace(&mut coset_indexes);
    }
    let coset_indexes_ref = &coset_indexes[..];

    let mut coset_destinations = Vec::with_capacity(num_cosets);
    for coset_dst in leaf_hashes.spare_capacity_mut()[..tree_size].chunks_exact_mut(coset_tree_size)
    {
        coset_destinations.push(coset_dst);
    }

    if bitreverse_evaluations {
        let offsets = offsets_vec_for_leaf_construction(trace_len, combine_by);
        let offsets_ref = &offsets[..];

        unsafe {
            worker.scope(coset_tree_size, |scope, geometry| {
                let mut coset_destinations = coset_destinations;
                for thread_idx in 0..geometry.len() {
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                    let mut dests = Vec::with_capacity(num_cosets);
                    let mut new_dests = Vec::with_capacity(num_cosets);
                    for el in coset_destinations.drain(..).into_iter() {
                        let (chunk, rest) = el.split_at_mut(chunk_size);
                        dests.push(chunk);
                        new_dests.push(rest);
                    }
                    core::mem::swap(&mut coset_destinations, &mut new_dests);
                    let src_range = chunk_start..(chunk_start + chunk_size);

                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        let mut hasher = Blake2sState::new();
                        let mut buffer = Vec::with_capacity(leaf_width_in_field_elements);
                        let dests = dests;
                        for (coset_index, dest) in coset_indexes_ref.iter().zip(dests.into_iter()) {
                            let coset = &trace[*coset_index];
                            let mut dst_ptr = dest.as_mut_ptr();
                            for i in src_range.clone() {
                                hasher.reset();
                                buffer.clear();
                                for column in coset.iter() {
                                    for offset in offsets_ref.iter() {
                                        let el = column[i + *offset];
                                        let as_base = extension_field_into_base_coeffs(el)
                                            .map(|el| el.as_u32_raw_repr_reduced());
                                        buffer.extend(as_base);
                                    }
                                }
                                debug_assert_eq!(buffer.len(), leaf_width_in_field_elements);

                                let (chunks, remainder) =
                                    buffer.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>();
                                let mut chunks = chunks.iter();

                                let write_into = (&mut *dst_ptr).assume_init_mut();
                                for i in 0..num_full_roudns {
                                    let last_round = i == num_full_roudns - 1;
                                    let block = chunks.next().unwrap_unchecked();

                                    if last_round && only_full_rounds {
                                        hasher.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
                                            block,
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
                                    block[..len].copy_from_slice(remainder);
                                    hasher.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
                                        &block, len, write_into,
                                    );
                                }

                                dst_ptr = dst_ptr.add(1);
                            }
                        }
                    });
                }

                for el in coset_destinations.into_iter() {
                    assert!(el.is_empty());
                }
            });

            leaf_hashes.set_len(tree_size)
        };
    } else {
        // we just need continuous pieces

        todo!();
    }

    #[cfg(feature = "timing_logs")]
    println!(
        "Merkle tree of size 2^{} leaf hashes taken {:?} for {} elements per leaf",
        tree_size.trailing_zeros(),
        now.elapsed(),
        combine_by,
    );

    if bitreverse_leaf_hashes {
        bitreverse_enumeration_inplace(&mut leaf_hashes);
    }

    leaf_hashes
}
