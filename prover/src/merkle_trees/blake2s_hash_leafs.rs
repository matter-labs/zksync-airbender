use super::*;
use crate::gkr::whir::offsets_vec_for_leaf_construction;
use crate::utils::extension_field_into_base_coeffs;
use blake2s_u32::*;
use fft::bitreverse_enumeration_inplace;
use field::PrimeField;

pub fn blake2s_leaf_hashes_from_columns<
    F: PrimeField,
    E: FieldExtension<F>,
    A: GoodAllocator,
    B: GoodAllocator,
    const USE_REDUCED_BLAKE2_ROUNDS: bool,
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
                                    hasher.absorb::<USE_REDUCED_BLAKE2_ROUNDS>(block);
                                }
                            }

                            if !only_full_rounds {
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

/// Per-thread scratch for the 4-way interleaved leaf hashing (hash states and
/// gather buffers reused across leaves and cosets).
struct LeafHashScratch {
    hashers: [Blake2sState; 4],
    buffers: [Vec<u32>; 4],
    tail_hasher: Blake2sState,
    tail_buffer: Vec<u32>,
}

impl LeafHashScratch {
    fn new(leaf_width: usize) -> Self {
        Self {
            hashers: [Blake2sState::new(); 4],
            buffers: core::array::from_fn(|_| Vec::with_capacity(leaf_width)),
            tail_hasher: Blake2sState::new(),
            tail_buffer: Vec::with_capacity(leaf_width),
        }
    }
}

/// Hash leaves `src_range` of ONE coset into the contiguous destination
/// `dst_ptr`, 4-WAY INTERLEAVED with a scalar tail.
///
/// Why interleaved: gathering one leaf's values and hashing it are perfectly
/// ADDITIVE when done one leaf at a time (measured 12.4 ns gather + 21.0 ns
/// hash = 33.4 ns/leaf at the 26-column base-commit shape) — the OoO window
/// can neither overlap a leaf's strided gather loads with its own absorb
/// (data dependency) nor reach across ~800 instructions of hashing into the
/// next leaf. Four independent hash states let the gathers of three leaves
/// execute UNDER the hash of another AND fill more ALU ports than a single
/// Blake2s dependency chain (measured 19.1 ns/leaf — below the single-chain
/// hash-only ceiling). Digests are untouched: each leaf's absorb sequence is
/// exactly the scalar one, only independent leaves are reordered in time.
unsafe fn hash_coset_leaf_range<
    F: PrimeField,
    E: FieldExtension<F>,
    const USE_REDUCED_BLAKE2_ROUNDS: bool,
>(
    coset: &[&[E]],
    offsets: &[usize],
    src_range: core::ops::Range<usize>,
    mut dst_ptr: *mut core::mem::MaybeUninit<[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]>,
    leaf_width_in_field_elements: usize,
    num_full_roudns: usize,
    only_full_rounds: bool,
    scratch: &mut LeafHashScratch,
) where
    [(); E::DEGREE]: Sized,
{
    const WAYS: usize = 4;
    let hashers = &mut scratch.hashers;
    let buffers = &mut scratch.buffers;

    let mut i = src_range.start;
    while i + WAYS <= src_range.end {
        for w in 0..WAYS {
            hashers[w].reset();
            buffers[w].clear();
        }
        for column in coset.iter() {
            for offset in offsets.iter() {
                for w in 0..WAYS {
                    let el = column[i + w + *offset];
                    let as_base =
                        extension_field_into_base_coeffs(el).map(|el| el.as_u32_raw_repr_reduced());
                    buffers[w].extend(as_base);
                }
            }
        }
        for w in 0..WAYS {
            debug_assert_eq!(buffers[w].len(), leaf_width_in_field_elements);
        }

        for round in 0..num_full_roudns {
            let last_round = round == num_full_roudns - 1;
            for w in 0..WAYS {
                let block = &*(buffers[w]
                    .as_ptr()
                    .add(round * BLAKE2S_BLOCK_SIZE_U32_WORDS)
                    as *const [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS]);
                if last_round && only_full_rounds {
                    let write_into = (&mut *dst_ptr.add(w)).assume_init_mut();
                    hashers[w].absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
                        block,
                        BLAKE2S_BLOCK_SIZE_U32_WORDS,
                        write_into,
                    );
                } else {
                    hashers[w].absorb::<USE_REDUCED_BLAKE2_ROUNDS>(block);
                }
            }
        }

        if only_full_rounds == false {
            let len = leaf_width_in_field_elements % BLAKE2S_BLOCK_SIZE_U32_WORDS;
            for w in 0..WAYS {
                let mut block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
                block[..len]
                    .copy_from_slice(&buffers[w][num_full_roudns * BLAKE2S_BLOCK_SIZE_U32_WORDS..]);
                let write_into = (&mut *dst_ptr.add(w)).assume_init_mut();
                hashers[w].absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(&block, len, write_into);
            }
        }

        dst_ptr = dst_ptr.add(WAYS);
        i += WAYS;
    }

    // scalar tail for the last < WAYS leaves
    let hasher = &mut scratch.tail_hasher;
    let buffer = &mut scratch.tail_buffer;
    for i in i..src_range.end {
        hasher.reset();
        buffer.clear();
        for column in coset.iter() {
            for offset in offsets.iter() {
                let el = column[i + *offset];
                let as_base =
                    extension_field_into_base_coeffs(el).map(|el| el.as_u32_raw_repr_reduced());
                buffer.extend(as_base);
            }
        }
        debug_assert_eq!(buffer.len(), leaf_width_in_field_elements);

        let (chunks, remainder) = buffer.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>();
        let mut chunks = chunks.iter();

        let write_into = (&mut *dst_ptr).assume_init_mut();
        for k in 0..num_full_roudns {
            let last_round = k == num_full_roudns - 1;
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
            hasher.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(&block, len, write_into);
        }

        dst_ptr = dst_ptr.add(1);
    }
}

pub fn blake2s_leaf_hashes_from_cosets<
    F: PrimeField,
    E: FieldExtension<F>,
    B: GoodAllocator,
    const USE_REDUCED_BLAKE2_ROUNDS: bool,
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

        // Scheduling: the historical scheme chunks LEAF INDICES within every
        // coset over the threads — its parallelism is capped at
        // `coset_tree_size`, and every thread touches every coset. For MANY
        // SMALL cosets (the late intermediate oracles: 524288 cosets of 16
        // leaves) that means 12+ threads fighting over 16 leaf slots while
        // walking half a million coset descriptors each. In that regime chunk
        // WHOLE COSETS over the threads instead ("thread per N cosets"):
        // perfect balance, one coset walked by exactly one thread, and the
        // destination chunks stay contiguous per thread.
        let over_cosets = num_cosets >= 4 * worker.get_num_cores();
        if over_cosets {
            unsafe {
                worker.scope(num_cosets, |scope, geometry| {
                    let mut coset_destinations = coset_destinations;
                    let mut idx_rest = coset_indexes_ref;
                    for thread_idx in 0..geometry.len() {
                        let chunk = geometry.get_chunk_size(thread_idx);
                        let dests: Vec<_> = coset_destinations.drain(..chunk).collect();
                        let (idx_chunk, rest) = idx_rest.split_at(chunk);
                        idx_rest = rest;
                        Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                            let mut scratch = LeafHashScratch::new(leaf_width_in_field_elements);
                            for (coset_index, dest) in idx_chunk.iter().zip(dests.into_iter()) {
                                let coset = &trace[*coset_index];
                                hash_coset_leaf_range::<F, E, USE_REDUCED_BLAKE2_ROUNDS>(
                                    coset,
                                    offsets_ref,
                                    0..coset_tree_size,
                                    dest.as_mut_ptr(),
                                    leaf_width_in_field_elements,
                                    num_full_roudns,
                                    only_full_rounds,
                                    &mut scratch,
                                );
                            }
                        });
                    }
                    assert!(coset_destinations.is_empty());
                });

                leaf_hashes.set_len(tree_size)
            };
        } else {
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
                            let mut scratch = LeafHashScratch::new(leaf_width_in_field_elements);
                            for (coset_index, dest) in
                                coset_indexes_ref.iter().zip(dests.into_iter())
                            {
                                let coset = &trace[*coset_index];
                                hash_coset_leaf_range::<F, E, USE_REDUCED_BLAKE2_ROUNDS>(
                                    coset,
                                    offsets_ref,
                                    src_range.clone(),
                                    dest.as_mut_ptr(),
                                    leaf_width_in_field_elements,
                                    num_full_roudns,
                                    only_full_rounds,
                                    &mut scratch,
                                );
                            }
                        });
                    }

                    for el in coset_destinations.into_iter() {
                        assert!(el.is_empty());
                    }
                });

                leaf_hashes.set_len(tree_size)
            };
        }
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

#[cfg(test)]
mod tests {
    use super::*;
    use field::baby_bear::base::BabyBearField;
    use field::Rand;

    /// The 4-way interleaved leaf hashing must produce exactly the digests of
    /// a naive per-leaf scalar computation, including the < WAYS tail and
    /// across worker chunk boundaries.
    #[test]
    fn interleaved_leaf_hashes_match_scalar_reference() {
        type F = BabyBearField;
        let mut rng = rand::rng();
        // the last two shapes trigger the "thread per N cosets" branch
        // (num_cosets >= 4 x threads)
        for (trace_len, num_cols, combine_by, threads, num_cosets) in [
            (64usize, 3usize, 2usize, 3usize, 2usize),
            (128, 26, 2, 5, 2),
            (256, 1, 8, 4, 2),
            (32, 3, 2, 2, 16),
            (16, 1, 4, 3, 64),
        ] {
            let worker = Worker::new_with_num_threads(threads);
            let cosets: Vec<Vec<Vec<F>>> = (0..num_cosets)
                .map(|_| {
                    (0..num_cols)
                        .map(|_| {
                            (0..trace_len)
                                .map(|_| F::random_element(&mut rng))
                                .collect()
                        })
                        .collect()
                })
                .collect();
            let coset_refs: Vec<Vec<&[F]>> = cosets
                .iter()
                .map(|c| c.iter().map(|col| &col[..]).collect())
                .collect();
            let trace: Vec<&[&[F]]> = coset_refs.iter().map(|c| &c[..]).collect();

            let got = blake2s_leaf_hashes_from_cosets::<F, F, std::alloc::Global, true>(
                &trace, combine_by, true, true, false, &worker,
            );

            // naive reference: per-leaf scalar absorb sequence
            let offsets = offsets_vec_for_leaf_construction(trace_len, combine_by);
            let mut coset_indexes: Vec<usize> = (0..trace.len()).collect();
            bitreverse_enumeration_inplace(&mut coset_indexes);
            let coset_tree_size = trace_len / combine_by;
            let leaf_w = combine_by * num_cols;
            let mut expected = Vec::new();
            for coset_index in coset_indexes.iter() {
                let coset = &trace[*coset_index];
                for i in 0..coset_tree_size {
                    let mut buffer: Vec<u32> = Vec::new();
                    for column in coset.iter() {
                        for offset in offsets.iter() {
                            buffer.push(column[i + *offset].as_u32_raw_repr_reduced());
                        }
                    }
                    assert_eq!(buffer.len(), leaf_w);
                    let mut hasher = Blake2sState::new();
                    let mut dst = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
                    let (chunks, remainder) = buffer.as_chunks::<BLAKE2S_BLOCK_SIZE_U32_WORDS>();
                    let only_full = remainder.is_empty();
                    let n_full = chunks.len();
                    for (k, block) in chunks.iter().enumerate() {
                        if k == n_full - 1 && only_full {
                            hasher.absorb_final_block::<true>(
                                block,
                                BLAKE2S_BLOCK_SIZE_U32_WORDS,
                                &mut dst,
                            );
                        } else {
                            hasher.absorb::<true>(block);
                        }
                    }
                    if !only_full {
                        let mut block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
                        block[..remainder.len()].copy_from_slice(remainder);
                        hasher.absorb_final_block::<true>(&block, remainder.len(), &mut dst);
                    }
                    expected.push(dst);
                }
            }
            assert_eq!(
                &got[..],
                &expected[..],
                "diverged at trace_len={trace_len} cols={num_cols} combine={combine_by} threads={threads}"
            );
        }
    }
}
