// NOTE: These oracles are not guaranteed to be used at all for CPU provers,
// but implementations are given for ease of porting of the same functionality on GPU

use crate::{definitions::LazyInitAndTeardown, ShuffleRamSetupAndTeardown};
use cs::definitions::{TimestampData, TimestampScalar};
use fft::GoodAllocator;
use worker::Worker;

pub mod delegation_oracle;
pub mod main_risc_v_circuit;

pub fn chunk_lazy_init_and_teardown<A: GoodAllocator>(
    total_num_chunks: usize,
    inits_chunk_size: usize,
    data: &[Vec<(u32, (TimestampScalar, u32))>],
    worker: &Worker,
) -> (
    usize, // number of empty ones to assume
    Vec<ShuffleRamSetupAndTeardown<A>>,
) {
    let now = std::time::Instant::now();

    assert!(data.len() > 0);
    let total_input_len: usize = data.iter().map(|el| el.len()).sum();

    let num_non_empty_ones = total_input_len.next_multiple_of(inits_chunk_size) / inits_chunk_size;

    assert!(num_non_empty_ones <= total_num_chunks);

    #[derive(Clone, Copy, Debug)]
    struct Chunk {
        starting_idx: usize,
        starting_offset: usize,
        end_idx: usize,
        end_offset: usize,
        prepadding: usize,
    }

    // determine chunk points
    let mut chunks = Vec::with_capacity(num_non_empty_ones);
    let mut current_end = (data.len() - 1, data.last().unwrap().len());

    for _ in 0..num_non_empty_ones {
        let mut to_fill = inits_chunk_size;
        let (idx, pos) = current_end;
        let mut chunk = Chunk {
            starting_idx: idx,
            starting_offset: pos,
            end_idx: idx,
            end_offset: pos,
            prepadding: 0,
        };
        while to_fill != 0 {
            if chunk.starting_offset != 0 {
                // process non-empty chunk
                if to_fill >= chunk.starting_offset {
                    // take in full and continue
                    to_fill -= chunk.starting_offset;
                    chunk.starting_offset = 0;
                } else {
                    chunk.starting_offset -= to_fill;
                    to_fill = 0;
                }
            } else {
                // offset is 0 here
                if chunk.starting_idx == 0 {
                    // we need prepadding
                    chunk.prepadding = to_fill;
                    to_fill = 0;
                } else {
                    // move to the next chunk
                    chunk.starting_idx -= 1;
                    chunk.starting_offset = data[chunk.starting_idx].len();
                }
            }
        }

        current_end = (chunk.starting_idx, chunk.starting_offset);

        chunks.push(chunk);
    }

    assert_eq!(chunks.len(), num_non_empty_ones);
    chunks.reverse();

    // then in parallel copy the chunk to destinations

    let mut results = Vec::with_capacity(num_non_empty_ones);
    let mut dst = &mut results.spare_capacity_mut()[..num_non_empty_ones];
    let src_ref = &chunks;

    worker.scope(num_non_empty_ones, |scope, geometry| {
        for i in 0..geometry.len() {
            let chunk_size = geometry.get_chunk_size(i);
            let chunk_start = geometry.get_chunk_start_pos(i);
            let (dst_chunk, rest) = dst.split_at_mut(chunk_size);
            dst = rest;
            let range = chunk_start..(chunk_start + chunk_size);
            let src = &src_ref[range];

            Worker::smart_spawn(scope, i == geometry.len() - 1, move |_| {
                for (dst, src) in dst_chunk.iter_mut().zip(src.iter()) {
                    let mut lazy_init_data: Vec<LazyInitAndTeardown, A> =
                        Vec::with_capacity_in(chunk_size.next_power_of_two(), A::default());

                    let mut src = *src;

                    if src.prepadding > 0 {
                        lazy_init_data.resize(src.prepadding, Default::default());
                    }

                    // just fill
                    loop {
                        if src.starting_idx == src.end_idx {
                            let data = &data[src.starting_idx];
                            for idx in src.starting_offset..src.end_offset {
                                let address = data[idx].0;
                                let (ts, value) = data[idx].1;
                                let data = LazyInitAndTeardown {
                                    address,
                                    teardown_value: value,
                                    teardown_timestamp: TimestampData::from_scalar(ts),
                                };
                                lazy_init_data.push(data);
                            }
                            break;
                        } else {
                            let data = &data[src.starting_idx];
                            let end_idx = data.len();
                            for idx in src.starting_offset..end_idx {
                                let address = data[idx].0;
                                let (ts, value) = data[idx].1;
                                let data = LazyInitAndTeardown {
                                    address,
                                    teardown_value: value,
                                    teardown_timestamp: TimestampData::from_scalar(ts),
                                };
                                lazy_init_data.push(data);
                            }

                            src.starting_idx += 1;
                            src.starting_offset = 0;
                        }
                    }

                    assert_eq!(lazy_init_data.len(), inits_chunk_size);

                    let data = ShuffleRamSetupAndTeardown { lazy_init_data };
                    dst.write(data);
                }
            });
        }

        assert!(dst.is_empty());
    });

    unsafe { results.set_len(num_non_empty_ones) };

    println!(
        "Chunking and materialization of lazy init/teardown took {:?}",
        now.elapsed()
    );

    (total_num_chunks - num_non_empty_ones, results)
}
