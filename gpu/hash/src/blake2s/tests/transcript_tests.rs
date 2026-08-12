use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::{BF, E4};
use rand::Rng;
#[cfg(feature = "deterministic_pow")]
use worker::Worker;

use super::super::*;

use super::{bitreverse_index, BLOCK_SIZE};
use crate::upstream::{
    draw_random_field_els, Blake2sState, Blake2sTranscript, Field, Seed, USE_REDUCED_BLAKE2_ROUNDS,
};

#[test]
fn pow() {
    const BITS_COUNT: u32 = 24;
    let h_seed = [42u32; STATE_SIZE];
    let mut h_result = [0u64; 1];
    let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
    let mut d_result = DeviceAllocation::alloc(1).unwrap();
    let stream = CudaStream::default();
    memory_copy_async(&mut d_seed, &h_seed, &stream).unwrap();
    blake2s_pow(&d_seed, BITS_COUNT, &mut d_result[0], &stream).unwrap();
    memory_copy_async(&mut h_result, &d_result, &stream).unwrap();
    stream.synchronize().unwrap();
    let mut state = Blake2sState::new();
    let mut block = [0; BLOCK_SIZE];
    block[..STATE_SIZE].copy_from_slice(&h_seed);
    block[STATE_SIZE] = h_result[0] as u32;
    block[STATE_SIZE + 1] = (h_result[0] >> 32) as u32;
    let mut digest = Digest::default();
    state.absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(&block, STATE_SIZE + 2, &mut digest);
    assert!(digest[0].leading_zeros() >= BITS_COUNT);
}

// Feature-gated: run with `--features deterministic_pow` (not part of the
// default suite). The CPU reference is kept deterministic via the dev-dep
// `transcript/deterministic_pow` feature; without it both sides return
// first-found nonces and the comparison is meaningless.
#[cfg(feature = "deterministic_pow")]
#[test]
fn pow_deterministic_matches_cpu_baseline() {
    let seeds = [
        Seed([0, 1, 2, 3, 4, 5, 6, 7]),
        Seed([42, 42, 42, 42, 42, 42, 42, 42]),
        Seed([
            0x01234567, 0x89abcdef, 0xfedcba98, 0x76543210, 0x0f0f0f0f, 0xf0f0f0f0, 0x13579bdf,
            0x2468ace0,
        ]),
    ];
    let worker = Worker::new_with_num_threads(4);
    let stream = CudaStream::default();

    for seed in seeds {
        for pow_bits in [17, 18, 20] {
            let (_, expected_nonce) = Blake2sTranscript::search_pow(&seed, pow_bits, &worker);
            let mut h_result = [0u64; 1];
            let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
            let mut d_result = DeviceAllocation::alloc(1).unwrap();
            memory_copy_async(&mut d_seed, &seed.0, &stream).unwrap();
            blake2s_pow(&d_seed, pow_bits, &mut d_result[0], &stream).unwrap();
            memory_copy_async(&mut h_result, &d_result, &stream).unwrap();
            stream.synchronize().unwrap();
            assert_eq!(
                h_result[0], expected_nonce,
                "seed={seed:?}, pow_bits={pow_bits}"
            );
        }
    }
}

// -----------------------------------------------------------------------
// Device-side transcript parity tests
// -----------------------------------------------------------------------

/// Helper: run device-side transcript_commit and return the resulting seed.
fn device_commit(seed: &[u32; STATE_SIZE], input: &[u32]) -> [u32; STATE_SIZE] {
    let stream = CudaStream::default();
    let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
    let mut d_input = DeviceAllocation::alloc(input.len()).unwrap();
    memory_copy_async(&mut d_seed, &seed[..], &stream).unwrap();
    memory_copy_async(&mut d_input, input, &stream).unwrap();
    super::transcript_commit(&mut d_seed, &d_input, &stream).unwrap();
    let mut h_result = [0u32; STATE_SIZE];
    memory_copy_async(&mut h_result[..], &d_seed, &stream).unwrap();
    stream.synchronize().unwrap();
    h_result
}

/// Helper: run host-side commit_initial and return the resulting seed.
fn host_commit_initial(input: &[u32]) -> [u32; STATE_SIZE] {
    Blake2sTranscript::commit_initial(input).0
}

/// Helper: run host-side commit_with_seed and return the resulting seed.
fn host_commit(seed: &[u32; STATE_SIZE], input: &[u32]) -> [u32; STATE_SIZE] {
    let mut s = Seed(*seed);
    Blake2sTranscript::commit_with_seed(&mut s, input);
    s.0
}

#[test]
fn transcript_commit_parity_two_blocks() {
    // 8 + 12 = 20 words — two blocks (16 + 4). The load-bearing backward
    // sumcheck case: commit_field_els with 3 E4 elements. Kept as an explicit
    // named case; the randomized sweep below covers the other block counts.
    let seed = [0x42; STATE_SIZE];
    let input: Vec<u32> = (100..112).collect();
    assert_eq!(device_commit(&seed, &input), host_commit(&seed, &input));
}

#[test]
fn transcript_commit_parity_randomized() {
    let mut rng = rand::rng();
    let stream = CudaStream::default();
    for input_len in [1, 4, 7, 8, 12, 15, 16, 20, 24, 31, 32, 48, 64] {
        let seed: [u32; STATE_SIZE] = std::array::from_fn(|_| rng.random());
        let input: Vec<u32> = (0..input_len).map(|_| rng.random()).collect();

        let expected = host_commit(&seed, &input);

        let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
        let mut d_input = DeviceAllocation::alloc(input_len).unwrap();
        memory_copy_async(&mut d_seed, &seed[..], &stream).unwrap();
        memory_copy_async(&mut d_input, &input, &stream).unwrap();
        super::transcript_commit(&mut d_seed, &d_input, &stream).unwrap();
        let mut actual = [0u32; STATE_SIZE];
        memory_copy_async(&mut actual[..], &d_seed, &stream).unwrap();
        stream.synchronize().unwrap();

        assert_eq!(
            actual, expected,
            "commit mismatch for input_len={input_len}"
        );
    }
}

/// Helper: run device-side `transcript_commit_initial_chunked` over
/// `chunks` (host-resident u32 slices) and return the resulting seed.
/// Each chunk is staged into its own device allocation so the kernel
/// receives separate source pointers.
fn device_commit_initial_chunked(chunks: &[Vec<u32>]) -> [u32; STATE_SIZE] {
    let stream = CudaStream::default();
    let mut d_chunks: Vec<DeviceAllocation<u32>> = chunks
        .iter()
        .map(|c| DeviceAllocation::alloc(c.len().max(1)).unwrap())
        .collect();
    for (d, h) in d_chunks.iter_mut().zip(chunks.iter()) {
        if !h.is_empty() {
            memory_copy_async(d, &h[..], &stream).unwrap();
        }
    }
    let chunk_args: Vec<(*const u32, u32)> = d_chunks
        .iter()
        .zip(chunks.iter())
        .map(|(d, h)| (d.as_ptr(), h.len() as u32))
        .collect();
    let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
    super::transcript_commit_initial_chunked(&mut d_seed, &chunk_args, &stream).unwrap();
    let mut h_seed = [0u32; STATE_SIZE];
    memory_copy_async(&mut h_seed[..], &d_seed, &stream).unwrap();
    stream.synchronize().unwrap();
    h_seed
}

#[test]
fn transcript_commit_initial_chunked_parity_block_aligned_split() {
    // Two chunks split exactly on a 16-word block boundary — the one edge the
    // randomized sweep below almost never hits. Other chunk counts and
    // mid-block splits (incl. the 5-chunk production pack shape) are covered
    // by the randomized test.
    let total: Vec<u32> = (0..32).collect();
    let chunks = vec![total[..16].to_vec(), total[16..].to_vec()];
    assert_eq!(
        device_commit_initial_chunked(&chunks),
        host_commit_initial(&total)
    );
}

#[test]
fn transcript_commit_initial_chunked_parity_randomized() {
    let mut rng = rand::rng();
    for total_len in [1usize, 4, 8, 16, 17, 20, 32, 48, 64, 100, 128, 256, 512] {
        let total: Vec<u32> = (0..total_len).map(|_| rng.random()).collect();
        // Pick 1..=5 chunk count; partition `total` into that many chunks
        // with mostly arbitrary boundaries.
        for num_chunks in [1usize, 2, 3, 5] {
            if num_chunks > total_len {
                continue;
            }
            let mut bounds: Vec<usize> = (0..num_chunks - 1)
                .map(|_| rng.random_range(1..total_len))
                .collect();
            bounds.sort();
            let mut chunks = Vec::with_capacity(num_chunks);
            let mut start = 0usize;
            for b in bounds {
                chunks.push(total[start..b].to_vec());
                start = b;
            }
            chunks.push(total[start..].to_vec());
            let actual = device_commit_initial_chunked(&chunks);
            let expected = host_commit_initial(&total);
            assert_eq!(
                actual, expected,
                "chunked commit_initial mismatch for total_len={total_len}, num_chunks={num_chunks}"
            );
        }
    }
}

#[test]
fn gather_tree_caps_inline_parity() {
    let stream = CudaStream::default();
    // Consolidated form: one contiguous backing of length `coset_count * stride`;
    // the kernel walks `base + natural_idx * stride` and writes to the
    // bit-reversed destination slot `dst[bitreverse(natural_idx, log_lde) * cap_words..]`.
    // Tight pack (`stride == cap_words_per_coset`) for the parity case.
    for &(cap_words_per_coset, coset_count) in
        &[(8usize, 1usize), (16, 2), (32, 4), (64, 8), (256, 4)]
    {
        let stride = cap_words_per_coset;
        let log_lde_factor = coset_count.trailing_zeros();
        let mut d_source: DeviceAllocation<u32> =
            DeviceAllocation::alloc(coset_count * stride).unwrap();
        let mut h_source: Vec<u32> = Vec::with_capacity(coset_count * stride);
        for i in 0..coset_count {
            for j in 0..stride {
                h_source.push(((i as u32) << 24) | (j as u32));
            }
        }
        memory_copy_async(&mut d_source, &h_source[..], &stream).unwrap();
        let mut d_dst: DeviceAllocation<u32> =
            DeviceAllocation::alloc(coset_count * cap_words_per_coset).unwrap();
        super::gather_tree_caps_inline(
            d_source.as_ptr(),
            cap_words_per_coset as u32,
            stride as u32,
            log_lde_factor,
            &mut d_dst,
            &stream,
        )
        .unwrap();
        let mut h_dst: Vec<u32> = vec![0u32; coset_count * cap_words_per_coset];
        memory_copy_async(&mut h_dst[..], &d_dst, &stream).unwrap();
        stream.synchronize().unwrap();
        for natural_idx in 0..coset_count {
            let bitrev_pos = bitreverse_index(natural_idx, log_lde_factor);
            let actual =
                &h_dst[bitrev_pos * cap_words_per_coset..(bitrev_pos + 1) * cap_words_per_coset];
            let expected =
                &h_source[natural_idx * stride..natural_idx * stride + cap_words_per_coset];
            assert_eq!(
                actual, expected,
                "gather mismatch for natural_idx {natural_idx} -> bitrev_pos {bitrev_pos} \
                 (cap_words={cap_words_per_coset}, count={coset_count})"
            );
        }
    }
}

#[test]
fn gather_tree_caps_inline_stride_greater_than_cap_words() {
    let stream = CudaStream::default();
    // Production case: the cap region sits at the tail of each per-coset
    // tree segment, so the source pointer is `backing + (segment_len - 2 * cap_size)`
    // and the stride equals `segment_len` (in u32 words).
    let cap_words_per_coset = 8usize;
    let stride = 32usize;
    let coset_count = 4usize;
    let log_lde_factor = coset_count.trailing_zeros();

    let mut d_source: DeviceAllocation<u32> =
        DeviceAllocation::alloc(coset_count * stride).unwrap();
    let mut h_source = vec![0u32; coset_count * stride];
    for i in 0..coset_count {
        let tail = (i + 1) * stride - cap_words_per_coset;
        for j in 0..cap_words_per_coset {
            h_source[tail + j] = ((i as u32) << 24) | (j as u32) | 0x4000_0000;
        }
    }
    memory_copy_async(&mut d_source, &h_source[..], &stream).unwrap();
    let mut d_dst: DeviceAllocation<u32> =
        DeviceAllocation::alloc(coset_count * cap_words_per_coset).unwrap();

    // Pass `base = d_source + (stride - cap_words_per_coset)` so the kernel
    // reads the cap-region tail of each per-coset segment.
    let tail_offset = stride - cap_words_per_coset;
    let base = unsafe { d_source.as_ptr().add(tail_offset) };
    super::gather_tree_caps_inline(
        base,
        cap_words_per_coset as u32,
        stride as u32,
        log_lde_factor,
        &mut d_dst,
        &stream,
    )
    .unwrap();
    let mut h_dst = vec![0u32; coset_count * cap_words_per_coset];
    memory_copy_async(&mut h_dst[..], &d_dst, &stream).unwrap();
    stream.synchronize().unwrap();
    for natural_idx in 0..coset_count {
        let bitrev_pos = bitreverse_index(natural_idx, log_lde_factor);
        let actual =
            &h_dst[bitrev_pos * cap_words_per_coset..(bitrev_pos + 1) * cap_words_per_coset];
        let tail = (natural_idx + 1) * stride - cap_words_per_coset;
        let expected = &h_source[tail..tail + cap_words_per_coset];
        assert_eq!(
            actual, expected,
            "stride-aware gather mismatch for natural_idx {natural_idx} -> bitrev_pos {bitrev_pos}"
        );
    }
}

#[test]
fn gather_e_addresses_parity() {
    let stream = CudaStream::default();
    // Each address holds `elements_per_addr` E4 values; the kernel copies
    // them into a contiguous destination in `src_ptrs` order.
    for &(elements_per_addr, num_addresses) in
        &[(1usize, 1usize), (2, 1), (4, 1), (2, 5), (4, 8), (8, 16)]
    {
        let mut d_sources: Vec<DeviceAllocation<u32>> = (0..num_addresses)
            .map(|_| DeviceAllocation::alloc(elements_per_addr * 4).unwrap())
            .collect();
        let mut h_sources: Vec<Vec<u32>> = Vec::with_capacity(num_addresses);
        for (i, d) in d_sources.iter_mut().enumerate() {
            let pattern: Vec<u32> = (0..elements_per_addr * 4)
                .map(|j| ((i as u32) << 24) | (j as u32))
                .collect();
            memory_copy_async(d, &pattern[..], &stream).unwrap();
            h_sources.push(pattern);
        }
        let src_ptrs: Vec<u64> = d_sources.iter().map(|d| d.as_ptr() as u64).collect();
        let mut d_dst: DeviceAllocation<E4> =
            DeviceAllocation::alloc(num_addresses * elements_per_addr).unwrap();
        super::gather_e_addresses(&src_ptrs[..], &mut d_dst, &stream).unwrap();
        let mut h_dst_words: Vec<u32> = vec![0u32; num_addresses * elements_per_addr * 4];
        let d_dst_as_u32 = unsafe { d_dst.transmute::<u32>() };
        memory_copy_async(&mut h_dst_words[..], d_dst_as_u32, &stream).unwrap();
        stream.synchronize().unwrap();
        for (addr_idx, expected) in h_sources.iter().enumerate() {
            let words_per_addr = elements_per_addr * 4;
            let actual = &h_dst_words[addr_idx * words_per_addr..(addr_idx + 1) * words_per_addr];
            assert_eq!(
                actual, &expected[..],
                "gather mismatch for address {addr_idx} (elements_per_addr={elements_per_addr}, num_addresses={num_addresses})"
            );
        }
    }
}

/// Helper: run device-side transcript_squeeze and return output + final seed.
fn device_squeeze(seed: &[u32; STATE_SIZE], output_len: usize) -> (Vec<u32>, [u32; STATE_SIZE]) {
    let stream = CudaStream::default();
    let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
    let mut d_output = DeviceAllocation::alloc(output_len).unwrap();
    memory_copy_async(&mut d_seed, &seed[..], &stream).unwrap();
    super::transcript_squeeze(&mut d_seed, &mut d_output, &stream).unwrap();
    let mut h_output = vec![0u32; output_len];
    let mut h_seed = [0u32; STATE_SIZE];
    memory_copy_async(&mut h_output, &d_output, &stream).unwrap();
    memory_copy_async(&mut h_seed[..], &d_seed, &stream).unwrap();
    stream.synchronize().unwrap();
    (h_output, h_seed)
}

/// Helper: run host-side draw_randomness and return output + final seed.
fn host_squeeze(seed: &[u32; STATE_SIZE], output_len: usize) -> (Vec<u32>, [u32; STATE_SIZE]) {
    let mut s = Seed(*seed);
    let mut output = vec![0u32; output_len];
    Blake2sTranscript::draw_randomness(&mut s, &mut output);
    (output, s.0)
}

#[test]
fn transcript_squeeze_parity_one_round() {
    // 8 words = 1 round, seed unchanged, output = seed.
    let seed = [10, 20, 30, 40, 50, 60, 70, 80];
    let (d_out, d_seed) = device_squeeze(&seed, STATE_SIZE);
    let (h_out, h_seed) = host_squeeze(&seed, STATE_SIZE);
    assert_eq!(d_out, h_out);
    assert_eq!(d_seed, h_seed);
    // Seed must be unchanged for single-round squeeze.
    assert_eq!(d_seed, seed);
}

#[test]
fn transcript_squeeze_parity_two_rounds() {
    // 16 words = 2 rounds. Second round hashes the seed.
    let seed = [0xff; STATE_SIZE];
    let (d_out, d_seed) = device_squeeze(&seed, STATE_SIZE * 2);
    let (h_out, h_seed) = host_squeeze(&seed, STATE_SIZE * 2);
    assert_eq!(d_out, h_out);
    assert_eq!(d_seed, h_seed);
}

#[test]
fn transcript_squeeze_parity_many_rounds() {
    // 40 words = 5 rounds.
    let seed = [0x42; STATE_SIZE];
    let (d_out, d_seed) = device_squeeze(&seed, STATE_SIZE * 5);
    let (h_out, h_seed) = host_squeeze(&seed, STATE_SIZE * 5);
    assert_eq!(d_out, h_out);
    assert_eq!(d_seed, h_seed);
}

#[test]
fn transcript_commit_then_squeeze_parity() {
    // Simulates the backward sumcheck pattern: commit 3 E4 coefficients (12
    // words), then draw 1 E4 challenge (4 words, padded to 8 = 1 round).
    let seed = [0xab; STATE_SIZE];
    let coeffs: Vec<u32> = (0..12).collect();

    // Host path.
    let mut h_seed = Seed(seed);
    Blake2sTranscript::commit_with_seed(&mut h_seed, &coeffs);
    let mut h_challenge = vec![0u32; STATE_SIZE];
    Blake2sTranscript::draw_randomness(&mut h_seed, &mut h_challenge);

    // Device path.
    let stream = CudaStream::default();
    let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
    let mut d_input = DeviceAllocation::alloc(coeffs.len()).unwrap();
    let mut d_challenge = DeviceAllocation::alloc(STATE_SIZE).unwrap();
    memory_copy_async(&mut d_seed, &seed[..], &stream).unwrap();
    memory_copy_async(&mut d_input, &coeffs, &stream).unwrap();
    super::transcript_commit(&mut d_seed, &d_input, &stream).unwrap();
    super::transcript_squeeze(&mut d_seed, &mut d_challenge, &stream).unwrap();
    let mut actual_seed = [0u32; STATE_SIZE];
    let mut actual_challenge = vec![0u32; STATE_SIZE];
    memory_copy_async(&mut actual_seed[..], &d_seed, &stream).unwrap();
    memory_copy_async(&mut actual_challenge, &d_challenge, &stream).unwrap();
    stream.synchronize().unwrap();

    assert_eq!(actual_seed, h_seed.0);
    assert_eq!(actual_challenge, h_challenge);
}

/// Helper: run device-side `transcript_squeeze_e4` and return output E4s + final seed.
fn device_squeeze_e4(seed: &[u32; STATE_SIZE], count: usize) -> (Vec<E4>, [u32; STATE_SIZE]) {
    let stream = CudaStream::default();
    let mut d_seed = DeviceAllocation::alloc(STATE_SIZE).unwrap();
    let mut d_output: DeviceAllocation<E4> = DeviceAllocation::alloc(count).unwrap();
    memory_copy_async(&mut d_seed, &seed[..], &stream).unwrap();
    super::transcript_squeeze_e4(&mut d_seed, &mut d_output, &stream).unwrap();
    let mut h_output = vec![E4::ZERO; count];
    let mut h_seed = [0u32; STATE_SIZE];
    memory_copy_async(&mut h_output, &d_output, &stream).unwrap();
    memory_copy_async(&mut h_seed[..], &d_seed, &stream).unwrap();
    stream.synchronize().unwrap();
    (h_output, h_seed)
}

/// Helper: host `draw_random_field_els::<BF, E4, Blake2sTranscript>` returning challenges + final seed.
fn host_draw_e4(seed: &[u32; STATE_SIZE], count: usize) -> (Vec<E4>, [u32; STATE_SIZE]) {
    let mut s = Seed(*seed);
    let challenges = draw_random_field_els::<BF, E4, Blake2sTranscript>(&mut s, count);
    (challenges, s.0)
}

#[test]
fn transcript_squeeze_e4_parity_three() {
    // 3 E4 = 12 u32 words, padded to 16 = 2 rounds. The load-bearing case: the
    // initial lookup challenge draw in prove() draws 3 E4 challenges off the
    // seed. Other counts are covered by the randomized sweep below.
    let seed = [0xab; STATE_SIZE];
    let (d_out, d_seed) = device_squeeze_e4(&seed, 3);
    let (h_out, h_seed) = host_draw_e4(&seed, 3);
    assert_eq!(d_out, h_out);
    assert_eq!(d_seed, h_seed);
}

#[test]
fn transcript_squeeze_e4_parity_randomized() {
    let mut rng = rand::rng();
    for count in [1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17] {
        let seed: [u32; STATE_SIZE] = std::array::from_fn(|_| rng.random());
        let (d_out, d_seed) = device_squeeze_e4(&seed, count);
        let (h_out, h_seed) = host_draw_e4(&seed, count);
        assert_eq!(d_out, h_out, "output mismatch for count={count}");
        assert_eq!(d_seed, h_seed, "seed mismatch for count={count}");
    }
}
