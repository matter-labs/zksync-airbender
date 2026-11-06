use super::*;

use blake2::*;

#[test]
fn single_round_debug() {
    let input_block = [0u32; 16];
    // input_block[0] = u32::from_le_bytes([1, 2, 3, 4]);
    let mut hasher = crate::baseline::Blake2sState::new();
    let mut u32_result = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
    hasher.absorb_final_block::<false>(&input_block, 0, &mut u32_result);
    println!("0x{:08x}", u32_result[0]);
}

#[test]
fn check_single_round_consistency() {
    let len_words = 4;
    let mut input_bytes = vec![0u8; len_words * 4];
    for (i, el) in input_bytes.iter_mut().enumerate() {
        *el = i as u8;
    }

    let mut input_as_u32_block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    for (dst, src) in input_as_u32_block
        .iter_mut()
        .zip(input_bytes.as_chunks::<4>().0)
    {
        *dst = u32::from_le_bytes(*src);
    }

    let naive_result = Blake2s256::digest(&input_bytes);

    let mut hasher = Blake2sState::new();
    let mut u32_result = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
    hasher.absorb_final_block::<false>(&input_as_u32_block, len_words, &mut u32_result);

    for (i, (a, b)) in u32_result
        .iter()
        .zip(naive_result.as_slice().as_chunks::<4>().0)
        .enumerate()
    {
        let b = u32::from_le_bytes(*b);
        assert_eq!(*a, b, "failed at word {}", i);
    }
}

#[test]
fn check_two_rounds_consistency() {
    let tail = 4;
    let len_words = BLAKE2S_BLOCK_SIZE_U32_WORDS + tail;
    let mut input_bytes = vec![0u8; len_words * 4];
    for (i, el) in input_bytes.iter_mut().enumerate() {
        *el = i as u8;
    }

    let naive_result = Blake2s256::digest(&input_bytes);

    // full round
    let mut hasher = Blake2sState::new();

    let mut input_as_u32_block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    for (dst, src) in input_as_u32_block
        .iter_mut()
        .zip(input_bytes.as_chunks::<4>().0)
    {
        *dst = u32::from_le_bytes(*src);
    }

    hasher.absorb::<false>(&input_as_u32_block);

    // padded round
    let mut input_as_u32_block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    for (dst, src) in input_as_u32_block
        .iter_mut()
        .zip(input_bytes[BLAKE2S_BLOCK_SIZE_BYTES..].as_chunks::<4>().0)
    {
        *dst = u32::from_le_bytes(*src);
    }
    let mut u32_result = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
    hasher.absorb_final_block::<false>(&input_as_u32_block, tail, &mut u32_result);

    for (i, (a, b)) in u32_result
        .iter()
        .zip(naive_result.as_slice().as_chunks::<4>().0)
        .enumerate()
    {
        let b = u32::from_le_bytes(*b);
        assert_eq!(*a, b, "failed at word {}", i);
    }
}

#[test]
fn check_compress_two_into_one_consistency() {
    let len_words = BLAKE2S_BLOCK_SIZE_U32_WORDS;
    let mut input_bytes = vec![0u8; len_words * 4];
    for (i, el) in input_bytes.iter_mut().enumerate() {
        *el = i as u8;
    }

    let mut input_as_u32_block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
    for (dst, src) in input_as_u32_block
        .iter_mut()
        .zip(input_bytes.as_chunks::<4>().0)
    {
        *dst = u32::from_le_bytes(*src);
    }

    let naive_result = Blake2s256::digest(&input_bytes);

    let mut u32_result = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
    Blake2sState::compress_two_to_one::<false>(&input_as_u32_block, &mut u32_result);

    for (i, (a, b)) in u32_result
        .iter()
        .zip(naive_result.as_slice().as_chunks::<4>().0)
        .enumerate()
    {
        let b = u32::from_le_bytes(*b);
        assert_eq!(*a, b, "failed at word {}", i);
    }
}
