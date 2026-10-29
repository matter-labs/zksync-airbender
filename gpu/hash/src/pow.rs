/// Warp chunk length in 32-nonce steps for the PoW searches (128-thread blocks): about 1/32 of the
/// expected nonces per thread, within [1, 32].
pub fn pow_chunk_steps(bits: u32, blocks: u32) -> u32 {
    let threads = blocks as u64 * 128;
    let expected_per_thread = (1u64 << bits.min(63)) / threads;
    (expected_per_thread / 32).clamp(1, 32) as u32
}
