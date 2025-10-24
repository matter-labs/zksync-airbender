use crate::*;
use core::arch::aarch64::uint32x4_t;

#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct Blake2sState {
    state: State,
    t: u32, // we limit ourselves to <4Gb inputs
}

impl Blake2sState {
    pub fn new() -> Self {
        unsafe {
            Self {
                state: State::initial_configured(),
                t: 0,
            }
        }
    }

    #[inline(always)]
    pub fn read_state_for_output(&self) -> [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] {
        unimplemented!("low level primitives are not implemented for vectorized case");
    }

    #[inline(always)]
    pub fn reset(&mut self) {
        unsafe { self.state.partial_reset() };
        // elements 8-15 will be overwritten in round function

        self.t = 0;
    }

    #[inline]
    pub unsafe fn run_round_function<const REDUCED_ROUNDS: bool>(
        &mut self,
        _input_size_words: usize,
        _last_round: bool,
    ) {
        unimplemented!("low level primitives are not implemented for vectorized case");
    }

    #[unroll::unroll_for_loops]
    #[inline(always)]
    pub fn absorb<const REDUCED_ROUNDS: bool>(
        &mut self,
        message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    ) {
        self.t += BLAKE2S_BLOCK_SIZE_BYTES as u32;
        let h0 = self.state.0[0];
        let h1 = self.state.0[1];

        unsafe {
            self.state.reset_for_round(self.t, false);

            if REDUCED_ROUNDS {
                for i in 0..7 {
                    let message_block = MessageBlock::load(message_block, &SIGMAS[i]);
                    mixing_function(&mut self.state, message_block);
                }
            } else {
                for i in 0..10 {
                    let message_block = MessageBlock::load(message_block, &SIGMAS[i]);
                    mixing_function(&mut self.state, message_block);
                }
            }
            // and need to xor-in back
            use core::arch::aarch64::veorq_u32;
            self.state.0[0] = veorq_u32(self.state.0[0], h0);
            self.state.0[1] = veorq_u32(self.state.0[1], h1);
            self.state.0[0] = veorq_u32(self.state.0[0], self.state.0[2]);
            self.state.0[1] = veorq_u32(self.state.0[1], self.state.0[3]);
        }
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub fn absorb_final_block<const REDUCED_ROUNDS: bool>(
        &mut self,
        message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
        block_len: usize,
        dst: &mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
    ) {
        self.t += (block_len * core::mem::size_of::<u32>()) as u32;
        let h0 = self.state.0[0];
        let h1 = self.state.0[1];

        unsafe {
            self.state.reset_for_round(self.t, true);

            if REDUCED_ROUNDS {
                for i in 0..7 {
                    let message_block = MessageBlock::load(message_block, &SIGMAS[i]);
                    mixing_function(&mut self.state, message_block);
                }
            } else {
                for i in 0..10 {
                    let message_block = MessageBlock::load(message_block, &SIGMAS[i]);
                    mixing_function(&mut self.state, message_block);
                }
            }
            // and need to xor-in back
            use core::arch::aarch64::veorq_u32;
            let h0 = veorq_u32(self.state.0[0], h0);
            let h1 = veorq_u32(self.state.0[1], h1);
            let h0 = veorq_u32(h0, self.state.0[2]);
            let h1 = veorq_u32(h1, self.state.0[3]);

            // and writeback
            let h0: [u32; 4] = core::mem::transmute(h0);
            let h1: [u32; 4] = core::mem::transmute(h1);

            for i in 0..4 {
                dst[i] = h0[i];
                dst[i + 4] = h1[i];
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
#[repr(align(16))]
pub struct State([uint32x4_t; 4]);

impl State {
    #[inline(always)]
    unsafe fn initial_configured() -> Self {
        use core::arch::aarch64::vld1q_u32;

        Self([
            vld1q_u32(&EXTENDED_CONFIGURED_IV[0] as *const u32),
            vld1q_u32(&EXTENDED_CONFIGURED_IV[4] as *const u32),
            vld1q_u32(&EXTENDED_CONFIGURED_IV[8] as *const u32),
            vld1q_u32(&EXTENDED_CONFIGURED_IV[12] as *const u32),
        ])
    }

    #[inline(always)]
    unsafe fn partial_reset(&mut self) {
        use core::arch::aarch64::vld1q_u32;
        self.0[0] = vld1q_u32(&EXTENDED_CONFIGURED_IV[0] as *const u32);
        self.0[1] = vld1q_u32(&EXTENDED_CONFIGURED_IV[4] as *const u32);
    }

    #[inline(always)]
    unsafe fn reset_for_round(&mut self, t: u32, is_last_round: bool) {
        use core::arch::aarch64::vld1q_u32;
        self.0[2] = vld1q_u32(&EXTENDED_CONFIGURED_IV[8] as *const u32);
        let el = vld1q_u32(&EXTENDED_CONFIGURED_IV[12] as *const u32);
        let xor_in = vld1q_u32(&[t, 0, (is_last_round as u32) * 0xffffffff, 0] as *const u32);
        use core::arch::aarch64::veorq_u32;
        let el = veorq_u32(el, xor_in);
        self.0[3] = el;
    }
}

#[derive(Clone, Copy, Debug)]
#[repr(align(16))]
struct MessageBlock([uint32x4_t; 4]);

impl MessageBlock {
    unsafe fn load(
        message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
        sigma: &[usize; 16],
    ) -> Self {
        use core::arch::aarch64::vld1q_u32;
        Self([
            vld1q_u32(&[
                message_block[sigma[0]],
                message_block[sigma[2]],
                message_block[sigma[4]],
                message_block[sigma[6]],
            ] as *const u32),
            vld1q_u32(&[
                message_block[sigma[1]],
                message_block[sigma[3]],
                message_block[sigma[5]],
                message_block[sigma[7]],
            ] as *const u32),
            vld1q_u32(&[
                message_block[sigma[8]],
                message_block[sigma[10]],
                message_block[sigma[12]],
                message_block[sigma[14]],
            ] as *const u32),
            vld1q_u32(&[
                message_block[sigma[9]],
                message_block[sigma[11]],
                message_block[sigma[13]],
                message_block[sigma[15]],
            ] as *const u32),
        ])
    }
}

#[inline(always)]
unsafe fn mixing_function(state: &mut State, message_block: MessageBlock) {
    use core::arch::aarch64::vaddq_u32;
    use core::arch::aarch64::veorq_u32;
    use core::arch::aarch64::vorrq_u32;
    use core::arch::aarch64::vshlq_n_u32;
    use core::arch::aarch64::vshrq_n_u32;

    let [x, y, xx, yy] = message_block.0;

    let [a, b, c, d] = &mut state.0;
    *a = vaddq_u32(vaddq_u32(*a, *b), x);
    *d = veorq_u32(*a, *d);
    *d = vorrq_u32(vshlq_n_u32::<16>(*d), vshrq_n_u32::<16>(*d));

    *c = vaddq_u32(*c, *d);
    *b = veorq_u32(*c, *b);
    *b = vorrq_u32(vshlq_n_u32::<20>(*b), vshrq_n_u32::<12>(*b));

    *a = vaddq_u32(vaddq_u32(*a, *b), y);
    *d = veorq_u32(*a, *d);
    *d = vorrq_u32(vshlq_n_u32::<24>(*d), vshrq_n_u32::<8>(*d));

    *c = vaddq_u32(*c, *d);
    *b = veorq_u32(*c, *b);
    *b = vorrq_u32(vshlq_n_u32::<25>(*b), vshrq_n_u32::<7>(*b));

    // to mix columns we need to "rotate left" row number 1 by 1,
    // row number 2 by 2 and 3 by 3

    use core::arch::aarch64::vextq_u32;
    // lowest from 1st operand, and highest from second
    *b = vextq_u32::<1>(*b, *b);
    *c = vextq_u32::<2>(*c, *c);
    *d = vextq_u32::<3>(*d, *d);

    *a = vaddq_u32(vaddq_u32(*a, *b), xx);
    *d = veorq_u32(*a, *d);
    *d = vorrq_u32(vshlq_n_u32::<16>(*d), vshrq_n_u32::<16>(*d));

    *c = vaddq_u32(*c, *d);
    *b = veorq_u32(*c, *b);
    *b = vorrq_u32(vshlq_n_u32::<20>(*b), vshrq_n_u32::<12>(*b));

    *a = vaddq_u32(vaddq_u32(*a, *b), yy);
    *d = veorq_u32(*a, *d);
    *d = vorrq_u32(vshlq_n_u32::<24>(*d), vshrq_n_u32::<8>(*d));

    *c = vaddq_u32(*c, *d);
    *b = veorq_u32(*c, *b);
    *b = vorrq_u32(vshlq_n_u32::<25>(*b), vshrq_n_u32::<7>(*b));

    // "rotate it back"
    *b = vextq_u32::<3>(*b, *b);
    *c = vextq_u32::<2>(*c, *c);
    *d = vextq_u32::<1>(*d, *d);
}

#[cfg(test)]
mod test {
    use super::*;

    use blake2::*;

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
            .zip(input_bytes.chunks_exact(4))
        {
            let t: [u8; 4] = src.try_into().unwrap();
            *dst = u32::from_le_bytes(t);
        }

        let naive_result = Blake2s256::digest(&input_bytes);

        let mut hasher = Blake2sState::new();
        let mut u32_result = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
        hasher.absorb_final_block::<false>(&input_as_u32_block, len_words, &mut u32_result);

        for (i, (a, b)) in u32_result
            .iter()
            .zip(naive_result.as_slice().chunks_exact(4))
            .enumerate()
        {
            let t: [u8; 4] = b.try_into().unwrap();
            let b = u32::from_le_bytes(t);
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
            .zip(input_bytes.chunks_exact(4))
        {
            let t: [u8; 4] = src.try_into().unwrap();
            *dst = u32::from_le_bytes(t);
        }

        hasher.absorb::<false>(&input_as_u32_block);

        // padded round
        let mut input_as_u32_block = [0u32; BLAKE2S_BLOCK_SIZE_U32_WORDS];
        for (dst, src) in input_as_u32_block
            .iter_mut()
            .zip(input_bytes[BLAKE2S_BLOCK_SIZE_BYTES..].chunks_exact(4))
        {
            let t: [u8; 4] = src.try_into().unwrap();
            *dst = u32::from_le_bytes(t);
        }
        let mut u32_result = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
        hasher.absorb_final_block::<false>(&input_as_u32_block, tail, &mut u32_result);

        for (i, (a, b)) in u32_result
            .iter()
            .zip(naive_result.as_slice().chunks_exact(4))
            .enumerate()
        {
            let t: [u8; 4] = b.try_into().unwrap();
            let b = u32::from_le_bytes(t);
            assert_eq!(*a, b, "failed at word {}", i);
        }
    }
}
