//! Four INDEPENDENT Blake2s hashes in the four lanes of NEON vectors
//! (multi-buffer hashing): state word `i` of messages `0..4` lives in lane
//! `0..4` of vector `h[i]`, every G step is one vector op per four scalar
//! ops, and nothing is shuffled between lanes. The message block is supplied
//! word-major (`block[i]` = word `i` of the four messages), which is the
//! layout a leaf gather can write directly.
//!
//! Byte-identical to four [`Blake2sState`](crate::Blake2sState) absorb
//! sequences (same configured IV, counter and finalization flag handling).

use crate::{
    BLAKE2S_BLOCK_SIZE_BYTES, BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS,
    CONFIGURED_IV, IV, SIGMAS,
};
use core::arch::aarch64::*;

#[derive(Clone, Copy)]
pub struct Blake2sNeonX4 {
    h: [uint32x4_t; 8],
    t: u32,
}

impl Default for Blake2sNeonX4 {
    fn default() -> Self {
        Self::new()
    }
}

#[inline(always)]
unsafe fn ror16(x: uint32x4_t) -> uint32x4_t {
    vreinterpretq_u32_u16(vrev32q_u16(vreinterpretq_u16_u32(x)))
}

#[inline(always)]
unsafe fn ror8(x: uint32x4_t) -> uint32x4_t {
    // byte rotate within each 32-bit lane: out byte k = in byte (k + 1) mod 4
    const IDX: [u8; 16] = [1, 2, 3, 0, 5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12];
    let idx = vld1q_u8(IDX.as_ptr());
    vreinterpretq_u32_u8(vqtbl1q_u8(vreinterpretq_u8_u32(x), idx))
}

#[inline(always)]
unsafe fn ror12(x: uint32x4_t) -> uint32x4_t {
    vsriq_n_u32::<12>(vshlq_n_u32::<20>(x), x)
}

#[inline(always)]
unsafe fn ror7(x: uint32x4_t) -> uint32x4_t {
    vsriq_n_u32::<7>(vshlq_n_u32::<25>(x), x)
}

#[inline(always)]
unsafe fn g(
    v: &mut [uint32x4_t; 16],
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    x: uint32x4_t,
    y: uint32x4_t,
) {
    v[a] = vaddq_u32(vaddq_u32(v[a], v[b]), x);
    v[d] = ror16(veorq_u32(v[d], v[a]));
    v[c] = vaddq_u32(v[c], v[d]);
    v[b] = ror12(veorq_u32(v[b], v[c]));
    v[a] = vaddq_u32(vaddq_u32(v[a], v[b]), y);
    v[d] = ror8(veorq_u32(v[d], v[a]));
    v[c] = vaddq_u32(v[c], v[d]);
    v[b] = ror7(veorq_u32(v[b], v[c]));
}

#[inline(always)]
unsafe fn round(v: &mut [uint32x4_t; 16], m: &[uint32x4_t; 16], s: &[usize; 16]) {
    g(v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
    g(v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
    g(v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
    g(v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
    g(v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
    g(v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
    g(v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
    g(v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
}

impl Blake2sNeonX4 {
    #[inline(always)]
    pub fn new() -> Self {
        unsafe {
            Self {
                h: core::array::from_fn(|i| vdupq_n_u32(CONFIGURED_IV[i])),
                t: 0,
            }
        }
    }

    #[inline(always)]
    pub fn reset(&mut self) {
        *self = Self::new();
    }

    /// Load a word-major interleaved block: `words[4 * i + lane]` is word `i`
    /// of message `lane`.
    ///
    /// # Safety
    ///
    /// `words` must be valid for reading 64 `u32`s.
    #[inline(always)]
    pub unsafe fn load_block(words: *const u32) -> [uint32x4_t; 16] {
        core::array::from_fn(|i| vld1q_u32(words.add(4 * i)))
    }

    /// Load four CONSECUTIVE 16-word messages (message-major, e.g. four
    /// pairs of child digests of a Merkle layer) as the word-major block of
    /// [`Self::load_block`]: four 4x4 transposes.
    ///
    /// # Safety
    ///
    /// `msgs` must be valid for reading 64 `u32`s.
    #[inline(always)]
    pub unsafe fn load_block_transposed(msgs: *const u32) -> [uint32x4_t; 16] {
        let mut out = [vdupq_n_u32(0); 16];
        for g in 0..4 {
            let a = vld1q_u32(msgs.add(4 * g));
            let b = vld1q_u32(msgs.add(16 + 4 * g));
            let c = vld1q_u32(msgs.add(32 + 4 * g));
            let d = vld1q_u32(msgs.add(48 + 4 * g));
            let t0 = vreinterpretq_u64_u32(vzip1q_u32(a, b));
            let t1 = vreinterpretq_u64_u32(vzip2q_u32(a, b));
            let t2 = vreinterpretq_u64_u32(vzip1q_u32(c, d));
            let t3 = vreinterpretq_u64_u32(vzip2q_u32(c, d));
            out[4 * g] = vreinterpretq_u32_u64(vzip1q_u64(t0, t2));
            out[4 * g + 1] = vreinterpretq_u32_u64(vzip2q_u64(t0, t2));
            out[4 * g + 2] = vreinterpretq_u32_u64(vzip1q_u64(t1, t3));
            out[4 * g + 3] = vreinterpretq_u32_u64(vzip2q_u64(t1, t3));
        }
        out
    }

    #[inline(always)]
    unsafe fn compress<const REDUCED_ROUNDS: bool>(
        &self,
        m: &[uint32x4_t; 16],
        t: u32,
        last: bool,
    ) -> [uint32x4_t; 8] {
        let mut v: [uint32x4_t; 16] = [vdupq_n_u32(0); 16];
        v[..8].copy_from_slice(&self.h);
        for i in 0..8 {
            v[8 + i] = vdupq_n_u32(IV[i]);
        }
        v[12] = veorq_u32(v[12], vdupq_n_u32(t));
        if last {
            v[14] = veorq_u32(v[14], vdupq_n_u32(0xffff_ffff));
        }
        let rounds = if REDUCED_ROUNDS { 7 } else { 10 };
        for r in 0..rounds {
            round(&mut v, m, &SIGMAS[r]);
        }
        core::array::from_fn(|i| veorq_u32(veorq_u32(self.h[i], v[i]), v[8 + i]))
    }

    /// Absorb one full (non-final) block of all four messages.
    ///
    /// # Safety
    ///
    /// NEON (always available on aarch64).
    #[inline(always)]
    pub unsafe fn absorb<const REDUCED_ROUNDS: bool>(&mut self, m: &[uint32x4_t; 16]) {
        self.t += BLAKE2S_BLOCK_SIZE_BYTES as u32;
        self.h = self.compress::<REDUCED_ROUNDS>(m, self.t, false);
    }

    /// Absorb the final block (`block_len_words` meaningful words, the rest
    /// zero in every lane) and write the four digests, `dst[lane]`.
    ///
    /// # Safety
    ///
    /// NEON (always available on aarch64).
    #[inline(always)]
    pub unsafe fn absorb_final_block<const REDUCED_ROUNDS: bool>(
        &mut self,
        m: &[uint32x4_t; 16],
        block_len_words: usize,
        dst: &mut [[u32; BLAKE2S_DIGEST_SIZE_U32_WORDS]; 4],
    ) {
        self.t += (block_len_words * core::mem::size_of::<u32>()) as u32;
        let out = self.compress::<REDUCED_ROUNDS>(m, self.t, true);
        // transpose the 8 state vectors (lane = message) into 4 digests
        let mut tmp = [[0u32; 4]; 8];
        for i in 0..8 {
            vst1q_u32(tmp[i].as_mut_ptr(), out[i]);
        }
        for lane in 0..4 {
            for i in 0..8 {
                dst[lane][i] = tmp[i][lane];
            }
        }
    }
}

const _: () = assert!(BLAKE2S_BLOCK_SIZE_U32_WORDS == 16);
