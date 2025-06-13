#![no_std]

// Keccak-256 implementation for RV32, using u32 words.
// This is a special implementation that can be run on our reduced machine
// therefore it can run as part of recursion flow.
// WARNING: this api is little-endian based (both inputs and outputs).

/// Keccak parameters for Keccak-256
const LANES: usize = 25; // 5×5 lanes
const RATE_BITS: usize = 1088;
const CAP_BITS: usize = 512;
const RATE_LANES: usize = RATE_BITS / 64; // = 17 lanes per block
const RATE_WORDS: usize = RATE_BITS / 32; // = 34 u32 words per block

/// A Keccak-256 sponge with u32-word inputs/outputs, for RV32. No heap allocations.
pub struct Keccak32 {
    state: [u64; LANES],       // internal 64-bit lanes
    buffer: [u32; RATE_WORDS], // fixed-size input buffer
    buf_len: usize,            // how many words are buffered
}

impl Keccak32 {
    /// Initialize a new Keccak-256 hasher.
    pub fn new() -> Self {
        assert!(
            RATE_BITS + CAP_BITS == 1600,
            "rate+capacity must equal 1600 bits"
        );
        Keccak32 {
            state: [0u64; LANES],
            buffer: [0u32; RATE_WORDS],
            buf_len: 0,
        }
    }

    /// Absorb a slice of u32 words (little-endian).
    pub fn update(&mut self, input: &[u32]) {
        let mut in_off = 0;
        let mut rem = self.buf_len;

        // 1) Fill the current buffer to a full block, if partially filled
        if rem > 0 {
            let needed = RATE_WORDS - rem;
            let take = needed.min(input.len());
            for i in 0..take {
                self.buffer[rem + i] = input[in_off + i];
            }
            rem += take;
            in_off += take;
            if rem == RATE_WORDS {
                // buffer now full → absorb
                let mut lanes = [0u64; RATE_LANES];
                for i in 0..RATE_LANES {
                    let lo = self.buffer[2 * i] as u64;
                    let hi = self.buffer[2 * i + 1] as u64;
                    lanes[i] = lo | (hi << 32);
                }
                self.absorb_block(&lanes);
                rem = 0; // buffer is now empty
            }
        }

        // 2) Absorb all full blocks directly from remaining input
        while input.len().saturating_sub(in_off) >= RATE_WORDS {
            let mut lanes = [0u64; RATE_LANES];
            for i in 0..RATE_LANES {
                let lo = input[in_off + 2 * i] as u64;
                let hi = input[in_off + 2 * i + 1] as u64;
                lanes[i] = lo | (hi << 32);
            }
            self.absorb_block(&lanes);
            in_off += RATE_WORDS;
        }

        // 3) Buffer any leftover words
        let take = input.len().saturating_sub(in_off);
        for i in 0..take {
            self.buffer[rem + i] = input[in_off + i];
        }
        rem += take;
        self.buf_len = rem;
    }

    /// Finalize and return 8 u32 words (32 bytes) of output.
    pub fn finalize(mut self) -> [u32; 8] {
        // Multi-rate pad10*1 on u32-word boundary
        let rem = self.buf_len;
        let mut lanes = [0u64; RATE_LANES];
        // fill lanes from buffer
        for i in 0..(rem / 2) {
            let lo = self.buffer[2 * i] as u64;
            let hi = self.buffer[2 * i + 1] as u64;
            lanes[i] = lo | (hi << 32);
        }
        if rem % 2 == 1 {
            lanes[rem / 2] = self.buffer[rem - 1] as u64;
        }
        // pad bit right after last word
        let lane_idx = rem / 2;
        let bit_pos = (rem % 2) * 32;
        lanes[lane_idx] |= 1u64 << bit_pos;
        // final pad bit at end of block
        lanes[RATE_LANES - 1] |= 1u64 << 63;
        self.absorb_block(&lanes);

        // Squeeze out 8 words
        let mut out = [0u32; 8];
        let mut cnt = 0;
        loop {
            for i in 0..RATE_LANES {
                if cnt < 8 {
                    out[cnt] = (self.state[i] & 0xFFFF_FFFF) as u32;
                    cnt += 1;
                }
                if cnt < 8 {
                    out[cnt] = (self.state[i] >> 32) as u32;
                    cnt += 1;
                }
                if cnt >= 8 {
                    break;
                }
            }
            if cnt >= 8 {
                break;
            }
            keccak_f(&mut self.state);
        }
        out
    }

    /// XOR lanes into state and run the permutation.
    fn absorb_block(&mut self, lanes: &[u64; RATE_LANES]) {
        for i in 0..RATE_LANES {
            self.state[i] ^= lanes[i];
        }
        keccak_f(&mut self.state);
    }
}

/// Convenience: hash u32-word slice to 8-word (32-byte) digest
pub fn keccak256_words(input: &[u32]) -> [u32; 8] {
    let mut hasher = Keccak32::new();
    hasher.update(input);
    hasher.finalize()
}

/// The 24-round permutation Keccak-f[1600].
fn keccak_f(state: &mut [u64; 25]) {
    for round in 0..24 {
        // Theta step
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
        }
        let mut d = [0u64; 5];
        for x in 0..5 {
            d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        }
        for x in 0..5 {
            for y in 0..5 {
                state[x + 5 * y] ^= d[x];
            }
        }

        // Rho and Pi steps combined
        let mut b = [0u64; 25];
        for x in 0..5 {
            for y in 0..5 {
                let idx = x + 5 * y;
                let new_x = y;
                let new_y = (2 * x + 3 * y) % 5;
                let new_idx = new_x + 5 * new_y;
                b[new_idx] = state[idx].rotate_left(RHO_OFFSETS[idx]);
            }
        }

        // Chi step
        for x in 0..5 {
            for y in 0..5 {
                let idx = x + 5 * y;
                state[idx] = b[idx] ^ ((!b[((x + 1) % 5) + 5 * y]) & b[((x + 2) % 5) + 5 * y]);
            }
        }

        // Iota step
        state[0] ^= ROUND_CONSTANTS[round];
    }
}

/// Rotation offsets for Rho step.
const RHO_OFFSETS: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

/// Round constants for the Iota step.
const ROUND_CONSTANTS: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

#[cfg(test)]
mod tests {
    use super::*;

    fn reverse_endianness(input: &[u32; 8]) -> [u32; 8] {
        let mut result = [0u32; 8];
        for i in 0..8 {
            result[i] = input[i].swap_bytes();
        }
        result
    }

    #[test]
    fn test_keccak256_words() {
        // Test vector 1: Empty input
        let input = [];
        let expected: [u32; 8] = [
            0xc5d2_4601,
            0x86f7_233c,
            0x927e_7db2,
            0xdcc7_03c0,
            0xe500_b653,
            0xca82_273b,
            0x7bfa_d804,
            0x5d85_a470,
        ];

        assert_eq!(reverse_endianness(&keccak256_words(&input)), expected);

        // Test vector 2: "16777216" - in little endian, so 0x00000001
        let input = [16777216];
        let expected = [
            0x51f81bcd, 0xfc324a0d, 0xff2b5bec, 0x9d92e21c, 0xbebc4d5e, 0x29d3a3d3, 0x0de3e03f,
            0xbeab8d7f,
        ];

        assert_eq!(
            reverse_endianness(&keccak256_words(&input)),
            expected,
            "Assertion failed! Expected: {:x?}, Got: {:x?}",
            expected,
            reverse_endianness(&keccak256_words(&input))
        );

        // Test vector 3: "1, 2, 3" - in little endian, so 0x01000000 02000000 03000000
        let input = [1, 2, 3];
        let expected = [
            0x9186e459, 0xff7edfa5, 0xacc87375, 0x3676278c, 0xc4c65f18, 0x3513b583, 0x46230c03,
            0x1fd46cad,
        ];
        assert_eq!(reverse_endianness(&keccak256_words(&input)), expected);
    }
}
