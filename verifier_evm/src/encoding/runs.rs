//! Bit-packed runs: `FE-run(n)` (123-bit field elements) and `TS-run` (19-bit timestamp
//! limb pairs), MSB-first, zero-padded to a byte boundary.

use field::Proth120;

/// Bits per packed field element: `p = 7·2^120 + 1 < 2^123`.
pub const FE_BITS: usize = 123;
/// Bits per timestamp limb (`common_constants::TIMESTAMP_COLUMNS_NUM_BITS`).
pub const TS_LIMB_BITS: usize = common_constants::TIMESTAMP_COLUMNS_NUM_BITS as usize;

/// Byte length of `FE-run(n)`.
pub const fn fe_run_len(n: usize) -> usize {
    (FE_BITS * n).div_ceil(8)
}

/// Byte length of a `TS-run` of `n` `(low, high)` pairs.
pub const fn ts_run_len(n: usize) -> usize {
    (2 * TS_LIMB_BITS * n).div_ceil(8)
}

fn pack(values: impl Iterator<Item = u128>, width: usize) -> Vec<u8> {
    let mut out = Vec::new();
    let mut bits = 0usize;
    for v in values {
        assert!(
            width == 128 || v >> width == 0,
            "value exceeds {width} bits"
        );
        for i in (0..width).rev() {
            if bits.is_multiple_of(8) {
                out.push(0);
            }
            if (v >> i) & 1 == 1 {
                *out.last_mut().unwrap() |= 0x80 >> (bits % 8);
            }
            bits += 1;
        }
    }
    out
}

/// `FE-run`: every element as its canonical 123-bit value.
pub fn write_fe_run(els: &[Proth120]) -> Vec<u8> {
    pack(els.iter().map(|e| e.to_u128()), FE_BITS)
}

/// `TS-run`: every `(low, high)` timestamp limb pair as `low ‖ high`, 19 bits each.
pub fn write_ts_run(pairs: &[(u32, u32)]) -> Vec<u8> {
    pack(
        pairs.iter().flat_map(|(lo, hi)| [*lo as u128, *hi as u128]),
        TS_LIMB_BITS,
    )
}
