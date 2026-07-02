use crate::Transcript;
use field::proth120::Proth120;
use field::PrimeField;
use sha3::{Digest, Keccak256};

// ---------------------------------------------------------------------------
// Keccak256-based transcript over the Proth120 field, modelled to match the
// EVM (Solidity) WHIR verifier byte-for-byte.
//
// - The seed is a raw 32-byte Keccak digest.
// - "Absorbing" data D against a seed S produces `keccak256(S || D)` and becomes
//   the new seed. `u32` inputs are hashed as their 4 little-endian bytes.
// - Field elements are absorbed as the 16-byte *big-endian* encoding of their
//   normal (`u128`) form (matching how the EVM packs field values).
// - Drawing a field element re-hashes the seed and takes the top 128 bits of the
//   digest (big-endian) reduced mod P — exactly the EVM's `draw1()`.
// - Proof-of-work over `nonce` hashes `keccak256(seed || nonce_be_8)` and
//   requires the top `pow_bits` bits of the digest to be zero.
//
// Only `Transcript<Proth120, Proth120>` is implemented (Proth120 has no
// extensions, so the extension type is Proth120 itself, degree 1).
// ---------------------------------------------------------------------------

/// Keccak256 transcript.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Keccak256Transcript;

/// Transcript seed: a raw 256-bit Keccak digest.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Keccak256Seed(pub [u8; 32]);

/// Stateless hasher marker (Keccak256 needs no carried state between calls).
#[derive(Clone, Copy, Debug, Default)]
pub struct Keccak256Hasher;

#[inline(always)]
fn keccak(bytes: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    out.copy_from_slice(Keccak256::digest(bytes).as_slice());
    out
}

/// `keccak256(seed || <u32 words as little-endian bytes>)`.
#[inline]
fn absorb_u32(seed: &mut Keccak256Seed, input: &[u32]) {
    let mut h = Keccak256::new();
    h.update(seed.0);
    for w in input.iter() {
        h.update(w.to_le_bytes());
    }
    seed.0.copy_from_slice(h.finalize().as_slice());
}

/// `keccak256(seed || <Proth120 elements as 16-byte big-endian u128>)`.
#[inline]
fn absorb_field(seed: &mut Keccak256Seed, els: &[Proth120]) {
    let mut h = Keccak256::new();
    h.update(seed.0);
    for el in els.iter() {
        h.update(el.to_u128().to_be_bytes());
    }
    seed.0.copy_from_slice(h.finalize().as_slice());
}

/// Squeeze one 128-bit field element: `seed = keccak256(seed)`, element is the
/// top 128 bits of the new seed (big-endian) reduced mod P. Matches EVM `draw1`.
#[inline]
fn draw_field(seed: &mut Keccak256Seed) -> Proth120 {
    seed.0 = keccak(&seed.0);
    let mut top = [0u8; 16];
    top.copy_from_slice(&seed.0[0..16]);
    Proth120::from_u128_with_reduction(u128::from_be_bytes(top))
}

/// True iff the top `pow_bits` bits of the big-endian digest are zero.
#[inline]
fn top_bits_are_zero(digest: &[u8; 32], pow_bits: u32) -> bool {
    debug_assert!(pow_bits <= 256);
    let full = (pow_bits / 8) as usize;
    let rem = (pow_bits % 8) as u8;
    let mut i = 0;
    while i < full {
        if digest[i] != 0 {
            return false;
        }
        i += 1;
    }
    if rem > 0 {
        // the top `rem` bits of `digest[full]` must be zero
        if digest[full] >> (8 - rem) != 0 {
            return false;
        }
    }
    true
}

impl Transcript<Proth120, Proth120> for Keccak256Transcript {
    type Seed = Keccak256Seed;
    type Hasher = Keccak256Hasher;

    fn commit_initial_u32(input: &[u32]) -> Self::Seed {
        // No prior seed: keccak256 over the little-endian input bytes.
        let mut seed = Keccak256Seed([0u8; 32]);
        let mut h = Keccak256::new();
        for w in input.iter() {
            h.update(w.to_le_bytes());
        }
        seed.0.copy_from_slice(h.finalize().as_slice());
        seed
    }

    fn commit_u32_with_seed(seed: &mut Self::Seed, input: &[u32]) {
        absorb_u32(seed, input);
    }

    fn commit_initial_u32_using_hasher(_hasher: &mut Self::Hasher, input: &[u32]) -> Self::Seed {
        Self::commit_initial_u32(input)
    }

    fn commit_u32_with_seed_using_hasher(
        _hasher: &mut Self::Hasher,
        seed: &mut Self::Seed,
        input: &[u32],
    ) {
        absorb_u32(seed, input);
    }

    fn draw_randomness(seed: &mut Self::Seed, dst: &mut [u32]) {
        // Re-hash the seed for every 8-word (32-byte) block and emit the digest
        // words in little-endian order.
        let mut i = 0;
        while i < dst.len() {
            seed.0 = keccak(&seed.0);
            let mut j = 0;
            while j < 8 && i < dst.len() {
                let b = 4 * j;
                dst[i] = u32::from_le_bytes([
                    seed.0[b],
                    seed.0[b + 1],
                    seed.0[b + 2],
                    seed.0[b + 3],
                ]);
                i += 1;
                j += 1;
            }
        }
    }

    fn draw_randomness_using_hasher(
        _hasher: &mut Self::Hasher,
        seed: &mut Self::Seed,
        dst: &mut [u32],
    ) {
        Self::draw_randomness(seed, dst);
    }

    fn pow_threshold(pow_bits: u32) -> u32 {
        // Kept for interface parity; the actual check is "top pow_bits are zero".
        u32::MAX.checked_shr(pow_bits).unwrap_or(0)
    }

    fn verify_pow(seed: &mut Self::Seed, nonce: u64, pow_bits: u32) {
        let mut h = Keccak256::new();
        h.update(seed.0);
        h.update(nonce.to_be_bytes());
        let mut digest = [0u8; 32];
        digest.copy_from_slice(h.finalize().as_slice());
        assert!(
            top_bits_are_zero(&digest, pow_bits),
            "Keccak256 PoW check failed for nonce {nonce} and {pow_bits} bits"
        );
        seed.0 = digest;
    }

    fn verify_pow_using_hasher(
        _hasher: &mut Self::Hasher,
        seed: &mut Self::Seed,
        nonce: u64,
        pow_bits: u32,
    ) {
        Self::verify_pow(seed, nonce, pow_bits);
    }

    #[cfg(feature = "pow")]
    fn search_pow(seed: &Self::Seed, pow_bits: u32, _worker: &worker::Worker) -> (Self::Seed, u64) {
        // Sequential grinding. Callers should keep `pow_bits` small in tests.
        let mut nonce = 0u64;
        loop {
            let mut h = Keccak256::new();
            h.update(seed.0);
            h.update(nonce.to_be_bytes());
            let mut digest = [0u8; 32];
            digest.copy_from_slice(h.finalize().as_slice());
            if top_bits_are_zero(&digest, pow_bits) {
                return (Keccak256Seed(digest), nonce);
            }
            nonce += 1;
        }
    }

    fn commit_base_field_elements(seed: &mut Self::Seed, els: &[Proth120]) {
        absorb_field(seed, els);
    }

    fn commit_extension_field_elements(seed: &mut Self::Seed, els: &[Proth120]) {
        absorb_field(seed, els);
    }

    fn draw_random_field_elements(seed: &mut Self::Seed, buffer: &mut [Proth120]) {
        for slot in buffer.iter_mut() {
            *slot = draw_field(seed);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // keccak256("") known vector.
    const KECCAK_EMPTY: [u8; 32] = [
        0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c, 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03,
        0xc0, 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b, 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85,
        0xa4, 0x70,
    ];

    #[test]
    fn keccak_empty_vector() {
        assert_eq!(keccak(&[]), KECCAK_EMPTY);
    }

    #[test]
    fn absorb_field_matches_manual_keccak() {
        let seed0 = Keccak256Seed([7u8; 32]);
        let els = [
            Proth120::new(1),
            Proth120::new(Proth120::ORDER - 1),
            Proth120::new(1u128 << 120),
        ];
        // manual: keccak256( seed || BE16(v0) || BE16(v1) || BE16(v2) )
        let mut preimage = Vec::new();
        preimage.extend_from_slice(&seed0.0);
        for e in els.iter() {
            preimage.extend_from_slice(&e.to_u128().to_be_bytes());
        }
        let expected = keccak(&preimage);

        let mut seed = seed0;
        <Keccak256Transcript as Transcript<Proth120, Proth120>>::commit_extension_field_elements(
            &mut seed, &els,
        );
        assert_eq!(seed.0, expected);
    }

    #[test]
    fn draw_field_matches_evm_draw1() {
        // EVM draw1: seed = keccak256(seed); r = top-128-bits(seed) mod P.
        let mut seed = Keccak256Seed([0x11u8; 32]);
        let expected_seed = keccak(&seed.0);
        let mut top = [0u8; 16];
        top.copy_from_slice(&expected_seed[0..16]);
        let expected_val =
            Proth120::from_u128_with_reduction(u128::from_be_bytes(top)).to_u128();

        let mut out = [Proth120::default(); 1];
        <Keccak256Transcript as Transcript<Proth120, Proth120>>::draw_random_field_elements(
            &mut seed, &mut out,
        );
        assert_eq!(seed.0, expected_seed, "seed must advance to keccak(seed)");
        assert_eq!(out[0].to_u128(), expected_val);
    }

    #[test]
    fn pow_roundtrip_small() {
        let seed0 = Keccak256Seed([0x42u8; 32]);
        let pow_bits = 8;
        // brute force a nonce with top 8 bits zero
        let mut nonce = 0u64;
        let good = loop {
            let mut h = Keccak256::new();
            h.update(seed0.0);
            h.update(nonce.to_be_bytes());
            let mut d = [0u8; 32];
            d.copy_from_slice(h.finalize().as_slice());
            if top_bits_are_zero(&d, pow_bits) {
                break nonce;
            }
            nonce += 1;
        };
        let mut seed = seed0;
        // must not panic
        <Keccak256Transcript as Transcript<Proth120, Proth120>>::verify_pow(
            &mut seed, good, pow_bits,
        );
    }
}
