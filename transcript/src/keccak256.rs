use crate::Transcript;
use field::proth120::Proth120;

// ---------------------------------------------------------------------------
// Stub Keccak256-based transcript.
//
// This is a placeholder that fixes the public surface (associated types and
// the `Transcript<Proth120, Proth120>` impl) so downstream code can be written
// generically against it. None of the methods are implemented yet — they all
// panic via `unimplemented!`. The intended modulus for this transcript is the
// 123-bit Proth prime `Proth120` (`7 * 2^120 + 1`), which is `Field` but not
// `PrimeField`, hence the relaxed `F: Field` bound on the `Transcript` trait.
// ---------------------------------------------------------------------------

/// Stub transcript that will eventually be backed by Keccak-256.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Keccak256Transcript;

/// Stub transcript seed (a 256-bit Keccak digest).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Keccak256Seed(pub [u8; 32]);

/// Stub incremental hasher state.
#[derive(Clone, Copy, Debug, Default)]
pub struct Keccak256Hasher;

impl Transcript<Proth120, Proth120> for Keccak256Transcript {
    type Seed = Keccak256Seed;
    type Hasher = Keccak256Hasher;

    fn commit_initial_u32(_input: &[u32]) -> Self::Seed {
        unimplemented!("Keccak256Transcript::commit_initial_u32 is not implemented yet")
    }

    fn commit_u32_with_seed(_seed: &mut Self::Seed, _input: &[u32]) {
        unimplemented!("Keccak256Transcript::commit_u32_with_seed is not implemented yet")
    }

    fn commit_initial_u32_using_hasher(_hasher: &mut Self::Hasher, _input: &[u32]) -> Self::Seed {
        unimplemented!(
            "Keccak256Transcript::commit_initial_u32_using_hasher is not implemented yet"
        )
    }

    fn commit_u32_with_seed_using_hasher(
        _hasher: &mut Self::Hasher,
        _seed: &mut Self::Seed,
        _input: &[u32],
    ) {
        unimplemented!(
            "Keccak256Transcript::commit_u32_with_seed_using_hasher is not implemented yet"
        )
    }

    fn draw_randomness(_seed: &mut Self::Seed, _dst: &mut [u32]) {
        unimplemented!("Keccak256Transcript::draw_randomness is not implemented yet")
    }

    fn draw_randomness_using_hasher(
        _hasher: &mut Self::Hasher,
        _seed: &mut Self::Seed,
        _dst: &mut [u32],
    ) {
        unimplemented!("Keccak256Transcript::draw_randomness_using_hasher is not implemented yet")
    }

    fn pow_threshold(_pow_bits: u32) -> u32 {
        unimplemented!("Keccak256Transcript::pow_threshold is not implemented yet")
    }

    fn verify_pow(_seed: &mut Self::Seed, _nonce: u64, _pow_bits: u32) {
        unimplemented!("Keccak256Transcript::verify_pow is not implemented yet")
    }

    fn verify_pow_using_hasher(
        _hasher: &mut Self::Hasher,
        _seed: &mut Self::Seed,
        _nonce: u64,
        _pow_bits: u32,
    ) {
        unimplemented!("Keccak256Transcript::verify_pow_using_hasher is not implemented yet")
    }

    #[cfg(feature = "pow")]
    fn search_pow(
        _seed: &Self::Seed,
        _pow_bits: u32,
        _worker: &worker::Worker,
    ) -> (Self::Seed, u64) {
        unimplemented!("Keccak256Transcript::search_pow is not implemented yet")
    }

    fn commit_base_field_elements(_seed: &mut Self::Seed, _els: &[Proth120]) {
        unimplemented!("Keccak256Transcript::commit_base_field_elements is not implemented yet")
    }

    fn commit_extension_field_elements(_seed: &mut Self::Seed, _els: &[Proth120]) {
        unimplemented!(
            "Keccak256Transcript::commit_extension_field_elements is not implemented yet"
        )
    }

    fn draw_random_field_elements(_seed: &mut Self::Seed, _buffer: &mut [Proth120]) {
        unimplemented!("Keccak256Transcript::draw_random_field_elements is not implemented yet")
    }
}
