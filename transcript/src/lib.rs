#![cfg_attr(not(feature = "pow"), no_std)]

// Glob-import the low-level blake2s helpers at the crate root so that both the
// `blake2s` and `pow` submodules can reach them via `crate::`/`super::*`.
#[allow(unused_imports)]
use blake2s_u32::*;

pub use blake2s_u32;
use field::{Field, FieldExtension};

mod blake2s;
pub use self::blake2s::*;

mod keccak256;
pub use self::keccak256::*;

#[cfg(feature = "pow")]
pub mod pow;

/// Fiat-Shamir transcript abstraction.
///
/// Implementors are effectively stateless and expose three families of
/// operations:
/// - committing raw `u32` words (and field elements) into a `Seed`,
/// - drawing pseudo-random `u32` words (and field elements) from a `Seed`,
/// - proof-of-work grinding / verification over a `Seed`.
///
/// The base field `F` is only required to be a [`Field`] (not `PrimeField`),
/// so that large fields such as [`field::proth120::Proth120`] — which cannot
/// fit the `u32`-centric `PrimeField` interface — can have a transcript too.
/// Concrete implementations add whatever stronger bounds (e.g. `PrimeField`)
/// they need for their own serialization.
pub trait Transcript<F: Field, E: FieldExtension<F>>:
    'static + Send + Sync + Clone + Copy + Default
{
    type Seed: 'static + Send + Sync + Clone + Copy + Default;
    type Hasher: 'static + Send + Sync + Clone + Copy;

    // --- committing raw u32 words ---
    fn commit_initial_u32(input: &[u32]) -> Self::Seed;
    fn commit_u32_with_seed(seed: &mut Self::Seed, input: &[u32]);
    fn commit_initial_u32_using_hasher(hasher: &mut Self::Hasher, input: &[u32]) -> Self::Seed;
    fn commit_u32_with_seed_using_hasher(
        hasher: &mut Self::Hasher,
        seed: &mut Self::Seed,
        input: &[u32],
    );

    // --- drawing raw u32 randomness ---
    fn draw_randomness(seed: &mut Self::Seed, dst: &mut [u32]);
    fn draw_randomness_using_hasher(
        hasher: &mut Self::Hasher,
        seed: &mut Self::Seed,
        dst: &mut [u32],
    );

    // --- proof of work ---
    fn pow_threshold(pow_bits: u32) -> u32;
    fn verify_pow(seed: &mut Self::Seed, nonce: u64, pow_bits: u32);
    fn verify_pow_using_hasher(
        hasher: &mut Self::Hasher,
        seed: &mut Self::Seed,
        nonce: u64,
        pow_bits: u32,
    );
    /// Grind for a proof-of-work nonce. Only available with the `pow` feature
    /// since it needs a `Worker` for the parallel search.
    #[cfg(feature = "pow")]
    fn search_pow(seed: &Self::Seed, pow_bits: u32, worker: &worker::Worker) -> (Self::Seed, u64);

    // --- absorbing / drawing field elements ---
    fn commit_base_field_elements(seed: &mut Self::Seed, els: &[F]);
    fn commit_extension_field_elements(seed: &mut Self::Seed, els: &[E]);
    fn draw_random_field_elements(seed: &mut Self::Seed, buffer: &mut [E]);
}
