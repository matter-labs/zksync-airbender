//! Upstream re-export manifest for `gpu_ntt`.
//!
//! Only items actually consumed by `ntt` and `ntt_twiddles` are listed here.

// -----------------------------------------------------------------------
// `field` — trait bounds used in twiddle generation
// -----------------------------------------------------------------------

pub(crate) use field::Field;
#[cfg(test)]
pub(crate) use field::PrimeField;

// -----------------------------------------------------------------------
// `fft` — twiddle-generation and bit-reversal helpers consumed by
// `ntt_twiddles` (and re-used by the parity tests). `fft` re-exports both
// `field_utils::*` and `utils::*` at its crate root, so the top-level paths
// are the canonical ones.
// -----------------------------------------------------------------------

pub(crate) use fft::{
    bitreverse_enumeration_inplace, distribute_powers_serial, domain_generator_for_size,
};
