//! Upstream re-export manifest for `gpu_ntt`.
//!
//! Only items actually consumed by `ntt` and `ntt_twiddles` are listed here.

// -----------------------------------------------------------------------
// `field` — trait bounds used in twiddle generation
// -----------------------------------------------------------------------

#[cfg(test)]
pub(crate) use field::PrimeField;
pub(crate) use field::{Field, TwoAdicField};

// -----------------------------------------------------------------------
// `fft` — twiddle-generation and bit-reversal helpers consumed by
// `ntt_twiddles` (and re-used by the parity tests). `fft` re-exports both
// `field_utils::*` and `utils::*` at its crate root, so the top-level paths
// are the canonical ones.
// -----------------------------------------------------------------------

pub(crate) use fft::{
    bitreverse_enumeration_inplace, distribute_powers_serial, domain_generator_for_size,
};

#[cfg(test)]
pub(crate) use fft::{
    column_major::naive::serial_ct_ntt_natural_to_bitreversed,
    precompute_twiddles_for_fft,
    proth120_lazy::{lde_coset_lazy_r8, lde_coset_lazy_r8_into},
    Twiddles,
};
#[cfg(test)]
pub(crate) use prover::{
    allocation_pool::GenericAllocationPool,
    gkr::prover::backend::{Backend, Proth120WorkStealingLazyBackend},
    gkr::whir::hypercube_to_monomial::multivariate_hypercube_evals_into_coeffs_radix4,
};
#[cfg(test)]
pub(crate) use worker::Worker;
