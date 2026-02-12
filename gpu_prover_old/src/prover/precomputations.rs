use super::E2;
use fft::{bitreverse_enumeration_inplace, domain_generator_for_size};
use field::{Field, TwoAdicField};
use std::sync::LazyLock;

const INVERSE_TWIDDLES_LOG_SIZE: usize = 8;
pub(crate) static PRECOMPUTATIONS: LazyLock<Precomputations> = LazyLock::new(Precomputations::new);

pub(crate) struct Precomputations {
    pub omegas: [E2; E2::TWO_ADICITY + 1],
    pub omegas_inv: [E2; E2::TWO_ADICITY + 1],
    pub inverse_twiddles: [E2; 1 << INVERSE_TWIDDLES_LOG_SIZE],
}

impl Precomputations {
    pub(crate) fn new() -> Self {
        let mut omegas = [E2::ZERO; E2::TWO_ADICITY + 1];
        let mut omega = E2::two_adic_generator();
        omegas.iter_mut().rev().for_each(|el| {
            *el = omega;
            omega.square();
        });
        for i in 0..E2::TWO_ADICITY + 1 {
            assert_eq!(omegas[i], domain_generator_for_size::<E2>(1 << i));
        }
        assert_eq!(omegas[0], E2::ONE);
        let mut omegas_inv = [E2::ZERO; E2::TWO_ADICITY + 1];
        let mut omega_inv = E2::two_adic_generator().inverse().unwrap();
        omegas_inv.iter_mut().rev().for_each(|el| {
            *el = omega_inv;
            omega_inv.square();
        });
        assert_eq!(omegas_inv[0], E2::ONE);
        let mut inverse_twiddles = [E2::ZERO; 1 << INVERSE_TWIDDLES_LOG_SIZE];
        let base = omegas_inv[INVERSE_TWIDDLES_LOG_SIZE + 1];
        let mut value = E2::ONE;
        inverse_twiddles.iter_mut().for_each(|el| {
            *el = value;
            value.mul_assign(&base);
        });
        bitreverse_enumeration_inplace(&mut inverse_twiddles);
        Self {
            omegas,
            omegas_inv,
            inverse_twiddles,
        }
    }

    pub(crate) fn ensure_initialized() {
        // This function is called to ensure that the static PRECOMPUTATIONS is initialized.
        // The LazyLock will initialize it on the first call.
        let _ = &*PRECOMPUTATIONS;
    }
}
