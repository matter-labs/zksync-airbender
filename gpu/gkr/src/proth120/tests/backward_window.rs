mod bank;
mod continuation;

use field::PrimeField;
use gpu_core::primitives::field::PR;
use rand::{rngs::StdRng, Rng};

fn random_canonical(rng: &mut StdRng) -> PR {
    loop {
        let raw = rng.random::<u128>() >> 5;
        if raw < PR::CHARACTERISTICS_U128 {
            return PR::from_raw_u128(raw);
        }
    }
}
