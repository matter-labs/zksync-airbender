use std::sync::RwLock;

use prover::cs::cs::oracle::Oracle;
use prover::cs::cs::placeholder::Placeholder;
use prover::field::PrimeField;
use rand::rngs::SmallRng;
use rand::Rng;

pub struct RngOracleConfig {
    // Limits the value of the program counter such that the circuit wont crash while fetching the
    // preprocessed decoder tables.
    pub pc_mod: u32,
}

pub struct RngOracle {
    rng: RwLock<SmallRng>,
    cfg: RngOracleConfig,
}

impl RngOracle {
    pub fn new(rng: SmallRng, cfg: RngOracleConfig) -> Self {
        RngOracle {
            rng: RwLock::new(rng),
            cfg,
        }
    }

    fn next<T: std::fmt::Debug>(&self, cb: impl FnOnce(&mut SmallRng) -> T) -> T {
        let value = {
            let mut rng = self.rng.write().unwrap();
            cb(&mut rng)
        };
        log::debug!(
            "Emitted random value of type {}: {value:?}",
            std::any::type_name::<T>()
        );
        value
    }
}

impl<F: PrimeField + std::fmt::Debug> Oracle<F> for RngOracle {
    fn get_witness_from_placeholder(
        &self,
        _placeholder: Placeholder,
        _subindex: usize,
        _trace_row: usize,
    ) -> F {
        self.next(|rng| F::from_u64_with_reduction(rng.next_u64()))
    }

    fn get_u32_witness_from_placeholder(&self, placeholder: Placeholder, _trace_row: usize) -> u32 {
        let value = self.next(|rng| rng.next_u32());
        use Placeholder::*;
        match placeholder {
            // PC register needs to be aligned to 4
            // We mod the aligned value divided by 4 to the pc mod and then reconstruct it.
            // We lose the first 2 MSB but that's actually good because of address alignment.
            PcInit | PcFin => ((value >> 2) % self.cfg.pc_mod) << 2,
            _ => value,
        }
    }

    fn get_timestamp_witness_from_placeholder(
        &self,
        _placeholder: Placeholder,
        _trace_row: usize,
    ) -> prover::common_constants::TimestampScalar {
        self.next(|rng| rng.next_u64())
    }
}
