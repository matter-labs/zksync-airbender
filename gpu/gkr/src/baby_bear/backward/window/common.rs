use crate::backward::window::common::BWD_COEFF_BANK_CAPACITY;
use gpu_core::primitives::field::E4;

const _: () = assert!(BWD_COEFF_BANK_CAPACITY * core::mem::size_of::<E4>() == 28 * 1_024);
