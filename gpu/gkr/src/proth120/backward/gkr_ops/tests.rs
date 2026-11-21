use crate::gkr_ops::tests::claims_parity_suite;
use crate::upstream::Field;
use era_cudart::{
    memory::{memory_copy_async, DeviceAllocation},
    stream::CudaStream,
};

fn sample_pr(seed: u32) -> gpu_core::primitives::field::PR {
    let limbs = [
        seed.wrapping_mul(0x9E3779B1),
        seed.wrapping_mul(0x85EBCA77),
        seed.wrapping_mul(0xC2B2AE3D),
        seed.wrapping_mul(0x27D4EB2F),
    ];
    let value = limbs
        .into_iter()
        .fold(0u128, |acc, word| (acc << 32) | u128::from(word));
    gpu_core::primitives::field::PR::from_u128_with_reduction(value)
}
claims_parity_suite!(
    proth120_claims,
    gpu_core::primitives::field::PR,
    sample_pr,
    crate::proth120::backward::gkr_ops::new_claims_two_var,
    crate::proth120::backward::gkr_ops::new_claims_linear,
    crate::proth120::backward::gkr_ops::dim_reducing_lsb_lines,
    crate::proth120::backward::gkr_ops::build_combined_claim
);
