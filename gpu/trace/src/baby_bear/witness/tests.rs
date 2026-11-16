use field::PrimeField;
use gpu_core::primitives::device_structures::DeviceMatrixMut;
use gpu_core::primitives::field::BF;
use gpu_prover_context::ProverContext;

use crate::witness::tests::MultiplicityField;

impl MultiplicityField for BF {
    fn count(value: u32) -> Self {
        BF::from_u32_unchecked(value)
    }
    fn generate(
        mapping: &mut DeviceMatrixMut<'_, u32>,
        counts: &mut DeviceMatrixMut<'_, Self>,
        active: usize,
        context: &ProverContext,
    ) {
        crate::baby_bear::witness::multiplicities::generate_lookup_multiplicities(
            mapping, counts, active, context,
        )
        .unwrap();
    }
}
