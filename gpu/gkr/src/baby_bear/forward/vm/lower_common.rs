use gpu_core::primitives::field::{BF, E4};

use crate::{forward::vm::lower_common::*, upstream::PrimeField};

impl LoweringField for BF {
    type Ext = E4;
    const NEEDS_SETUP_FILL: bool = true;
    const SEPARATE_DECODER_MAPPING: bool = false;
    fn canonical_constant(value: u128) -> Self {
        let canonical = u32::try_from(value)
            .ok()
            .filter(|&v| v < BF::CHARACTERISTICS_U32)
            .unwrap_or_else(|| {
                panic!("forward constant {value} is not a canonical BabyBear value")
            });
        BF::from_u32_with_reduction(canonical)
    }
    fn inits_top_bits(raw: u32, shift: u32) -> Self {
        BF::from_u32_with_reduction(raw.checked_shl(shift).unwrap_or(0))
    }
}
