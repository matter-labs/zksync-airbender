use super::*;

#[derive(Clone, Copy, Debug)]
pub struct ScalarWitnessTypeSet<F: PrimeField, const MERGE_MULTIPLICITY_COUNT: bool> {
    _marker: core::marker::PhantomData<F>,
}

impl<F: PrimeField, const MERGE_MULTIPLICITY_COUNT: bool> WitnessTypeSet<F>
    for ScalarWitnessTypeSet<F, MERGE_MULTIPLICITY_COUNT>
{
    const CAN_BRANCH: bool = true;
    const MERGE_LOOKUP_AND_MULTIPLICITY_COUNT: bool = MERGE_MULTIPLICITY_COUNT;

    type Mask = bool;
    type Field = F;
    type I32 = i32;
    type U32 = u32;
    type U16 = u16;
    type U8 = u8;

    #[inline(always)]
    fn branch(mask: &Self::Mask) -> bool {
        *mask
    }
}
