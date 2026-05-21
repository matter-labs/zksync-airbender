use crate::{baby_bear::ext4::BabyBearExt4, Field};

#[no_mangle]
#[inline(never)]
pub fn test_e4_fma_option(a: &mut BabyBearExt4, b: &BabyBearExt4) {
    a.mul_assign(b);
}

#[no_mangle]
#[inline(never)]
pub fn test_e4_fma_square_option(a: &mut BabyBearExt4) {
    a.square();
}
