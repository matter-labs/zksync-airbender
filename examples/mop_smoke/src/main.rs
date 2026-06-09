#![no_std]
#![no_main]

use field::baby_bear::base::BabyBearField;
use field::{Field, PrimeField};
use riscv_common::zksync_os_finish_success;

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

#[inline(never)]
fn main() -> ! {
    let a = BabyBearField::from_nonreduced_u32(core::hint::black_box(0xDEAD_BEEFu32));
    let b = BabyBearField::from_nonreduced_u32(core::hint::black_box(0x0000_0032u32)); // 50

    let mut prod = a;
    Field::mul_assign(&mut prod, &b);

    let mut acc = prod;
    Field::add_assign_product(&mut acc, &a, &b);

    let out = [
        a.as_u32_raw_repr_reduced(),
        b.as_u32_raw_repr_reduced(),
        prod.as_u32_raw_repr_reduced(),
        acc.as_u32_raw_repr_reduced(),
        0,
        0,
        0xC0FF_EE00,
        0,
    ];
    zksync_os_finish_success(&out)
}
