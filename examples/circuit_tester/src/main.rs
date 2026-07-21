#![no_std]
#![no_main]
#![no_builtins]

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
    riscv_common::boot_sequence::init();
    unsafe { workload() }
}

unsafe fn workload() -> ! {
    let mut a = 1;
    let mut b = 1;
    for _i in 0..10 {
        let c = a + b;
        a = b;
        b = c;
    }

    {
        use ::field::*;
        use ::field::baby_bear::base::BabyBearField;

        let a = core::hint::black_box(BabyBearField::from_u32_with_reduction(3));
        let b = core::hint::black_box(BabyBearField::from_u32_with_reduction(7));

        let mut addition_result = a;
        addition_result.add_assign(&b);
        assert_eq!(addition_result, BabyBearField::from_u32_with_reduction(10));

        let mut subtraction_result = b;
        subtraction_result.sub_assign(&a);
        assert_eq!(subtraction_result, BabyBearField::from_u32_with_reduction(4));

        let mut multiplication_result = a;
        multiplication_result.mul_assign(&b);
        assert_eq!(multiplication_result, BabyBearField::from_u32_with_reduction(21));

        let mut fma_result = addition_result;
        fma_result.add_assign_product(&a, &b);
        assert_eq!(fma_result, BabyBearField::from_u32_with_reduction(31));
    }

    zksync_os_finish_success(&[b, 0, 0, 0, 0, 0, 0, 0]);
}
