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

    // ---- UNREDUCED (non-canonical) operand path ----
    // A BabyBear register word is a raw Montgomery repr; canonical values are < ORDER, but the
    // mop.rr opcodes (addmod/submod/mulmod/fmamod) must ALSO accept non-reduced words (≥ ORDER,
    // ≤ u32::MAX) and reduce them before operating, still emitting a canonical result. Exercise
    // that path end-to-end so the unified circuit's non-canonical handling is actually proven.
    {
        use ::field::baby_bear::base::BabyBearField;
        use ::field::*;

        // Non-canonical reprs of 3 and 7: add ORDER to the canonical raw word. Since raw + ORDER <
        // 2·ORDER < u32::MAX and Montgomery reprs are compared mod ORDER, the field elements are
        // unchanged, so every result must match the reduced computation (10 / 4 / 21 / 31). The
        // black_box calls keep the non-reduced words in registers so real mop.rr ops are emitted.
        let a3 = core::hint::black_box(BabyBearField::from_u32_with_reduction(3));
        let b7 = core::hint::black_box(BabyBearField::from_u32_with_reduction(7));
        let a = core::hint::black_box(BabyBearField(
            core::hint::black_box(a3.raw_u32_value()) + BabyBearField::ORDER,
        ));
        let b = core::hint::black_box(BabyBearField(
            core::hint::black_box(b7.raw_u32_value()) + BabyBearField::ORDER,
        ));

        let mut addition_result = a;
        addition_result.add_assign(&b);
        assert_eq!(addition_result, BabyBearField::from_u32_with_reduction(10));

        let mut subtraction_result = b;
        subtraction_result.sub_assign(&a);
        assert_eq!(subtraction_result, BabyBearField::from_u32_with_reduction(4));

        let mut multiplication_result = a;
        multiplication_result.mul_assign(&b);
        assert_eq!(multiplication_result, BabyBearField::from_u32_with_reduction(21));

        let mut fma_result = addition_result; // 10
        fma_result.add_assign_product(&a, &b); // 10 + 3*7 = 31
        assert_eq!(fma_result, BabyBearField::from_u32_with_reduction(31));

        // Worst-case subtraction: 0 − (u32::MAX as a raw word). u32::MAX ≥ ORDER is the maximal
        // non-canonical subtrahend; the submod circuit's +3p offset must absorb the borrow. Compare
        // against the SAME element written in canonical raw form (u32::MAX mod ORDER).
        let max_nc = core::hint::black_box(BabyBearField(u32::MAX));
        let max_canon =
            core::hint::black_box(BabyBearField(u32::MAX % BabyBearField::ORDER));
        let mut sub_from_zero_nc = BabyBearField::from_u32_with_reduction(0);
        sub_from_zero_nc.sub_assign(&max_nc);
        let mut sub_from_zero_canon = BabyBearField::from_u32_with_reduction(0);
        sub_from_zero_canon.sub_assign(&max_canon);
        assert_eq!(sub_from_zero_nc, sub_from_zero_canon);
    }

    zksync_os_finish_success(&[b, 0, 0, 0, 0, 0, 0, 0]);
}
