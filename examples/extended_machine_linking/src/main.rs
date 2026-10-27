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

/// `.rodata`: a byte table (sub-word loads) and a word table, both read through `black_box` so
/// the compiler keeps them in memory.
static BYTES: [u8; 16] = [
    0x01, 0x80, 0xfe, 0x7f, 0x10, 0x20, 0x30, 0x40, 0xaa, 0xbb, 0xcc, 0xdd, 0x00, 0xff, 0x55,
    0x99,
];
static HALFWORDS: [u16; 8] = [1, 0x8000, 0xfffe, 0x7fff, 0x1234, 0xabcd, 0, 0xffff];
static WORDS: [u32; 6] = [3, 0x89ab_cdef, 0x1234_5678, 0xffff_ffff, 7, 0xdead_beef];

/// `.data`: initialised and then modified in place (byte / halfword / word stores). Exported
/// and accessed through volatile pointers so that LTO cannot fold the statics into constants
/// (which would leave `.data` empty).
#[no_mangle]
#[used]
static mut COUNTERS: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
#[no_mangle]
#[used]
static mut SMALL: [u8; 8] = [9, 8, 7, 6, 5, 4, 3, 2];
#[no_mangle]
#[used]
static mut HALVES: [u16; 4] = [0x0102, 0x0304, 0x0506, 0x0708];

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

    // --- .rodata through sub-word and word loads, with the signedness of each width ---
    let bytes = core::hint::black_box(&BYTES);
    let halfwords = core::hint::black_box(&HALFWORDS);
    let words = core::hint::black_box(&WORDS);
    let mut acc: u32 = 0;
    for (i, byte) in bytes.iter().enumerate() {
        let unsigned = *byte as u32;
        let signed = (*byte as i8) as i32 as u32;
        acc = acc.wrapping_add(unsigned.wrapping_mul(i as u32 + 1)).wrapping_add(signed);
    }
    for (i, half) in halfwords.iter().enumerate() {
        let unsigned = *half as u32;
        let signed = (*half as i16) as i32 as u32;
        acc = acc.wrapping_add(unsigned ^ signed).wrapping_mul(2 * i as u32 + 1);
    }
    for word in words.iter() {
        acc = acc.wrapping_mul(*word).wrapping_add(((*word as u64 * acc as u64) >> 32) as u32);
    }
    assert_eq!(bytes[1], 0x80);
    assert_eq!((bytes[2] as i8) as i32, -2);
    assert_eq!(halfwords[1], 0x8000);
    assert_eq!((halfwords[2] as i16) as i32, -2);
    assert_eq!(words[1], 0x89ab_cdef);

    // --- .data: read the initial content, then rewrite it with sub-word stores ---
    use core::ptr::{read_volatile, write_volatile};
    let counters = core::hint::black_box((&raw mut COUNTERS).cast::<u32>());
    let small = core::hint::black_box((&raw mut SMALL).cast::<u8>());
    let halves = core::hint::black_box((&raw mut HALVES).cast::<u16>());
    let mut sum = 0u32;
    for i in 0..8 {
        let c = read_volatile(counters.add(i));
        assert_eq!(c, i as u32 + 1);
        write_volatile(counters.add(i), c.wrapping_mul(acc | 1));
        sum = sum.wrapping_add(read_volatile(counters.add(i)));
        let s = read_volatile(small.add(i));
        assert_eq!(s, 9 - i as u8);
        write_volatile(small.add(i), s.wrapping_add(c as u8));
        sum = sum.wrapping_add(read_volatile(small.add(i)) as u32);
    }
    for i in 0..4 {
        let h = read_volatile(halves.add(i));
        assert_eq!(h, 0x0102 + 0x0202 * i as u16);
        write_volatile(
            halves.add(i),
            h.wrapping_mul(3).wrapping_add(read_volatile(small.add(i)) as u16),
        );
        sum = sum.wrapping_add(read_volatile(halves.add(i)) as u32);
    }

    // The modular-arithmetic opcodes of the unified machines (mop.rr), as in circuit_tester.
    {
        use ::field::baby_bear::base::BabyBearField;
        use ::field::*;

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

    zksync_os_finish_success(&[b, acc, sum, 0, 0, 0, 0, 0]);
}
