
#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]


use riscv_common::{csr_read_word, zksync_os_finish_success};

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

#[inline(always)]
fn csr_trigger_delegation(
    input_a: *mut u32,
    input_b: *const u32,
    round_mask: &mut u32,
) {
    unsafe {
        core::arch::asm!(
            "csrrw x0, 0x7ca, x0",
            in("x10") input_a.addr(),
            in("x11") input_b.addr(),
            inlateout("x12") *round_mask,
            options(nostack, preserves_flags)
        )
    }
}

#[repr(C)]
#[repr(align(32))]
pub struct U256(pub [u32; 8]);

// Little Endian
unsafe fn workload() -> ! {
    fn run_case(a: &mut U256, b: &U256, out: &mut [u32], mut mask: u32) {
        csr_trigger_delegation(a.0.as_mut_ptr(), b.0.as_ptr(), &mut mask);
        out[0] = a.0[0];
        out[1] = a.0[1];
        out[2] = a.0[2];
        out[3] = a.0[3];
        out[4] = a.0[4];
        out[5] = a.0[5];
        out[6] = a.0[6];
        out[7] = a.0[7];
        out[8] = mask;
    }
    let mut out: [u32; 9] = [0; 9];
    // Case 1: simple add, no overflow
    let mut a = U256([1, 2, 3, 4, 5, 6, 7, 8]);
    let b = U256([9, 10, 11, 12, 13, 14, 15, 16]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [10, 12, 14, 16, 18, 20, 22, 24, 0]);



    out = [0; 9];
    // Case 2: single limb carry
    let mut a = U256([0xffff_ffff, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0, 1, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 3: ripple carry across first 3 limbs
    let mut a = U256([0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0, 0, 0, 0, 0]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0, 0, 0, 1, 0, 0, 0, 0, 0]);
    out = [0; 9];
    // Case 4: full overflow wraps to 0 with carry out
    let mut a = U256([0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 5: boundary half range 
    let mut a = U256([0x8000_0000, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0x8000_0000, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0, 1, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 6: max + max
    let mut a = U256([0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff]);
    let b = U256([0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff, 0xffff_ffff]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 7: zeros
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 8: zero add something
    let mut a = U256([5, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [5, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 9: mixed carries in the middle limbs
    let mut a = U256([0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0x0000_0000, 0xFFFF_FFFF, 0x0000_0000, 0x8000_0000, 0x0000_0000]);
    let b = U256([0x1111_1111, 0x2222_2222, 0xFFFF_FFFF, 0x0000_0001, 0x0000_0001, 0xFFFF_FFFF, 0x8000_0000, 0x0000_0000]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0x2345_6789, 0xBCDF_0112, 0x0000_0000, 0x0000_0002, 0x0000_0000, 0x0000_0000, 0x0000_0001, 0x0000_0001, 0]);

    out = [0; 9];
    // Case 10: propagate carry through lower 7 limbs. no final overflow
    let mut a = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x7FFF_FFFF]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0x8000_0000, 0]);

    out = [0; 9];
    // Case 11: top limb overflow only
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 12: alternating patterns with no carries per limb
    let mut a = U256([0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA]);
    let b = U256([0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0]);

    out = [0; 9];
    // Case 13: edge carry into second limb only
    let mut a = U256([0xFFFF_FFFE, 0x0000_0000, 0x0000_0001, 0, 0, 0, 0, 0]);
    let b = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0x0000_0000, 0x0000_0001, 0x0000_0001, 0, 0, 0, 0, 0, 0]);

    // Case 14: Carry-in set.  0xFFFF_FFFE + 1 + carry(1) => 0 with carry out into limb 1
    let mut a = U256([0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [0, 1, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 15: Carry-in, no overflow beyond limb 
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [1, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 16: Carry-in causes ripple across first 3 limbs
    let mut a = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [0, 0, 0, 1, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 17: Carry-in with boundary half-range
    let mut a = U256([0x8000_0000, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0x8000_0000, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [1, 1, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 18: Carry-in with max + 0
    let mut a = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 19: Mixed values with carry-in that does not cause further carries
    let mut a = U256([0x1234_5678, 0x0000_0001, 0, 0, 0, 0, 0, 0]);
    let b = U256([0x0000_0001, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [0x1234_567A, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0]);
    
    out = [0; 9];
    // Case 20: Alternating + complement with carry-in all
    let mut a = U256([0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA]);
    let b = U256([0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 21: Top limb overflow due to carry-in only
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [1, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0]);

    out = [0; 9];
    // Case 22: Long carry ripple across 7 limbs, increments top to 0x8000_0000, no overflow
    let mut a = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x7FFF_FFFF]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0x8000_0000, 0]);

    out = [0; 9];
    // Case 23: ADD with carry-in where b is max and a is zero 
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 24: mid-limb exact fill (no carry)
    let mut a = U256([0x0000_0000, 0x0000_0000, 0x0000_0000, 0x7FFF_FFFF, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000]);
    let b = U256([0x0000_0000, 0x0000_0000, 0x0000_0000, 0x8000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0x0000_0000, 0x0000_0000, 0x0000_0000, 0xFFFF_FFFF, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0]);

    out = [0; 9];
    // Case 25: single mid-limb overflow into next limb only
    let mut a = U256([0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0xFFFF_FFFF, 0x0000_0000, 0x0000_0000, 0x0000_0000]);
    let b = U256([0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0001, 0x0000_0000, 0x0000_0000, 0x0000_0000]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0001, 0x0000_0000, 0x0000_0000, 0]);

    out = [0; 9];
    // Case 26: segmented carries 
    let mut a = U256([0xFFFF_FFFF, 0x0000_0000, 0xFFFF_FFFF, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000]);
    let b = U256([0x0000_0001, 0x0000_0000, 0x0000_0001, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0x0000_0000, 0x0000_0001, 0x0000_0000, 0x0000_0001, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0]);

    out = [0; 9];
    // Case 27: sparse high limbs + big low mask
    let mut a = U256([0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0001, 0x8000_0000]);
    let b = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0001, 0x8000_0000, 0]);

    out = [0; 9];
    // Case 28: all limbs 0x8000_0000 + same 
    let mut a = U256([0x8000_0000; 8]);
    let b = U256([0x8000_0000; 8]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0x0000_0000, 0x0000_0001, 0x0000_0001, 0x0000_0001, 0x0000_0001, 0x0000_0001, 0x0000_0001, 0x0000_0001, 1]);

    out = [0; 9];
    // Case 29: x + (-x) =  0 with carry-out = 1
    let mut a = U256([0xDEAD_BEEF, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006, 0x0000_0007]);
    let b = U256([0x2152_4111, 0xFFFF_FFFE, 0xFFFF_FFFD, 0xFFFF_FFFC, 0xFFFF_FFFB, 0xFFFF_FFFA, 0xFFFF_FFF9, 0xFFFF_FFF8]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 1]);

    out = [0; 9];
    // Case 30: max + 2 -> ripple across all lower limbs and set carry-out
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([0x0000_0002, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0x0000_0001, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 1]);

    out = [0; 9];
    // Case 31: carry-in ripples through 7 lower limbs
    let mut a = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x7FFF_FFFF]);
    let b = U256([0; 8]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x8000_0000, 0]);

    out = [0; 9];
    // Case 32: carry-in that doesn't propagate 
    let mut a = U256([0xFFFF_FFFE, 0xAAAA_AAAA, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000]);
    let b = U256([0; 8]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [0xFFFF_FFFF, 0xAAAA_AAAA, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0]);

    out = [0; 9];
    // Case 33: carry-in ripples one limb
    let mut a = U256([0xFFFF_FFFF, 0x1234_5678, 0, 0, 0, 0, 0, 0]);
    let b = U256([0; 8]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [0x0000_0000, 0x1234_5679, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0]);

    out = [0; 9];
    // Case 34: mid-limb with carry to next
    let mut a = U256([0, 0, 0, 0, 0, 0x8000_0001, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0x8000_0000, 0, 0]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0, 0, 0, 0, 0, 0x0000_0001, 0x0000_0001, 0, 0]);

    out = [0; 9];
    // Case 35: limbs sum to all 0xFFFF_FFFF without any carry
    let mut a = U256([0xFFFF_0000; 8]);
    let b = U256([0x0000_FFFF; 8]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0]);

    out = [0; 9];
    // Case 36: ripple across 4 lower limbs then stop at limb4
    let mut a = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x1234_5678, 0, 0, 0]);
    let b = U256([0x0000_0001, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0, 0, 0, 0, 0x1234_5679, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 37: near-overflow, add 1 into limb0 and limb7
    let mut a = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE]);
    let b = U256([0x0000_0001, 0, 0, 0, 0, 0, 0, 0x0000_0001]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 38: long ripple + top half+half -> total overflow 
    let mut a = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x7FFF_FFFF]);
    let b = U256([0x0000_0001, 0, 0, 0, 0, 0, 0, 0x8000_0000]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 39: multiple separated carries & exact-fill limbs in one vector
    let mut a = U256([0xFFFF_FFFF, 0x0000_0000, 0x7FFF_FFFF, 0x0000_0000, 0xFFFF_FFFF, 0x0000_0000, 0x0000_0000, 0x0000_0000]);
    let b = U256([0x0000_0001, 0x8000_0000, 0x8000_0000, 0x0000_0000, 0x0000_0001, 0x0000_0000, 0x0000_0000, 0x0000_0000]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0x0000_0000, 0x8000_0001, 0xFFFF_FFFF, 0x0000_0000, 0x0000_0000, 0x0000_0001, 0x0000_0000, 0x0000_0000, 0]);

    out = [0; 9];
    // Case 40: carry-in with all 0x8000_0000 
    let mut a = U256([0x8000_0000; 8]);
    let b = U256([0; 8]);
    run_case(&mut a, &b, &mut out, (1 | 1 << 6));
    assert_eq!(out, [0x8000_0001, 0x8000_0000, 0x8000_0000, 0x8000_0000, 0x8000_0000, 0x8000_0000, 0x8000_0000, 0x8000_0000, 0]);

    out = [0; 9];
    // Case 41: high-bit preserved (no carry from low limbs)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0x8000_0000]);
    let b = U256([5, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0x0000_0005, 0, 0, 0, 0, 0, 0, 0x8000_0000, 0]);

    out = [0; 9];
    // Case 42: two adjacent mid-limb carries 
    let mut a39 = U256([0, 0, 0, 0, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0]);
    let b39 = U256([0, 0, 0, 0, 0x0000_0001, 0x0000_0001, 0, 0]);
    run_case(&mut a39, &b39, &mut out, 1);
    assert_eq!(out, [0, 0, 0, 0, 0, 0x0000_0001, 0x0000_0001, 0, 0]);

    out = [0; 9];
    // Case 43: all F, no overflow
    let mut a = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x7FFF_FFFF]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0x8000_0000]);
    run_case(&mut a, &b, &mut out, 1);
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0]);

    out = [0; 9];
    // Case 44 (SUB): simple subtract, no borrow
    let mut a = U256([10, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [9, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 45 (SUB): zero minus one -> all F, borrow out
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 46 (SUB): borrow ripples through first two limbs then stops
    let mut a = U256([0, 0, 1, 0, 0, 0, 0, 0]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0x0000_0000, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 47 (SUB+borrow)
    let mut a = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (2 | (1 << 6)));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 48 (SUB+borrow)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (2 | (1 << 6)));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 49 (SUB): top-limb borrow only
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0x0000_0000]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0x0000_0001]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 50 (SUB)
    let mut a = U256([0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA, 0xAAAA_AAAA]);
    let b = U256([0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0]);

    out = [0; 9];
    // Case 51 (SUB): equal operands -> zero, no borrow
    let mut a = U256([0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006]);
    let b = U256([0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 52 (SUB+borrow): equal operands with borrow-in -> all F, borrow out
    let mut a = U256([0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006]);
    let b = U256([0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006]);
    run_case(&mut a, &b, &mut out, 2 | (1 << 6));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 53 (SUB): borrow stops at second limb 
    let mut a = U256([1, 1, 0, 0, 0, 0, 0, 0]);
    let b = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0xFFFF_FFFF, 0x0000_0000, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 54 (SUB): all zero
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 55: simple per-limb subtract, no borrows anywhere
    let mut a = U256([10, 20, 30, 40, 50, 60, 70, 80]);
    let b = U256([1,  2,  3,  4,  5,  6,  7,  8]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0x0000_0009, 0x0000_0012, 0x0000_001B, 0x0000_0024, 0x0000_002D, 0x0000_0036, 0x0000_003F, 0x0000_0048, 0]);

    out = [0; 9];
    // Case 56: ripple borrow across 3 limbs, then stop
    let mut a = U256([0, 0, 0, 1, 0, 0, 0, 0]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x0000_0000, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 57: equal numbers => zero, no borrow-out
    let mut a = U256([5, 6, 7, 8, 9, 10, 11, 12]);
    let b = U256([5, 6, 7, 8, 9, 10, 11, 12]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 58: identity 
    let mut a = U256([5, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0x0000_0005, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 59: 0 - 0 = 0, no borrow
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 60: top-limb only underflow
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 44: exact-fill mid-limb 
    let mut a = U256([0, 0, 0, 0x8000_0000, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0x8000_0000, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 45: borrow-out=1 
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0x0000_0001, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 46: max - max = 0
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([0xFFFF_FFFF; 8]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 47: long ripple from LSW into top limb 
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0x1000_0000]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x0FFF_FFFF, 0]);

    out = [0; 9];
    // Case 61: alternating patterns 
    let mut a = U256([0xAAAA_AAAA; 8]);
    let b = U256([0x5555_5555; 8]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0x5555_5555, 0]);

    out = [0; 9];
    // Case 62: multiple adjacent borrows in the middle
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([1, 1, 0, 0, 1, 1, 0, 0]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 63: borrow-in only
    let mut a = U256([5, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([3, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (2 | 1 << 6));
    assert_eq!(out, [0x0000_0001, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 64: borrow-in ripples across two zero limbs
    let mut a = U256([0, 0, 1, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (2 | 1 << 6));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0x0000_0000, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 65: a == b plus borrow-in
    let mut a = U256([0x1234_5678; 8]);
    let b = U256([0x1234_5678; 8]);
    run_case(&mut a, &b, &mut out, (2 | 1 << 6));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 66: borrow-in stops at top limb 
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (2 | 1 << 6));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x0000_0000, 0]);

    out = [0; 9];
    // Case 67: mixed pattern 
    let mut a = U256([0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0x0000_0000, 0xFFFF_FFFF, 0x0000_0000, 0x8000_0000, 0x0000_0000]);
    let b = U256([0x1111_1111, 0x2222_2222, 0xFFFF_FFFF, 0x0000_0001, 0x0000_0001, 0xFFFF_FFFF, 0x8000_0000, 0x0000_0000]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0x0123_4567, 0x789A_BCCE, 0x0000_0002, 0xFFFF_FFFE, 0xFFFF_FFFD, 0x0000_0001, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 68: high-limb pays for long underflow from LSW 
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    let b = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, 2);
    assert_eq!(out, [0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x0000_0000, 0]);

    out = [0; 9];
    // Case 69 (SUB&NEG): simple b > a, no borrow-in
    let mut a = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([10, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [9, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 70 (SUB&NEG): b < a -> underflow wrap to all 0xFFFF_FFFF
    let mut a = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 71 (SUB&NEG): ripple one limb. Using limb1 only
    let mut a = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 1, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0xFFFF_FFFF, 0x0000_0000, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 72 (SUB&NEG + borrow-in)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, ((1 << 2) | (1 << 6)));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 73 (SUB&NEG + borrow-in): long ripple from carry-in with a having bit in limb2
    let mut a = U256([0, 0, 1, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, ((1 << 2) | (1 << 6)));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 74 (SUB&NEG): equal operands 
    let mut a = U256([0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6]);
    let b = U256([0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 75 (SUB&NEG + borrow-in): equal operands with borrow-in 
    let mut a = U256([0x1234_5678; 8]);
    let b = U256([0x1234_5678; 8]);
    run_case(&mut a, &b, &mut out, ((1 << 2) | (1 << 6)));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 76 (SUB&NEG): b = max, a = 0 -> result = max
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0xFFFF_FFFF; 8]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0]);

    out = [0; 9];
    // Case 77 (SUB&NEG): b = 0, a = max -> result = 1 with borrow-out
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [1, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 78 (SUB&NEG): top limb only (1 at top) minus 0 -> keep top limb
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 1, 0]);

    out = [0; 9];
    // Case 79 (SUB&NEG + borrow-in): equal operands with borrow-in 
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([0x1111_1111, 0x2222_2222, 0xFFFF_FFFF, 0x0000_0001, 0x0000_0001, 0xFFFF_FFFF, 0x8000_0000, 0x0000_0000]);
    run_case(&mut a, &b, &mut out, ((1 << 2) | (1 << 6)));
    assert_eq!(out, [ 0x1111_1111, 0x2222_2222, 0xFFFF_FFFF, 0x0000_0001, 0x0000_0001, 0xFFFF_FFFF, 0x8000_0000, 0x0000_0000, 1]);

    out = [0; 9];
    // Case 80 (SUB&NEG): b = a + 1 across limb1 boundary 
    let mut a = U256([0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0x0000_0000, 0x0000_0001, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0x0000_0001, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 81 (SUB&NEG): b=0, a has LSW and MSW bits set 
    let mut a = U256([0x0000_0001, 0, 0, 0, 0, 0, 0, 0x0000_0001]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 1]);

    out = [0; 9];
    // Case 82 (SUB&NEG): b = all F, a = mixed
    let mut a = U256([0x0123_4567, 0x89AB_CDEF, 0x0000_0000, 0xFFFF_FFFF, 0x8000_0000, 0x7FFF_FFFF, 0x0000_0000, 0x0000_0001]);
    let b = U256([0xFFFF_FFFF; 8]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0xFEDC_BA98, 0x7654_3210, 0xFFFF_FFFF, 0x0000_0000, 0x7FFF_FFFF, 0x8000_0000, 0xFFFF_FFFF, 0xFFFF_FFFE, 0]);

    out = [0; 9];
    // Case 83 (SUB&NEG): exact mid-limb 
    let mut a = U256([0, 0, 0, 0x7FFF_FFFF, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0x8000_0000, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0, 0, 0, 0x0000_0001, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 84 (SUB&NEG): borrow chain: limb5 lends to limb3 
    let mut a = U256([0, 0, 0, 0x0000_0002, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0x0000_0001, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0, 0, 0, 0xFFFF_FFFE, 0xFFFF_FFFF, 0x0000_0000, 0, 0, 0]);

    out = [0; 9];
    // Case 85 (SUB&NEG + borrow-in)
    let mut a = U256([0, 0, 0, 0x0000_0002, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0x0000_0001, 0, 0]);
    run_case(&mut a, &b, &mut out, ((1 << 2) | (1 << 6)));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFD, 0xFFFF_FFFF, 0x0000_0000, 0, 0, 0]);

    out = [0; 9];
    // Case 86 (SUB&NEG): only limb3 differs by +1
    let mut a = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x1234_5678, 0, 0, 0, 0]);
    let b = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x1234_5679, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0, 0, 0, 0x0000_0001, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 87 (SUB&NEG)
    let mut a = U256([0x0000_0000, 0x0000_0001, 0, 0, 0, 0, 0, 0]);
    let b = U256([0xFFFF_FFFF, 0x0000_0000, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 88 (SUB&NEG)
    let mut a = U256([0x1111_1110, 0x2222_2220, 0x3333_3330, 0x4444_4440, 0x5555_5550, 0x6666_6660, 0x7777_7770, 0x8888_8880]);
    let b = U256([0x1111_1115, 0x2222_2225, 0x3333_3335, 0x4444_4445, 0x5555_5555, 0x6666_6665, 0x7777_7775, 0x8888_8885]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [5, 5, 5, 5, 5, 5, 5, 5, 0]);

    out = [0; 9];
    // Case 89 (SUB&NEG + borrow-in)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0x0000_0001, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, ((1 << 2) | (1 << 6)));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x0000_0000, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 90 (SUB&NEG)
    let mut a = U256([0x8000_0000, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0x8000_0000, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 91 (SUB&NEG): top-limb underflow only
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0x8000_0000]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0x7FFF_FFFF]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 92 (SUB&NEG)
    let mut a = U256([0x0000_0001, 0, 0x0000_0001, 0, 0, 0x0000_0001, 0, 0x0000_0001]);
    let b = U256([0; 8]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFE, 1]);

    out = [0; 9];
    // Case 93 (SUB&NEG + borrow-in)
    let mut a = U256([0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0x0000_0001, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, ((1 << 2) | (1 << 6)));
    assert_eq!(out, [0x0000_0001, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 94 (SUB&NEG)
    let mut a = U256([0x0000_0001, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0x0000_0001, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x0000_0000, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 95 (SUB&NEG + borrow-in): complex mixed 
    let mut a = U256([0x1234_5678, 0x9ABC_DEF0, 0x0000_0001, 0x0000_0000, 0xFFFF_FFFF, 0x0000_0000, 0x8000_0000, 0x0000_0000]);
    let b = U256([0x1111_1111, 0x2222_2222, 0xFFFF_FFFF, 0x0000_0001, 0x0000_0001, 0xFFFF_FFFF, 0x8000_0000, 0x0000_0000]);
    run_case(&mut a, &b, &mut out, ((1 << 2) | (1 << 6)));
    assert_eq!(out, [0xFEDC_BA98, 0x8765_4331, 0xFFFF_FFFD, 0x0000_0001, 0x0000_0002, 0xFFFF_FFFE, 0x0000_0000, 0x0000_0000, 0]);

    out = [0; 9];
    // Case 96 (SUB&NEG + borrow-in): b=0, a=all F -> b - a - 1 == 0, borrow-out=1
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([0; 8]);
    run_case(&mut a, &b, &mut out, ((1 << 2) | (1 << 6)));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 97 (SUB&NEG)
    let mut a = U256([0x0000_0002, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0x0000_0001]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0x0000_0000, 0]);

    out = [0; 9];
    // Case 98 (SUB&NEG + borrow-in): tiny b < a, plus −1 => underflow to 2^256 − 2
    let mut a = U256([0x0000_0002, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0x0000_0001, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, ((1 << 2) | (1 << 6)));
    assert_eq!(out, [0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 99 (SUB&NEG): b=0 minus mixed a -> complement with borrow-out=1
    let mut a = U256([0xDEAD_BEEF, 0x0000_0001, 0x2222_2222, 0x0000_0000, 0xABCD_EF01, 0x8000_0000, 0, 0xFFFF_FFFF]);
    let b = U256([0; 8]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0x2152_4111, 0xFFFF_FFFE, 0xDDDD_DDDD, 0xFFFF_FFFF, 0x5432_10FE, 0x7FFF_FFFF, 0xFFFF_FFFF, 0x0000_0000, 1]);

    out = [0; 9];
    // Case 100 (SUB&NEG)
    let mut a = U256([0x8000_0000, 0x0000_0001, 0, 0, 0, 0, 0, 0]);
    let b = U256([0x8000_0000, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 2));
    assert_eq!(out, [0x0000_0000, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 101 (MUL_LOW)
    let mut a = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([3, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [6, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 102 (MUL_LOW): single-limb with carry into limb1 (0xFFFF_FFFF * 2)
    let mut a = U256([0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0xFFFF_FFFE, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 103 (MUL_LOW): 0x8000_0000 * 0x8000_0000 -> limb1 = 0x4000_0000
    let mut a = U256([0x8000_0000, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0x8000_0000, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0x0000_0000, 0x4000_0000, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 104 (MUL_LOW): top-limb only (limb7 * limb7) -> low part zero, overflow=1
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 105 (MUL_LOW): all F times 1 -> identity, no overflow
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0]);

    out = [0; 9];
    // Case 106 (MUL_LOW): all F times all F -> low is 1, overflow=1
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([0xFFFF_FFFF; 8]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [1, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 107 (MUL_LOW): all F times 2 -> ripple across all limbs, overflow=1
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 108 (MUL_LOW): mid-limb multiply (limb3 * limb3) -> result at limb6
    let mut a = U256([0, 0, 0, 1, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 1, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 1, 0, 0]);

    out = [0; 9];
    // Case 109 (MUL_LOW): zero multiplicand -> zero result, no overflow
    let mut a = U256([0; 8]);
    let b = U256([0xDEAD_BEEF, 0xCAFEBABE, 0x0123_4567, 0, 1, 2, 3, 4]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 110 (MUL_LOW): identity by 1 with mixed pattern
    let mut a = U256([0x0000_0001, 0x8000_0000, 0x7FFF_FFFF, 0x0123_4567, 0x89AB_CDEF, 0, 0xFFFF_FFFF, 0x0000_0001]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0x0000_0001, 0x8000_0000, 0x7FFF_FFFF, 0x0123_4567, 0x89AB_CDEF, 0, 0xFFFF_FFFF, 0x0000_0001, 0]);

    out = [0; 9];
    // Case 111 (MUL_LOW): cross-limb within boundary (limb1 * limb6) -> limb7=1, no overflow
    let mut a = U256([0, 1, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 1, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 1, 0]);

    out = [0; 9];
    // Case 112 (MUL_LOW): cross-limb beyond boundary (limb2 * limb6) -> low zero, overflow=1
    let mut a = U256([0, 0, 1, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 1, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 113 (MUL_LOW): (0xFFFF_FFFF * 0xFFFF_FFFF)
    let mut a = U256([0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0x0000_0001, 0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 114 (MUL_LOW): (a0=1,a1=1) * (b1=1) -> limb1=1, limb2=1
    let mut a = U256([1, 1, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 1, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 1, 1, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 115 (MUL_LOW): doubling multi-limb with carry propagation
    let mut a = U256([0xFFFF_FFFF, 0x0000_0001, 0, 0, 0, 0, 0, 0]);
    let b = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0xFFFF_FFFE, 0x0000_0003, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 116 (MUL_LOW): top*low causing high-only carry -> low zeros, overflow=1
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 2]);
    let b = U256([0x8000_0000, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 117 (MUL_LOW): shift by one limb (2^32 * x), no overflow
    let mut a = U256([0, 1, 0, 0, 0, 0, 0, 0]);
    let b = U256([0xDEAD_BEEF, 0xCAFE_BABE, 1, 2, 3, 4, 5, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0x0000_0000, 0xDEAD_BEEF, 0xCAFE_BABE, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0]);

    out = [0; 9];
    // Case 118 (MUL_LOW): shift by one limb with overflow (top limb spills)
    let mut a = U256([0, 1, 0, 0, 0, 0, 0, 0]);
    let b = U256([0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006, 0x0000_0007, 0x0000_0008]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0x0000_0000, 0x0000_0001, 0x0000_0002, 0x0000_0003, 0x0000_0004, 0x0000_0005, 0x0000_0006, 0x0000_0007, 1]);

    out = [0; 9];
    // Case 119 (MUL_LOW): mid-limb square -> stays inside (2^64 * 2^64 = 2^128)
    let mut a = U256([0, 0, 1, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 1, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 1, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 120 (MUL_LOW): exact boundary -> zero low, overflow (2^128 * 2^128 = 2^256)
    let mut a = U256([0, 0, 0, 0, 1, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 1, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 121 (MUL_LOW)
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([5, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0xFFFF_FFFB, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 122 (MUL_LOW): (-1) * (1 + 2^32) => low = - (1+2^32)
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([1, 1, 0, 0, 0, 0, 0, 0]); // 2^32 + 1
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 123 (MUL_LOW): 0x8000_0000 * 3 => low limb set
    let mut a = U256([0x8000_0000, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([3, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0x8000_0000, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 124 (MUL_LOW): (1 + 2^32)^2 = 1 + 2*2^32 + 2^64
    let mut a = U256([1, 1, 0, 0, 0, 0, 0, 0]);
    let b = U256([1, 1, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0x0000_0001, 0x0000_0002, 0x0000_0001, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 125 (MUL_LOW)
    let mut a = U256([0xFFFF_FFFF, 0x0000_0001, 0, 0, 0, 0, 0, 0]);
    let b = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0xFFFF_FFFE, 0x0000_0003, 0x0000_0000, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 126 (MUL_LOW): limb6 * limb1 -> index 7 within low range
    let mut a = U256([0, 0, 0, 0, 0, 0x0000_0001, 0, 0]);
    let b = U256([0, 0x0000_0001, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));

    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0x0000_0001, 0, 0]);

    out = [0; 9];
    // Case 127 (MUL_LOW): limb7 * limb1 -> exact boundary to limb8 => overflow
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0x0000_0001]);
    let b = U256([0, 0x0000_0001, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 128 (MUL_LOW): limb5 * limb2 -> index 7 within low
    let mut a = U256([0, 0, 0, 0, 0, 0x0000_0001, 0, 0]);
    let b = U256([0, 0, 0x0000_0001, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0x0000_0001, 0]);

    out = [0; 9];
    // Case 129 (MUL_LOW): limb5 * limb3 -> index 8 -> overflow only
    let mut a = U256([0, 0, 0, 0, 0, 0x0000_0001, 0, 0]);
    let b = U256([0, 0, 0, 0x0000_0001, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 130 (MUL_LOW): (2^64) * (-1) 
    let mut a = U256([0, 0x0000_0001, 0, 0, 0, 0, 0, 0]); // 2^32
    let b = U256([0xFFFF_FFFF; 8]); // -1 mod 2^256
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0x0000_0000, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 131 (MUL_LOW): high-half squares with high 32-bit carry -> overflow via high half
    let mut a = U256([0, 0, 0, 0x8000_0000, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0x8000_0000, 0, 0, 0]); 
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0x0000_0000, 1]);

    out = [0; 9];
    // Case 132 (MUL_LOW): (0x8000_0001)^2 = 2^62 + 2^32 + 1
    let mut a = U256([0x8000_0001, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0x8000_0001, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0x0000_0001, 0x4000_0001, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 133 (MUL_LOW): 0xFFFF_FFFF * 0x8000_0000 
    let mut a = U256([0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0x8000_0000, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0x8000_0000, 0x7FFF_FFFF, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 134 (MUL_LOW): 2^128 * 2^97 -> lands in limb7 with bit1 set
    let mut a = U256([0, 0, 0, 0, 1, 0, 0, 0]); // 2^128
    let b = U256([0, 0, 0, 2, 0, 0, 0, 0]);     // 2^97
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0x0000_0002, 0]);

    out = [0; 9];
    // Case 135 (MUL_LOW): 2^224 * 2^32 -> exact boundary 2^256 => overflow only
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 1]); // 2^224
    let b = U256([0, 1, 0, 0, 0, 0, 0, 0]);     // 2^32
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 136 (MUL_LOW): two-limb a times 2, partial sums meet in limb1
    let mut a = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0]);
    let b = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 3));
    assert_eq!(out, [0xFFFF_FFFE, 0xFFFF_FFFF, 0x0000_0001, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 137 (MUL_HIGH)
    let mut a = U256([2, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([3, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 138 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 1, 0]);
    let b = U256([0, 0, 1, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [1, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 139 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0]);
    let b = U256([0, 0, 0xFFFF_FFFF, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0x0000_0001, 0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 140 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 1, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0, 0, 0, 0, 1, 0, 0, 0]);

    out = [0; 9];
    // Case 141 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 1, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0, 0, 0, 1, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 142 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 1, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 1, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [1, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 143 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 1, 0]);
    let b = U256([0, 1, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 144 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    let b = U256([0, 0, 1, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 1, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 145 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    let b = U256([0, 0, 0, 0, 0, 0, 1, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0, 0, 0, 0, 1, 0, 0, 0]);

    out = [0; 9];
    // Case 146 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 1, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 1, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [1, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 147 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 1, 0, 0]);

    out = [0; 9];
    // Case 148 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    let b = U256([1, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 149 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0xFFFF_FFFF, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0xFFFF_FFFF, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 150 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    let b = U256([0, 0, 1, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 151 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0x0000_0001]);
    let b = U256([0, 0xFFFF_FFFF, 0x0000_0001, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFC, 0x0000_0003, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 152 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0x0000_0001, 0xFFFF_FFFE, 0]);

    out = [0; 9];
    // Case 153 (MUL_HIGH)
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([0, 1, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 154 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0xFFFF_0000, 0]);
    let b = U256([0, 0, 0xFFFF_0000, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0xFFFE_0001, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 155 (MUL_HIGH)
    let mut a = U256([1, 1, 1, 1, 1, 1, 1, 1]);
    let b = U256([1, 1, 1, 1, 1, 1, 1, 1]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [7, 6, 5, 4, 3, 2, 1, 0, 0]);

    out = [0; 9];
    // Case 156 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 1]);
    let b = U256([0, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 157 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF]);
    let b = U256([0, 2, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFE, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 158 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0x8000_0000, 0, 0]);
    let b = U256([0, 0, 0, 0x8000_0000, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0x4000_0000, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 159 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF]);
    let b = U256([0, 0x0000_0001, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 160 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF]);
    let b = U256([0, 0x0000_0002, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFE, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 161 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0x8000_0000]);
    let b = U256([0, 0x8000_0000, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0x0000_0000, 0x4000_0000, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 162 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0]);
    let b = U256([0, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 163 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0xFFFF_FFFF, 0xFFFF_FFFF, 0]);
    let b = U256([0, 0xFFFF_FFFF, 0xFFFF_FFFF, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFE, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 164 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0x0000_0001]);
    let b = U256([0, 0xFFFF_FFFF, 0x0000_0001, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFC, 0x0000_0003, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 165 (MUL_HIGH)
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([0, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 166 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0xFFFF_0000, 0]);
    let b = U256([0, 0, 0xFFFF_0000, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0x0000_0000, 0xFFFE_0001, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 167 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0x0001_0000]);
    let b = U256([0, 0x0001_0000, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0x0000_0000, 0x0000_0001, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 168 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0x0000_0001, 0xFFFF_FFFE, 0]);

    out = [0; 9];
    // Case 169 (MUL_HIGH)
    let mut a = U256([
    0xFFFF_0001, 0x0000_FFFF, 0x8000_0000, 0x7FFF_FFFF,
    0xAAAA_AAAA, 0x5555_5555, 0xDEAD_BEEF, 0xFFFF_FFFF
    ]);
    let b = U256([0, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xDEAD_BEEF, 0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 170 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0xFFFF_FFFF]);
    let b = U256([0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0xFFFF_FFFF]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0, 0, 0, 0x0000_0001, 0, 0xFFFF_FFFE, 0xFFFF_FFFF, 0]);

    out = [0; 9];
    // Case 171 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0x0000_0001]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0, 0]);

    out = [0; 9];
    // Case 172 (MUL_HIGH)
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0x8000_0001]);
    let b = U256([0, 0xFFFF_FFFE, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));   
    assert_eq!(out, [0xFFFF_FFFE, 0x7FFF_FFFF, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 173 (MUL_HIGH): ALL×ALL  =>  (2^256-1)^2 = 2^512 - 2^257 + 1
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([0xFFFF_FFFF; 8]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFE, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0]);

    out = [0; 9];
    // Case 174 (MUL_HIGH)
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b     = U256([0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 175 (MUL_HIGH)
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b     = U256([0, 0xFFFF_FFFF, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFE, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 176 (MUL_HIGH)
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b     = U256([0, 0, 0, 0, 0xFFFF_FFFF, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 177 (MUL_HIGH)
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b     = U256([0, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF]);
    run_case(&mut a, &b, &mut out, (1 << 4));
    assert_eq!(out, [ 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFE, 0]);

    out = [0; 9];
    // Case 178 (EQ): zeros equal -> unchanged a, flag=1
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 5));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 179 (EQ): mixed equal pattern -> unchanged a, flag=1
    let mut a = U256([0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6]);
    let b = U256([0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6]);
    run_case(&mut a, &b, &mut out, (1 << 5));
    assert_eq!(out, [0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6, 1]);

    out = [0; 9];
    // Case 180 (EQ): differ in one limb -> unchanged a, flag=0
    let mut a = U256([0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6]);
    let b = U256([0x1234_5678, 0x9ABC_DEF0, 1, 3, 3, 4, 5, 6]);
    run_case(&mut a, &b, &mut out, (1 << 5));
    assert_eq!(out, [0x1234_5678, 0x9ABC_DEF0, 1, 2, 3, 4, 5, 6, 0]);

    out = [0; 9];
    // Case 181 (EQ): all-ones equal -> unchanged a, flag=1
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([0xFFFF_FFFF; 8]);
    run_case(&mut a, &b, &mut out, (1 << 5));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 1]);

    out = [0; 9];
    // Case 182 (EQ): max vs zero -> unchanged a (max), flag=0
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 5));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0]);

    out = [0; 9];
    // Case 183 (EQ + CARRY): equal with carry bit set -> carry ignored, flag=1
    let mut a = U256([1, 2, 3, 4, 5, 6, 7, 8]);
    let b = U256([1, 2, 3, 4, 5, 6, 7, 8]);
    run_case(&mut a, &b, &mut out, ((1 << 5) | (1 << 6)));
    assert_eq!(out, [1, 2, 3, 4, 5, 6, 7, 8, 1]);

    out = [0; 9];
    // Case 184 (EQ + CARRY): not equal with carry bit set -> carry ignored, flag=0
    let mut a = U256([1, 2, 3, 4, 5, 6, 7, 8]);
    let b = U256([1, 2, 3, 4, 5, 6, 7, 9]);
    run_case(&mut a, &b, &mut out, ((1 << 5) | (1 << 6)));
    assert_eq!(out, [1, 2, 3, 4, 5, 6, 7, 8, 0]);

    out = [0; 9];
    // Case 185 (EQ): differ only at top limb -> unchanged a, flag=0
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0x8000_0000]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0x8000_0001]);
    run_case(&mut a, &b, &mut out, (1 << 5));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0x8000_0000, 0]);

    out = [0; 9];
    // Case 186 (EQ): equal sparse highs -> unchanged a, flag=1
    let mut a = U256([0, 0, 0, 0x0000_0001, 0, 0x8000_0000, 0, 0]);
    let b = U256([0, 0, 0, 0x0000_0001, 0, 0x8000_0000, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 5));
    assert_eq!(out, [0, 0, 0, 0x0000_0001, 0, 0x8000_0000, 0, 0, 1]);

    out = [0; 9];
    // Case 187 (MEMCOPY): basic copy, carry=0 -> out = b, flag=0
    let mut a = U256([0xAAAA_AAAA, 0xBBBB_BBBB, 0xCCCC_CCCC, 0xDDDD_DDDD, 1, 2, 3, 4]);
    let b = U256([0x1111_1111, 0x2222_2222, 0x3333_3333, 0x4444_4444, 5, 6, 7, 8]);
    run_case(&mut a, &b, &mut out, (1 << 7));
    assert_eq!(out, [0x1111_1111, 0x2222_2222, 0x3333_3333, 0x4444_4444, 5, 6, 7, 8, 0]);

    out = [0; 9];
    // Case 188 (MEMCOPY + CARRY): adds 1 to b before copy -> out = b+1, flag=overflow from increment
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, ((1 << 7) | (1 << 6)));
    assert_eq!(out, [0, 1, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 189 (MEMCOPY + CARRY): carry ripples across many limbs
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0xFFFF_FFFF, 0xFFFF_FFFF, 0x0000_0000, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, ((1 << 7) | (1 << 6)));
    assert_eq!(out, [0, 0, 1, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 190 (MEMCOPY + CARRY): full overflow when b = all-ones -> wraps to zero, flag=1
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0xFFFF_FFFF; 8]);
    run_case(&mut a, &b, &mut out, ((1 << 7) | (1 << 6)));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    out = [0; 9];
    // Case 191 (MEMCOPY): copy zeros -> zeros, flag=0
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, (1 << 7));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 192 (MEMCOPY): copy max -> max, flag=0
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0xFFFF_FFFF; 8]);
    run_case(&mut a, &b, &mut out, (1 << 7));
    assert_eq!(out, [0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0xFFFF_FFFF, 0]);

    out = [0; 9];
    // Case 193 (MEMCOPY + CARRY): increment mixed b, no ripple
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([5, 0x1234_5678, 0, 0, 0, 0, 0, 0]);
    run_case(&mut a, &b, &mut out, ((1 << 7) | (1 << 6)));
    assert_eq!(out, [6, 0x1234_5678, 0, 0, 0, 0, 0, 0, 0]);

    out = [0; 9];
    // Case 194 (MEMCOPY + CARRY): increment with ripple into top limb only
    let mut a = U256([0, 0, 0, 0, 0, 0, 0, 0]);
    let b = U256([0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0xFFFF_FFFF]);
    run_case(&mut a, &b, &mut out, ((1 << 7) | (1 << 6)));
    assert_eq!(out, [0, 1, 0, 0, 0, 0, 0, 0xFFFF_FFFF, 0]);

    out = [0; 9];
    // Case 195 (MEMCOPY): ensure a is untouched (copy reads from b)
    let mut a = U256([0xDEAD_BEEF, 2, 3, 4, 5, 6, 7, 8]);
    let b = U256([9, 8, 7, 6, 5, 4, 3, 2]);
    run_case(&mut a, &b, &mut out, (1 << 7));
    assert_eq!(out, [9, 8, 7, 6, 5, 4, 3, 2, 0]);

    out = [0; 9];
    // Case 196 (MEMCOPY + CARRY): all-ones wrap to zero, flag=1
    let mut a = U256([0xFFFF_FFFF; 8]);
    let b = U256([0xFFFF_FFFF; 8]);
    run_case(&mut a, &b, &mut out, ((1 << 7) | (1 << 6)));
    assert_eq!(out, [0, 0, 0, 0, 0, 0, 0, 0, 1]);

    zksync_os_finish_success(&[0, 0, 0, 0, 0, 0, 0, 0]);
}

#[inline(never)]
fn main() -> ! {
    riscv_common::boot_sequence::init();
    unsafe { workload() }
}
