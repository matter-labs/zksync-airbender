#![no_std]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(generic_const_exprs)]
#![no_main]
#![no_builtins]

use core::arch::asm;

use riscv_common::{csr_read_word, zksync_os_finish_success};

extern "C" {
    static mut _sheap: usize;
    static mut _eheap: usize;
    static mut _sstack: usize;
    static mut _estack: usize;
}

core::arch::global_asm!(include_str!("../../scripts/asm/asm_reduced.S"));

#[no_mangle]
extern "C" fn eh_personality() {}

#[link_section = ".init.rust"]
#[export_name = "_start_rust"]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

#[export_name = "_setup_interrupts"]
pub unsafe fn custom_setup_interrupts() {
    extern "C" {
        fn _machine_start_trap();
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct MachineTrapFrame {
    pub registers: [u32; 32],
}

#[link_section = ".trap.rust"]
#[export_name = "_machine_start_trap_rust"]
pub extern "C" fn machine_start_trap_rust(_trap_frame: *mut MachineTrapFrame) -> usize {
    unsafe { core::hint::unreachable_unchecked() }
}

const MAGIC: u32 = 0x4f50_434b;
const CSRRW_INPUT: u32 = 0x1234_5678;
const FNV_OFFSET_BASIS: u32 = 0x811c_9dc5;
const FNV_PRIME: u32 = 0x0100_0193;

#[inline(always)]
fn mix_signature(signature: &mut u32, observed: u32) {
    *signature = signature.wrapping_mul(FNV_PRIME) ^ observed;
}

#[inline(always)]
fn record_check(failures: &mut u64, bit: u32, signature: &mut u32, observed: u32, expected: u32) {
    mix_signature(signature, observed);
    if observed != expected {
        *failures |= 1u64 << bit;
    }
}

#[inline(never)]
fn test_add() -> u32 {
    let out;
    unsafe {
        asm!(
            "add {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) 10u32,
            rhs = in(reg) 20u32,
        );
    }
    out
}

#[inline(never)]
fn test_sub() -> u32 {
    let out;
    unsafe {
        asm!(
            "sub {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) 50u32,
            rhs = in(reg) 20u32,
        );
    }
    out
}

#[inline(never)]
fn test_addi() -> u32 {
    let out;
    unsafe {
        asm!(
            "addi {out}, {lhs}, 42",
            out = lateout(reg) out,
            lhs = in(reg) 0u32,
        );
    }
    out
}

#[inline(never)]
fn test_lui() -> u32 {
    let out;
    unsafe {
        asm!("lui {out}, 0x12345", out = lateout(reg) out);
    }
    out
}

#[inline(never)]
fn test_auipc_delta() -> u32 {
    let out;
    unsafe {
        asm!(
            "auipc {upper}, 0x12345",
            "auipc {base}, 0",
            "sub {out}, {upper}, {base}",
            upper = lateout(reg) _,
            base = lateout(reg) _,
            out = lateout(reg) out,
        );
    }
    out
}

#[inline(never)]
fn test_slt() -> u32 {
    let out;
    unsafe {
        asm!(
            "slt {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) (-1i32) as u32,
            rhs = in(reg) 1u32,
        );
    }
    out
}

#[inline(never)]
fn test_sltu() -> u32 {
    let out;
    unsafe {
        asm!(
            "sltu {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) 1u32,
            rhs = in(reg) 2u32,
        );
    }
    out
}

#[inline(never)]
fn test_slti() -> u32 {
    let out;
    unsafe {
        asm!(
            "slti {out}, {lhs}, 5",
            out = lateout(reg) out,
            lhs = in(reg) 3u32,
        );
    }
    out
}

#[inline(never)]
fn test_sltiu() -> u32 {
    let out;
    unsafe {
        asm!(
            "sltiu {out}, {lhs}, 5",
            out = lateout(reg) out,
            lhs = in(reg) 3u32,
        );
    }
    out
}

#[inline(never)]
fn test_beq() -> u32 {
    let out;
    unsafe {
        asm!(
            "beq {lhs}, {rhs}, 2f",
            "li {out}, 0",
            "j 3f",
            "2:",
            "li {out}, 42",
            "3:",
            out = lateout(reg) out,
            lhs = in(reg) 7u32,
            rhs = in(reg) 7u32,
        );
    }
    out
}

#[inline(never)]
fn test_bne() -> u32 {
    let out;
    unsafe {
        asm!(
            "bne {lhs}, {rhs}, 2f",
            "li {out}, 0",
            "j 3f",
            "2:",
            "li {out}, 42",
            "3:",
            out = lateout(reg) out,
            lhs = in(reg) 7u32,
            rhs = in(reg) 5u32,
        );
    }
    out
}

#[inline(never)]
fn test_blt() -> u32 {
    let out;
    unsafe {
        asm!(
            "blt {lhs}, {rhs}, 2f",
            "li {out}, 0",
            "j 3f",
            "2:",
            "li {out}, 42",
            "3:",
            out = lateout(reg) out,
            lhs = in(reg) (-1i32) as u32,
            rhs = in(reg) 1u32,
        );
    }
    out
}

#[inline(never)]
fn test_bge() -> u32 {
    let out;
    unsafe {
        asm!(
            "bge {lhs}, {rhs}, 2f",
            "li {out}, 0",
            "j 3f",
            "2:",
            "li {out}, 42",
            "3:",
            out = lateout(reg) out,
            lhs = in(reg) 7u32,
            rhs = in(reg) 5u32,
        );
    }
    out
}

#[inline(never)]
fn test_bltu() -> u32 {
    let out;
    unsafe {
        asm!(
            "bltu {lhs}, {rhs}, 2f",
            "li {out}, 0",
            "j 3f",
            "2:",
            "li {out}, 42",
            "3:",
            out = lateout(reg) out,
            lhs = in(reg) 5u32,
            rhs = in(reg) 7u32,
        );
    }
    out
}

#[inline(never)]
fn test_bgeu() -> u32 {
    let out;
    unsafe {
        asm!(
            "bgeu {lhs}, {rhs}, 2f",
            "li {out}, 0",
            "j 3f",
            "2:",
            "li {out}, 42",
            "3:",
            out = lateout(reg) out,
            lhs = in(reg) 7u32,
            rhs = in(reg) 5u32,
        );
    }
    out
}

#[inline(never)]
fn test_jal_link_delta() -> u32 {
    let out;
    unsafe {
        asm!(
            "jal {link}, 2f",
            "li {out}, 0",
            "j 3f",
            "2:",
            "auipc {pc}, 0",
            "sub {out}, {pc}, {link}",
            "3:",
            link = lateout(reg) _,
            pc = lateout(reg) _,
            out = lateout(reg) out,
        );
    }
    out
}

#[inline(never)]
fn test_jalr_link_delta() -> u32 {
    let out;
    unsafe {
        asm!(
            "la {target}, 2f",
            "jalr {link}, 0({target})",
            "li {out}, 0",
            "j 3f",
            "2:",
            "auipc {pc}, 0",
            "sub {out}, {pc}, {link}",
            "3:",
            target = lateout(reg) _,
            link = lateout(reg) _,
            pc = lateout(reg) _,
            out = lateout(reg) out,
        );
    }
    out
}

#[inline(never)]
fn test_sll() -> u32 {
    let out;
    unsafe {
        asm!(
            "sll {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) 1u32,
            rhs = in(reg) 4u32,
        );
    }
    out
}

#[inline(never)]
fn test_srl() -> u32 {
    let out;
    unsafe {
        asm!(
            "srl {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) 64u32,
            rhs = in(reg) 4u32,
        );
    }
    out
}

#[inline(never)]
fn test_sra() -> u32 {
    let out;
    unsafe {
        asm!(
            "sra {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) (-16i32) as u32,
            rhs = in(reg) 1u32,
        );
    }
    out
}

#[inline(never)]
fn test_xor() -> u32 {
    let out;
    unsafe {
        asm!(
            "xor {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) 0xffu32,
            rhs = in(reg) 0x0fu32,
        );
    }
    out
}

#[inline(never)]
fn test_and() -> u32 {
    let out;
    unsafe {
        asm!(
            "and {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) 0xf0u32,
            rhs = in(reg) 0x55u32,
        );
    }
    out
}

#[inline(never)]
fn test_or() -> u32 {
    let out;
    unsafe {
        asm!(
            "or {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) 0xf0u32,
            rhs = in(reg) 0x0fu32,
        );
    }
    out
}

#[inline(never)]
fn test_slli() -> u32 {
    let out;
    unsafe {
        asm!(
            "slli {out}, {lhs}, 4",
            out = lateout(reg) out,
            lhs = in(reg) 1u32,
        );
    }
    out
}

#[inline(never)]
fn test_srli() -> u32 {
    let out;
    unsafe {
        asm!(
            "srli {out}, {lhs}, 3",
            out = lateout(reg) out,
            lhs = in(reg) 64u32,
        );
    }
    out
}

#[inline(never)]
fn test_srai() -> u32 {
    let out;
    unsafe {
        asm!(
            "srai {out}, {lhs}, 12",
            out = lateout(reg) out,
            lhs = in(reg) 0xffff_f000u32,
        );
    }
    out
}

#[inline(never)]
fn test_xori() -> u32 {
    let out;
    unsafe {
        asm!(
            "xori {out}, {lhs}, 0x0f",
            out = lateout(reg) out,
            lhs = in(reg) 0xffu32,
        );
    }
    out
}

#[inline(never)]
fn test_andi() -> u32 {
    let out;
    unsafe {
        asm!(
            "andi {out}, {lhs}, 0x0f",
            out = lateout(reg) out,
            lhs = in(reg) 0xf0u32,
        );
    }
    out
}

#[inline(never)]
fn test_ori() -> u32 {
    let out;
    unsafe {
        asm!(
            "ori {out}, {lhs}, 0x0f",
            out = lateout(reg) out,
            lhs = in(reg) 0xf0u32,
        );
    }
    out
}

#[inline(never)]
fn test_csrrw() -> u32 {
    csr_read_word()
}

#[inline(never)]
fn test_mul() -> u32 {
    let out;
    unsafe {
        asm!(
            "mul {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) 6u32,
            rhs = in(reg) 7u32,
        );
    }
    out
}

#[inline(never)]
fn test_mulhu() -> u32 {
    let out;
    unsafe {
        asm!(
            "mulhu {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) 0x4000_0000u32,
            rhs = in(reg) 0x4000_0000u32,
        );
    }
    out
}

#[inline(never)]
fn test_divu() -> u32 {
    let out;
    unsafe {
        asm!(
            "divu {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) 42u32,
            rhs = in(reg) 7u32,
        );
    }
    out
}

#[inline(never)]
fn test_remu() -> u32 {
    let out;
    unsafe {
        asm!(
            "remu {out}, {lhs}, {rhs}",
            out = lateout(reg) out,
            lhs = in(reg) 42u32,
            rhs = in(reg) 5u32,
        );
    }
    out
}

#[inline(never)]
fn test_sw_roundtrip() -> u32 {
    let mut slot = 0u32;
    let ptr = (&mut slot as *mut u32).cast::<u8>();
    let out;
    unsafe {
        asm!(
            "sw {value}, 0({ptr})",
            "lw {out}, 0({ptr})",
            ptr = in(reg) ptr,
            value = in(reg) 42u32,
            out = lateout(reg) out,
        );
    }
    out
}

#[inline(never)]
fn test_lw() -> u32 {
    let mut slot = 1234u32;
    let ptr = (&mut slot as *mut u32).cast::<u8>();
    let out;
    unsafe {
        asm!(
            "lw {out}, 0({ptr})",
            ptr = in(reg) ptr,
            out = lateout(reg) out,
        );
    }
    out
}

#[inline(never)]
fn test_sb_lb_roundtrip() -> u32 {
    let mut slot = [0u8; 4];
    let ptr = slot.as_mut_ptr();
    let out;
    unsafe {
        asm!(
            "sb {value}, 0({ptr})",
            "lb {out}, 0({ptr})",
            ptr = in(reg) ptr,
            value = in(reg) 127u32,
            out = lateout(reg) out,
        );
    }
    out
}

#[inline(never)]
fn test_lb_sign_extend() -> u32 {
    let mut slot = [0xffu8; 4];
    let ptr = slot.as_mut_ptr();
    let out;
    unsafe {
        asm!(
            "lb {out}, 0({ptr})",
            ptr = in(reg) ptr,
            out = lateout(reg) out,
        );
    }
    out
}

#[inline(never)]
fn test_lbu_zero_extend() -> u32 {
    let mut slot = [0xffu8; 4];
    let ptr = slot.as_mut_ptr();
    let out;
    unsafe {
        asm!(
            "lbu {out}, 0({ptr})",
            ptr = in(reg) ptr,
            out = lateout(reg) out,
        );
    }
    out
}

#[inline(never)]
fn test_sh_lh_roundtrip() -> u32 {
    let mut slot = [0u8; 4];
    let ptr = slot.as_mut_ptr();
    let out;
    unsafe {
        asm!(
            "sh {value}, 0({ptr})",
            "lh {out}, 0({ptr})",
            ptr = in(reg) ptr,
            value = in(reg) 1234u32,
            out = lateout(reg) out,
        );
    }
    out
}

#[inline(never)]
fn test_lh_sign_extend() -> u32 {
    let mut slot = [0xffu8, 0xffu8, 0u8, 0u8];
    let ptr = slot.as_mut_ptr();
    let out;
    unsafe {
        asm!(
            "lh {out}, 0({ptr})",
            ptr = in(reg) ptr,
            out = lateout(reg) out,
        );
    }
    out
}

#[inline(never)]
fn test_lhu_zero_extend() -> u32 {
    let mut slot = [0xffu8, 0xffu8, 0u8, 0u8];
    let ptr = slot.as_mut_ptr();
    let out;
    unsafe {
        asm!(
            "lhu {out}, 0({ptr})",
            ptr = in(reg) ptr,
            out = lateout(reg) out,
        );
    }
    out
}

unsafe fn workload() -> ! {
    let mut failures = 0u64;
    let mut signature = FNV_OFFSET_BASIS;
    let mut checks = 0u32;

    macro_rules! check {
        ($observed:expr, $expected:expr) => {{
            let observed = $observed;
            record_check(&mut failures, checks, &mut signature, observed, $expected);
            checks += 1;
            observed
        }};
    }

    check!(test_add(), 30);
    check!(test_sub(), 30);
    check!(test_addi(), 42);
    check!(test_lui(), 0x1234_5000);
    check!(test_auipc_delta(), 0x1234_4ffc);
    check!(test_slt(), 1);
    check!(test_sltu(), 1);
    check!(test_slti(), 1);
    check!(test_sltiu(), 1);
    check!(test_beq(), 42);
    check!(test_bne(), 42);
    check!(test_blt(), 42);
    check!(test_bge(), 42);
    check!(test_bltu(), 42);
    check!(test_bgeu(), 42);
    let jal_delta = check!(test_jal_link_delta(), 8);
    let jalr_delta = check!(test_jalr_link_delta(), 8);
    check!(test_sll(), 16);
    check!(test_srl(), 4);
    check!(test_sra(), 0xffff_fff8);
    check!(test_xor(), 0x0000_00f0);
    check!(test_and(), 0x0000_0050);
    check!(test_or(), 0x0000_00ff);
    check!(test_slli(), 16);
    check!(test_srli(), 8);
    check!(test_srai(), 0xffff_ffff);
    check!(test_xori(), 0x0000_00f0);
    check!(test_andi(), 0x0000_0000);
    check!(test_ori(), 0x0000_00ff);
    let csrrw = check!(test_csrrw(), CSRRW_INPUT);
    check!(test_mul(), 42);
    check!(test_mulhu(), 0x1000_0000);
    check!(test_divu(), 6);
    check!(test_remu(), 2);
    check!(test_sw_roundtrip(), 42);
    check!(test_lw(), 1234);
    check!(test_sb_lb_roundtrip(), 127);
    check!(test_lb_sign_extend(), 0xffff_ffff);
    check!(test_lbu_zero_extend(), 0x0000_00ff);
    check!(test_sh_lh_roundtrip(), 1234);
    check!(test_lh_sign_extend(), 0xffff_ffff);
    check!(test_lhu_zero_extend(), 0x0000_ffff);

    let outputs = [
        MAGIC,
        failures as u32,
        (failures >> 32) as u32,
        checks,
        signature,
        csrrw,
        jal_delta | (jalr_delta << 16),
        0,
    ];

    zksync_os_finish_success(&outputs)
}

#[inline(never)]
fn main() -> ! {
    unsafe { workload() }
}
