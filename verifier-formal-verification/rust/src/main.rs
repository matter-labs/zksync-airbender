//! PoC guest program in the style of zksync-airbender/examples/basic_fibonacci.
#![no_std]
#![no_main]

core::arch::global_asm!(include_str!("start.S"));

/// PoC input convention (Airbender reads input via CSR 0x7c0; we start without CSRs):
/// the input word is placed at the start of the .bss region (first RAM page after the stack).
#[unsafe(no_mangle)]
static mut INPUT: u32 = 0;

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn inc(x: u32) -> u32 {
    x.wrapping_add(1)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn double(x: u32) -> u32 {
    x.wrapping_mul(2)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn combine(x: u32) -> u32 {
    inc(x).wrapping_add(double(x))
}

/// Mersenne31 field arithmetic, as in zksync-airbender `field/src/ops.rs` (generic, non-`use_division` kernels).
/// Elements are u32 in 0..=P (P itself is a second representation of 0).
const P: u32 = (1 << 31) - 1;

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn add_mod(a: u32, b: u32) -> u32 {
    let mut sum = a.wrapping_add(b);
    let msb = sum & (1 << 31);
    sum ^= msb;
    sum += (msb != 0) as u32;
    sum
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn mul_mod(a: u32, b: u32) -> u32 {
    let product = (a as u64) * (b as u64);
    let product_low = (product as u32) & P;
    let product_high = (product >> 31) as u32;
    add_mod(product_low, product_high)
}

/// Horner: ((c[n-1] x + c[n-2]) x + ...) x + c[0].
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn poly_eval(coeffs: *const u32, n: u32, x: u32) -> u32 {
    let mut acc = 0u32;
    let mut i = n;
    while i != 0 {
        i -= 1;
        acc = add_mod(mul_mod(acc, x), unsafe { coeffs.add(i as usize).read() });
    }
    acc
}

const N: usize = 100;

/// Fixed coefficients (in ROM): c_i = 31 i^2 + 7.
static COEFFS: [u32; N] = {
    let mut c = [0u32; N];
    let mut i = 0;
    while i < N {
        c[i] = 31 * (i as u32) * (i as u32) + 7;
        i += 1;
    }
    c
};

/// Like riscv_common::zksync_os_finish_success: results in x10, x11, then spin forever at `_halt` (start.S).
fn finish(r0: u32, r1: u32) -> ! {
    unsafe { core::arch::asm!("j _halt", in("x10") r0, in("x11") r1, options(noreturn)) }
}

#[unsafe(link_section = ".init.rust")]
#[unsafe(export_name = "_start_rust")]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

#[inline(never)]
fn main() -> ! {
    let x = unsafe { core::ptr::read_volatile(&raw const INPUT) };
    let c = combine(x);
    let p = poly_eval(COEFFS.as_ptr(), N as u32, x);
    finish(c, p)
}

/// Like riscv_common's rust_abort: `unimp` (= csrrw x0, cycle, x0), which Airbender treats as failure.
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    unsafe { core::arch::asm!("unimp", options(noreturn)) }
}
