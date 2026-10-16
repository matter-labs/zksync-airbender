//! PoC guest program in the style of zksync-airbender/examples/basic_fibonacci.
#![no_std]
#![no_main]

mod bb;

/// The Blake2s evaluator (state, message block, byte counter), zero at start like all RAM.
#[unsafe(no_mangle)]
static mut BLAKE: blake2s_u32::DelegatedBlake2sState = unsafe { core::mem::zeroed() };

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn u32_inc(x: u32) -> u32 {
    x.wrapping_add(1)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn u32_double(x: u32) -> u32 {
    x.wrapping_mul(2)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn u32_combine(x: u32) -> u32 {
    u32_inc(x).wrapping_add(u32_double(x))
}

/// Mersenne31 field arithmetic, as in zksync-airbender `field/src/ops.rs` (generic, non-`use_division` kernels).
/// Elements are u32 in 0..=P (P itself is a second representation of 0).
const P: u32 = (1 << 31) - 1;

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn m31_add(a: u32, b: u32) -> u32 {
    let mut sum = a.wrapping_add(b);
    let msb = sum & (1 << 31);
    sum ^= msb;
    sum += (msb != 0) as u32;
    sum
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn m31_mul(a: u32, b: u32) -> u32 {
    let product = (a as u64) * (b as u64);
    let product_low = (product as u32) & P;
    let product_high = (product >> 31) as u32;
    m31_add(product_low, product_high)
}

/// Horner: ((c[n-1] x + c[n-2]) x + ...) x + c[0].
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn m31_poly_eval(coeffs: *const u32, n: u32, x: u32) -> u32 {
    let mut acc = 0u32;
    let mut i = n;
    while i != 0 {
        i -= 1;
        acc = m31_add(m31_mul(acc, x), unsafe { coeffs.add(i as usize).read() });
    }
    acc
}

const N: usize = 100;

/// Fixed coefficients (.rodata: in ROM, copied to RAM by `init`): c_i = 31 i^2 + 7.
static COEFFS: [u32; N] = {
    let mut c = [0u32; N];
    let mut i = 0;
    while i < N {
        c[i] = 31 * (i as u32) * (i as u32) + 7;
        i += 1;
    }
    c
};

const N4: usize = 32;

/// Fixed Ext4 coefficients (.rodata, Montgomery form): c_i = (i + 1, 2 i + 3, i^2, 7) (canonical limbs).
static COEFFS4: [bb::Ext4; N4] = {
    let z = bb::Ext2 { c0: 0, c1: 0 };
    let mut c = [bb::Ext4 { c0: z, c1: z }; N4];
    let mut i = 0;
    while i < N4 {
        let k = i as u32;
        c[i] = bb::Ext4 {
            c0: bb::Ext2 { c0: bb::new_ct(k + 1), c1: bb::new_ct(2 * k + 3) },
            c1: bb::Ext2 { c0: bb::new_ct(k * k), c1: bb::new_ct(7) },
        };
        i += 1;
    }
    c
};

/// `out = ∑ c_i y^i` over `COEFFS4`, for `y` given by canonical limbs; `out` canonical limbs (the `field` crate's
/// `new` / `to_u32` around Horner).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ext4_poly(out: &mut [u32; 4], y: &[u32; 4]) {
    let yy = bb::Ext4 {
        c0: bb::Ext2 { c0: bb::new(y[0]), c1: bb::new(y[1]) },
        c1: bb::Ext2 { c0: bb::new(y[2]), c1: bb::new(y[3]) },
    };
    let mut e = yy;
    bb::ext4_horner(&mut e, COEFFS4.as_ptr(), N4 as u32, &yy);
    *out = [bb::to_u32(e.c0.c0), bb::to_u32(e.c0.c1), bb::to_u32(e.c1.c0), bb::to_u32(e.c1.c1)];
}

/// A word as a BabyBear element: at most two subtractions of the modulus (`2^32 < 3p`), as `field`'s
/// `from_raw_repr_with_reduction`.
#[inline(always)]
fn reduce(x: u32) -> u32 {
    let c = if x >= bb::ORDER { x - bb::ORDER } else { x };
    if c >= bb::ORDER { c - bb::ORDER } else { c }
}

/// Fiat-Shamir check: the digest in `st` is the transcript seed; the challenge `z` (4 BabyBear limbs) is its first four
/// words, reduced as the field crate's `from_raw_repr_with_reduction`. The prover claims `v = ∑ c_i z^i` (over
/// `COEFFS4`; `v` reduced the same way). A wrong claim ends the run with `zksync_os_finish_error` (unprovable).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn fs_check(st: &blake2s_u32::DelegatedBlake2sState, v: &[u32; 4]) {
    let z = [reduce(st.state[0]), reduce(st.state[1]), reduce(st.state[2]), reduce(st.state[3])];
    let mut ez = [0u32; 4];
    ext4_poly(&mut ez, &z);
    let diff = (ez[0] ^ reduce(v[0])) | (ez[1] ^ reduce(v[1])) | (ez[2] ^ reduce(v[2])) | (ez[3] ^ reduce(v[3]));
    // one value, one branch (`black_box` keeps LLVM from splitting the comparison into four)
    if core::hint::black_box(diff) != 0 {
        riscv_common::zksync_os_finish_error()
    }
}

/// One Blake2s compression with 7 rounds, as the verifier's transcript: `Blake2RoundFunctionEvaluator` (baseline,
/// plain Rust in both images). `len_bytes` more input bytes, `last` marks the final block.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn blake2s_compress(st: &mut blake2s_u32::DelegatedBlake2sState, len_bytes: u32, last: bool) {
    unsafe { st.run_round_function_with_byte_len::<true>(len_bytes as usize, last) }
}

#[unsafe(link_section = ".init.rust")]
#[unsafe(export_name = "_start_rust")]
unsafe extern "C" fn start_rust() -> ! {
    main()
}

#[inline(never)]
fn main() -> ! {
    riscv_common::boot_sequence::init();
    // the input, read from Airbender's non-determinism source (CSR 0x7c0): a Mersenne31 element `x`, then a BabyBear
    // Ext4 element `y` (4 canonical limbs, `field` crate order)
    let input: [u32; 5] = core::array::from_fn(|_| riscv_common::csr_read_word());
    let x = input[0];
    let c = u32_combine(x);
    let p = m31_poly_eval(COEFFS.as_ptr(), N as u32, x);
    let mut e = [0u32; 4];
    ext4_poly(&mut e, &[input[1], input[2], input[3], input[4]]);
    // Blake2s (7 rounds) of the 5 input words: one last block of 20 bytes (the evaluator in .bss: zero at start)
    let st = unsafe { &mut *(&raw mut BLAKE) };
    st.state = blake2s_u32::CONFIGURED_IV;
    st.get_witness_buffer()[..5].copy_from_slice(&input);
    blake2s_compress(st, 20, true);
    // Fiat-Shamir: the prover's claim `v` about the challenge drawn from the digest, from the non-determinism
    // source; `fs_check` fails the run if it is wrong
    let v: [u32; 4] = core::array::from_fn(|_| riscv_common::csr_read_word());
    fs_check(st, &v);
    riscv_common::zksync_os_finish_success(&[c, p, e[0], e[1], e[2], e[3], st.state[0], st.state[1]])
}
