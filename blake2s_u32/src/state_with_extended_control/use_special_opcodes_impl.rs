use super::*;
use common_constants::mops::MOP_TRI_ADD;

// #[inline(always)]
// fn tri_add(a: u32, b: u32, mut c: u32) -> u32 {
//     unsafe {
//         core::arch::asm!(
//             "mop.rr.{idx} {c}, {a}, {b}",
//             a = in(reg) a,
//             b = in(reg) b,
//             c = inout(reg) c,
//             idx = const MOP_TRI_ADD,
//             options(nomem, nostack, preserves_flags)
//         );
//     }

//     c
// }

// #[inline(always)]
// fn xor_rotate<const AMT: u32>(a: u32, mut b: u32) -> u32 {
//     unsafe {
//         core::arch::asm!(
//             "mop.r.{amt} {rd}, {rs1}",
//             rs1 = in(reg) a,
//             rd = inout(reg) b,
//             amt = const AMT,
//             options(nomem, nostack, preserves_flags)
//         );
//     }

//     b
// }

// #[inline(always)]
// fn spec_g_function(
//     mut a: u32,
//     mut b: u32,
//     mut c: u32,
//     mut d: u32,
//     x: u32,
//     y: u32,
// ) -> (u32, u32, u32, u32) {
//     a = tri_add(a, b, x);
//     d = xor_rotate::<16>(a, d);
//     c = c.wrapping_add(d);
//     b = xor_rotate::<12>(c, b);
//     a = tri_add(a, b, y);
//     d = xor_rotate::<8>(a, d);
//     c = c.wrapping_add(d);
//     b = xor_rotate::<7>(c, b);

//     (a, b, c, d)
// }

#[inline(always)]
fn spec_g_function(
    mut a: u32,
    mut b: u32,
    mut c: u32,
    mut d: u32,
    x: u32,
    y: u32,
) -> (u32, u32, u32, u32) {
    unsafe {
        core::arch::asm!(
            "mop.rr.{idx} {a}, {b}, {x}",
            "mop.r.16 {d}, {a}",
            "add {c}, {c}, {d}",
            "mop.r.12 {b}, {c}",
            "mop.rr.{idx} {a}, {b}, {y}",
            "mop.r.8 {d}, {a}",
            "add {c}, {c}, {d}",
            "mop.r.7 {b}, {c}",
            a = inout(reg) a,
            b = inout(reg) b,
            c = inout(reg) c,
            d = inout(reg) d,
            x = in(reg) x,
            y = in(reg) y,
            idx = const MOP_TRI_ADD,
            options(nomem, nostack, preserves_flags)
        );
    }

    (a, b, c, d)
}

#[inline(always)]
fn first_round_spec_mixing_function(
    state: &[u32; BLAKE2S_STATE_WIDTH_IN_U32_WORDS],
    t: u32,
    finalization: u32,
    message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    sigma: &[usize; 16],
) -> [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] {
    // mix rows and columns
    unsafe {
        let [mut s0, mut s1, mut s2, mut s3, mut s4, mut s5, mut s6, mut s7] = *state;

        let [mut s8, mut s9, mut s10, mut s11, mut s12, mut s13, mut s14, mut s15] = IV;
        s12 ^= t;
        s14 ^= finalization;

        (s0, s4, s8, s12) = spec_g_function(
            s0,
            s4,
            s8,
            s12,
            *message_block.get_unchecked(sigma[0]),
            *message_block.get_unchecked(sigma[1]),
        );
        (s1, s5, s9, s13) = spec_g_function(
            s1,
            s5,
            s9,
            s13,
            *message_block.get_unchecked(sigma[2]),
            *message_block.get_unchecked(sigma[3]),
        );
        (s2, s6, s10, s14) = spec_g_function(
            s2,
            s6,
            s10,
            s14,
            *message_block.get_unchecked(sigma[4]),
            *message_block.get_unchecked(sigma[5]),
        );
        (s3, s7, s11, s15) = spec_g_function(
            s3,
            s7,
            s11,
            s15,
            *message_block.get_unchecked(sigma[6]),
            *message_block.get_unchecked(sigma[7]),
        );

        (s0, s5, s10, s15) = spec_g_function(
            s0,
            s5,
            s10,
            s15,
            *message_block.get_unchecked(sigma[8]),
            *message_block.get_unchecked(sigma[9]),
        );
        (s1, s6, s11, s12) = spec_g_function(
            s1,
            s6,
            s11,
            s12,
            *message_block.get_unchecked(sigma[10]),
            *message_block.get_unchecked(sigma[11]),
        );
        (s2, s7, s8, s13) = spec_g_function(
            s2,
            s7,
            s8,
            s13,
            *message_block.get_unchecked(sigma[12]),
            *message_block.get_unchecked(sigma[13]),
        );
        (s3, s4, s9, s14) = spec_g_function(
            s3,
            s4,
            s9,
            s14,
            *message_block.get_unchecked(sigma[14]),
            *message_block.get_unchecked(sigma[15]),
        );

        [
            s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15,
        ]
    }
}

#[inline(always)]
fn spec_mixing_function(
    state: &mut [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS],
    message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
    sigma: &[usize; 16],
) {
    // mix rows and columns
    unsafe {
        let [mut s0, mut s1, mut s2, mut s3, mut s4, mut s5, mut s6, mut s7, mut s8, mut s9, mut s10, mut s11, mut s12, mut s13, mut s14, mut s15] =
            *state;

        (s0, s4, s8, s12) = spec_g_function(
            s0,
            s4,
            s8,
            s12,
            *message_block.get_unchecked(sigma[0]),
            *message_block.get_unchecked(sigma[1]),
        );
        (s1, s5, s9, s13) = spec_g_function(
            s1,
            s5,
            s9,
            s13,
            *message_block.get_unchecked(sigma[2]),
            *message_block.get_unchecked(sigma[3]),
        );
        (s2, s6, s10, s14) = spec_g_function(
            s2,
            s6,
            s10,
            s14,
            *message_block.get_unchecked(sigma[4]),
            *message_block.get_unchecked(sigma[5]),
        );
        (s3, s7, s11, s15) = spec_g_function(
            s3,
            s7,
            s11,
            s15,
            *message_block.get_unchecked(sigma[6]),
            *message_block.get_unchecked(sigma[7]),
        );

        (s0, s5, s10, s15) = spec_g_function(
            s0,
            s5,
            s10,
            s15,
            *message_block.get_unchecked(sigma[8]),
            *message_block.get_unchecked(sigma[9]),
        );
        (s1, s6, s11, s12) = spec_g_function(
            s1,
            s6,
            s11,
            s12,
            *message_block.get_unchecked(sigma[10]),
            *message_block.get_unchecked(sigma[11]),
        );
        (s2, s7, s8, s13) = spec_g_function(
            s2,
            s7,
            s8,
            s13,
            *message_block.get_unchecked(sigma[12]),
            *message_block.get_unchecked(sigma[13]),
        );
        (s3, s4, s9, s14) = spec_g_function(
            s3,
            s4,
            s9,
            s14,
            *message_block.get_unchecked(sigma[14]),
            *message_block.get_unchecked(sigma[15]),
        );

        *state = [
            s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15,
        ];
    }
}

#[allow(dead_code)]
#[inline(always)]
#[unroll::unroll_for_loops]
fn spec_round_function_reduced_rounds(
    state: &[u32; BLAKE2S_STATE_WIDTH_IN_U32_WORDS],
    t: u32,
    finalization: u32,
    message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
) -> [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] {
    #[cfg(feature = "verifier_stats")]
    common_constants::stats::GKR_VERIFY_STATS.with_borrow_mut(|s| s.blake2s_hashes += 1);

    // first one we make it from state
    let mut ext_state =
        first_round_spec_mixing_function(state, t, finalization, message_block, &SIGMAS[0]);

    // reduced rounds
    for i in 1..7 {
        let sigma = &SIGMAS[i];
        spec_mixing_function(&mut ext_state, message_block, sigma);
    }

    ext_state
}

#[inline(always)]
#[unroll::unroll_for_loops]
fn spec_round_function_full_rounds(
    state: &[u32; BLAKE2S_STATE_WIDTH_IN_U32_WORDS],
    t: u32,
    finalization: u32,
    message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
) -> [u32; BLAKE2S_EXTENDED_STATE_WIDTH_IN_U32_WORDS] {
    #[cfg(feature = "verifier_stats")]
    common_constants::stats::GKR_VERIFY_STATS.with_borrow_mut(|s| s.blake2s_hashes += 1);

    // first one we make it from state
    let mut ext_state =
        first_round_spec_mixing_function(state, t, finalization, message_block, &SIGMAS[0]);

    // full rounds
    for i in 1..10 {
        let sigma = &SIGMAS[i];
        spec_mixing_function(&mut ext_state, message_block, sigma);
    }

    ext_state
}

macro_rules! blake2s_msg_load {
    ([$offset:literal]) => {
        concat!("lw a1, ", $offset, "(a0)\n")
    };
    ($reg:ident) => {
        ""
    };
}

macro_rules! blake2s_msg_reg {
    ([$offset:literal]) => {
        "a1"
    };
    ($reg:ident) => {
        stringify!($reg)
    };
}

#[rustfmt::skip]
macro_rules! blake2s_g {
    ($a:ident, $b:ident, $c:ident, $d:ident; $x:tt, $y:tt) => {
        concat!(
            blake2s_msg_load!($x),
            "mop.rr.{tri_add} ", stringify!($a), ", ", stringify!($b), ", ", blake2s_msg_reg!($x), "\n",
            "mop.r.16 ", stringify!($d), ", ", stringify!($a), "\n",
            "add ", stringify!($c), ", ", stringify!($c), ", ", stringify!($d), "\n",
            "mop.r.12 ", stringify!($b), ", ", stringify!($c), "\n",
            blake2s_msg_load!($y),
            "mop.rr.{tri_add} ", stringify!($a), ", ", stringify!($b), ", ", blake2s_msg_reg!($y), "\n",
            "mop.r.8 ", stringify!($d), ", ", stringify!($a), "\n",
            "add ", stringify!($c), ", ", stringify!($c), ", ", stringify!($d), "\n",
            "mop.r.7 ", stringify!($b), ", ", stringify!($c), "\n",
        )
    };
}

// v0..v15: a2..a7, s2..s11; m4..m15: t0..t6, ra, gp, tp, s0, s1; m0..m3 load from 0..12(a0) into a1
macro_rules! blake2s_reduced_rounds {
    () => {
        concat!(
            blake2s_g!(a2, a6, s4, s8; [0], [4]),
            blake2s_g!(a3, a7, s5, s9; [8], [12]),
            blake2s_g!(a4, s2, s6, s10; t0, t1),
            blake2s_g!(a5, s3, s7, s11; t2, t3),
            blake2s_g!(a2, a7, s6, s11; t4, t5),
            blake2s_g!(a3, s2, s7, s8; t6, ra),
            blake2s_g!(a4, s3, s4, s9; gp, tp),
            blake2s_g!(a5, a6, s5, s10; s0, s1),
            blake2s_g!(a2, a6, s4, s8; s0, t6),
            blake2s_g!(a3, a7, s5, s9; t0, t4),
            blake2s_g!(a4, s2, s6, s10; t5, s1),
            blake2s_g!(a5, s3, s7, s11; tp, t2),
            blake2s_g!(a2, a7, s6, s11; [4], gp),
            blake2s_g!(a3, s2, s7, s8; [0], [8]),
            blake2s_g!(a4, s3, s4, s9; ra, t3),
            blake2s_g!(a5, a6, s5, s10; t1, [12]),
            blake2s_g!(a2, a6, s4, s8; ra, t4),
            blake2s_g!(a3, a7, s5, s9; gp, [0]),
            blake2s_g!(a4, s2, s6, s10; t1, [8]),
            blake2s_g!(a5, s3, s7, s11; s1, tp),
            blake2s_g!(a2, a7, s6, s11; t6, s0),
            blake2s_g!(a3, s2, s7, s8; [12], t2),
            blake2s_g!(a4, s3, s4, s9; t3, [4]),
            blake2s_g!(a5, a6, s5, s10; t5, t0),
            blake2s_g!(a2, a6, s4, s8; t3, t5),
            blake2s_g!(a3, a7, s5, s9; [12], [4]),
            blake2s_g!(a4, s2, s6, s10; tp, gp),
            blake2s_g!(a5, s3, s7, s11; ra, s0),
            blake2s_g!(a2, a7, s6, s11; [8], t2),
            blake2s_g!(a3, s2, s7, s8; t1, t6),
            blake2s_g!(a4, s3, s4, s9; t0, [0]),
            blake2s_g!(a5, a6, s5, s10; s1, t4),
            blake2s_g!(a2, a6, s4, s8; t5, [0]),
            blake2s_g!(a3, a7, s5, s9; t1, t3),
            blake2s_g!(a4, s2, s6, s10; [8], t0),
            blake2s_g!(a5, s3, s7, s11; t6, s1),
            blake2s_g!(a2, a7, s6, s11; s0, [4]),
            blake2s_g!(a3, s2, s7, s8; ra, gp),
            blake2s_g!(a4, s3, s4, s9; t2, t4),
            blake2s_g!(a5, a6, s5, s10; [12], tp),
            blake2s_g!(a2, a6, s4, s8; [8], gp),
            blake2s_g!(a3, a7, s5, s9; t2, t6),
            blake2s_g!(a4, s2, s6, s10; [0], ra),
            blake2s_g!(a5, s3, s7, s11; t4, [12]),
            blake2s_g!(a2, a7, s6, s11; t0, tp),
            blake2s_g!(a3, s2, s7, s8; t3, t1),
            blake2s_g!(a4, s3, s4, s9; s1, s0),
            blake2s_g!(a5, a6, s5, s10; [4], t5),
            blake2s_g!(a2, a6, s4, s8; gp, t1),
            blake2s_g!(a3, a7, s5, s9; [4], s1),
            blake2s_g!(a4, s2, s6, s10; s0, tp),
            blake2s_g!(a5, s3, s7, s11; t0, t6),
            blake2s_g!(a2, a7, s6, s11; [0], t3),
            blake2s_g!(a3, s2, s7, s8; t2, [12]),
            blake2s_g!(a4, s3, s4, s9; t5, [8]),
            blake2s_g!(a5, a6, s5, s10; t4, ra),
        )
    };
}

static BLAKE2S_IV: [u32; 8] = IV;
static BLAKE2S_NODE_EXTENDED_STATE: [u32; 16] =
    crate::state_with_extended_control_flags::COMPRESSION_MODE_EXTENDED_CONFIGURED_IV;

const _: () = assert!(core::mem::offset_of!(Blake2RoundFunctionEvaluator, state) == 0);
const _: () = assert!(core::mem::offset_of!(Blake2RoundFunctionEvaluator, input_buffer) == 64);

// Reduced-round compression of the block at `a0` into the chaining value at `a1`, with `t` in `a2`
// and the finalization mask in `a3`. Preserves only `sp`, `gp`, `tp`, `s0` and `s1`.
core::arch::global_asm!(
    ".pushsection .text.blake2s_u32_reduced_rounds_block,\"ax\",@progbits",
    ".globl blake2s_u32_reduced_rounds_block",
    ".type blake2s_u32_reduced_rounds_block,@function",
    ".p2align 2",
    "blake2s_u32_reduced_rounds_block:",
    ".option push",
    ".option arch, +zimop",
    "addi sp, sp, -32",
    "sw ra, 28(sp)",
    "sw gp, 24(sp)",
    "sw tp, 20(sp)",
    "sw s0, 16(sp)",
    "sw s1, 12(sp)",
    "sw a1, 8(sp)",
    "la t0, {iv}",
    "lw s4, 0(t0)",
    "lw s5, 4(t0)",
    "lw s6, 8(t0)",
    "lw s7, 12(t0)",
    "lw s8, 16(t0)",
    "lw s9, 20(t0)",
    "lw s10, 24(t0)",
    "lw s11, 28(t0)",
    "xor s8, s8, a2",
    "xor s10, s10, a3",
    "lw a2, 0(a1)",
    "lw a3, 4(a1)",
    "lw a4, 8(a1)",
    "lw a5, 12(a1)",
    "lw a6, 16(a1)",
    "lw a7, 20(a1)",
    "lw s2, 24(a1)",
    "lw s3, 28(a1)",
    "lw t0, 16(a0)",
    "lw t1, 20(a0)",
    "lw t2, 24(a0)",
    "lw t3, 28(a0)",
    "lw t4, 32(a0)",
    "lw t5, 36(a0)",
    "lw t6, 40(a0)",
    "lw ra, 44(a0)",
    "lw gp, 48(a0)",
    "lw tp, 52(a0)",
    "lw s0, 56(a0)",
    "lw s1, 60(a0)",
    blake2s_reduced_rounds!(),
    "lw ra, 28(sp)",
    "lw gp, 24(sp)",
    "lw tp, 20(sp)",
    "lw s0, 16(sp)",
    "lw s1, 12(sp)",
    "lw a0, 8(sp)",
    "addi sp, sp, 32",
    "lw t1, 0(a0)",
    "xor a2, a2, s4",
    "xor a2, a2, t1",
    "sw a2, 0(a0)",
    "lw t1, 4(a0)",
    "xor a3, a3, s5",
    "xor a3, a3, t1",
    "sw a3, 4(a0)",
    "lw t1, 8(a0)",
    "xor a4, a4, s6",
    "xor a4, a4, t1",
    "sw a4, 8(a0)",
    "lw t1, 12(a0)",
    "xor a5, a5, s7",
    "xor a5, a5, t1",
    "sw a5, 12(a0)",
    "lw t1, 16(a0)",
    "xor a6, a6, s8",
    "xor a6, a6, t1",
    "sw a6, 16(a0)",
    "lw t1, 20(a0)",
    "xor a7, a7, s9",
    "xor a7, a7, t1",
    "sw a7, 20(a0)",
    "lw t1, 24(a0)",
    "xor s2, s2, s10",
    "xor s2, s2, t1",
    "sw s2, 24(a0)",
    "lw t1, 28(a0)",
    "xor s3, s3, s11",
    "xor s3, s3, t1",
    "sw s3, 28(a0)",
    "ret",
    ".option pop",
    ".size blake2s_u32_reduced_rounds_block, .-blake2s_u32_reduced_rounds_block",
    ".popsection",
    iv = sym BLAKE2S_IV,
    tri_add = const MOP_TRI_ADD,
);

// Reduced-round Merkle node compression of the evaluator at `a0`: the state is the right child
// if `a1` is non-zero, else the left one, and the sibling is in the other half of the input
// buffer. Preserves only `sp`, `gp`, `tp`, `s0` and `s1`.
core::arch::global_asm!(
    ".pushsection .text.blake2s_u32_reduced_rounds_node,\"ax\",@progbits",
    ".globl blake2s_u32_reduced_rounds_node",
    ".type blake2s_u32_reduced_rounds_node,@function",
    ".p2align 2",
    "blake2s_u32_reduced_rounds_node:",
    ".option push",
    ".option arch, +zimop",
    "addi sp, sp, -32",
    "sw ra, 28(sp)",
    "sw gp, 24(sp)",
    "sw tp, 20(sp)",
    "sw s0, 16(sp)",
    "sw s1, 12(sp)",
    "sw a0, 8(sp)",
    "la t0, {node}",
    "lw a2, 0(t0)",
    "lw a3, 4(t0)",
    "lw a4, 8(t0)",
    "lw a5, 12(t0)",
    "lw a6, 16(t0)",
    "lw a7, 20(t0)",
    "lw s2, 24(t0)",
    "lw s3, 28(t0)",
    "lw s4, 32(t0)",
    "lw s5, 36(t0)",
    "lw s6, 40(t0)",
    "lw s7, 44(t0)",
    "lw s8, 48(t0)",
    "lw s9, 52(t0)",
    "lw s10, 56(t0)",
    "lw s11, 60(t0)",
    "bnez a1, 1f",
    "lw t0, 16(a0)",
    "lw t1, 20(a0)",
    "lw t2, 24(a0)",
    "lw t3, 28(a0)",
    "lw t4, 96(a0)",
    "lw t5, 100(a0)",
    "lw t6, 104(a0)",
    "lw ra, 108(a0)",
    "lw gp, 112(a0)",
    "lw tp, 116(a0)",
    "lw s0, 120(a0)",
    "lw s1, 124(a0)",
    "j 2f",
    "1:",
    "addi a0, a0, 64",
    "lw t0, 16(a0)",
    "lw t1, 20(a0)",
    "lw t2, 24(a0)",
    "lw t3, 28(a0)",
    "lw t4, -64(a0)",
    "lw t5, -60(a0)",
    "lw t6, -56(a0)",
    "lw ra, -52(a0)",
    "lw gp, -48(a0)",
    "lw tp, -44(a0)",
    "lw s0, -40(a0)",
    "lw s1, -36(a0)",
    "2:",
    blake2s_reduced_rounds!(),
    "lw ra, 28(sp)",
    "lw gp, 24(sp)",
    "lw tp, 20(sp)",
    "lw s0, 16(sp)",
    "lw s1, 12(sp)",
    "lw a0, 8(sp)",
    "addi sp, sp, 32",
    "la t0, {node}",
    "lw t1, 0(t0)",
    "xor a2, a2, s4",
    "xor a2, a2, t1",
    "sw a2, 0(a0)",
    "lw t1, 4(t0)",
    "xor a3, a3, s5",
    "xor a3, a3, t1",
    "sw a3, 4(a0)",
    "lw t1, 8(t0)",
    "xor a4, a4, s6",
    "xor a4, a4, t1",
    "sw a4, 8(a0)",
    "lw t1, 12(t0)",
    "xor a5, a5, s7",
    "xor a5, a5, t1",
    "sw a5, 12(a0)",
    "lw t1, 16(t0)",
    "xor a6, a6, s8",
    "xor a6, a6, t1",
    "sw a6, 16(a0)",
    "lw t1, 20(t0)",
    "xor a7, a7, s9",
    "xor a7, a7, t1",
    "sw a7, 20(a0)",
    "lw t1, 24(t0)",
    "xor s2, s2, s10",
    "xor s2, s2, t1",
    "sw s2, 24(a0)",
    "lw t1, 28(t0)",
    "xor s3, s3, s11",
    "xor s3, s3, t1",
    "sw s3, 28(a0)",
    "ret",
    ".option pop",
    ".size blake2s_u32_reduced_rounds_node, .-blake2s_u32_reduced_rounds_node",
    ".popsection",
    node = sym BLAKE2S_NODE_EXTENDED_STATE,
    tri_add = const MOP_TRI_ADD,
);

#[inline(always)]
unsafe fn compress_block_reduced_rounds(
    chaining_value: &mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
    block: *const u32,
    t: u32,
    last_round: bool,
) {
    #[cfg(feature = "verifier_stats")]
    common_constants::stats::GKR_VERIFY_STATS.with_borrow_mut(|s| s.blake2s_hashes += 1);

    core::arch::asm!(
        "call blake2s_u32_reduced_rounds_block",
        in("a0") block,
        in("a1") chaining_value.as_mut_ptr(),
        in("a2") t,
        in("a3") 0xffffffff * last_round as u32,
        out("s2") _,
        out("s3") _,
        out("s4") _,
        out("s5") _,
        out("s6") _,
        out("s7") _,
        out("s8") _,
        out("s9") _,
        out("s10") _,
        out("s11") _,
        clobber_abi("C"),
    );
}

impl Blake2RoundFunctionEvaluator {
    pub const SUPPORT_SPEC_SINGLE_ROUND: bool = false;

    /// Same as `run_round_function_with_input::<true>`, but the chaining value is
    /// `chaining_value` instead of `self.state`, which is left untouched. `self.t` counts as usual.
    ///
    /// # Safety
    ///
    /// Same as `run_round_function_with_input`.
    #[inline(always)]
    pub unsafe fn run_round_function_with_input_and_chaining_value(
        &mut self,
        chaining_value: &mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
        input_buffer: &AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>,
        input_size_words: usize,
        last_round: bool,
    ) {
        self.t += (input_size_words * core::mem::size_of::<u32>()) as u32;
        compress_block_reduced_rounds(chaining_value, input_buffer.as_ptr(), self.t, last_round);
    }

    /// # Safety
    ///
    /// Not supported by this implementation (`SUPPORT_SPEC_SINGLE_ROUND` is `false`): it panics.
    #[unroll::unroll_for_loops]
    #[inline(always)]
    pub unsafe fn spec_run_single_round_into_destination<const REDUCED_ROUNDS: bool>(
        &mut self,
        _block_len: usize,
        _dst: *mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
    ) {
        unreachable!("unsupported")
    }

    /// NOTE: caller must explicitly "reset" before using if use mode is not compression
    #[allow(invalid_value)]
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self {
            state: CONFIGURED_IV,
            input_buffer: AlignedArray64::from_value(0u32),
            t: 0,
        }
    }

    #[inline(always)]
    pub fn reset(&mut self) {
        unsafe {
            crate::spec_memcopy_u32_nonoverlapping(
                CONFIGURED_IV.as_ptr().cast::<u32>(),
                self.state.as_mut_ptr().cast::<u32>(),
                8,
            );
        }

        self.t = 0;
    }

    /// caller must fill the buffer (do not forget to zero-pad),
    /// and then specify the parameters of the input block
    ///
    /// # Safety
    ///
    /// `input_buffer` must hold the block, zero-padded past `input_size_words`, and
    /// `input_size_words` must not exceed `BLAKE2S_BLOCK_SIZE_U32_WORDS`.
    #[inline(always)]
    pub unsafe fn run_round_function_with_input<const REDUCED_ROUNDS: bool>(
        &mut self,
        input_buffer: &AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>,
        input_size_words: usize,
        last_round: bool,
    ) {
        self.run_round_function_with_input_and_byte_len::<REDUCED_ROUNDS>(
            input_buffer,
            input_size_words * core::mem::size_of::<u32>(),
            last_round,
        );
    }

    /// # Safety
    ///
    /// `input_buffer` must hold the block, zero-padded past `input_size_bytes`, and
    /// `input_size_bytes` must not exceed `BLAKE2S_BLOCK_SIZE_BYTES`.
    #[inline(always)]
    pub unsafe fn run_round_function_with_input_and_byte_len<const REDUCED_ROUNDS: bool>(
        &mut self,
        input_buffer: &AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>,
        input_size_bytes: usize,
        last_round: bool,
    ) {
        if REDUCED_ROUNDS {
            self.t += input_size_bytes as u32;
            compress_block_reduced_rounds(
                &mut self.state,
                input_buffer.as_ptr(),
                self.t,
                last_round,
            );
        } else {
            self.run_round_function_with_input_and_byte_len_full_rounds(
                input_buffer,
                input_size_bytes,
                last_round,
            );
        }
    }

    #[inline]
    #[unroll::unroll_for_loops]
    unsafe fn run_round_function_with_input_and_byte_len_full_rounds(
        &mut self,
        input_buffer: &AlignedArray64<u32, BLAKE2S_BLOCK_SIZE_U32_WORDS>,
        input_size_bytes: usize,
        last_round: bool,
    ) {
        self.t += input_size_bytes as u32;

        {
            let extended_state = spec_round_function_full_rounds(
                &self.state,
                self.t,
                0xffffffff * last_round as u32,
                input_buffer,
            );

            for i in 0..8 {
                self.state[i] ^= extended_state[i];
                self.state[i] ^= extended_state[i + 8];
            }
        }
    }

    /// # Safety
    ///
    /// `self.input_buffer` must hold the block, zero-padded past `input_size_words`, and
    /// `input_size_words` must not exceed `BLAKE2S_BLOCK_SIZE_U32_WORDS`.
    #[inline(always)]
    pub unsafe fn run_round_function<const REDUCED_ROUNDS: bool>(
        &mut self,
        input_size_words: usize,
        last_round: bool,
    ) {
        self.run_round_function_with_byte_len::<REDUCED_ROUNDS>(
            input_size_words * core::mem::size_of::<u32>(),
            last_round,
        );
    }

    /// # Safety
    ///
    /// `self.input_buffer` must hold the block, zero-padded past `input_size_bytes`, and
    /// `input_size_bytes` must not exceed `BLAKE2S_BLOCK_SIZE_BYTES`.
    #[inline(always)]
    pub unsafe fn run_round_function_with_byte_len<const REDUCED_ROUNDS: bool>(
        &mut self,
        input_size_bytes: usize,
        last_round: bool,
    ) {
        if REDUCED_ROUNDS {
            self.t += input_size_bytes as u32;
            let block = self.input_buffer.as_ptr();
            compress_block_reduced_rounds(&mut self.state, block, self.t, last_round);
        } else {
            self.run_round_function_with_byte_len_full_rounds(input_size_bytes, last_round);
        }
    }

    #[inline]
    #[unroll::unroll_for_loops]
    unsafe fn run_round_function_with_byte_len_full_rounds(
        &mut self,
        input_size_bytes: usize,
        last_round: bool,
    ) {
        self.t += input_size_bytes as u32;

        {
            let extended_state = spec_round_function_full_rounds(
                &self.state,
                self.t,
                0xffffffff * last_round as u32,
                &self.input_buffer,
            );

            for i in 0..8 {
                self.state[i] ^= extended_state[i];
                self.state[i] ^= extended_state[i + 8];
            }
        }
    }

    #[inline(always)]
    pub fn compress_two_to_one<const REDUCED_ROUNDS: bool>(
        _message_block: &[u32; BLAKE2S_BLOCK_SIZE_U32_WORDS],
        _dst: &mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
    ) {
        panic!("Must not be used in conjunction with prover, please check the features across your build chain");
    }

    /// This function will use witness scratch of self as path witness input,
    /// and self-state as the hash input and destination. Trashes the input buffer
    #[inline(always)]
    pub fn compress_node<const REDUCED_ROUNDS: bool>(&mut self, is_right: bool) {
        if REDUCED_ROUNDS {
            #[cfg(feature = "verifier_stats")]
            common_constants::stats::GKR_VERIFY_STATS.with_borrow_mut(|s| s.blake2s_hashes += 1);

            unsafe {
                core::arch::asm!(
                    "call blake2s_u32_reduced_rounds_node",
                    in("a0") self as *mut Self,
                    in("a1") is_right as u32,
                    out("s2") _,
                    out("s3") _,
                    out("s4") _,
                    out("s5") _,
                    out("s6") _,
                    out("s7") _,
                    out("s8") _,
                    out("s9") _,
                    out("s10") _,
                    out("s11") _,
                    clobber_abi("C"),
                );
            }
        } else {
            self.compress_node_full_rounds(is_right);
        }
    }

    #[unroll::unroll_for_loops]
    fn compress_node_full_rounds(&mut self, is_right: bool) {
        {
            // Caller has written path witness into get_merkle_path_proof_buffer(is_right).
            // We copy self.state into the other half.
            if is_right {
                self.input_buffer[8..16].copy_from_slice(&self.state);
            } else {
                self.input_buffer[0..8].copy_from_slice(&self.state);
            }

            let extended_state = spec_round_function_full_rounds(
                &CONFIGURED_IV,
                BLAKE2S_BLOCK_SIZE_BYTES as u32,
                0xffffffff,
                &self.input_buffer,
            );

            for i in 0..8 {
                self.state[i] = CONFIGURED_IV[i] ^ extended_state[i] ^ extended_state[i + 8];
            }
        }
    }

    // if "is right" then the hash contained in the state is "right node"
    #[inline(always)]
    pub fn get_merkle_path_proof_buffer(
        &mut self,
        is_right: bool,
    ) -> &mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] {
        // we use proper "half" of the internal input buffer and only copy over the state to the "other one"
        unsafe {
            let (l, r) = self.input_buffer.split_at_mut_unchecked(8);
            let l: &mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] = l.as_mut_array().unwrap_unchecked();
            let r: &mut [u32; BLAKE2S_DIGEST_SIZE_U32_WORDS] = r.as_mut_array().unwrap_unchecked();
            if is_right {
                l
            } else {
                r
            }
        }
    }
}
