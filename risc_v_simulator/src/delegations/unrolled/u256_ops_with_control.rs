use super::*;
use crate::cycle::state::NON_DETERMINISM_CSR;
use crate::cycle::state_new::RiscV32StateForUnrolledProver;
use cs::definitions::{TimestampData, TimestampScalar};
use ruint::aliases::{U256, U512};

pub const U256_OPS_WITH_CONTROL_ACCESS_ID: u32 = NON_DETERMINISM_CSR + 10;
const TOTAL_RAM_ACCESSES: usize = 8 * 2;
const BASE_ABI_REGISTER: u32 = 10;

pub const NUM_CONTROL_BITS: usize = 8;
pub const ADD_OP_BIT_IDX: usize = 0;
pub const SUB_OP_BIT_IDX: usize = 1;
pub const SUB_AND_NEGATE_OP_BIT_IDX: usize = 2;
pub const MUL_LOW_OP_BIT_IDX: usize = 3;
pub const MUL_HIGH_OP_BIT_IDX: usize = 4;
pub const EQ_OP_BIT_IDX: usize = 5;
pub const CARRY_BIT_IDX: usize = 6;
pub const MEMCOPY_BIT_IDX: usize = 7;

pub fn u256_ops_with_control_impl_over_unrolled_state<
    M: MemorySource,
    TR: Tracer<C>,
    C: MachineConfig,
>(
    machine_state: &mut RiscV32StateForUnrolledProver<C>,
    memory_source: &mut M,
    tracer: &mut TR,
) {
    // read registers first
    let x10 = machine_state.registers[10];
    let x11 = machine_state.registers[11];
    let x12 = machine_state.registers[12];

    assert!(x10 % 32 == 0, "input pointer is unaligned");
    assert!(x11 % 32 == 0, "input pointer is unaligned");

    // self-check so that we do not touch ROM
    assert!(x10 >= 1 << 21);
    assert!(x11 >= 1 << 21);

    assert!(x10 != x11);

    let mut a_accesses: [RegisterOrIndirectReadWriteData; 8] =
        register_indirect_read_write_continuous_noexcept::<_, 8>(x10 as usize, memory_source);
    let a_read_addresses: [u32; 8] =
        std::array::from_fn(|i| x10 + (core::mem::size_of::<u32>() * i) as u32);
    let mut b_accesses: [RegisterOrIndirectReadData; 8] =
        register_indirect_read_continuous_noexcept::<_, 8>(x11 as usize, memory_source);
    let b_read_addresses: [u32; 8] =
        std::array::from_fn(|i| x11 + (core::mem::size_of::<u32>() * i) as u32);

    fn make_u256_from_readonly(words: &[RegisterOrIndirectReadData; 8]) -> U256 {
        unsafe {
            let mut result = U256::ZERO;
            for (dst, [l, h]) in result
                .as_limbs_mut()
                .iter_mut()
                .zip(words.array_chunks::<2>())
            {
                *dst = ((h.read_value as u64) << 32) | (l.read_value as u64);
            }

            result
        }
    }

    fn make_u256_from_rw(words: &[RegisterOrIndirectReadWriteData; 8]) -> U256 {
        unsafe {
            let mut result = U256::ZERO;
            for (dst, [l, h]) in result
                .as_limbs_mut()
                .iter_mut()
                .zip(words.array_chunks::<2>())
            {
                *dst = ((h.read_value as u64) << 32) | (l.read_value as u64);
            }

            result
        }
    }

    let a = make_u256_from_rw(&a_accesses);
    let b = make_u256_from_readonly(&b_accesses);

    let result;
    let control_mask = x12;
    assert!(
        control_mask < (1 << NUM_CONTROL_BITS),
        "control bits mask is too large"
    );
    assert_eq!(
        (control_mask & !(1 << CARRY_BIT_IDX)).count_ones(),
        1,
        "at most one control bit must be set, except carry flag"
    );
    let carry_bit = control_mask & (1 << CARRY_BIT_IDX) != 0;
    let carry_or_borrow = U256::from(carry_bit as u64);

    let of = if control_mask & (1 << ADD_OP_BIT_IDX) != 0 {
        let (t, of0) = a.overflowing_add(b);
        let (t, of1) = t.overflowing_add(carry_or_borrow);
        result = t;

        of0 || of1
    } else if control_mask & (1 << SUB_OP_BIT_IDX) != 0 {
        let (t, of0) = a.overflowing_sub(b);
        let (t, of1) = t.overflowing_sub(carry_or_borrow);
        result = t;

        of0 || of1
    } else if control_mask & (1 << SUB_AND_NEGATE_OP_BIT_IDX) != 0 {
        let (t, of0) = b.overflowing_sub(a);
        let (t, of1) = t.overflowing_sub(carry_or_borrow);
        result = t;

        of0 || of1
    } else if control_mask & (1 << MUL_LOW_OP_BIT_IDX) != 0 {
        let t: U512 = a.widening_mul(b);
        result = U256::from_limbs(t.as_limbs()[..4].try_into().unwrap());

        t.as_limbs()[4..].iter().any(|el| *el != 0)
    } else if control_mask & (1 << MUL_HIGH_OP_BIT_IDX) != 0 {
        let t: U512 = a.widening_mul(b);
        result = U256::from_limbs(t.as_limbs()[4..8].try_into().unwrap());

        false
    } else if control_mask & (1 << EQ_OP_BIT_IDX) != 0 {
        result = a; // unchanged

        a == b
    } else if control_mask & (1 << MEMCOPY_BIT_IDX) != 0 {
        if carry_bit {
            let (t, of) = b.overflowing_add(carry_or_borrow);
            result = t;

            of
        } else {
            result = b;

            false
        }
    } else {
        panic!("unknown op: control mask is 0b{:08b}", control_mask);
    };

    for ([l, h], src) in a_accesses
        .array_chunks_mut::<2>()
        .zip(result.as_limbs().iter())
    {
        l.write_value = *src as u32;
        h.write_value = (*src >> 32) as u32;
    }

    write_indirect_accesses_noexcept::<_, 8>(x10 as usize, &a_accesses, memory_source);

    // update register
    machine_state.registers[12] = of as u32;

    // make witness structures
    let mut register_accesses = [
        RegisterOrIndirectReadWriteData {
            read_value: x10,
            write_value: x10,
            timestamp: TimestampData::EMPTY,
        },
        RegisterOrIndirectReadWriteData {
            read_value: x11,
            write_value: x11,
            timestamp: TimestampData::EMPTY,
        },
        RegisterOrIndirectReadWriteData {
            read_value: x12,
            write_value: of as u32,
            timestamp: TimestampData::EMPTY,
        },
    ];

    tracer.record_delegation(
        U256_OPS_WITH_CONTROL_ACCESS_ID,
        10,
        &mut register_accesses,
        &b_read_addresses,
        &mut b_accesses,
        &a_read_addresses,
        &mut a_accesses,
    );
}
