use super::*;
use common_constants::*;
use ruint::aliases::U256;
use ruint::aliases::U512;

#[inline(always)]
fn peek_read_u256<R: RAM>(offset: u32, ram: &R) -> U256 {
    unsafe {
        let mut result = U256::ZERO;
        let mut addr = offset;
        for dst in result.as_limbs_mut().iter_mut() {
            let low = ram.peek_word(addr);
            addr += core::mem::size_of::<u32>() as u32;
            let high = ram.peek_word(addr);
            addr += core::mem::size_of::<u32>() as u32;
            *dst = ((high as u64) << 32) | (low as u64);
        }

        result
    }
}

#[inline(always)]
fn read_u256<C: Counters, S: Snapshotter<C>, R: RAM>(
    offset: u32,
    ram: &mut R,
    snapshotter: &mut S,
    timestamp: TimestampScalar,
) -> U256 {
    unsafe {
        let mut result = U256::ZERO;
        let mut addr = offset;
        for dst in result.as_limbs_mut().iter_mut() {
            let (read_ts, low) = ram.read_word(addr, timestamp);
            snapshotter.append_memory_read(addr, low, read_ts, timestamp);
            addr += core::mem::size_of::<u32>() as u32;
            let (read_ts, high) = ram.read_word(addr, timestamp);
            snapshotter.append_memory_read(addr, high, read_ts, timestamp);
            addr += core::mem::size_of::<u32>() as u32;
            *dst = ((high as u64) << 32) | (low as u64);
        }

        result
    }
}

#[inline(always)]
fn write_back_u256<C: Counters, S: Snapshotter<C>, R: RAM>(
    offset: u32,
    ram: &mut R,
    snapshotter: &mut S,
    timestamp: TimestampScalar,
    value: &U256,
) {
    let mut addr = offset;
    for src in value.as_limbs().iter() {
        let new_low = *src as u32;
        let (read_ts, low) = ram.write_word(addr, new_low, timestamp);
        snapshotter.append_memory_read(addr, low, read_ts, timestamp);
        addr += core::mem::size_of::<u32>() as u32;
        let new_high = (*src >> 32) as u32;
        let (read_ts, high) = ram.write_word(addr, new_high, timestamp);
        snapshotter.append_memory_read(addr, high, read_ts, timestamp);
        addr += core::mem::size_of::<u32>() as u32;
    }
}

#[inline(never)]
pub(crate) fn bigint_call<C: Counters, S: Snapshotter<C>, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    snapshotter: &mut S,
) {
    let x10 = read_register::<C, 3>(state, 10);
    let x11 = read_register::<C, 3>(state, 11);
    let x12 = state.registers[12].value;

    assert!(x10 >= 1 << 21);
    assert!(x11 >= 1 << 21);

    assert!(x10 != x11);

    assert!(x10 % 32 == 0, "input pointer is unaligned");
    assert!(x11 % 32 == 0, "input pointer is unaligned");

    let write_ts = state.timestamp | 3;

    let a = peek_read_u256(x10, &*ram);
    let b = read_u256(x11, ram, snapshotter, write_ts);

    let (result, of) = bigint_impl(a, b, x12);

    // write back
    write_register::<C, 3>(state, 12, &mut (of as u32));
    write_back_u256::<C, S, R>(x10, ram, snapshotter, write_ts, &result);

    state.counters.bump_bigint();
}

#[inline(always)]
pub(crate) fn bigint_impl(a: U256, b: U256, x12: u32) -> (U256, bool) {
    let mut result;
    let control_mask = x12;
    assert!(
        control_mask < (1 << BIGINT_NUM_CONTROL_BITS),
        "control bits mask is too large"
    );
    assert_eq!(
        (control_mask & !(1 << CARRY_BIT_IDX)).count_ones(),
        1,
        "at most one control bit must be set, except carry flag"
    );
    let carry_bit = control_mask & (1 << CARRY_BIT_IDX) != 0;
    let carry_or_borrow = carry_bit;

    let of = unsafe {
        use ruint::algorithms::*;

        if control_mask & (1 << ADD_OP_BIT_IDX) != 0 {
            result = a;
            let of = carrying_add_n(result.as_limbs_mut(), b.as_limbs(), carry_or_borrow);

            of
        } else if control_mask & (1 << SUB_OP_BIT_IDX) != 0 {
            result = a;
            let of = borrowing_sub_n(result.as_limbs_mut(), b.as_limbs(), carry_or_borrow);

            of
        } else if control_mask & (1 << SUB_AND_NEGATE_OP_BIT_IDX) != 0 {
            result = b;
            let of = borrowing_sub_n(result.as_limbs_mut(), a.as_limbs(), carry_or_borrow);

            of
        } else if control_mask & (1 << MUL_LOW_OP_BIT_IDX) != 0 {
            let t: U512 = a.widening_mul(b);
            result = U256::from_limbs(t.as_limbs()[..4].try_into().unwrap_unchecked());

            t.as_limbs()[4..].iter().any(|el| *el != 0)
        } else if control_mask & (1 << MUL_HIGH_OP_BIT_IDX) != 0 {
            let t: U512 = a.widening_mul(b);
            result = U256::from_limbs(t.as_limbs()[4..8].try_into().unwrap_unchecked());

            false
        } else if control_mask & (1 << EQ_OP_BIT_IDX) != 0 {
            result = a; // unchanged

            a == b
        } else if control_mask & (1 << MEMCOPY_BIT_IDX) != 0 {
            if carry_bit {
                result = b;
                let mut of = carry_or_borrow;
                for dst in result.as_limbs_mut().iter_mut() {
                    let (t, new_of) = dst.overflowing_add(of as u64);
                    of = new_of;
                    *dst = t;
                }

                of
            } else {
                result = b;

                false
            }
        } else {
            panic!("unknown op: control mask is 0b{:08b}", control_mask);
        }
    };

    (result, of)
}
