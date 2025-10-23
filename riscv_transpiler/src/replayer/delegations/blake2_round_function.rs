use std::mem::MaybeUninit;

use crate::witness::delegation::blake2_round_function::Blake2sRoundFunctionDelegationWitness;

use super::*;
use crate::vm::delegations::blake2_round_function::blake2_round_function_impl;
use blake2s_u32::*;
use common_constants::*;

// NOTE: in forward execution we read through x11 and dump witness, and then dump writes via x10,
// so in the function below we will just read via x11 and x10

#[inline(always)]
fn read_words<R: RAM, const N: usize>(
    offset: u32,
    ram: &mut R,
    timestamp: TimestampScalar,
    witness: &mut [RegisterOrIndirectReadData; N],
) -> [u32; N] {
    unsafe {
        let mut result = [MaybeUninit::uninit(); N];
        let mut addr = offset;
        for (dst, wit) in result.iter_mut().zip(witness.iter_mut()) {
            let (read_ts, value) = ram.read_word(addr, timestamp);
            wit.read_value = value;
            wit.timestamp = TimestampData::from_scalar(read_ts);
            addr += core::mem::size_of::<u32>() as u32;
            dst.write(value);
        }

        result.map(|el| el.assume_init())
    }
}

#[inline(always)]
fn read_words_for_update<R: RAM, const N: usize>(
    offset: u32,
    ram: &mut R,
    timestamp: TimestampScalar,
    witness: &mut [RegisterOrIndirectReadWriteData; N],
) -> [u32; N] {
    unsafe {
        let mut result = [MaybeUninit::uninit(); N];
        let mut addr = offset;
        for (dst, wit) in result.iter_mut().zip(witness.iter_mut()) {
            let (read_ts, value) = ram.read_word(addr, timestamp);
            wit.read_value = value;
            wit.timestamp = TimestampData::from_scalar(read_ts);
            addr += core::mem::size_of::<u32>() as u32;
            dst.write(value);
        }

        result.map(|el| el.assume_init())
    }
}

#[inline(never)]
pub(crate) fn blake2_round_function_call<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    tracer: &mut impl WitnessTracer,
) {
    let mut witness = Blake2sRoundFunctionDelegationWitness::empty();
    let write_ts = state.timestamp | 3;
    witness.write_timestamp = write_ts;

    let (x10, x10_ts) = read_register_with_ts::<C, 3>(state, 10);
    let (x11, x11_ts) = read_register_with_ts::<C, 3>(state, 11);
    let (x12, x12_ts) = read_register_with_ts::<C, 3>(state, 12);
    let (x13, x13_ts) = read_register_with_ts::<C, 3>(state, 13);

    witness.reg_accesses[0] = RegisterOrIndirectReadWriteData {
        read_value: x10,
        write_value: x10,
        timestamp: TimestampData::from_scalar(x10_ts),
    };
    witness.reg_accesses[1] = RegisterOrIndirectReadWriteData {
        read_value: x11,
        write_value: x11,
        timestamp: TimestampData::from_scalar(x11_ts),
    };
    witness.reg_accesses[2] = RegisterOrIndirectReadWriteData {
        read_value: x12,
        write_value: x12,
        timestamp: TimestampData::from_scalar(x12_ts),
    };
    witness.reg_accesses[3] = RegisterOrIndirectReadWriteData {
        read_value: x13,
        write_value: x13,
        timestamp: TimestampData::from_scalar(x13_ts),
    };

    let input: [u32; BLAKE2S_BLOCK_SIZE_U32_WORDS] =
        read_words(x11, ram, write_ts, &mut witness.indirect_reads);
    let mut state_accesses: [u32; BLAKE2S_X10_NUM_WRITES] =
        read_words_for_update(x10, ram, write_ts, &mut witness.indirect_writes);

    blake2_round_function_impl(&mut state_accesses, input, x12, x13);

    // write back nothing
    for (dst, src) in witness
        .indirect_writes
        .iter_mut()
        .zip(state_accesses.iter())
    {
        dst.write_value = *src;
    }

    tracer.write_delegation::<{common_constants::blake2s_with_control::BLAKE2S_DELEGATION_CSR_REGISTER as u16}, _, _, _, _>(witness);

    // state.counters.bump_blake2_round_function();
}
