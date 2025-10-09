use crate::witness::delegation::bigint::BigintDelegationWitness;

use super::*;
use crate::vm::delegations::bigint::bigint_impl;
use ruint::aliases::U256;

// NOTE: in forward execution we read through x11 and dump witness, and then dump writes via x10,
// so in the function below we will just read via x11 and x10

#[inline(always)]
fn read_u256<R: RAM>(
    offset: u32,
    ram: &mut R,
    timestamp: TimestampScalar,
    witness: &mut [RegisterOrIndirectReadData; 8],
) -> U256 {
    unsafe {
        let mut result = U256::ZERO;
        let mut addr = offset;
        let mut offset = 0;
        for dst in result.as_limbs_mut().iter_mut() {
            let (read_ts, low) = ram.read_word(addr, timestamp);
            witness[offset] = RegisterOrIndirectReadData {
                read_value: low,
                timestamp: TimestampData::from_scalar(read_ts),
            };
            offset += 1;
            addr += core::mem::size_of::<u32>() as u32;

            let (read_ts, high) = ram.read_word(addr, timestamp);
            witness[offset] = RegisterOrIndirectReadData {
                read_value: high,
                timestamp: TimestampData::from_scalar(read_ts),
            };
            addr += core::mem::size_of::<u32>() as u32;
            *dst = ((high as u64) << 32) | (low as u64);
            offset += 1;
        }

        result
    }
}

#[inline(always)]
fn read_u256_for_update<R: RAM>(
    offset: u32,
    ram: &mut R,
    timestamp: TimestampScalar,
    witness: &mut [RegisterOrIndirectReadWriteData; 8],
) -> U256 {
    unsafe {
        let mut result = U256::ZERO;
        let mut addr = offset;
        let mut offset = 0;
        for dst in result.as_limbs_mut().iter_mut() {
            let (read_ts, low) = ram.read_word(addr, timestamp);
            witness[offset].read_value = low;
            witness[offset].timestamp = TimestampData::from_scalar(read_ts);
            offset += 1;
            addr += core::mem::size_of::<u32>() as u32;

            let (read_ts, high) = ram.read_word(addr, timestamp);
            witness[offset].read_value = high;
            witness[offset].timestamp = TimestampData::from_scalar(read_ts);
            addr += core::mem::size_of::<u32>() as u32;
            *dst = ((high as u64) << 32) | (low as u64);
            offset += 1;
        }

        result
    }
}

#[inline(never)]
pub(crate) fn bigint_call<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    tracer: &mut impl WitnessTracer,
) {
    let mut witness = BigintDelegationWitness::empty();
    let write_ts = state.timestamp | 3;
    witness.write_timestamp = write_ts;

    let (x10, x10_ts) = read_register_with_ts::<C, 3>(state, 10);
    let (x11, x11_ts) = read_register_with_ts::<C, 3>(state, 11);
    let x12 = state.registers[12].value;

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

    let b = read_u256(x11, ram, write_ts, &mut witness.indirect_reads);
    let a = read_u256_for_update(x10, ram, write_ts, &mut witness.indirect_writes);

    let (_, of) = bigint_impl(a, b, x12);

    // write back is not needed for RAM, only for register
    let (_old_x12, x12_ts) = write_register_with_ts::<C, 3>(state, 12, &mut (of as u32));
    witness.reg_accesses[2] = RegisterOrIndirectReadWriteData {
        read_value: x12,
        write_value: x12,
        timestamp: TimestampData::from_scalar(x12_ts),
    };

    tracer.write_delegation::<{common_constants::bigint_with_control::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16}, _, _, _, _>(witness);

    // state.counters.bump_bigint();
}
