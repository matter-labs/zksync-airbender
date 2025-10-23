use crate::witness::delegation::keccak_special5::KeccakSpecial5DelegationWitness;

use super::*;
use crate::vm::delegations::keccak_special5::{
    keccak_special5_impl_bump_control, keccak_special5_impl_compute_outputs,
    keccak_special5_impl_decode_control, keccak_special5_impl_extract_indices,
};
use common_constants::*;

#[inline(always)]
fn read_u64_words<R: RAM, const N: usize>(
    addr_base: usize,
    offsets: [usize; N],
    ram: &mut R,
    write_timestamp: TimestampScalar,
    witness: &mut KeccakSpecial5DelegationWitness,
) -> [u64; N] {
    core::array::from_fn(|i| {
        let offset = offsets[i];
        let addr_low = (addr_base + offset * core::mem::size_of::<u64>()) as u32;
        let addr_high =
            (addr_base + offset * core::mem::size_of::<u64>() + core::mem::size_of::<u32>()) as u32;
        let (read_timestamp_low, low) = ram.read_word(addr_low, write_timestamp);
        let (read_timestamp_high, high) = ram.read_word(addr_high, write_timestamp);
        witness.indirect_writes[i * 2].read_value = low;
        witness.indirect_writes[i * 2].timestamp = TimestampData::from_scalar(read_timestamp_low);
        witness.indirect_writes[i * 2 + 1].read_value = high;
        witness.indirect_writes[i * 2 + 1].timestamp =
            TimestampData::from_scalar(read_timestamp_high);
        low as u64 | (high as u64) << 32
    })
}

#[inline(never)]
pub(crate) fn keccak_special5_call<C: Counters, R: RAM>(
    state: &mut State<C>,
    ram: &mut R,
    tracer: &mut impl WitnessTracer,
) {
    let mut witness = KeccakSpecial5DelegationWitness::empty();

    // record timestamp
    let write_timestamp = state.timestamp | 3;
    witness.write_timestamp = write_timestamp;

    // record registers
    let x10 = state.registers[10].value; // will proces later when writing..
    let (x11, x11_read_timestamp) = read_register_with_ts::<C, 3>(state, 11);
    assert!(x11 >= 1 << 21, "state ptr is not in RAM");
    assert!(x10 < 1 << 11, "control info is too big");
    assert!(x11 % 256 == 0, "state ptr is not aligned");
    let control = x10;
    let (precompile, iteration, round) = keccak_special5_impl_decode_control(control);
    let control_next = keccak_special5_impl_bump_control(precompile, iteration, round);
    let mut x10_next = control_next;
    let (_x10_old, x10_write_timestamp) = write_register_with_ts::<C, 3>(state, 10, &mut x10_next); // extremely weird &mut
    witness.reg_accesses[0] = RegisterOrIndirectReadWriteData {
        read_value: x10,
        write_value: x10_next,
        timestamp: TimestampData::from_scalar(x10_write_timestamp),
    };
    witness.reg_accesses[1] = RegisterOrIndirectReadWriteData {
        read_value: x11,
        write_value: x11,
        timestamp: TimestampData::from_scalar(x11_read_timestamp),
    };

    // record indexes
    let state_indexes = keccak_special5_impl_extract_indices(precompile, iteration, round);
    for i in 0..KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS {
        witness.variables_offsets[i] = state_indexes[i] as u16;
    }

    // record reads
    let state_inputs = read_u64_words(
        x11 as usize,
        state_indexes,
        ram,
        write_timestamp,
        &mut witness,
    );

    // get outputs
    let state_outputs =
        keccak_special5_impl_compute_outputs(precompile, iteration, round, state_inputs);

    // record writes
    for i in 0..KECCAK_SPECIAL5_NUM_VARIABLE_OFFSETS {
        let value = state_outputs[i];
        let low = value as u32;
        let high = (value >> 32) as u32;
        witness.indirect_writes[i * 2].write_value = low;
        witness.indirect_writes[i * 2 + 1].write_value = high;
    }

    tracer.write_delegation::<{common_constants::keccak_special5::KECCAK_SPECIAL5_CSR_REGISTER as u16}, _, _, _, _>(witness);

    // KEEP INACTIVE?
    // state.counters.bump_keccak_special5();
}
