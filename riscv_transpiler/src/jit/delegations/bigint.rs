use super::*;
use crate::vm::delegations::bigint::*;
use common_constants::*;
use ruint::aliases::U256;
use std::mem::MaybeUninit;

pub fn bigint_implementation(
    trace_piece: &mut TraceChunk,
    memory_holder: &mut MemoryHolder,
    machine_state: &mut MachineState,
) -> u64 {
    // Implementer here is responsible for ALL the bookkeeping, and eventually MUST update trace piece chunk via context, and and update machine state to reflect filled part of trace chunk
    assert!((trace_piece.len as usize) < TRACE_CHUNK_LEN);
    debug_assert_eq!(machine_state.timestamp % 4, 3);
    let a_ptr = machine_state.registers[10];
    let b_ptr = machine_state.registers[11];
    let x12 = machine_state.registers[12];
    assert!(a_ptr as usize >= common_constants::rom::ROM_BYTE_SIZE);
    assert!(b_ptr as usize >= common_constants::rom::ROM_BYTE_SIZE);
    assert_eq!(a_ptr % 32, 0, "`a` pointer is unaligned");
    assert_eq!(b_ptr % 32, 0, "`b` pointer is unaligned");

    assert!(a_ptr != b_ptr);

    let write_ts = machine_state.timestamp;

    machine_state.register_timestamps[10] = write_ts;
    machine_state.register_timestamps[11] = write_ts;
    machine_state.register_timestamps[12] = write_ts;

    // read and save into snapshots

    // NOTE: read `b`` first, then `a` for snapshotting purposes

    let b = unsafe {
        let offset = (b_ptr as usize) / core::mem::size_of::<u32>();
        let integer = memory_holder
            .memory
            .as_ptr()
            .add(offset)
            .cast::<U256>()
            .as_ref_unchecked();
        let timestamps = memory_holder
            .timestamps
            .as_mut_ptr()
            .add(offset)
            .cast::<[TimestampScalar; 8]>()
            .as_mut_unchecked();

        for i in 0..4 {
            let limb = integer.as_limbs()[i];
            let low = limb as u32;
            let high = (limb >> 32) as u32;
            trace_piece.add_element(low, timestamps[2 * i]);
            timestamps[2 * i] = write_ts;
            trace_piece.add_element(high, timestamps[2 * i + 1]);
            timestamps[2 * i + 1] = write_ts;
        }

        integer
    };

    let a = unsafe {
        let offset = (a_ptr as usize) / core::mem::size_of::<u32>();
        let integer = memory_holder
            .memory
            .as_mut_ptr()
            .add(offset)
            .cast::<U256>()
            .as_mut_unchecked();
        let timestamps = memory_holder
            .timestamps
            .as_mut_ptr()
            .add(offset)
            .cast::<[TimestampScalar; 8]>()
            .as_mut_unchecked();

        for i in 0..4 {
            let limb = integer.as_limbs()[i];
            let low = limb as u32;
            let high = (limb >> 32) as u32;
            trace_piece.add_element(low, timestamps[2 * i]);
            timestamps[2 * i] = write_ts;
            trace_piece.add_element(high, timestamps[2 * i + 1]);
            timestamps[2 * i + 1] = write_ts;
        }

        integer
    };

    let (result, of) = bigint_impl(*a, *b, x12);
    trace_piece.append_arbitrary_value(of as u32);

    // write back the value
    *a = result;

    machine_state.registers[12] = of as u32;

    assert!((trace_piece.len as usize) < MAX_TRACE_CHUNK_LEN);
    let should_flush = ((trace_piece.len as usize) >= TRACE_CHUNK_LEN) as u64;

    // println!("Bigint, should flush = {}", should_flush);

    should_flush
}
