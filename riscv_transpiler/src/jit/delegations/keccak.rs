use super::*;
use crate::vm::delegations::keccak_special5::*;
use common_constants::*;
use std::mem::MaybeUninit;

pub fn keccak_unrolled_implementation(
    trace_piece: &mut TraceChunk,
    memory_holder: &mut MemoryHolder,
    machine_state: &mut MachineState,
) -> u64 {
    // Implementer here is responsible for ALL the bookkeeping, and eventually MUST update trace piece chunk via context, and and update machine state to reflect filled part of trace chunk
    assert!((trace_piece.len as usize) < TRACE_CHUNK_LEN);
    debug_assert_eq!(machine_state.timestamp % 4, 3);
    assert_eq!(
        machine_state.registers[10],
        INITIAL_KECCAK_F1600_CONTROL_VALUE
    ); // initial control flow is expected to be zero
    let state_ptr = machine_state.registers[11];
    assert!(state_ptr as usize >= common_constants::rom::ROM_BYTE_SIZE);
    assert_eq!(state_ptr % 256, 0, "state pointer is unaligned");

    // now we will effectively "unroll" all the invocation

    // Register accesses are easy - we just need to write final control flow value, and update timestamps

    machine_state.registers[10] = FINAL_KECCAK_F1600_CONTROL_VALUE;

    // save for accesses in individual cycles
    let initial_ts = machine_state.timestamp;

    // and full machine state also moves!

    // x0 touch at the very end
    machine_state.register_timestamps[0] +=
        ((NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 - 1) as TimestampScalar) * TIMESTAMP_STEP;
    // timestamp itself
    machine_state.timestamp +=
        ((NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 - 1) as TimestampScalar) * TIMESTAMP_STEP;
    // pc is not needed

    machine_state.register_timestamps[10] = machine_state.timestamp;
    machine_state.register_timestamps[11] = machine_state.timestamp;

    // just stamp keccak_f1600 on top of it...

    // now we need to be careful with accessed state elements. We always access u64s only, and for replaying purposes we will need
    // to read 31 state elements (for snapshot), and then we will work over the
    unsafe {
        let offset = (state_ptr as usize) / core::mem::size_of::<u32>();
        let keccak_state = memory_holder
            .memory
            .as_mut_ptr()
            .add(offset)
            .cast::<[u64; 31]>()
            .as_mut_unchecked();
        let timestamps = memory_holder
            .timestamps
            .as_mut_ptr()
            .add(offset)
            .cast::<[TimestampScalar; 31 * 2]>()
            .as_mut_unchecked();

        // we read and push to snapshotter

        // TODO: unroll?
        for i in 0..31 {
            // low and high
            let ts_offset = KECCAK_FINAL_TIMESTAMP_OFFSETS[i];
            let write_ts = initial_ts + ts_offset;

            debug_assert_eq!(write_ts % TIMESTAMP_STEP, 3);

            let value = keccak_state[i];
            let low = value as u32;
            let high = (value >> 32) as u32;

            trace_piece.add_element(low, timestamps[2 * i]);
            timestamps[2 * i] = write_ts;
            trace_piece.add_element(high, timestamps[2 * i + 1]);
            timestamps[2 * i + 1] = write_ts;
        }

        keccak_f1600_impl_ext(keccak_state);
    }

    assert!((trace_piece.len as usize) < MAX_TRACE_CHUNK_LEN);
    let should_flush = ((trace_piece.len as usize) >= TRACE_CHUNK_LEN) as u64;

    // println!("Keccak, should flush = {}", should_flush);

    should_flush
}
