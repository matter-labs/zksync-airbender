use super::*;
use crate::vm::delegations::keccak_k2::*;

pub fn keccak_k2_unrolled_implementation(
    trace_piece: &mut TraceChunk,
    memory_holder: &mut MemoryHolder,
    machine_state: &mut MachineState,
) -> u64 {
    assert!((trace_piece.len as usize) < TRACE_CHUNK_LEN);
    debug_assert_eq!(machine_state.timestamp % 4, 3);
    assert_eq!(
        machine_state.get_register(10),
        INITIAL_KECCAK_K2_CONTROL_VALUE
    );
    let state_ptr = machine_state.get_register(11);
    assert!(state_ptr as usize >= common_constants::rom::ROM_BYTE_SIZE);
    assert_eq!(state_ptr % 256, 0, "state pointer is unaligned");

    *machine_state.get_register_mut(10) = FINAL_KECCAK_K2_CONTROL_VALUE;
    machine_state.counters[CounterType::KeccakK2Delegation as u8 as usize] +=
        NUM_DELEGATION_CALLS_FOR_KECCAK_K2_F1600 as u64;
    let initial_ts = machine_state.timestamp;
    machine_state.timestamp +=
        ((NUM_DELEGATION_CALLS_FOR_KECCAK_K2_F1600 - 1) as TimestampScalar) * TIMESTAMP_STEP;
    machine_state.register_timestamps[0] = (machine_state.timestamp & !(TIMESTAMP_STEP - 1)) + 2;
    machine_state.register_timestamps[10] = machine_state.timestamp;
    machine_state.register_timestamps[11] = machine_state.timestamp;

    unsafe {
        let offset = (state_ptr as usize) / core::mem::size_of::<u32>();
        let (mem, ts) = memory_holder.memory_and_timestamps_mut();
        let keccak_state = mem
            .as_mut_ptr()
            .add(offset)
            .cast::<[u64; 31]>()
            .as_mut_unchecked();
        let timestamps = ts
            .as_mut_ptr()
            .add(offset)
            .cast::<[TimestampScalar; 31 * 2]>()
            .as_mut_unchecked();
        for i in 0..KECCAK_K2_ACCESSED_SLOTS {
            let write_ts = initial_ts + KECCAK_K2_FINAL_TIMESTAMP_OFFSETS[i].unwrap();
            debug_assert_eq!(write_ts % TIMESTAMP_STEP, 3);
            let value = keccak_state[i];
            trace_piece.add_element(value as u32, timestamps[2 * i]);
            timestamps[2 * i] = write_ts;
            trace_piece.add_element((value >> 32) as u32, timestamps[2 * i + 1]);
            timestamps[2 * i + 1] = write_ts;
        }
        keccak_k2_f1600_impl_ext(keccak_state);
    }

    assert!((trace_piece.len as usize) < MAX_TRACE_CHUNK_LEN);
    ((trace_piece.len as usize) >= TRACE_CHUNK_LEN) as u64
}
