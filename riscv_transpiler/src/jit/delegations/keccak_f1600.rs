use super::*;
use crate::vm::delegations::keccak_f1600::*;

pub fn keccak_f1600_unrolled_implementation(
    trace_piece: &mut TraceChunk,
    memory_holder: &mut MemoryHolder,
    machine_state: &mut MachineState,
) -> u64 {
    assert!((trace_piece.len as usize) < TRACE_CHUNK_LEN);
    debug_assert_eq!(machine_state.timestamp % 4, 3);
    assert_eq!(
        machine_state.get_register(10),
        KECCAK_F1600_INITIAL_CONTROL_VALUE
    );
    let state_ptr = machine_state.get_register(11);
    assert!(state_ptr as usize >= common_constants::rom::ROM_BYTE_SIZE);
    assert_eq!(state_ptr % 256, 0, "state pointer is unaligned");

    *machine_state.get_register_mut(10) = KECCAK_F1600_FINAL_CONTROL_VALUE;
    machine_state.counters[CounterType::KeccakF1600Delegation as u8 as usize] +=
        NUM_KECCAK_F1600_CALLS as u64;
    let initial_ts = machine_state.timestamp;
    machine_state.timestamp += ((NUM_KECCAK_F1600_CALLS - 1) as TimestampScalar) * TIMESTAMP_STEP;
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
        for i in 0..KECCAK_F1600_ACCESSED_SLOTS {
            let write_ts = initial_ts + KECCAK_F1600_FINAL_TIMESTAMP_OFFSETS[i].unwrap();
            debug_assert_eq!(write_ts % TIMESTAMP_STEP, 3);
            let value = keccak_state[i];
            trace_piece.add_element(value as u32, timestamps[2 * i]);
            timestamps[2 * i] = write_ts;
            trace_piece.add_element((value >> 32) as u32, timestamps[2 * i + 1]);
            timestamps[2 * i + 1] = write_ts;
        }
        keccak_f1600_delegation_impl(keccak_state);
    }

    assert!((trace_piece.len as usize) < MAX_TRACE_CHUNK_LEN);
    ((trace_piece.len as usize) >= TRACE_CHUNK_LEN) as u64
}
