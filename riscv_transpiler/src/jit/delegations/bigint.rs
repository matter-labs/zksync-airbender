use super::*;
use crate::vm::delegations::bigint::*;
use ruint::aliases::U256;

pub fn bigint_implementation(
    trace_piece: &mut TraceChunk,
    memory_holder: &mut MemoryHolder,
    machine_state: &mut MachineState,
) -> u64 {
    // Implementer here is responsible for ALL the bookkeeping, and eventually MUST update trace piece chunk via context, and and update machine state to reflect filled part of trace chunk
    assert!((trace_piece.len as usize) < TRACE_CHUNK_LEN);
    debug_assert_eq!(machine_state.timestamp % 4, 3);
    let a_ptr = machine_state.get_register(10);
    let b_ptr = machine_state.get_register(11);
    let x12 = machine_state.get_register(12);
    assert!(a_ptr as usize >= common_constants::rom::ROM_BYTE_SIZE);
    assert!(b_ptr as usize >= common_constants::rom::ROM_BYTE_SIZE);
    assert_eq!(a_ptr % 32, 0, "`a` pointer is unaligned");
    assert_eq!(b_ptr % 32, 0, "`b` pointer is unaligned");
    // the operands are 32 bytes each, and the accesses below are not bounds-checked
    let ram_size = machine_state.ram_config.ram_size();
    debug_assert_eq!(ram_size, memory_holder.ram_size());
    assert!(
        a_ptr as usize + 32 <= ram_size,
        "`a` extends beyond the end of RAM"
    );
    assert!(
        b_ptr as usize + 32 <= ram_size,
        "`b` extends beyond the end of RAM"
    );

    assert!(a_ptr != b_ptr);

    let write_ts = machine_state.timestamp;

    // Precompile post-cycle register-timestamp effect (a0/a1/a2 = x10/x11/x12 -> 3 mod 4).
    // Merged with per-cycle timestamps by `register_timestamps_array`.
    machine_state.register_timestamps[10] = write_ts;
    machine_state.register_timestamps[11] = write_ts;
    machine_state.register_timestamps[12] = write_ts;

    // read and save into snapshots

    // NOTE: read `b`` first, then `a` for snapshotting purposes

    let b = unsafe {
        let offset = (b_ptr as usize) / core::mem::size_of::<u32>();
        let (mem, ts) = memory_holder.memory_and_timestamps_mut();
        let integer = mem.as_ptr().add(offset).cast::<U256>().as_ref_unchecked();
        let timestamps = ts
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
        let (mem, ts) = memory_holder.memory_and_timestamps_mut();
        let integer = mem
            .as_mut_ptr()
            .add(offset)
            .cast::<U256>()
            .as_mut_unchecked();
        let timestamps = ts
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

    *machine_state.get_register_mut(12) = of as u32;

    assert!((trace_piece.len as usize) < MAX_TRACE_CHUNK_LEN);
    let should_flush = ((trace_piece.len as usize) >= TRACE_CHUNK_LEN) as u64;

    // println!("Bigint, should flush = {}", should_flush);

    should_flush
}

#[cfg(test)]
mod tests {
    use super::*;
    use common_constants::delegation_types::bigint_with_control::ADD_OP_BIT_IDX;

    /// The Rust handler rejects operands that extend beyond the end of RAM, like the routine of the x86-64 JIT
    fn rust_handler_with_operands(a: u32, b: u32) {
        let ram_config = JitRunnerRam::Tiny;
        let mut memory = MemoryHolder::allocate_zeroed(ram_config, std::alloc::Global);
        let mut trace: Box<TraceChunk> = unsafe { Box::new_zeroed().assume_init() };
        let mut state = Box::new(MachineState::initial());
        *state.get_register_mut(10) = a;
        *state.get_register_mut(11) = b;
        *state.get_register_mut(12) = 1 << ADD_OP_BIT_IDX;
        state.timestamp = INITIAL_TIMESTAMP + 3;
        state.ram_config = ram_config;
        bigint_implementation(&mut trace, &mut memory, &mut state);
    }

    #[test]
    fn rust_handler_accepts_the_last_operand_of_ram() {
        let ram_size = JitRunnerRam::Tiny.ram_size() as u32;
        rust_handler_with_operands(ram_size - 32, ram_size - 64);
        rust_handler_with_operands(ram_size - 64, ram_size - 32);
    }

    #[test]
    #[should_panic(expected = "`a` extends beyond the end of RAM")]
    fn rust_handler_rejects_a_beyond_ram() {
        let ram_size = JitRunnerRam::Tiny.ram_size() as u32;
        rust_handler_with_operands(ram_size, ram_size - 32);
    }

    #[test]
    #[should_panic(expected = "`b` extends beyond the end of RAM")]
    fn rust_handler_rejects_b_beyond_ram() {
        let ram_size = JitRunnerRam::Tiny.ram_size() as u32;
        rust_handler_with_operands(ram_size - 32, ram_size + 64);
    }
}
