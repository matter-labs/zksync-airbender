use super::ram::FlamegraphReadableRam;
use crate::vm::{Counters, State};

// Hard cap prevents pathological frame-pointer loops from creating unbounded
// work during profiling.
const MAX_CALLSTACK_DEPTH: usize = 512;

/// Reconstructs a raw callstack by following the frame-pointer chain.
///
/// This is intentionally best-effort: any suspicious memory/layout condition is
/// treated as end-of-stack so profiling never interferes with VM execution.
pub(super) fn collect_stacktrace_raw<C: Counters, R: FlamegraphReadableRam>(
    state: &State<C>,
    ram: &R,
) -> (u32, Vec<u32>) {
    let mut callstack = Vec::with_capacity(8);
    let pc = state.pc;

    // Current frame.
    callstack.push(pc);

    let mut fp = state.registers[8].value;
    if fp == 0 {
        // Frame-pointer-less samples are common and should be ignored quietly.
        return (pc, Vec::new());
    }

    while callstack.len() < MAX_CALLSTACK_DEPTH {
        // Every guard below treats invalid chain data as a graceful stop.
        if fp < 8 {
            break;
        }
        if fp % 4 != 0 {
            break;
        }

        let Some(addr) = ram.try_peek_word_for_flamegraph(fp - 4) else {
            break;
        };
        let Some(next) = ram.try_peek_word_for_flamegraph(fp - 8) else {
            break;
        };

        if addr < 4 {
            break;
        }
        if next == fp {
            break;
        }
        if addr == 0 {
            break;
        }

        // Return address points to the instruction after the callsite.
        // For stack traces we normalize to the callsite itself.
        callstack.push(addr - 4);
        fp = next;
    }

    (pc, callstack)
}

#[cfg(test)]
mod tests {
    use super::collect_stacktrace_raw;
    use crate::vm::{DelegationsAndFamiliesCounters, Register, State};

    fn state_with_pc_and_fp(pc: u32, fp: u32) -> State<DelegationsAndFamiliesCounters> {
        let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
        state.pc = pc;
        state.registers[8] = Register {
            timestamp: 0,
            value: fp,
        };

        state
    }

    #[test]
    fn collects_callstack_from_frame_pointer_chain() {
        let mut ram = [0u32; 64];

        // fp = 0x40
        ram[(0x40 - 4) as usize / 4] = 0x200;
        ram[(0x40 - 8) as usize / 4] = 0x30;

        // fp = 0x30
        ram[(0x30 - 4) as usize / 4] = 0x300;
        ram[(0x30 - 8) as usize / 4] = 0x10;

        // fp = 0x10 terminates: addr is too small.
        ram[(0x10 - 4) as usize / 4] = 0x0;
        ram[(0x10 - 8) as usize / 4] = 0x0;

        let state = state_with_pc_and_fp(0x100, 0x40);
        let (_pc, frames) = collect_stacktrace_raw(&state, &ram);

        assert_eq!(frames, vec![0x100, 0x1fc, 0x2fc]);
    }

    #[test]
    fn skips_sample_without_frame_pointer() {
        let ram = [0u32; 64];
        let state = state_with_pc_and_fp(0x100, 0);
        let (_pc, frames) = collect_stacktrace_raw(&state, &ram);
        assert!(frames.is_empty());
    }
}
