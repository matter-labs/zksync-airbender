use std::{ptr::addr_of, sync::atomic::AtomicU64};

use super::*;

#[repr(C, align(16))]
pub struct ChunkPostSnapshot {
    pub state_with_counters: MachineState,
    pub trace_chunk: TraceChunk,
}

impl ChunkPostSnapshot {
    pub fn empty() -> Self {
        Self {
            state_with_counters: MachineState::initial(),
            trace_chunk: TraceChunk::empty(),
        }
    }
}

#[repr(C, align(16))]
pub struct PreallocatedSnapshots<'a, const N: usize, A: Allocator> {
    buffer: Box<[ChunkPostSnapshot; N], A>,
    filled: AtomicU64,
    non_determinism: &'a mut dyn NonDeterminismCSRSource,
}

impl<'a, const N: usize, A: Allocator> PreallocatedSnapshots<'a, N, A> {
    pub fn new_in(allocator: A, non_determinism: &'a mut dyn NonDeterminismCSRSource) -> Self {
        unsafe {
            // let buffer = Box::new_zeroed_in(allocator).assume_init();
            // let buffer = {
            //     Box::new_uninit_in(allocator).assume_init()
            // };
            let buffer = {
                let mut buffer: Box<std::mem::MaybeUninit<[ChunkPostSnapshot; N]>, A> =
                    Box::new_uninit_in(allocator);
                let t = buffer.as_mut().as_mut_ptr().cast::<ChunkPostSnapshot>();
                for i in 0..N {
                    t.add(i).write(ChunkPostSnapshot::empty());
                    // buffer[i].write(ChunkPostSnapshot::empty());
                }
                buffer.assume_init()
            };
            Self {
                buffer,
                filled: AtomicU64::new(0),
                non_determinism,
            }
        }
    }

    pub fn initial_snapshot(&mut self) -> NonNull<TraceChunk> {
        unsafe {
            let filled = self.filled.load(std::sync::atomic::Ordering::Acquire) as usize;
            assert_eq!(filled, 0);
            let next = NonNull::new_unchecked(
                &mut self.buffer.get_unchecked_mut(0).trace_chunk as *mut TraceChunk,
            );

            next
        }
    }

    pub fn snapshots(&'_ self) -> &'_ [ChunkPostSnapshot] {
        let filled = self.filled.load(std::sync::atomic::Ordering::Acquire) as usize;
        unsafe { core::slice::from_raw_parts(self.buffer.as_ptr(), filled) }
    }
}

impl<'a, const N: usize, A: Allocator> ContextImpl for PreallocatedSnapshots<'a, N, A> {
    #[inline(always)]
    fn read_nondeterminism(&mut self) -> u32 {
        self.non_determinism.read()
    }
    #[inline(always)]
    fn write_nondeterminism(&mut self, value: u32, memory: &[u32; RAM_SIZE]) {
        self.non_determinism
            .write_with_memory_access_dyn(memory, value);
    }
    fn take_final_state(&mut self) -> Option<MachineState> {
        self.final_state_ref().map(|el| *el)
    }
    fn final_state_ref(&'_ self) -> Option<&'_ MachineState> {
        let filled = self.filled.load(std::sync::atomic::Ordering::Acquire) as usize;
        debug_assert!(filled < N);
        if filled > 0 {
            let state_ref = &self.buffer[filled - 1].state_with_counters;

            Some(state_ref)
        } else {
            None
        }
    }
    #[inline(always)]
    fn receive_trace(
        &mut self,
        trace_piece: NonNull<TraceChunk>,
        machine_state: &MachineState,
    ) -> NonNull<TraceChunk> {
        unsafe {
            let mut filled = self.filled.load(std::sync::atomic::Ordering::Acquire) as usize;
            debug_assert!(filled < N);
            assert_eq!(
                trace_piece,
                NonNull::new_unchecked(
                    &mut self.buffer.get_unchecked_mut(filled).trace_chunk as *mut TraceChunk
                )
            );

            core::ptr::copy_nonoverlapping(
                machine_state as *const _,
                &mut self.buffer.get_unchecked_mut(filled).state_with_counters as *mut _,
                1,
            );

            filled += 1;
            let next = NonNull::new_unchecked(
                &mut self.buffer.get_unchecked_mut(filled).trace_chunk as *mut TraceChunk,
            );

            // we do VERY stupid prefetch here
            unsafe {
                std::intrinsics::prefetch_write_data::<u32, 2>(
                    addr_of!((*(next.as_ptr() as *const TraceChunk)).values).cast(),
                );
                std::intrinsics::prefetch_write_data::<TimestampScalar, 2>(
                    addr_of!((*(next.as_ptr() as *const TraceChunk)).timestamps).cast(),
                );
            }

            self.filled
                .store(filled as u64, std::sync::atomic::Ordering::SeqCst);

            next
        }
    }

    #[inline(always)]
    fn receive_final_trace_piece(
        &mut self,
        trace_piece: NonNull<TraceChunk>,
        machine_state: &MachineState,
    ) {
        self.receive_trace(trace_piece, machine_state);

        // unsafe {
        //     let mut filled = self.filled.load(std::sync::atomic::Ordering::Acquire) as usize;
        //     debug_assert!(filled < N);
        //     assert_eq!(trace_piece, NonNull::new_unchecked(&mut self.buffer.get_unchecked_mut(filled).trace_chunk as *mut TraceChunk));

        //     core::ptr::copy_nonoverlapping(machine_state as *const _, &mut self.buffer.get_unchecked_mut(filled).state_with_counters as *mut _, 1);
        //     filled += 1;

        //     self.filled.store(filled as u64, std::sync::atomic::Ordering::SeqCst);
        // }
    }
}
