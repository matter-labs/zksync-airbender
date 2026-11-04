use std::alloc::Layout;

use super::*;

impl TraceChunk {
    pub fn empty() -> Self {
        Self {
            values: [0u32; MAX_TRACE_CHUNK_LEN],
            timestamps: [0; MAX_TRACE_CHUNK_LEN],
            len: 0,
        }
    }

    #[inline(always)]
    pub fn add_element(&mut self, value: u32, ts: TimestampScalar) {
        debug_assert!((self.len as usize) < MAX_TRACE_CHUNK_LEN);
        unsafe {
            self.values.as_mut_ptr().add(self.len as usize).write(value);
            self.timestamps
                .as_mut_ptr()
                .add(self.len as usize)
                .write(ts);

            self.len += 1;
        }
    }

    #[inline(always)]
    pub fn append_arbitrary_value(&mut self, value: u32) {
        self.add_element(value, 0);
    }

    pub fn data(&'_ self) -> (&'_ [u32], &'_ [TimestampScalar]) {
        unsafe {
            let values =
                core::slice::from_raw_parts(self.values.as_ptr().cast::<u32>(), self.len as usize);
            let timestamps = core::slice::from_raw_parts(
                self.timestamps.as_ptr().cast::<TimestampScalar>(),
                self.len as usize,
            );

            (values, timestamps)
        }
    }

    pub fn reset(&mut self) {
        self.values.fill(0);
        self.timestamps.fill(0);
        self.len = 0;
    }

    pub(crate) const TIMESTAMPS_OFFSET: usize = offset_of!(Self, timestamps);
    pub(crate) const LEN_OFFSET: usize = offset_of!(Self, len);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(u64)]
pub enum JitRunnerRam {
    UninitPlaceholder = 0,
    Tiny = 32 * (1 << 20),
    Small = 128 * (1 << 20),
    Medium = 1 << 30,
    Full = 1 << 32,
}

impl JitRunnerRam {
    pub fn ram_size(&self) -> usize {
        (*self as u64) as usize
    }

    /// Byte offset from the start of the buffer to the timestamps image. The memory
    /// image occupies exactly `ram_size` bytes, so the two coincide.
    pub(crate) fn timestamps_offset(&self) -> u64 {
        *self as u64
    }

    /// Bytes a `MemoryHolder` for this configuration occupies: the image, plus one
    /// `TimestampScalar` per word of it. This is the host memory a caller commits by
    /// choosing this configuration, and page-locks if it registers the holder.
    pub fn holder_byte_size(&self) -> usize {
        self.memory_holder_buffer_size() * core::mem::size_of::<u64>()
    }

    /// Length in `u64` words of the backing buffer: `ram_size / 4` words of `u32`
    /// memory plus `ram_size / 4` words of `u64` timestamps.
    pub(crate) fn memory_holder_buffer_size(&self) -> usize {
        let num_u32_words = self.ram_size() / core::mem::size_of::<u32>();
        assert_eq!(num_u32_words % 2, 0);
        num_u32_words * 3 / 2
    }
}

// Unsized, so it can only be built through a boxed allocation. Alignment is 2 Mb - the
// huge page size on x86-64. `repr(C)` because `allocate_zeroed`, `as_mut_ptr` and the
// reconstruction in `process_csr` all take the buffer to start at offset 0, and for a
// `repr(Rust)` struct that would only be incidentally true.
#[repr(C, align(2097152))]
pub struct MemoryHolder {
    buffer: [u64],
}

impl MemoryHolder {
    pub const ALIGNMENT: usize = 1 << 21;

    fn num_words(&self) -> usize {
        debug_assert_eq!((self.buffer.len() * 2) % 3, 0);
        self.buffer.len() * 2 / 3
    }

    pub fn as_mut_ptr(&mut self) -> NonNull<u64> {
        unsafe { NonNull::new_unchecked(self.buffer.as_mut_ptr()) }
    }

    pub fn ram_size(&self) -> usize {
        self.num_words() * core::mem::size_of::<u32>()
    }

    pub fn byte_size(&self) -> usize {
        self.buffer.len() * core::mem::size_of::<u64>()
    }

    pub fn memory(&self) -> &[u32] {
        unsafe { core::slice::from_raw_parts(self.buffer.as_ptr().cast(), self.num_words()) }
    }

    pub fn memory_mut(&mut self) -> &mut [u32] {
        let num_words = self.num_words();
        unsafe { core::slice::from_raw_parts_mut(self.buffer.as_mut_ptr().cast(), num_words) }
    }

    pub fn timestamps(&self) -> &[TimestampScalar] {
        let num_words = self.num_words();
        unsafe {
            core::slice::from_raw_parts(
                self.buffer
                    .as_ptr()
                    .cast::<u32>()
                    .add(num_words)
                    .cast::<TimestampScalar>(),
                num_words,
            )
        }
    }

    pub fn timestamps_mut(&mut self) -> &mut [TimestampScalar] {
        let num_words = self.num_words();
        unsafe {
            core::slice::from_raw_parts_mut(
                self.buffer
                    .as_mut_ptr()
                    .cast::<u32>()
                    .add(num_words)
                    .cast::<TimestampScalar>(),
                num_words,
            )
        }
    }

    pub fn memory_and_timestamps_mut(&mut self) -> (&mut [u32], &mut [TimestampScalar]) {
        let num_words = self.num_words();
        unsafe {
            let base = self.buffer.as_mut_ptr().cast::<u32>();
            let mem = core::slice::from_raw_parts_mut(base, num_words);
            let ts = core::slice::from_raw_parts_mut(
                base.add(num_words).cast::<TimestampScalar>(),
                num_words,
            );
            (mem, ts)
        }
    }

    pub fn allocate_zeroed<A: Allocator>(size: JitRunnerRam, allocator: A) -> Box<Self, A> {
        assert_ne!(size, JitRunnerRam::UninitPlaceholder);
        let num_words = size.memory_holder_buffer_size();
        // `pad_to_align` is what makes this equal to the layout `Box`'s drop glue will
        // deallocate with: `Layout::for_value` rounds the size up to the type's
        // alignment, and `align_to` on its own does not.
        let layout = Layout::array::<u64>(num_words)
            .expect("proper array layout for [u64]")
            .align_to(Self::ALIGNMENT)
            .expect("proper extra alignment for [u64]")
            .pad_to_align();
        let boxed = unsafe {
            let backing = allocator
                .allocate_zeroed(layout)
                .expect("MemoryHolder allocated");
            let fat =
                NonNull::slice_from_raw_parts(backing.as_non_null_ptr().cast::<u64>(), num_words);
            // `MemoryHolder` is a slice-DST whose only field is the `[u64]`, so the
            // element-count metadata carries over unchanged.
            Box::<MemoryHolder, A>::from_non_null_in(
                NonNull::new_unchecked(fat.as_ptr() as *mut MemoryHolder),
                allocator,
            )
        };
        debug_assert_eq!(Layout::for_value(&*boxed), layout);

        boxed
    }

    pub fn reset<A: Allocator>(this: &mut Box<Self, A>) {
        this.buffer.fill(0);
    }

    pub fn collect_inits_and_teardowns<A: Allocator + Clone + Send + Sync>(
        &self,
        worker: &worker::Worker,
        allocator: A,
    ) -> Vec<Vec<(u32, (TimestampScalar, u32)), A>> {
        // parallel collect
        // first we will walk over access_bitmask and collect subparts
        let mut chunks: Vec<Vec<(u32, (TimestampScalar, u32)), A>> =
            vec![Vec::new_in(allocator).clone(); worker.get_num_cores()];
        let mut dst = &mut chunks[..];
        let work_size = self.num_words();
        worker.scope(work_size, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                let range = chunk_start..(chunk_start + chunk_size);
                let (el, rest) = dst.split_at_mut(1);
                dst = rest;
                let values = &self.memory()[range.clone()];
                let timestamps = &self.timestamps()[range];

                worker::Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let el = &mut el[0];
                    let mut address = chunk_start * core::mem::size_of::<u32>();
                    for (idx, ts) in timestamps.iter().enumerate() {
                        if *ts != 0 {
                            let mut word_value = unsafe { *values.get_unchecked(idx) };
                            // we mask ROM region to be zero-valued
                            if address < common_constants::rom::ROM_BYTE_SIZE {
                                word_value = 0;
                            }
                            let last_timestamp: TimestampScalar = *ts;
                            el.push((address as u32, (last_timestamp, word_value)));
                        }

                        address += core::mem::size_of::<u32>();
                    }
                });
            }
        });

        chunks
    }
}

#[derive(Debug)]
pub struct ReplayerMemChunks<'a> {
    pub chunks: &'a mut [(&'a [u32], &'a [TimestampScalar])],
}

impl<'a> RamPeek for ReplayerMemChunks<'a> {
    #[inline(always)]
    fn peek_word(&self, address: u32) -> u32 {
        debug_assert_eq!(address % 4, 0);
        debug_assert!(self.chunks.len() > 0);
        unsafe {
            let value = *self.chunks.get_unchecked(0).0.get_unchecked(0);

            value
        }
    }
}

impl<'a> RAM for ReplayerMemChunks<'a> {
    const REPLAY_NON_DETERMINISM_VIA_RAM_STUB: bool = true;

    #[track_caller]
    #[inline(always)]
    fn read_word(&mut self, address: u32, timestamp: TimestampScalar) -> (TimestampScalar, u32) {
        debug_assert_eq!(address % 4, 0);
        debug_assert!(self.chunks.len() > 0);
        unsafe {
            let src = self.chunks.get_unchecked_mut(0);
            let value = *src.0.get_unchecked(0);
            let read_timestamp = *src.1.get_unchecked(0);
            let next_values = src.0.get_unchecked(1..);
            let next_timestamps = src.1.get_unchecked(1..);
            if next_values.len() > 0 {
                *src = (next_values, next_timestamps);
            } else {
                self.chunks = core::mem::transmute(self.chunks.get_unchecked_mut(1..));
            }

            debug_assert!(read_timestamp < timestamp, "trying to read replay log at address 0x{:08x} with timestamp {}, but read timestamp is {}", address, timestamp, read_timestamp);

            // println!("Read at address 0x{:08x} at timestamp {} into value {} and read timestamp {}", address, timestamp, value, read_timestamp);
            (read_timestamp, value)
        }
    }

    #[inline(always)]
    fn mask_read_for_witness(&self, address: &mut u32, value: &mut u32) {
        debug_assert_eq!(*address % 4, 0);
        if (*address as usize) < common_constants::rom::ROM_BYTE_SIZE {
            // NOTE: we no longer mask an address, just a value as it's only initialized to
            // 0 via inits, and can not be written over by circuits
            // *address = 0u32;
            *value = 0u32;
        }
    }

    #[inline(always)]
    fn write_word(
        &mut self,
        address: u32,
        _word: u32,
        timestamp: TimestampScalar,
    ) -> (TimestampScalar, u32) {
        debug_assert_eq!(address % 4, 0);
        debug_assert!(self.chunks.len() > 0);
        unsafe {
            let src = self.chunks.get_unchecked_mut(0);
            let value = *src.0.get_unchecked(0);
            let read_timestamp = *src.1.get_unchecked(0);
            let next_values = src.0.get_unchecked(1..);
            let next_timestamps = src.1.get_unchecked(1..);
            if next_values.len() > 0 {
                *src = (next_values, next_timestamps);
            } else {
                self.chunks = core::mem::transmute(self.chunks.get_unchecked_mut(1..));
            }

            debug_assert!(read_timestamp < timestamp, "trying to read replay log at address 0x{:08x} with timestamp {}, but read timestamp is {}", address, timestamp, read_timestamp);

            // println!("Read at address 0x{:08x} at timestamp {} into value {} and read timestamp {}", address, timestamp, value, read_timestamp);
            (read_timestamp, value)
        }
    }

    #[inline(always)]
    fn skip_if_replaying(&mut self, num_snapshots: usize) {
        unsafe {
            let src = self.chunks.get_unchecked_mut(0);
            debug_assert!(src.0.len() >= num_snapshots);
            debug_assert!(src.1.len() >= num_snapshots);
            let next_values = src.0.get_unchecked(num_snapshots..);
            let next_timestamps = src.1.get_unchecked(num_snapshots..);
            if next_values.len() > 0 {
                *src = (next_values, next_timestamps);
            } else {
                self.chunks = core::mem::transmute(self.chunks.get_unchecked_mut(1..));
            }
        }
    }
}

pub struct DefaultContextImpl<'a, N: NonDeterminismCSRSource> {
    pub(crate) non_determinism_source: &'a mut N,
    pub(crate) trace_len: usize,
    pub(crate) final_state: Option<MachineState>,
}

impl<'a, N: NonDeterminismCSRSource> DefaultContextImpl<'a, N> {
    pub fn new(non_determinism_source: &'a mut N) -> Self {
        Self {
            non_determinism_source,
            trace_len: 0,
            final_state: None,
        }
    }
}

impl<'a, N: NonDeterminismCSRSource> ContextImpl for DefaultContextImpl<'a, N> {
    fn read_nondeterminism(&mut self) -> u32 {
        self.non_determinism_source.read()
    }

    fn write_nondeterminism(&mut self, value: u32, memory: &[u32]) {
        self.non_determinism_source
            .write_with_memory_access(&memory, value);
    }

    fn receive_trace(
        &mut self,
        mut trace_chunk: NonNull<TraceChunk>,
        machine_state: &MachineState,
    ) -> NonNull<TraceChunk> {
        debug_assert!((machine_state as *const MachineState)
            .is_aligned_to(core::mem::align_of::<MachineState>()));
        debug_assert!((trace_chunk.as_ptr() as *const TraceChunk)
            .is_aligned_to(core::mem::align_of::<TraceChunk>()));

        let trace_piece = unsafe { trace_chunk.as_mut() };
        assert!((trace_piece.len as usize) >= TRACE_CHUNK_LEN);
        assert!((trace_piece.len as usize) <= MAX_TRACE_CHUNK_LEN);
        // println!(
        //     "Received snapshot of length {} after {} cycles",
        //     trace_piece.len,
        //     (machine_state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP
        // );
        self.trace_len += trace_piece.len as usize;

        #[cfg(debug_assertions)]
        {
            for i in (trace_piece.len as usize)..MAX_TRACE_CHUNK_LEN {
                assert_eq!(
                    trace_piece.values[i], 0,
                    "invalid canary value at slot {}",
                    i
                );
                assert_eq!(
                    trace_piece.timestamps[i], 0,
                    "invalid canary timestamp at slot {}",
                    i
                );
            }

            trace_piece.values.fill(0);
            trace_piece.timestamps.fill(0);
        }
        trace_piece.len = 0;

        trace_chunk
    }

    fn receive_final_trace_piece(
        &mut self,
        mut trace_chunk: NonNull<TraceChunk>,
        machine_state: &MachineState,
    ) {
        println!("Execution completed");
        debug_assert!((machine_state as *const MachineState)
            .is_aligned_to(core::mem::align_of::<MachineState>()));
        debug_assert!((trace_chunk.as_ptr() as *const TraceChunk)
            .is_aligned_to(core::mem::align_of::<TraceChunk>()));
        let trace_piece = unsafe { trace_chunk.as_mut() };
        // println!(
        //     "In total {} cycles passed",
        //     (machine_state.timestamp - INITIAL_TIMESTAMP) / TIMESTAMP_STEP
        // );
        // println!("Final trace chunk len = {}", trace_piece.len);
        // println!("Final PC = 0x{:08x}", machine_state.pc);
        self.trace_len += trace_piece.len as usize;
        self.final_state = Some(*machine_state);
    }

    fn take_final_state(&mut self) -> Option<MachineState> {
        self.final_state.take()
    }
    fn final_state_ref(&'_ self) -> Option<&'_ MachineState> {
        self.final_state.as_ref()
    }
}
