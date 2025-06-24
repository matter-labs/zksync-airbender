use cs::definitions::{TimestampData, TimestampScalar, TIMESTAMP_STEP};
use fft::GoodAllocator;
use prover::definitions::LazyInitAndTeardown;
use prover::risc_v_simulator::abstractions::memory::{AccessType, MemorySource};
use prover::risc_v_simulator::abstractions::tracer::{
    RegisterOrIndirectReadData, RegisterOrIndirectReadWriteData, Tracer,
};
use prover::risc_v_simulator::cycle::state_new::RiscV32StateForUnrolledProver;
use prover::risc_v_simulator::cycle::status_registers::TrapReason;
use prover::risc_v_simulator::cycle::MachineConfig;
use prover::tracers::delegation::DelegationWitness;
use prover::tracers::main_cycle_optimized::{
    RegIndexOrMemWordIndex, SingleCycleTracingData, EMPTY_SINGLE_CYCLE_TRACING_DATA,
};
use std::alloc::Global;
use std::collections::HashMap;
// NOTE: this tracer ALLOWS for delegations to initialize memory, so we should use enough cycles
// to eventually perform all the inits

const PAGE_WORDS_LOG_SIZE: usize = 10; // 4 KiB page size, 1K x 4 bytes per word
const PAGE_WORDS_SIZE: usize = 1 << PAGE_WORDS_LOG_SIZE;

#[derive(Clone, Debug)]
pub struct RamTracingData<const RAM_SIZE: usize, const TRACE_TOUCHED_RAM: bool> {
    pub register_last_live_timestamps: [TimestampScalar; 32],
    pub ram_words_last_live_timestamps: Box<[TimestampScalar]>,
    pub num_touched_ram_cells_in_pages: Box<[u32]>,
}

impl<const RAM_SIZE: usize, const TRACE_TOUCHED_RAM: bool>
    RamTracingData<RAM_SIZE, TRACE_TOUCHED_RAM>
{
    pub fn new() -> Self {
        assert_eq!(RAM_SIZE % 4, 0);
        let num_words = RAM_SIZE / 4;
        let ram_words_last_live_timestamps =
            unsafe { Box::new_zeroed_slice(num_words).assume_init() };
        let num_pages = if TRACE_TOUCHED_RAM {
            num_words.div_ceil(1 << PAGE_WORDS_LOG_SIZE)
        } else {
            0
        };
        let num_touched_ram_cells_in_page =
            unsafe { Box::new_zeroed_slice(num_pages).assume_init() };
        Self {
            register_last_live_timestamps: [0; 32],
            ram_words_last_live_timestamps,
            num_touched_ram_cells_in_pages: num_touched_ram_cells_in_page,
        }
    }

    #[inline(always)]
    pub(crate) fn mark_register_use(
        &mut self,
        reg_idx: u32,
        write_timestamp: TimestampScalar,
    ) -> TimestampScalar {
        unsafe {
            let read_timestamp = core::mem::replace(
                self.register_last_live_timestamps
                    .get_unchecked_mut(reg_idx as usize),
                write_timestamp,
            );
            debug_assert!(read_timestamp < write_timestamp);

            read_timestamp
        }
    }

    #[inline(always)]
    pub(crate) fn mark_ram_slot_use(
        &mut self,
        phys_word_idx: u32,
        write_timestamp: TimestampScalar,
    ) -> TimestampScalar {
        let read_timestamp = unsafe {
            core::mem::replace(
                self.ram_words_last_live_timestamps
                    .get_unchecked_mut(phys_word_idx as usize),
                write_timestamp,
            )
        };
        debug_assert!(read_timestamp < write_timestamp);

        if TRACE_TOUCHED_RAM {
            if read_timestamp == 0 {
                // this is a new cell
                let page_idx = (phys_word_idx >> PAGE_WORDS_LOG_SIZE) as usize;
                unsafe {
                    *self
                        .num_touched_ram_cells_in_pages
                        .get_unchecked_mut(page_idx) += 1
                };
            }
        }
        read_timestamp
    }

    pub fn get_touched_ram_cells_count(&self) -> u32 {
        assert!(TRACE_TOUCHED_RAM);
        self.num_touched_ram_cells_in_pages.iter().sum::<u32>()
    }
}

pub struct SetupAndTeardownChunker<I: Iterator<Item = LazyInitAndTeardown>> {
    pub touched_ram_cells_count: usize,
    pub chunk_size: usize,
    pub next_chunk_index: usize,
    iterator: I,
}

impl<I: Iterator<Item = LazyInitAndTeardown>> SetupAndTeardownChunker<I> {
    pub fn get_chunks_count(&self) -> usize {
        self.touched_ram_cells_count.div_ceil(self.chunk_size)
    }

    pub fn populate_next_chunk(&mut self, chunk: &mut [LazyInitAndTeardown]) {
        let chunks_count = self.get_chunks_count();
        assert!(self.next_chunk_index < chunks_count);
        assert_eq!(self.chunk_size, chunk.len());
        let dst = if self.next_chunk_index == 0 {
            let padding_size = chunks_count * self.chunk_size - self.touched_ram_cells_count;
            let (padding, dst) = chunk.split_at_mut(padding_size);
            padding.fill(LazyInitAndTeardown::default());
            dst
        } else {
            chunk
        };
        dst.fill_with(|| unsafe { self.iterator.next().unwrap_unchecked() });
    }
}

pub fn create_setup_and_teardown_chunker<'a>(
    pages: &'a [u32],
    memory: &'a [u32],
    timestamps: &'a [TimestampScalar],
    chunk_size: usize,
) -> SetupAndTeardownChunker<impl Iterator<Item = LazyInitAndTeardown> + 'a> {
    let touched_ram_cells_count = pages.iter().sum::<u32>() as usize;
    let get_value_fn = |index| unsafe {
        let timestamp = *timestamps.get_unchecked(index);
        if timestamp != 0 {
            let result = LazyInitAndTeardown {
                address: (index as u32) << 2,
                teardown_value: *memory.get_unchecked(index),
                teardown_timestamp: TimestampData::from_scalar(timestamp),
            };
            Some(result)
        } else {
            None
        }
    };
    let iterator = pages
        .iter()
        .copied()
        .enumerate()
        .filter_map(|(index, count)| {
            if count == 0 {
                None
            } else {
                Some(index << PAGE_WORDS_LOG_SIZE)
            }
        })
        .flat_map(move |index| (index..index + PAGE_WORDS_SIZE).filter_map(get_value_fn));
    SetupAndTeardownChunker {
        touched_ram_cells_count,
        chunk_size,
        next_chunk_index: 0,
        iterator,
    }
}

#[derive(Debug)]
pub struct CycleTracingData<A: GoodAllocator = Global> {
    pub per_cycle_data: Vec<SingleCycleTracingData, A>,
}

impl<A: GoodAllocator> CycleTracingData<A> {
    pub fn with_cycles_capacity(capacity: usize) -> Self {
        Self {
            per_cycle_data: Vec::with_capacity_in(capacity, A::default()),
        }
    }
}

#[derive(Default)]
pub struct DelegationTracingData<A: GoodAllocator = Global> {
    pub witnesses: HashMap<u16, DelegationWitness<A>>,
}

// type SwapDelegationWitnessFn<A> = Box<dyn for<'b> Fn(u16, &'b mut DelegationWitness<A>) + 'a>;

pub struct ExecutionTracer<
    'a,
    const RAM_SIZE: usize,
    const LOG_ROM_BOUND: u32,
    S: Fn(u16, Option<DelegationWitness<A>>) -> DelegationWitness<A>,
    A: GoodAllocator = Global,
    const TRACE_TOUCHED_RAM: bool = false,
    const TRACE_CYCLES: bool = false,
    const TRACE_DELEGATIONS: bool = false,
> {
    pub ram_tracing_data: &'a mut RamTracingData<RAM_SIZE, TRACE_TOUCHED_RAM>,
    pub cycle_tracing_data: CycleTracingData<A>,
    pub delegation_tracing_data: DelegationTracingData<A>,
    pub swap_delegation_witness_fn: S,
    pub current_timestamp: TimestampScalar,
}

const RS1_ACCESS_IDX: TimestampScalar = 0;
const RS2_ACCESS_IDX: TimestampScalar = 1;
const RD_ACCESS_IDX: TimestampScalar = 2;
const DELEGATION_ACCESS_IDX: TimestampScalar = 3;

const RAM_READ_ACCESS_IDX: TimestampScalar = RS2_ACCESS_IDX;
const RAM_WRITE_ACCESS_IDX: TimestampScalar = RD_ACCESS_IDX;

impl<
        'a,
        const RAM_SIZE: usize,
        const LOG_ROM_BOUND: u32,
        S: Fn(u16, Option<DelegationWitness<A>>) -> DelegationWitness<A>,
        A: GoodAllocator,
        const TRACE_TOUCHED_RAM: bool,
        const TRACE_CYCLES: bool,
        const TRACE_DELEGATIONS: bool,
    >
    ExecutionTracer<
        'a,
        RAM_SIZE,
        LOG_ROM_BOUND,
        S,
        A,
        TRACE_TOUCHED_RAM,
        TRACE_CYCLES,
        TRACE_DELEGATIONS,
    >
{
    const ROM_MASK: u32 = (1u32 << LOG_ROM_BOUND) - 1;

    pub fn new(
        ram_tracing_data: &'a mut RamTracingData<RAM_SIZE, TRACE_TOUCHED_RAM>,
        cycle_tracing_data: CycleTracingData<A>,
        delegation_tracing_data: DelegationTracingData<A>,
        swap_delegation_witness_fn: S,
        initial_timestamp: TimestampScalar,
    ) -> Self {
        Self {
            ram_tracing_data,
            cycle_tracing_data,
            delegation_tracing_data,
            swap_delegation_witness_fn,
            current_timestamp: initial_timestamp,
        }
    }
}

impl<
        'a,
        C: MachineConfig,
        const RAM_SIZE: usize,
        const LOG_ROM_BOUND: u32,
        S: Fn(u16, Option<DelegationWitness<A>>) -> DelegationWitness<A>,
        A: GoodAllocator,
        const TRACE_TOUCHED_RAM: bool,
        const TRACE_CYCLES: bool,
        const TRACE_DELEGATIONS: bool,
    > Tracer<C>
    for ExecutionTracer<
        'a,
        RAM_SIZE,
        LOG_ROM_BOUND,
        S,
        A,
        TRACE_TOUCHED_RAM,
        TRACE_CYCLES,
        TRACE_DELEGATIONS,
    >
{
    #[allow(deprecated)]
    #[inline(always)]
    fn at_cycle_start(
        &mut self,
        current_state: &prover::risc_v_simulator::cycle::state::RiscV32State<C>,
    ) {
        if !TRACE_CYCLES {
            return;
        }
        let mut element = EMPTY_SINGLE_CYCLE_TRACING_DATA;
        element.pc = current_state.pc;
        unsafe {
            self.cycle_tracing_data
                .per_cycle_data
                .push_within_capacity(element)
                .unwrap_unchecked();
        }
    }

    #[allow(deprecated)]
    #[inline(always)]
    fn at_cycle_end(
        &mut self,
        _current_state: &prover::risc_v_simulator::cycle::state::RiscV32State<C>,
    ) {
        self.current_timestamp += TIMESTAMP_STEP;
    }

    #[inline(always)]
    fn at_cycle_start_ext(&mut self, current_state: &RiscV32StateForUnrolledProver<C>) {
        if !TRACE_CYCLES {
            return;
        }
        let mut element = EMPTY_SINGLE_CYCLE_TRACING_DATA;
        element.pc = current_state.pc;
        unsafe {
            self.cycle_tracing_data
                .per_cycle_data
                .push_within_capacity(element)
                .unwrap_unchecked();
        }
    }

    #[inline(always)]
    fn at_cycle_end_ext(&mut self, _current_state: &RiscV32StateForUnrolledProver<C>) {
        self.current_timestamp += TIMESTAMP_STEP;
    }

    #[inline(always)]
    fn trace_opcode_read(&mut self, _phys_address: u64, _read_value: u32) {
        // Nothing, opcodes are expected to be read from ROM
    }

    #[inline(always)]
    fn trace_rs1_read(&mut self, reg_idx: u32, read_value: u32) {
        debug_assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);

        let write_timestamp = self.current_timestamp + RS1_ACCESS_IDX;

        let read_timestamp = self
            .ram_tracing_data
            .mark_register_use(reg_idx, write_timestamp);

        if !TRACE_CYCLES {
            return;
        }
        unsafe {
            let dst = self
                .cycle_tracing_data
                .per_cycle_data
                .last_mut()
                .unwrap_unchecked();
            dst.rs1_read_value = read_value;
            dst.rs1_read_timestamp = TimestampData::from_scalar(read_timestamp);
            dst.rs1_reg_idx = reg_idx as u16;
        }
    }

    #[inline(always)]
    fn trace_rs2_read(&mut self, reg_idx: u32, read_value: u32) {
        debug_assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);

        let write_timestamp = self.current_timestamp + RS2_ACCESS_IDX;

        let read_timestamp = self
            .ram_tracing_data
            .mark_register_use(reg_idx, write_timestamp);

        // NOTE: we reuse this access for RAM LOAD, but it's not traced if LOAD op happens

        if !TRACE_CYCLES {
            return;
        }
        unsafe {
            let dst = self
                .cycle_tracing_data
                .per_cycle_data
                .last_mut()
                .unwrap_unchecked();
            dst.rs2_or_mem_word_read_value = read_value;
            dst.rs2_or_mem_word_address = RegIndexOrMemWordIndex::register(reg_idx as u8);
            dst.rs2_or_mem_read_timestamp = TimestampData::from_scalar(read_timestamp);
        }
    }

    #[inline(always)]
    fn trace_rd_write(&mut self, reg_idx: u32, read_value: u32, written_value: u32) {
        debug_assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);

        // this happens only if RAM write didn't happen (and opcodes like BRANCH write 0 into x0)

        let write_timestamp = self.current_timestamp + RD_ACCESS_IDX;

        let read_timestamp = self
            .ram_tracing_data
            .mark_register_use(reg_idx, write_timestamp);

        if !TRACE_CYCLES {
            return;
        }
        unsafe {
            let dst = self
                .cycle_tracing_data
                .per_cycle_data
                .last_mut()
                .unwrap_unchecked();

            let mut written_value = written_value;
            if reg_idx == 0 {
                assert_eq!(read_value, 0);
                // we can flush anything here
                written_value = 0;
            }

            dst.rd_or_mem_word_read_value = read_value;
            dst.rd_or_mem_word_write_value = written_value;
            dst.rd_or_mem_word_address = RegIndexOrMemWordIndex::register(reg_idx as u8);
            dst.rd_or_mem_read_timestamp = TimestampData::from_scalar(read_timestamp);
        }
    }

    #[inline(always)]
    fn trace_non_determinism_read(&mut self, read_value: u32) {
        debug_assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);

        if !TRACE_CYCLES {
            return;
        }
        unsafe {
            self.cycle_tracing_data
                .per_cycle_data
                .last_mut()
                .unwrap_unchecked()
                .non_determinism_read = read_value;
        }
    }

    #[inline(always)]
    fn trace_non_determinism_write(&mut self, _written_value: u32) {
        // do nothing
    }

    #[inline(always)]
    fn trace_ram_read(&mut self, phys_address: u64, read_value: u32) {
        debug_assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);
        // assert!(phys_address < (1u32 << 32));
        // assert_eq!(phys_address % 4, 0);
        let phys_address = phys_address as u32;

        let (address, read_value) = if (phys_address & !Self::ROM_MASK) == 0 {
            // ROM read, substituted as read 0 from 0
            (0, 0)
        } else {
            (phys_address, read_value)
        };

        let write_timestamp = self.current_timestamp + RAM_READ_ACCESS_IDX;

        let phys_word_idx = address / 4;
        let read_timestamp = self
            .ram_tracing_data
            .mark_ram_slot_use(phys_word_idx, write_timestamp);

        if !TRACE_CYCLES {
            return;
        }
        unsafe {
            let dst = self
                .cycle_tracing_data
                .per_cycle_data
                .last_mut()
                .unwrap_unchecked();
            // record
            dst.rs2_or_mem_word_read_value = read_value;
            dst.rs2_or_mem_word_address = RegIndexOrMemWordIndex::memory(address);
            dst.rs2_or_mem_read_timestamp = TimestampData::from_scalar(read_timestamp);
        }
    }

    #[inline(always)]
    fn trace_ram_read_write(&mut self, phys_address: u64, read_value: u32, written_value: u32) {
        debug_assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);
        // assert!(phys_address < (1u32 << 32));
        // assert_eq!(phys_address % 4, 0);

        let phys_address = phys_address as u32;
        assert_ne!(phys_address & !Self::ROM_MASK, 0, "Cannot write to ROM");

        // RAM write happens BEFORE rd write

        let write_timestamp = self.current_timestamp + RAM_WRITE_ACCESS_IDX;

        let phys_word_idx = phys_address / 4;
        let read_timestamp = self
            .ram_tracing_data
            .mark_ram_slot_use(phys_word_idx, write_timestamp);

        if !TRACE_CYCLES {
            return;
        }
        // record
        unsafe {
            let dst = self
                .cycle_tracing_data
                .per_cycle_data
                .last_mut()
                .unwrap_unchecked();
            dst.rd_or_mem_word_read_value = read_value;
            dst.rd_or_mem_word_write_value = written_value;
            dst.rd_or_mem_word_address = RegIndexOrMemWordIndex::memory(phys_address);
            dst.rd_or_mem_read_timestamp = TimestampData::from_scalar(read_timestamp);
        }
    }

    #[inline(always)]
    fn trace_address_translation(
        &mut self,
        _satp_value: u32,
        _virtual_address: u64,
        _phys_address: u64,
    ) {
        // nothing
    }

    fn record_delegation(
        &mut self,
        access_id: u32,
        base_register: u32,
        register_accesses: &mut [RegisterOrIndirectReadWriteData],
        indirect_read_addresses: &[u32],
        indirect_reads: &mut [RegisterOrIndirectReadData],
        indirect_write_addresses: &[u32],
        indirect_writes: &mut [RegisterOrIndirectReadWriteData],
    ) {
        debug_assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);
        debug_assert_eq!(indirect_read_addresses.len(), indirect_reads.len());
        debug_assert_eq!(indirect_write_addresses.len(), indirect_writes.len());

        let delegation_type = access_id as u16;

        if TRACE_CYCLES {
            // mark as delegation
            unsafe {
                let dst = self
                    .cycle_tracing_data
                    .per_cycle_data
                    .last_mut()
                    .unwrap_unchecked();
                dst.delegation_request = delegation_type;
            }
        }

        let write_timestamp = self.current_timestamp + DELEGATION_ACCESS_IDX;

        if TRACE_DELEGATIONS {
            let current_tracer = self
                .delegation_tracing_data
                .witnesses
                .entry(delegation_type)
                .or_insert_with(|| (self.swap_delegation_witness_fn)(delegation_type, None));
            debug_assert_eq!(current_tracer.base_register_index, base_register);

            // trace register part
            let mut register_index = base_register;
            for dst in register_accesses.iter_mut() {
                let read_timestamp = self
                    .ram_tracing_data
                    .mark_register_use(register_index, write_timestamp);
                dst.timestamp = TimestampData::from_scalar(read_timestamp);

                register_index += 1;
            }

            // formal reads and writes
            for (phys_address, dst) in indirect_read_addresses
                .iter()
                .zip(indirect_reads.iter_mut())
            {
                let phys_address = *phys_address;
                let phys_word_idx = phys_address / 4;

                let read_timestamp = self
                    .ram_tracing_data
                    .mark_ram_slot_use(phys_word_idx, write_timestamp);

                dst.timestamp = TimestampData::from_scalar(read_timestamp);
            }

            for (phys_address, dst) in indirect_write_addresses
                .iter()
                .zip(indirect_writes.iter_mut())
            {
                let phys_address = *phys_address;
                let phys_word_idx = phys_address / 4;

                let read_timestamp = self
                    .ram_tracing_data
                    .mark_ram_slot_use(phys_word_idx, write_timestamp);

                dst.timestamp = TimestampData::from_scalar(read_timestamp);
            }

            current_tracer
                .register_accesses
                .extend_from_slice(&*register_accesses);
            current_tracer
                .indirect_reads
                .extend_from_slice(&*indirect_reads);
            current_tracer
                .indirect_writes
                .extend_from_slice(&*indirect_writes);
            current_tracer
                .write_timestamp
                .push_within_capacity(TimestampData::from_scalar(write_timestamp))
                .unwrap();

            current_tracer.assert_consistency();
            // swap if needed
            let should_replace = current_tracer.at_capacity();
            if should_replace {
                let witness = self
                    .delegation_tracing_data
                    .witnesses
                    .remove(&delegation_type)
                    .unwrap();
                let witness = (self.swap_delegation_witness_fn)(delegation_type, Some(witness));
                self.delegation_tracing_data
                    .witnesses
                    .insert(delegation_type, witness);
            }
        } else {
            // we only need to mark RAM and register use

            // trace register part
            let mut register_index = base_register;
            for _reg in register_accesses.iter() {
                let _read_timestamp = self
                    .ram_tracing_data
                    .mark_register_use(register_index, write_timestamp);

                register_index += 1;
            }

            // formal reads and writes
            for phys_address in indirect_read_addresses.iter() {
                let phys_address = *phys_address;
                let phys_word_idx = phys_address / 4;

                let _read_timestamp = self
                    .ram_tracing_data
                    .mark_ram_slot_use(phys_word_idx, write_timestamp);
            }

            for phys_address in indirect_write_addresses.iter() {
                let phys_address = *phys_address;
                let phys_word_idx = phys_address / 4;

                let _read_timestamp = self
                    .ram_tracing_data
                    .mark_ram_slot_use(phys_word_idx, write_timestamp);
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct BoxedMemoryImplWithRom<const RAM_SIZE: usize, const LOG_ROM_BOUND: u32>(Box<[u32]>);

impl<const RAM_SIZE: usize, const LOG_ROM_BOUND: u32>
    BoxedMemoryImplWithRom<RAM_SIZE, LOG_ROM_BOUND>
{
    const ROM_BOUND: u32 = 1 << LOG_ROM_BOUND;
    const ROM_BOUND_MASK: u32 = Self::ROM_BOUND - 1;

    pub fn new() -> Self {
        assert!(RAM_SIZE >= Self::ROM_BOUND as usize);
        assert_eq!(RAM_SIZE % 4, 0);
        Self(unsafe { Box::new_zeroed_slice(RAM_SIZE / 4).assume_init() })
    }

    pub fn populate(&mut self, address: u32, value: u32) {
        // assert!(address % 4 == 0);
        self.0[(address / 4) as usize] = value;
    }

    pub fn load_image<'a, B>(&mut self, entry_point: u32, bytes: B)
    where
        B: Iterator<Item = u8>,
    {
        let mut address = entry_point;
        for word in bytes.array_chunks::<4>() {
            self.populate(address, u32::from_le_bytes(word));
            address += 1;
        }
    }

    pub fn get_final_ram_state(self) -> Box<[u32]> {
        // NOTE: important: even though we use single allocation for ROM and RAM,
        // we should NOT expose ROM values, so we will instead zero-out
        let mut ram = self.0;
        ram[..(1 << (LOG_ROM_BOUND - 2))].fill(0);
        ram
    }
}

impl<const RAM_SIZE: usize, const LOG_ROM_BOUND: u32> MemorySource
    for BoxedMemoryImplWithRom<RAM_SIZE, LOG_ROM_BOUND>
{
    #[inline(always)]
    fn set(
        &mut self,
        phys_address: u64,
        value: u32,
        access_type: AccessType,
        trap: &mut TrapReason,
    ) {
        let phys_address = phys_address as u32;
        debug_assert!(phys_address % 4 == 0);
        if (phys_address as usize) < RAM_SIZE {
            if phys_address & !Self::ROM_BOUND_MASK == 0 {
                panic!(
                    "can not set ROM range: requested write into {}, but ROM bound is {}",
                    phys_address,
                    Self::ROM_BOUND
                );
            }
            unsafe { *self.0.get_unchecked_mut((phys_address / 4) as usize) = value };
        } else {
            match access_type {
                AccessType::Instruction => *trap = TrapReason::InstructionAccessFault,
                AccessType::MemLoad => *trap = TrapReason::LoadAccessFault,
                AccessType::MemStore => *trap = TrapReason::StoreOrAMOAccessFault,
                _ => unreachable!(),
            }
        }
    }

    #[inline(always)]
    fn get(&self, phys_address: u64, access_type: AccessType, trap: &mut TrapReason) -> u32 {
        let phys_address = phys_address as u32;
        debug_assert!(phys_address % 4 == 0);
        if (phys_address as usize) < RAM_SIZE {
            if phys_address & Self::ROM_BOUND_MASK == 0 {
                assert!(
                    access_type == AccessType::Instruction || access_type == AccessType::MemLoad
                );
            }
            unsafe { *self.0.get_unchecked((phys_address / 4) as usize) }
        } else {
            match access_type {
                AccessType::Instruction => *trap = TrapReason::InstructionAccessFault,
                AccessType::MemLoad => *trap = TrapReason::LoadAccessFault,
                AccessType::MemStore => *trap = TrapReason::StoreOrAMOAccessFault,
                _ => unreachable!(),
            }
            0
        }
    }

    #[inline(always)]
    fn set_noexcept(&mut self, phys_address: u64, value: u32) {
        let phys_address = phys_address as u32;
        debug_assert!(phys_address % 4 == 0);
        if (phys_address as usize) < RAM_SIZE {
            if phys_address & !Self::ROM_BOUND_MASK == 0 {
                panic!(
                    "can not set ROM range: requested write into {}, but ROM bound is {}",
                    phys_address,
                    Self::ROM_BOUND
                );
            }
            unsafe { *self.0.get_unchecked_mut((phys_address / 4) as usize) = value };
        } else {
            panic!("Out of bound memory access at address 0x{:x}", phys_address);
        }
    }

    #[inline(always)]
    fn get_noexcept(&self, phys_address: u64) -> u32 {
        let phys_address = phys_address as u32;
        debug_assert!(phys_address % 4 == 0);
        if (phys_address as usize) < RAM_SIZE {
            unsafe { *self.0.get_unchecked((phys_address / 4) as usize) }
        } else {
            panic!("Out of bound memory access at address 0x{:x}", phys_address);
        }
    }

    #[inline(always)]
    fn get_opcode_noexcept(&self, phys_address: u64) -> u32 {
        let phys_address = phys_address as u32;
        debug_assert!(phys_address % 4 == 0);
        debug_assert_eq!(
            phys_address & !Self::ROM_BOUND_MASK,
            0,
            "Out of bound opcode access at address 0x{:x}",
            phys_address
        );
        unsafe { *self.0.get_unchecked((phys_address / 4) as usize) }
    }
}
