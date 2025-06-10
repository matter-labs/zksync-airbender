// - rs1 is register and read only
// - rs2 is register or RAM read
// - rd is register or RAM write

use std::alloc::Global;
use std::collections::HashMap;

use crate::tracers::delegation::DelegationWitness;
use cs::definitions::{TimestampData, TimestampScalar, TIMESTAMP_STEP};
use fft::GoodAllocator;
use risc_v_simulator::abstractions::tracer::*;
use risc_v_simulator::cycle::{state::RiscV32State, *};

// NOTE: this tracer ALLOWS for delegations to initialize memory, so we should use enough cycles
// to eventually perform all the inits

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize,
)]
#[repr(C, align(8))]
pub struct SingleCycleTracingData {
    pub pc: u32,
    pub rs1_read_value: u32,
    pub rs1_read_timestamp: TimestampData,
    pub rs1_reg_idx: u16,
    // 16
    pub rs2_or_mem_word_read_value: u32,
    pub rs2_or_mem_word_address: RegIndexOrMemWordIndex,
    pub rs2_or_mem_read_timestamp: TimestampData,
    pub delegation_request: u16,
    // 32
    pub rd_or_mem_word_read_value: u32,
    pub rd_or_mem_word_write_value: u32,
    pub rd_or_mem_word_address: RegIndexOrMemWordIndex,
    pub rd_or_mem_read_timestamp: TimestampData,
    // 52
    pub non_determinism_read: u32,
}

// Hopefully compiler can see that it's just memzero
pub const EMPTY_SINGLE_CYCLE_TRACING_DATA: SingleCycleTracingData = SingleCycleTracingData {
    pc: 0,
    rs1_read_value: 0,
    rs1_read_timestamp: TimestampData::EMPTY,
    rs1_reg_idx: 0,

    rs2_or_mem_word_read_value: 0,
    rs2_or_mem_word_address: RegIndexOrMemWordIndex::EMPTY,
    rs2_or_mem_read_timestamp: TimestampData::EMPTY,
    delegation_request: 0,

    rd_or_mem_word_read_value: 0,
    rd_or_mem_word_write_value: 0,
    rd_or_mem_word_address: RegIndexOrMemWordIndex::EMPTY,
    rd_or_mem_read_timestamp: TimestampData::EMPTY,

    non_determinism_read: 0,
};

// Total size of per-cycle data: 4 + 1 + 6 + 4 + 4 + 6 + 4 + 4 + 4 + 6 + 4 + 4 + 2 = 53 bytes per cycle
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[serde(
    bound = "C: serde::Serialize + serde::de::DeserializeOwned, Vec<SingleCycleTracingData, A>: serde::Serialize + serde::de::DeserializeOwned"
)]
pub struct CycleData<C: MachineConfig, A: GoodAllocator = Global> {
    // we reshuffle fields to move all bytes into a separate structure
    pub cycles_traced: usize,
    pub per_cycle_data: Vec<SingleCycleTracingData, A>,
    pub num_cycles_chunk_size: usize,
    _marker: std::marker::PhantomData<C>,
}

impl<C: MachineConfig, A: GoodAllocator> CycleData<C, A> {
    pub fn dummy() -> Self {
        Self {
            cycles_traced: 0,
            per_cycle_data: Vec::new_in(A::default()),
            num_cycles_chunk_size: 0,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn new_with_cycles_capacity(num_cycles: usize) -> Self {
        let capacity = num_cycles + 1;
        assert!(capacity.is_power_of_two());
        Self {
            cycles_traced: 0,
            per_cycle_data: Vec::with_capacity_in(capacity, A::default()),
            num_cycles_chunk_size: num_cycles,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn assert_at_capacity(&self) {
        assert_eq!(self.per_cycle_data.len(), self.num_cycles_chunk_size);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(transparent)]
pub struct RegIndexOrMemWordIndex(u32);

impl Default for RegIndexOrMemWordIndex {
    #[inline(always)]
    fn default() -> Self {
        Self::register(0)
    }
}

impl RegIndexOrMemWordIndex {
    pub const EMPTY: Self = Self(0);

    const IS_RAM_MASK: u32 = 0x80000000;

    #[inline(always)]
    pub const fn register(index: u8) -> Self {
        Self(index as u32)
    }

    #[inline(always)]
    pub const fn memory(absolute_address: u32) -> Self {
        debug_assert!(absolute_address % 4 == 0);
        Self((absolute_address >> 2) | Self::IS_RAM_MASK)
    }

    #[inline(always)]
    pub const fn as_u32_formal_address(&self) -> u32 {
        if self.0 & Self::IS_RAM_MASK > 0 {
            self.0 << 2
        } else {
            self.0
        }
    }

    #[inline(always)]
    pub const fn is_register(&self) -> bool {
        self.0 & Self::IS_RAM_MASK == 0
    }

    #[inline(always)]
    pub const fn is_ram(&self) -> bool {
        self.0 & Self::IS_RAM_MASK > 0
    }
}

#[derive(Clone, Debug)]
pub struct RamTracingData<const TRACE_FOR_TEARDOWNS: bool> {
    pub register_last_live_timestamps: [TimestampScalar; 32],
    pub ram_words_last_live_timestamps: Vec<TimestampScalar>,
    pub access_bitmask: Vec<usize>,
    pub num_touched_ram_cells: usize,
    pub rom_bound: usize,
}

impl<const TRACE_FOR_TEARDOWNS: bool> RamTracingData<TRACE_FOR_TEARDOWNS> {
    pub fn new_for_ram_size_and_rom_bound(ram_size: usize, rom_bound: usize) -> Self {
        assert!(ram_size % 4 == 0);
        assert!(rom_bound % 4 == 0);

        let num_words = ram_size / 4;
        let mut num_bitmask_words = num_words / (usize::BITS as usize);
        if num_words % (usize::BITS as usize) != 0 {
            num_bitmask_words += 1;
        }

        Self {
            register_last_live_timestamps: [0; 32],
            ram_words_last_live_timestamps: vec![0; num_words],
            access_bitmask: vec![0; num_bitmask_words],
            num_touched_ram_cells: 0,
            rom_bound,
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

        if TRACE_FOR_TEARDOWNS {
            // mark memory slot as touched
            let bookkeeping_word_idx = (phys_word_idx / usize::BITS) as usize;
            let bit_idx = phys_word_idx % usize::BITS;
            unsafe {
                let is_new_cell = (*self.access_bitmask.get_unchecked(bookkeeping_word_idx)
                    & (1 << bit_idx))
                    == 0;
                *self.access_bitmask.get_unchecked_mut(bookkeeping_word_idx) |= 1 << bit_idx;
                self.num_touched_ram_cells += is_new_cell as usize;
            }
        }

        read_timestamp
    }
}

pub struct DelegationTracingData<A: GoodAllocator = Global> {
    pub current_per_type_logs: HashMap<u16, DelegationWitness<A>>,
    pub num_traced_registers: u32,
    pub mem_reads_offset: usize,
    pub mem_writes_offset: usize,
    pub all_per_type_logs: HashMap<u16, Vec<DelegationWitness<A>>>,
    pub delegation_witness_factories: HashMap<u16, Box<dyn Fn() -> DelegationWitness<A>>>,
}

pub struct GPUFriendlyTracer<
    C: MachineConfig = IMStandardIsaConfig,
    A: GoodAllocator = Global,
    const TRACE_FOR_TEARDOWNS: bool = true,
    const TRACE_FOR_PROVING: bool = true,
    const TRACE_DELEGATIONS: bool = true,
> {
    pub bookkeeping_aux_data: RamTracingData<TRACE_FOR_TEARDOWNS>,
    pub trace_chunk: CycleData<C, A>,
    pub traced_chunks: Vec<CycleData<C, A>>, // just in Global
    pub delegation_tracer: DelegationTracingData<A>,
    pub chunk_size: usize,
    pub current_timestamp: TimestampScalar,
}

const RS1_ACCESS_IDX: TimestampScalar = 0;
const RS2_ACCESS_IDX: TimestampScalar = 1;
const RD_ACCESS_IDX: TimestampScalar = 2;
const DELEGATION_ACCESS_IDX: TimestampScalar = 3;

const RAM_READ_ACCESS_IDX: TimestampScalar = RS2_ACCESS_IDX;
const RAM_WRITE_ACCESS_IDX: TimestampScalar = RD_ACCESS_IDX;

impl<
        C: MachineConfig,
        A: GoodAllocator,
        const TRACE_FOR_TEARDOWNS: bool,
        const TRACE_FOR_PROVING: bool,
        const TRACE_DELEGATIONS: bool,
    > GPUFriendlyTracer<C, A, TRACE_FOR_TEARDOWNS, TRACE_FOR_PROVING, TRACE_DELEGATIONS>
{
    pub fn new(
        initial_timestamp: TimestampScalar,
        bookkeeping_aux_data: RamTracingData<TRACE_FOR_TEARDOWNS>,
        delegation_tracer: DelegationTracingData<A>,
        chunk_size: usize,
        max_num_chunks: usize,
    ) -> Self {
        if TRACE_FOR_PROVING {
            assert!(
                TRACE_FOR_TEARDOWNS,
                "RAM timestamps bookkeeping is needed for full proving witness"
            );
        } else {
            assert!(
                TRACE_FOR_TEARDOWNS,
                "if full witness is not needed then at least teardown must be traced"
            );
        }

        if TRACE_DELEGATIONS {
            assert!(
                TRACE_FOR_TEARDOWNS,
                "RAM timestamps bookkeeping is needed for delegation witness"
            );
        } else {
            assert!(
                TRACE_FOR_TEARDOWNS,
                "if full witness is not needed then at least teardown must be traced"
            );
        }

        assert!((chunk_size + 1).is_power_of_two());

        let trace_chunk = if TRACE_FOR_PROVING == false {
            CycleData::<C, A>::dummy()
        } else {
            CycleData::<C, A>::new_with_cycles_capacity(chunk_size)
        };

        Self {
            bookkeeping_aux_data,
            trace_chunk,
            traced_chunks: Vec::with_capacity(max_num_chunks),
            delegation_tracer,
            chunk_size,
            current_timestamp: initial_timestamp,
        }
    }

    pub fn prepare_for_next_chunk(&mut self, timestamp: TimestampScalar) {
        if TRACE_FOR_PROVING {
            self.trace_chunk.assert_at_capacity();
            let processed = std::mem::replace(
                &mut self.trace_chunk,
                CycleData::<C, A>::new_with_cycles_capacity(self.chunk_size),
            );
            self.traced_chunks.push(processed);
        }
        self.current_timestamp = timestamp;
    }

    pub fn prepare_for_next_chunk_and_return_processed(
        &mut self,
        timestamp: TimestampScalar,
    ) -> CycleData<C, A> {
        assert!(TRACE_FOR_PROVING);
        self.trace_chunk.assert_at_capacity();
        let processed = std::mem::replace(
            &mut self.trace_chunk,
            CycleData::<C, A>::new_with_cycles_capacity(self.chunk_size),
        );
        self.current_timestamp = timestamp;

        processed
    }
}

impl<C: MachineConfig, A: GoodAllocator, const TRACE_DELEGATIONS: bool>
    GPUFriendlyTracer<C, A, true, true, TRACE_DELEGATIONS>
{
    pub fn skip_tracing_chunk(
        self,
        timestamp: TimestampScalar,
    ) -> (
        GPUFriendlyTracer<C, A, true, false, TRACE_DELEGATIONS>,
        CycleData<C, A>,
    ) {
        let Self {
            bookkeeping_aux_data,
            trace_chunk,
            traced_chunks,
            delegation_tracer,
            chunk_size,
            current_timestamp,
        } = self;
        assert!(traced_chunks.is_empty(), "chunks must not be accumulated");
        let _ = current_timestamp;

        trace_chunk.assert_at_capacity();

        let new_self = GPUFriendlyTracer {
            bookkeeping_aux_data,
            trace_chunk: CycleData::<C, A>::dummy(),
            traced_chunks,
            delegation_tracer,
            chunk_size,
            current_timestamp: timestamp,
        };

        (new_self, trace_chunk)
    }
}

impl<C: MachineConfig, A: GoodAllocator, const TRACE_DELEGATIONS: bool>
    GPUFriendlyTracer<C, A, true, false, TRACE_DELEGATIONS>
{
    pub fn start_tracing_chunk(
        self,
        timestamp: TimestampScalar,
    ) -> GPUFriendlyTracer<C, A, true, true, TRACE_DELEGATIONS> {
        let Self {
            bookkeeping_aux_data,
            trace_chunk,
            traced_chunks,
            delegation_tracer,
            chunk_size,
            current_timestamp,
        } = self;
        assert!(traced_chunks.is_empty(), "chunks must not be accumulated");
        let _ = current_timestamp;
        let _ = trace_chunk;

        GPUFriendlyTracer {
            bookkeeping_aux_data,
            trace_chunk: CycleData::<C, A>::new_with_cycles_capacity(self.chunk_size),
            traced_chunks,
            delegation_tracer,
            chunk_size,
            current_timestamp: timestamp,
        }
    }
}

impl<
        C: MachineConfig,
        A: GoodAllocator,
        const TRACE_FOR_TEARDOWNS: bool,
        const TRACE_FOR_PROVING: bool,
        const TRACE_DELEGATIONS: bool,
    > Tracer<C>
    for GPUFriendlyTracer<C, A, TRACE_FOR_TEARDOWNS, TRACE_FOR_PROVING, TRACE_DELEGATIONS>
{
    #[inline(always)]
    fn at_cycle_start(&mut self, current_state: &RiscV32State<C>) {
        if TRACE_FOR_PROVING {
            unsafe {
                self.trace_chunk
                    .per_cycle_data
                    .push_within_capacity(EMPTY_SINGLE_CYCLE_TRACING_DATA)
                    .unwrap_unchecked();
                self.trace_chunk
                    .per_cycle_data
                    .last_mut()
                    .unwrap_unchecked()
                    .pc = current_state.pc;
            }
        }
    }

    #[inline(always)]
    fn at_cycle_start_ext(&mut self, current_state: &state_new::RiscV32StateForUnrolledProver<C>) {
        if TRACE_FOR_PROVING {
            unsafe {
                self.trace_chunk
                    .per_cycle_data
                    .push_within_capacity(EMPTY_SINGLE_CYCLE_TRACING_DATA)
                    .unwrap_unchecked();
                self.trace_chunk
                    .per_cycle_data
                    .last_mut()
                    .unwrap_unchecked()
                    .pc = current_state.pc;
            }
        }
    }

    #[inline(always)]
    fn at_cycle_end(&mut self, _current_state: &RiscV32State<C>) {
        self.current_timestamp += TIMESTAMP_STEP;
        self.trace_chunk.cycles_traced += 1;
    }

    #[inline(always)]
    fn at_cycle_end_ext(&mut self, _current_state: &state_new::RiscV32StateForUnrolledProver<C>) {
        self.current_timestamp += TIMESTAMP_STEP;
        self.trace_chunk.cycles_traced += 1;
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
            .bookkeeping_aux_data
            .mark_register_use(reg_idx, write_timestamp);

        unsafe {
            if TRACE_FOR_PROVING {
                let dst = self
                    .trace_chunk
                    .per_cycle_data
                    .last_mut()
                    .unwrap_unchecked();
                dst.rs1_read_value = read_value;
                dst.rs1_read_timestamp = TimestampData::from_scalar(read_timestamp);
                dst.rs1_reg_idx = reg_idx as u16;
            }
        }
    }

    #[inline(always)]
    fn trace_rs2_read(&mut self, reg_idx: u32, read_value: u32) {
        debug_assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);

        let write_timestamp = self.current_timestamp + RS2_ACCESS_IDX;

        let read_timestamp = self
            .bookkeeping_aux_data
            .mark_register_use(reg_idx, write_timestamp);

        // NOTE: we reuse this access for RAM LOAD, but it's not traced if LOAD op happens

        unsafe {
            if TRACE_FOR_PROVING {
                let dst = self
                    .trace_chunk
                    .per_cycle_data
                    .last_mut()
                    .unwrap_unchecked();
                dst.rs2_or_mem_word_read_value = read_value;
                dst.rs2_or_mem_word_address = RegIndexOrMemWordIndex::register(reg_idx as u8);
                dst.rs2_or_mem_read_timestamp = TimestampData::from_scalar(read_timestamp);
            }
        }
    }

    #[inline(always)]
    fn trace_rd_write(&mut self, reg_idx: u32, read_value: u32, written_value: u32) {
        debug_assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);

        // this happens only if RAM write didn't happen (and opcodes like BRANCH write 0 into x0)

        let write_timestamp = self.current_timestamp + RD_ACCESS_IDX;

        let read_timestamp = self
            .bookkeeping_aux_data
            .mark_register_use(reg_idx, write_timestamp);

        unsafe {
            if TRACE_FOR_PROVING {
                let dst = self
                    .trace_chunk
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
    }

    #[inline(always)]
    fn trace_non_determinism_read(&mut self, read_value: u32) {
        debug_assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);

        unsafe {
            if TRACE_FOR_PROVING {
                let dst = self
                    .trace_chunk
                    .per_cycle_data
                    .last_mut()
                    .unwrap_unchecked();
                dst.non_determinism_read = read_value;
            }
        }
    }

    #[inline(always)]
    fn trace_non_determinism_write(&mut self, _written_value: u32) {
        // do nothing
    }

    #[inline(always)]
    fn trace_ram_read(&mut self, phys_address: u64, read_value: u32) {
        debug_assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);
        assert!(phys_address < (1u64 << 32));
        assert_eq!(phys_address % 4, 0);

        let (address, read_value) = if phys_address < self.bookkeeping_aux_data.rom_bound as u64 {
            // ROM read, substituted as read 0 from 0
            (0, 0)
        } else {
            (phys_address, read_value)
        };

        let write_timestamp = self.current_timestamp + RAM_READ_ACCESS_IDX;

        let phys_word_idx = address / 4;
        let read_timestamp = self
            .bookkeeping_aux_data
            .mark_ram_slot_use(phys_word_idx as u32, write_timestamp);

        if TRACE_FOR_PROVING {
            unsafe {
                let dst = self
                    .trace_chunk
                    .per_cycle_data
                    .last_mut()
                    .unwrap_unchecked();
                // record
                dst.rs2_or_mem_word_read_value = read_value;
                dst.rs2_or_mem_word_address = RegIndexOrMemWordIndex::memory(address as u32);
                dst.rs2_or_mem_read_timestamp = TimestampData::from_scalar(read_timestamp);
            }
        }
    }

    #[inline(always)]
    fn trace_ram_read_write(&mut self, phys_address: u64, read_value: u32, written_value: u32) {
        debug_assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);
        assert!(phys_address < (1u64 << 32));
        assert_eq!(phys_address % 4, 0);

        assert!(
            phys_address >= self.bookkeeping_aux_data.rom_bound as u64,
            "Cannot write to ROM"
        );

        // RAM write happens BEFORE rd write

        let write_timestamp = self.current_timestamp + RAM_WRITE_ACCESS_IDX;

        let phys_word_idx = phys_address / 4;
        let read_timestamp = self
            .bookkeeping_aux_data
            .mark_ram_slot_use(phys_word_idx as u32, write_timestamp);

        if TRACE_FOR_PROVING {
            // record
            unsafe {
                let dst = self
                    .trace_chunk
                    .per_cycle_data
                    .last_mut()
                    .unwrap_unchecked();
                dst.rd_or_mem_word_read_value = read_value;
                dst.rd_or_mem_word_write_value = written_value;
                dst.rd_or_mem_word_address = RegIndexOrMemWordIndex::memory(phys_address as u32);
                dst.rd_or_mem_read_timestamp = TimestampData::from_scalar(read_timestamp);
            }
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
        assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);
        assert_eq!(indirect_read_addresses.len(), indirect_reads.len());
        assert_eq!(indirect_write_addresses.len(), indirect_writes.len());

        let write_timestamp = self.current_timestamp + DELEGATION_ACCESS_IDX;

        if TRACE_DELEGATIONS {
            let delegation_type = access_id as u16;
            let current_tracer = self
                .delegation_tracer
                .current_per_type_logs
                .entry(delegation_type)
                .or_insert_with(|| {
                    let new_tracer = (self
                        .delegation_tracer
                        .delegation_witness_factories
                        .get(&delegation_type)
                        .unwrap())();

                    new_tracer
                });

            assert_eq!(current_tracer.base_register_index, base_register);

            unsafe {
                if TRACE_FOR_PROVING {
                    // mark as delegation
                    let dst = self
                        .trace_chunk
                        .per_cycle_data
                        .last_mut()
                        .unwrap_unchecked();
                    dst.delegation_request = delegation_type;
                }

                // trace register part
                let mut register_index = base_register;
                for dst in register_accesses.iter_mut() {
                    let read_timestamp = self
                        .bookkeeping_aux_data
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
                        .bookkeeping_aux_data
                        .mark_ram_slot_use(phys_word_idx as u32, write_timestamp);

                    dst.timestamp = TimestampData::from_scalar(read_timestamp);
                }

                for (phys_address, dst) in indirect_write_addresses
                    .iter()
                    .zip(indirect_writes.iter_mut())
                {
                    let phys_address = *phys_address;
                    let phys_word_idx = phys_address / 4;

                    let read_timestamp = self
                        .bookkeeping_aux_data
                        .mark_ram_slot_use(phys_word_idx as u32, write_timestamp);

                    dst.timestamp = TimestampData::from_scalar(read_timestamp);
                }
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

            // swap if needed
            // assert that all lengths are the same
            current_tracer.assert_consistency();
            let should_replace = current_tracer.at_capacity();
            if should_replace {
                let new_tracer = (self
                    .delegation_tracer
                    .delegation_witness_factories
                    .get(&delegation_type)
                    .unwrap())();
                let current_tracer = core::mem::replace(
                    self.delegation_tracer
                        .current_per_type_logs
                        .get_mut(&delegation_type)
                        .unwrap(),
                    new_tracer,
                );
                self.delegation_tracer
                    .all_per_type_logs
                    .entry(delegation_type)
                    .or_insert(vec![])
                    .push(current_tracer);
            }
        } else {
            // we only need to mark RAM and register use

            // trace register part
            let mut register_index = base_register;
            for _reg in register_accesses.iter() {
                let _read_timestamp = self
                    .bookkeeping_aux_data
                    .mark_register_use(register_index, write_timestamp);

                register_index += 1;
            }

            // formal reads and writes
            for phys_address in indirect_read_addresses.iter() {
                let phys_address = *phys_address;
                let phys_word_idx = phys_address / 4;

                let _read_timestamp = self
                    .bookkeeping_aux_data
                    .mark_ram_slot_use(phys_word_idx as u32, write_timestamp);
            }

            for phys_address in indirect_write_addresses.iter() {
                let phys_address = *phys_address;
                let phys_word_idx = phys_address / 4;

                let _read_timestamp = self
                    .bookkeeping_aux_data
                    .mark_ram_slot_use(phys_word_idx as u32, write_timestamp);
            }
        }
    }
}
