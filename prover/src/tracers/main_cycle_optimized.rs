// - rs1 is register and read only
// - rs2 is register or RAM read
// - rd is register or RAM write

use std::alloc::Global;
use std::collections::HashMap;

use crate::tracers::delegation::DelegationWitness;
use cs::definitions::{
    timestamp_from_absolute_cycle_index, TimestampData, TimestampScalar, TIMESTAMP_STEP,
};
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
    pub fn new_with_cycles_capacity(
        _initial_cycle_counter: usize,
        _initial_state: &RiscV32State<C>,
        num_cycles: usize,
    ) -> Self {
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
pub struct RamTracingData {
    pub register_last_live_timestamps: [TimestampScalar; 32],
    pub ram_words_last_live_timestamps: Vec<TimestampScalar>,
    pub access_bitmask: Vec<usize>,
    pub num_touched_ram_cells: usize,
    pub rom_bound: usize,
}

impl RamTracingData {
    pub fn new_for_ram_size_and_rom_bound(ram_size: usize, rom_bound: usize) -> Self {
        assert!(ram_size % 4 == 0);
        assert!(rom_bound % 4 == 0);

        let num_words = ram_size / 4;
        let num_bitmask_words = num_words / (usize::BITS as usize);

        Self {
            register_last_live_timestamps: [0; 32],
            ram_words_last_live_timestamps: vec![0; num_words],
            access_bitmask: vec![0; num_bitmask_words],
            num_touched_ram_cells: 0,
            rom_bound,
        }
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

pub struct GPUFriendlyTracer<C: MachineConfig = IMStandardIsaConfig, A: GoodAllocator = Global> {
    pub bookkeeping_aux_data: RamTracingData,
    pub cycles_passed: usize,
    pub current_timestamp: TimestampScalar,
    pub current_tracing_delegation_type: Option<u16>,
    pub current_tracing_delegation_cycle_timestamp: Option<TimestampScalar>,
    pub trace_chunk: CycleData<C, A>,
    pub delegation_tracer: DelegationTracingData<A>,
}

const RS1_ACCESS_IDX: TimestampScalar = 0;
const RS2_ACCESS_IDX: TimestampScalar = 1;
const RD_ACCESS_IDX: TimestampScalar = 2;
const DELEGATION_ACCESS_IDX: TimestampScalar = 3;

const RAM_READ_ACCESS_IDX: TimestampScalar = RS2_ACCESS_IDX;
const RAM_WRITE_ACCESS_IDX: TimestampScalar = RD_ACCESS_IDX;

impl<C: MachineConfig, A: GoodAllocator> Tracer<C> for GPUFriendlyTracer<C, A> {
    type AuxData = (usize, RamTracingData, DelegationTracingData<A>);

    fn create_from_initial_state_for_num_cycles_and_chunk_size(
        state: &RiscV32State<C>,
        aux_data: Self::AuxData,
        _num_cycles: usize,
        chunk_size: usize,
    ) -> Self {
        assert!((chunk_size + 1).is_power_of_two());
        let (initial_cycle_counter, ram_tracer, delegation_tracer) = aux_data;

        let trace_chunk =
            CycleData::<C, A>::new_with_cycles_capacity(initial_cycle_counter, state, chunk_size);
        let timestamp = timestamp_from_absolute_cycle_index(initial_cycle_counter, chunk_size);

        let new = Self {
            trace_chunk,
            bookkeeping_aux_data: ram_tracer,
            delegation_tracer,
            cycles_passed: initial_cycle_counter,
            current_timestamp: timestamp,
            current_tracing_delegation_type: None,
            current_tracing_delegation_cycle_timestamp: None,
        };

        new
    }

    #[inline(always)]
    fn at_cycle_start(&mut self, current_state: &RiscV32State<C>) {
        unsafe {
            self.trace_chunk
                .per_cycle_data
                .push_within_capacity(SingleCycleTracingData {
                    pc: current_state.pc,
                    ..Default::default()
                })
                .unwrap_unchecked();
        }
    }

    #[inline(always)]
    fn at_cycle_end(&mut self, _current_state: &RiscV32State<C>) {
        self.cycles_passed += 1;
        let chunk_capacity = self.trace_chunk.num_cycles_chunk_size;
        self.current_timestamp =
            timestamp_from_absolute_cycle_index(self.cycles_passed, chunk_capacity);
        self.trace_chunk.cycles_traced += 1;
    }

    #[inline(always)]
    fn trace_opcode_read(&mut self, _phys_address: u64, _read_value: u32) {
        // Nothing, opcodes are expected to be read from ROM
    }

    #[inline(always)]
    fn trace_rs1_read(&mut self, reg_idx: u32, read_value: u32) {
        assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);

        let write_timestamp = self.current_timestamp + RS1_ACCESS_IDX;

        unsafe {
            let read_timestamp = core::mem::replace(
                self.bookkeeping_aux_data
                    .register_last_live_timestamps
                    .get_unchecked_mut(reg_idx as usize),
                write_timestamp,
            );
            debug_assert!(read_timestamp < write_timestamp);

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

    #[inline(always)]
    fn trace_rs2_read(&mut self, reg_idx: u32, read_value: u32) {
        assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);

        let write_timestamp = self.current_timestamp + RS2_ACCESS_IDX;

        // This always(!) happens before RAM access even if it's merged
        // BUT we should not forget to "rollback" it if we actually perform LOAD
        unsafe {
            let read_timestamp = core::mem::replace(
                self.bookkeeping_aux_data
                    .register_last_live_timestamps
                    .get_unchecked_mut(reg_idx as usize),
                write_timestamp,
            );
            debug_assert!(read_timestamp < write_timestamp);

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

    #[inline(always)]
    fn trace_rd_write(&mut self, reg_idx: u32, read_value: u32, written_value: u32) {
        assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);

        unsafe {
            let dst = self
                .trace_chunk
                .per_cycle_data
                .last_mut()
                .unwrap_unchecked();
            // this happens AFTER ram write (if RAM write happens at all)
            if dst.rd_or_mem_word_address.is_ram() {
                // we had RAM write, so just do nothing
                assert_eq!(reg_idx, 0);
                assert_eq!(read_value, 0);
                assert_eq!(written_value, 0);
                return;
            }

            let mut written_value = written_value;
            if reg_idx == 0 {
                assert_eq!(read_value, 0);
                // we can flush anything here
                written_value = 0;
            }

            let write_timestamp = self.current_timestamp + RD_ACCESS_IDX;

            let read_timestamp = core::mem::replace(
                self.bookkeeping_aux_data
                    .register_last_live_timestamps
                    .get_unchecked_mut(reg_idx as usize),
                write_timestamp,
            );
            debug_assert!(read_timestamp < write_timestamp);

            dst.rd_or_mem_word_read_value = read_value;
            dst.rd_or_mem_word_write_value = written_value;
            dst.rd_or_mem_word_address = RegIndexOrMemWordIndex::register(reg_idx as u8);
            dst.rd_or_mem_read_timestamp = TimestampData::from_scalar(read_timestamp);
        }
    }

    #[inline(always)]
    fn trace_non_determinism_read(&mut self, read_value: u32) {
        assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);

        unsafe {
            let dst = self
                .trace_chunk
                .per_cycle_data
                .last_mut()
                .unwrap_unchecked();
            dst.non_determinism_read = read_value;
        }
    }

    #[inline(always)]
    fn trace_non_determinism_write(&mut self, _written_value: u32) {
        // do nothing
    }

    #[inline(always)]
    fn trace_ram_read(&mut self, phys_address: u64, read_value: u32) {
        assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);

        assert_eq!(phys_address % 4, 0);

        let (address, read_value) = if phys_address < self.bookkeeping_aux_data.rom_bound as u64 {
            // ROM read, substituted as read 0 from 0
            (0, 0)
        } else {
            (phys_address, read_value)
        };

        let write_timestamp = self.current_timestamp + RAM_READ_ACCESS_IDX;

        unsafe {
            // RS2 formal read would happen before,
            // so we SHOULD rollback it it terms of last accessed timestamp

            let dst = self
                .trace_chunk
                .per_cycle_data
                .last_mut()
                .unwrap_unchecked();
            assert!(dst.rs2_or_mem_word_address.is_register());
            let reg_idx = dst.rs2_or_mem_word_address.as_u32_formal_address();
            let formal_read_timestamp = dst.rs2_or_mem_read_timestamp.as_scalar();
            *self
                .bookkeeping_aux_data
                .register_last_live_timestamps
                .get_unchecked_mut(reg_idx as usize) = formal_read_timestamp;

            // and now we can modify this access to reflect LOAD
            let phys_word_idx = address / 4;
            let read_timestamp = core::mem::replace(
                &mut self.bookkeeping_aux_data.ram_words_last_live_timestamps
                    [phys_word_idx as usize],
                write_timestamp,
            );
            debug_assert!(read_timestamp < write_timestamp);
            // mark memory slot as touched
            let bookkeeping_word_idx = (phys_word_idx as u32 / usize::BITS) as usize;
            let bit_idx = phys_word_idx as u32 % usize::BITS;
            let is_new_cell = (self.bookkeeping_aux_data.access_bitmask[bookkeeping_word_idx]
                & (1 << bit_idx))
                == 0;
            self.bookkeeping_aux_data.access_bitmask[bookkeeping_word_idx] |= 1 << bit_idx;
            self.bookkeeping_aux_data.num_touched_ram_cells += is_new_cell as usize;

            // record
            dst.rs2_or_mem_word_read_value = read_value;
            dst.rs2_or_mem_word_address = RegIndexOrMemWordIndex::memory(address as u32);
            dst.rs2_or_mem_read_timestamp = TimestampData::from_scalar(read_timestamp);
        }
    }

    #[inline(always)]
    fn trace_ram_read_write(&mut self, phys_address: u64, read_value: u32, written_value: u32) {
        assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);

        assert_eq!(phys_address % 4, 0);

        assert!(
            phys_address >= self.bookkeeping_aux_data.rom_bound as u64,
            "Cannot write to ROM"
        );

        // RAM write happens BEFORE rd write

        let write_timestamp = self.current_timestamp + RAM_WRITE_ACCESS_IDX;

        let phys_word_idx = phys_address / 4;
        let read_timestamp = core::mem::replace(
            &mut self.bookkeeping_aux_data.ram_words_last_live_timestamps[phys_word_idx as usize],
            write_timestamp,
        );
        debug_assert!(read_timestamp < write_timestamp);

        // mark memory slot as touched
        let bookkeeping_word_idx = (phys_word_idx as u32 / usize::BITS) as usize;
        let bit_idx = phys_word_idx as u32 % usize::BITS;
        let is_new_cell =
            (self.bookkeeping_aux_data.access_bitmask[bookkeeping_word_idx] & (1 << bit_idx)) == 0;
        self.bookkeeping_aux_data.access_bitmask[bookkeeping_word_idx] |= 1 << bit_idx;
        self.bookkeeping_aux_data.num_touched_ram_cells += is_new_cell as usize;

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

        let write_timestamp = self.current_timestamp + DELEGATION_ACCESS_IDX;
        unsafe {
            // mark as delegation
            let dst = self
                .trace_chunk
                .per_cycle_data
                .last_mut()
                .unwrap_unchecked();
            dst.delegation_request = delegation_type;

            // trace register part
            let mut register_index = base_register;
            for dst in register_accesses.iter_mut() {
                let read_timestamp = core::mem::replace(
                    self.bookkeeping_aux_data
                        .register_last_live_timestamps
                        .get_unchecked_mut(register_index as usize),
                    write_timestamp,
                );
                debug_assert!(read_timestamp < write_timestamp);
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
                let read_timestamp = core::mem::replace(
                    &mut self.bookkeeping_aux_data.ram_words_last_live_timestamps
                        [phys_word_idx as usize],
                    write_timestamp,
                );
                debug_assert!(
                    read_timestamp < write_timestamp,
                    "read timestamp {} is not less than write timestamp {} for memory address {}",
                    read_timestamp,
                    write_timestamp,
                    phys_address
                );
                // mark memory slot as touched
                let bookkeeping_word_idx = (phys_word_idx as u32 / usize::BITS) as usize;
                let bit_idx = phys_word_idx as u32 % usize::BITS;
                let is_new_cell = (self.bookkeeping_aux_data.access_bitmask[bookkeeping_word_idx]
                    & (1 << bit_idx))
                    == 0;
                self.bookkeeping_aux_data.access_bitmask[bookkeeping_word_idx] |= 1 << bit_idx;
                self.bookkeeping_aux_data.num_touched_ram_cells += is_new_cell as usize;

                dst.timestamp = TimestampData::from_scalar(read_timestamp);
            }

            for (phys_address, dst) in indirect_write_addresses
                .iter()
                .zip(indirect_writes.iter_mut())
            {
                let phys_address = *phys_address;
                let phys_word_idx = phys_address / 4;
                let read_timestamp = core::mem::replace(
                    &mut self.bookkeeping_aux_data.ram_words_last_live_timestamps
                        [phys_word_idx as usize],
                    write_timestamp,
                );
                debug_assert!(
                    read_timestamp < write_timestamp,
                    "read timestamp {} is not less than write timestamp {} for memory address {}",
                    read_timestamp,
                    write_timestamp,
                    phys_address
                );
                // mark memory slot as touched
                let bookkeeping_word_idx = (phys_word_idx as u32 / usize::BITS) as usize;
                let bit_idx = phys_word_idx as u32 % usize::BITS;
                let is_new_cell = (self.bookkeeping_aux_data.access_bitmask[bookkeeping_word_idx]
                    & (1 << bit_idx))
                    == 0;
                self.bookkeeping_aux_data.access_bitmask[bookkeeping_word_idx] |= 1 << bit_idx;
                self.bookkeeping_aux_data.num_touched_ram_cells += is_new_cell as usize;

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
    }
}
