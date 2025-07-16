use crate::fft::GoodAllocator;
use risc_v_simulator::abstractions::tracer::RegisterOrIndirectReadData;
use risc_v_simulator::abstractions::tracer::RegisterOrIndirectReadWriteData;
use std::alloc::Global;
use std::collections::HashMap;

use crate::tracers::main_cycle_optimized::DelegationTracingData;
use crate::tracers::main_cycle_optimized::RamTracingData;
use cs::definitions::{TimestampData, TimestampScalar, TIMESTAMP_STEP};
use risc_v_simulator::cycle::IMStandardIsaConfig;
use risc_v_simulator::cycle::MachineConfig;
use risc_v_simulator::machine_mode_only_unrolled::*;

const NUM_OPCODE_FAMILIES_NO_RAM: usize = 4;
const NUM_OPCODE_FAMILIES_WITH_RAM: usize = 2;

pub struct NonMemTracingFamilyChunk {
    pub num_cycles: usize,
    pub data: Vec<NonMemoryOpcodeTracingDataWithTimestamp>,
}

impl NonMemTracingFamilyChunk {
    pub fn new_for_num_cycles(num_cycles: usize) -> Self {
        let capacity = num_cycles + 1;
        assert!(capacity.is_power_of_two());

        Self {
            num_cycles,
            data: Vec::with_capacity(capacity),
        }
    }
}

pub struct MemTracingFamilyChunk {
    pub num_cycles: usize,
    pub data: Vec<MemoryOpcodeTracingDataWithTimestamp>,
}

impl MemTracingFamilyChunk {
    pub fn new_for_num_cycles(num_cycles: usize) -> Self {
        let capacity = num_cycles + 1;
        assert!(capacity.is_power_of_two());

        Self {
            num_cycles,
            data: Vec::with_capacity(capacity),
        }
    }
}

pub struct UnrolledGPUFriendlyTracer<
    C: MachineConfig = IMStandardIsaConfig,
    A: GoodAllocator = Global,
    const TRACE_FOR_TEARDOWNS: bool = true,
    const TRACE_FOR_PROVING: bool = true,
    const TRACE_DELEGATIONS: bool = true,
> {
    pub bookkeeping_aux_data: RamTracingData<TRACE_FOR_TEARDOWNS>,
    pub current_timestamp: TimestampScalar,
    pub current_family_chunks: [NonMemTracingFamilyChunk; NUM_OPCODE_FAMILIES_NO_RAM],
    pub completed_family_chunks: HashMap<u8, Vec<NonMemTracingFamilyChunk>>,
    pub current_mem_family_chunk: MemTracingFamilyChunk,
    pub completed_mem_family_chunks: Vec<MemTracingFamilyChunk>,
    pub opcode_family_chunk_factories: HashMap<u8, Box<dyn Fn() -> NonMemTracingFamilyChunk>>,
    pub mem_family_chunk_factory: Box<dyn Fn() -> MemTracingFamilyChunk>,
    pub delegation_tracer: DelegationTracingData,
    pub _marker: core::marker::PhantomData<C>,
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
    > UnrolledGPUFriendlyTracer<C, A, TRACE_FOR_TEARDOWNS, TRACE_FOR_PROVING, TRACE_DELEGATIONS>
{
    pub fn new(
        bookkeeping_aux_data: RamTracingData<TRACE_FOR_TEARDOWNS>,
        opcode_family_chunk_factories: HashMap<u8, Box<dyn Fn() -> NonMemTracingFamilyChunk>>,
        mem_family_chunk_factory: Box<dyn Fn() -> MemTracingFamilyChunk>,
        delegation_tracer: DelegationTracingData,
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

        let current_family_chunks = std::array::from_fn(|i| {
            let family = (i + 1) as u8;
            (opcode_family_chunk_factories[&family])()
        });
        let current_mem_family_chunk = (mem_family_chunk_factory)();

        Self {
            bookkeeping_aux_data,
            current_timestamp: INITIAL_TIMESTAMP,
            current_family_chunks,
            completed_family_chunks: HashMap::with_capacity(4),
            current_mem_family_chunk,
            completed_mem_family_chunks: Vec::new(),
            opcode_family_chunk_factories,
            mem_family_chunk_factory,
            delegation_tracer,
            _marker: core::marker::PhantomData,
        }
    }

    #[inline]
    fn update_reg_access_timestamp<const ACCESS_IDX: u64>(
        &mut self,
        reg_idx: u8,
        dst: &mut TimestampData,
    ) {
        let write_timestamp = self.current_timestamp + ACCESS_IDX;

        let read_timestamp = self
            .bookkeeping_aux_data
            .mark_register_use(reg_idx as u32, write_timestamp);

        if TRACE_FOR_PROVING {
            *dst = TimestampData::from_scalar(read_timestamp);
        }
    }

    #[inline]
    fn update_ram_access_timestmap<const ACCESS_IDX: u64>(
        &mut self,
        phys_address: u64,
        is_write: bool,
        dst: &mut TimestampData,
    ) {
        assert_eq!(phys_address % 4, 0);

        let address = if phys_address < self.bookkeeping_aux_data.rom_bound as u64 {
            assert!(is_write == false);
            // ROM read, substituted as read 0 from 0
            0
        } else {
            phys_address
        };

        let phys_word_idx = address / 4;
        let write_timestamp = self.current_timestamp + ACCESS_IDX;

        let read_timestamp = self
            .bookkeeping_aux_data
            .mark_ram_slot_use(phys_word_idx as u32, write_timestamp);

        if TRACE_FOR_PROVING {
            *dst = TimestampData::from_scalar(read_timestamp);
        }
    }
}

// const RS1_ACCESS_IDX: TimestampScalar = 0;
// const RS2_ACCESS_IDX: TimestampScalar = 1;
// const RD_ACCESS_IDX: TimestampScalar = 2;
// const DELEGATION_ACCESS_IDX: TimestampScalar = 3;

// const RAM_READ_ACCESS_IDX: TimestampScalar = RS2_ACCESS_IDX;
// const RAM_WRITE_ACCESS_IDX: TimestampScalar = RD_ACCESS_IDX;

impl<
        C: MachineConfig,
        A: GoodAllocator,
        const TRACE_FOR_TEARDOWNS: bool,
        const TRACE_FOR_PROVING: bool,
        const TRACE_DELEGATIONS: bool,
    > UnrolledTracer<C>
    for UnrolledGPUFriendlyTracer<C, A, TRACE_FOR_TEARDOWNS, TRACE_FOR_PROVING, TRACE_DELEGATIONS>
{
    #[inline(always)]
    fn at_cycle_start(&mut self, _current_state: &RiscV32StateForUnrolledProver<C>) {
        // we grow inside of cycles, and have no global state
    }

    #[inline(always)]
    fn at_cycle_end(&mut self, _current_state: &RiscV32StateForUnrolledProver<C>) {
        self.current_timestamp += TIMESTAMP_STEP;
    }

    #[inline(always)]
    fn trace_decoder_step(&mut self, _data: TracingDecoderData) {
        // Nothing - we do not needed it, and just feed corresponding opcode
        // families below
    }

    #[inline]
    fn trace_non_mem_step(&mut self, family: u8, mut data: NonMemoryOpcodeTracingData) {
        let mut rs1_read_timestamp = TimestampData::EMPTY;
        let mut rs2_read_timestamp = TimestampData::EMPTY;
        let mut rd_read_timestamp = TimestampData::EMPTY;

        let (rs1, rs2, rd) = formally_parse_rs1_rs2_rd_props_for_tracer(data.opcode);
        if rd == 0 {
            // easier to re-adjust
            data.rd_value = 0;
        }
        self.update_reg_access_timestamp::<RS1_ACCESS_IDX>(rs1, &mut rs1_read_timestamp);
        self.update_reg_access_timestamp::<RS2_ACCESS_IDX>(rs2, &mut rs2_read_timestamp);
        self.update_reg_access_timestamp::<RD_ACCESS_IDX>(rd, &mut rd_read_timestamp);

        if TRACE_FOR_PROVING {
            let data = NonMemoryOpcodeTracingDataWithTimestamp {
                opcode_data: data,
                rs1_read_timestamp: TimestampData::EMPTY,
                rs2_read_timestamp: TimestampData::EMPTY,
                rd_read_timestamp: TimestampData::EMPTY,
                cycle_timestamp: TimestampData::from_scalar(self.current_timestamp),
            };
            let dst = &mut self.current_family_chunks[family as usize - 1];
            dst.data.push(data);
            if dst.data.len() == dst.num_cycles {
                let next = (self.opcode_family_chunk_factories[&family])();
                let completed = core::mem::replace(dst, next);
                self.completed_family_chunks
                    .entry(family)
                    .or_insert(vec![])
                    .push(completed);
            }
        }
    }

    #[inline]
    fn trace_mem_load_step(&mut self, data: LoadOpcodeTracingData) {
        let mut rs1_read_timestamp = TimestampData::EMPTY;
        let mut rs2_or_ram_read_timestamp = TimestampData::EMPTY;
        let mut rd_or_ram_read_timestamp = TimestampData::EMPTY;

        let (rs1, _, rd) = formally_parse_rs1_rs2_rd_props_for_tracer(data.opcode);
        if rd == 0 {
            debug_assert_eq!(data.rd_value, 0);
        }
        self.update_reg_access_timestamp::<RS1_ACCESS_IDX>(rs1, &mut rs1_read_timestamp);
        self.update_ram_access_timestmap::<RAM_READ_ACCESS_IDX>(
            data.aligned_ram_address as u64,
            false,
            &mut rs2_or_ram_read_timestamp,
        );
        self.update_reg_access_timestamp::<RD_ACCESS_IDX>(rd, &mut rd_or_ram_read_timestamp);

        if TRACE_FOR_PROVING {
            let data = MemoryOpcodeTracingDataWithTimestamp {
                opcode_data: data,
                discr: MEM_LOAD_TRACE_DATA_MARKER,
                rs1_read_timestamp,
                rs2_or_ram_read_timestamp,
                rd_or_ram_read_timestamp,
                cycle_timestamp: TimestampData::from_scalar(self.current_timestamp),
            };
            self.current_mem_family_chunk.data.push(data);
            if self.current_mem_family_chunk.data.len() == self.current_mem_family_chunk.num_cycles
            {
                let next = (self.mem_family_chunk_factory)();
                let completed = core::mem::replace(&mut self.current_mem_family_chunk, next);
                self.completed_mem_family_chunks.push(completed);
            }
        }
    }

    fn trace_mem_store_step(&mut self, data: StoreOpcodeTracingData) {
        let mut rs1_read_timestamp = TimestampData::EMPTY;
        let mut rs2_or_ram_read_timestamp = TimestampData::EMPTY;
        let mut rd_or_ram_read_timestamp = TimestampData::EMPTY;

        let (rs1, rs2, _) = formally_parse_rs1_rs2_rd_props_for_tracer(data.opcode);
        self.update_reg_access_timestamp::<RS1_ACCESS_IDX>(rs1, &mut rs1_read_timestamp);
        self.update_reg_access_timestamp::<RS2_ACCESS_IDX>(rs2, &mut rs2_or_ram_read_timestamp);
        self.update_ram_access_timestmap::<RAM_WRITE_ACCESS_IDX>(
            data.aligned_ram_address as u64,
            true,
            &mut rd_or_ram_read_timestamp,
        );

        if TRACE_FOR_PROVING {
            let data = MemoryOpcodeTracingDataWithTimestamp {
                opcode_data: unsafe { core::mem::transmute(data) },
                discr: MEM_STORE_TRACE_DATA_MARKER,
                rs1_read_timestamp,
                rs2_or_ram_read_timestamp,
                rd_or_ram_read_timestamp,
                cycle_timestamp: TimestampData::from_scalar(self.current_timestamp),
            };
            self.current_mem_family_chunk.data.push(data);
            if self.current_mem_family_chunk.data.len() == self.current_mem_family_chunk.num_cycles
            {
                let next = (self.mem_family_chunk_factory)();
                let completed = core::mem::replace(&mut self.current_mem_family_chunk, next);
                self.completed_mem_family_chunks.push(completed);
            }
        }
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

        //     assert_eq!(self.current_timestamp % TIMESTAMP_STEP, 0);
        //     assert_eq!(indirect_read_addresses.len(), indirect_reads.len());
        //     assert_eq!(indirect_write_addresses.len(), indirect_writes.len());

        //     let delegation_type = access_id as u16;
        //     let current_tracer = self
        //         .delegation_tracer
        //         .current_per_type_logs
        //         .entry(delegation_type)
        //         .or_insert_with(|| {
        //             let new_tracer = (self
        //                 .delegation_tracer
        //                 .delegation_witness_factories
        //                 .get(&delegation_type)
        //                 .unwrap())();

        //             new_tracer
        //         });

        //     assert_eq!(current_tracer.base_register_index, base_register);

        //     let write_timestamp = self.current_timestamp + DELEGATION_ACCESS_IDX;
        //     unsafe {
        //         // trace register part
        //         let mut register_index = base_register;
        //         for dst in register_accesses.iter_mut() {
        //             let read_timestamp = core::mem::replace(
        //                 self.bookkeeping_aux_data
        //                     .register_last_live_timestamps
        //                     .get_unchecked_mut(register_index as usize),
        //                 write_timestamp,
        //             );
        //             debug_assert!(read_timestamp < write_timestamp);
        //             dst.timestamp = TimestampData::from_scalar(read_timestamp);

        //             register_index += 1;
        //         }

        //         // formal reads and writes

        //         for (phys_address, dst) in indirect_read_addresses
        //             .iter()
        //             .zip(indirect_reads.iter_mut())
        //         {
        //             let phys_address = *phys_address;
        //             let phys_word_idx = phys_address / 4;
        //             let read_timestamp = core::mem::replace(
        //                 &mut self.bookkeeping_aux_data.ram_words_last_live_timestamps
        //                     [phys_word_idx as usize],
        //                 write_timestamp,
        //             );
        //             debug_assert!(
        //                 read_timestamp < write_timestamp,
        //                 "read timestamp {} is not less than write timestamp {} for memory address {}",
        //                 read_timestamp,
        //                 write_timestamp,
        //                 phys_address
        //             );
        //             // mark memory slot as touched
        //             let bookkeeping_word_idx = (phys_word_idx as u32 / usize::BITS) as usize;
        //             let bit_idx = phys_word_idx as u32 % usize::BITS;
        //             let is_new_cell = (self.bookkeeping_aux_data.access_bitmask[bookkeeping_word_idx]
        //                 & (1 << bit_idx))
        //                 == 0;
        //             self.bookkeeping_aux_data.access_bitmask[bookkeeping_word_idx] |= 1 << bit_idx;
        //             self.bookkeeping_aux_data.num_touched_ram_cells += is_new_cell as usize;

        //             dst.timestamp = TimestampData::from_scalar(read_timestamp);
        //         }

        //         for (phys_address, dst) in indirect_write_addresses
        //             .iter()
        //             .zip(indirect_writes.iter_mut())
        //         {
        //             let phys_address = *phys_address;
        //             let phys_word_idx = phys_address / 4;
        //             let read_timestamp = core::mem::replace(
        //                 &mut self.bookkeeping_aux_data.ram_words_last_live_timestamps
        //                     [phys_word_idx as usize],
        //                 write_timestamp,
        //             );
        //             debug_assert!(
        //                 read_timestamp < write_timestamp,
        //                 "read timestamp {} is not less than write timestamp {} for memory address {}",
        //                 read_timestamp,
        //                 write_timestamp,
        //                 phys_address
        //             );
        //             // mark memory slot as touched
        //             let bookkeeping_word_idx = (phys_word_idx as u32 / usize::BITS) as usize;
        //             let bit_idx = phys_word_idx as u32 % usize::BITS;
        //             let is_new_cell = (self.bookkeeping_aux_data.access_bitmask[bookkeeping_word_idx]
        //                 & (1 << bit_idx))
        //                 == 0;
        //             self.bookkeeping_aux_data.access_bitmask[bookkeeping_word_idx] |= 1 << bit_idx;
        //             self.bookkeeping_aux_data.num_touched_ram_cells += is_new_cell as usize;

        //             dst.timestamp = TimestampData::from_scalar(read_timestamp);
        //         }
        //     }

        //     current_tracer
        //         .register_accesses
        //         .extend_from_slice(&*register_accesses);
        //     current_tracer
        //         .indirect_reads
        //         .extend_from_slice(&*indirect_reads);
        //     current_tracer
        //         .indirect_writes
        //         .extend_from_slice(&*indirect_writes);
        //     current_tracer
        //         .write_timestamp
        //         .push_within_capacity(TimestampData::from_scalar(write_timestamp))
        //         .unwrap();

        //     // swap if needed
        //     // assert that all lengths are the same
        //     current_tracer.assert_consistency();
        //     let should_replace = current_tracer.at_capacity();
        //     if should_replace {
        //         let new_tracer = (self
        //             .delegation_tracer
        //             .delegation_witness_factories
        //             .get(&delegation_type)
        //             .unwrap())();
        //         let current_tracer = core::mem::replace(
        //             self.delegation_tracer
        //                 .current_per_type_logs
        //                 .get_mut(&delegation_type)
        //                 .unwrap(),
        //             new_tracer,
        //         );
        //         self.delegation_tracer
        //             .all_per_type_logs
        //             .entry(delegation_type)
        //             .or_insert(vec![])
        //             .push(current_tracer);
        //     }
    }
}
