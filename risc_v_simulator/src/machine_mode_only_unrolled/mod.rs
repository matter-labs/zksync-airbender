// This simulator follows a paradigm of the unrolled cycle circuits

use std::collections::HashMap;
use std::hint::unreachable_unchecked;

mod decoder_utils;
mod utils;
pub use self::decoder_utils::*;
use self::utils::*;
mod tracer;
pub use self::tracer::UnrolledTracer;
use crate::utils::{sign_extend, sign_extend_16, sign_extend_8, zero_extend_16, zero_extend_8};

use crate::abstractions::csr_processor::NoExtraCSRs;
use crate::abstractions::memory::{AccessType, MemorySource};
use crate::abstractions::non_determinism::NonDeterminismCSRSource;
use crate::cycle::state::report_opcode;
use crate::cycle::state::MARKER_CSR;
use crate::cycle::state::NON_DETERMINISM_CSR;
use crate::cycle::state::NUM_REGISTERS;
use crate::cycle::status_registers::TrapReason;
use crate::cycle::IMStandardIsaConfig;
use crate::cycle::MachineConfig;
use crate::mmu::MMUImplementation;

mod delegations;

use crate::cycle::opcode_formats::*;
use cs::definitions::{TimestampData, TimestampScalar, INITIAL_TIMESTAMP, TIMESTAMP_STEP};

// In general we need to output decoder immediate output, but it's easier to just re-parse it in circuits,
// so we just output PC and timestamp
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct TracingDecoderData {
    pub pc: u32,
    // pub timestamp: TimestampData,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct NonMemoryOpcodeTracingData {
    pub initial_pc: u32,
    pub opcode: u32,
    pub rs1_value: u32,
    pub rs2_value: u32,
    pub rd_old_value: u32,
    pub rd_value: u32,
    pub new_pc: u32,
    pub delegation_type: u16,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct LoadOpcodeTracingData {
    pub initial_pc: u32,
    pub opcode: u32,
    pub rs1_value: u32,
    pub aligned_ram_address: u32,
    pub aligned_ram_read_value: u32,
    pub rd_old_value: u32,
    pub rd_value: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct StoreOpcodeTracingData {
    pub initial_pc: u32,
    pub opcode: u32,
    pub rs1_value: u32,
    pub aligned_ram_address: u32,
    pub aligned_ram_old_value: u32,
    pub rs2_value: u32,
    pub aligned_ram_write_value: u32,
}

const _: () = const {
    assert!(
        core::mem::size_of::<LoadOpcodeTracingData>()
            == core::mem::size_of::<StoreOpcodeTracingData>()
    );
    assert!(
        core::mem::align_of::<LoadOpcodeTracingData>()
            == core::mem::align_of::<StoreOpcodeTracingData>()
    );

    ()
};

pub const MEM_LOAD_TRACE_DATA_MARKER: u16 = 0;
pub const MEM_STORE_TRACE_DATA_MARKER: u16 = MEM_LOAD_TRACE_DATA_MARKER + 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct NonMemoryOpcodeTracingDataWithTimestamp {
    pub opcode_data: NonMemoryOpcodeTracingData,
    pub rs1_read_timestamp: TimestampData,
    pub rs2_read_timestamp: TimestampData,
    pub rd_read_timestamp: TimestampData,
    pub cycle_timestamp: TimestampData,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[repr(C)]
pub struct MemoryOpcodeTracingDataWithTimestamp {
    pub opcode_data: LoadOpcodeTracingData,
    pub discr: u16,
    pub rs1_read_timestamp: TimestampData,
    pub rs2_or_ram_read_timestamp: TimestampData,
    pub rd_or_ram_read_timestamp: TimestampData,
    pub cycle_timestamp: TimestampData,
}

impl MemoryOpcodeTracingDataWithTimestamp {
    pub fn initial_pc(&self) -> u32 {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => {
                let as_memstore: &StoreOpcodeTracingData =
                    unsafe { core::mem::transmute(&self.opcode_data) };
                as_memstore.initial_pc
            }
            MEM_LOAD_TRACE_DATA_MARKER => self.opcode_data.initial_pc,
            _ => unreachable!(),
        }
    }

    pub fn as_load_data(&self) -> LoadOpcodeTracingData {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => {
                panic!("is store data");
            }
            MEM_LOAD_TRACE_DATA_MARKER => self.opcode_data,
            _ => unreachable!(),
        }
    }

    pub fn as_store_data(&self) -> StoreOpcodeTracingData {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => unsafe { core::mem::transmute(self.opcode_data) },
            MEM_LOAD_TRACE_DATA_MARKER => {
                panic!("is load data");
            }
            _ => unreachable!(),
        }
    }

    pub fn rs2_or_ram_read_value(&self) -> u32 {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => {
                let as_memstore: &StoreOpcodeTracingData =
                    unsafe { core::mem::transmute(&self.opcode_data) };
                as_memstore.rs2_value
            }
            MEM_LOAD_TRACE_DATA_MARKER => self.opcode_data.aligned_ram_read_value,
            _ => unreachable!(),
        }
    }

    pub fn ram_address(&self) -> u32 {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => {
                let as_memstore: &StoreOpcodeTracingData =
                    unsafe { core::mem::transmute(&self.opcode_data) };
                as_memstore.aligned_ram_address
            }
            MEM_LOAD_TRACE_DATA_MARKER => self.opcode_data.aligned_ram_address,
            _ => unreachable!(),
        }
    }

    pub fn rd_or_ram_read_value(&self) -> u32 {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => {
                let as_memstore: &StoreOpcodeTracingData =
                    unsafe { core::mem::transmute(&self.opcode_data) };
                as_memstore.aligned_ram_old_value
            }
            MEM_LOAD_TRACE_DATA_MARKER => self.opcode_data.rd_old_value,
            _ => unreachable!(),
        }
    }

    pub fn rd_or_ram_write_value(&self) -> u32 {
        match self.discr {
            MEM_STORE_TRACE_DATA_MARKER => {
                let as_memstore: &StoreOpcodeTracingData =
                    unsafe { core::mem::transmute(&self.opcode_data) };
                as_memstore.aligned_ram_write_value
            }
            MEM_LOAD_TRACE_DATA_MARKER => self.opcode_data.rd_value,
            _ => unreachable!(),
        }
    }
}

pub trait DelegationCSRProcessor: 'static + Clone + std::fmt::Debug {
    fn process_write<
        M: MemorySource,
        TR: UnrolledTracer<C>,
        ND: NonDeterminismCSRSource<M>,
        C: MachineConfig,
    >(
        &mut self,
        state: &mut RiscV32StateForUnrolledProver<C>,
        csr_index: u16,
        memory_source: &mut M,
        non_determinism_source: &mut ND,
        tracer: &mut TR,
    );
}

impl DelegationCSRProcessor for NoExtraCSRs {
    #[inline(always)]
    fn process_write<
        M: MemorySource,
        TR: UnrolledTracer<C>,
        ND: NonDeterminismCSRSource<M>,
        C: MachineConfig,
    >(
        &mut self,
        _state: &mut RiscV32StateForUnrolledProver<C>,
        csr_index: u16,
        _memory_source: &mut M,
        _non_determinism_source: &mut ND,
        _tracer: &mut TR,
    ) {
        panic!("Unsupported CSR index {}", csr_index);
    }
}

impl DelegationCSRProcessor for crate::delegations::DelegationsCSRProcessor {
    #[inline(always)]
    fn process_write<
        M: MemorySource,
        TR: UnrolledTracer<C>,
        ND: NonDeterminismCSRSource<M>,
        C: MachineConfig,
    >(
        &mut self,
        state: &mut RiscV32StateForUnrolledProver<C>,
        csr_index: u16,
        memory_source: &mut M,
        _non_determinism_source: &mut ND,
        tracer: &mut TR,
    ) {
        use self::delegations::blake2_round_function_with_compression_mode::*;
        use self::delegations::u256_ops_with_control::*;

        match csr_index as u32 {
            BLAKE2_ROUND_FUNCTION_WITH_EXTENDED_CONTROL_ACCESS_ID => {
                blake2_round_function_with_extended_control_over_unrolled_state(
                    state,
                    memory_source,
                    tracer,
                );
            }
            U256_OPS_WITH_CONTROL_ACCESS_ID => {
                u256_ops_with_control_impl_over_unrolled_state(state, memory_source, tracer);
            }
            csr => {
                panic!("Unsupported CSR = 0x{:04x}", csr);
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct RiscV32StateForUnrolledProver<Config: MachineConfig = IMStandardIsaConfig> {
    pub registers: [u32; NUM_REGISTERS],
    pub pc: u32,
    pub timestamp: TimestampScalar,
    _marker: std::marker::PhantomData<Config>,
}

impl<Config: MachineConfig> RiscV32StateForUnrolledProver<Config> {
    pub fn initial(initial_pc: u32) -> Self {
        // we should start in machine mode, the rest is not important and can be by default
        let registers = [0u32; NUM_REGISTERS];
        let pc = initial_pc;

        #[cfg(feature = "opcode_stats")]
        OPCODES_COUNTER.with_borrow_mut(|el| el.clear());

        Self {
            registers,
            pc,
            timestamp: INITIAL_TIMESTAMP,
            _marker: std::marker::PhantomData,
        }
    }

    #[must_use]
    #[inline(always)]
    pub fn get_register(&self, reg_idx: u32) -> u32 {
        unsafe {
            core::hint::assert_unchecked(reg_idx < 32);
        }
        let res = unsafe { *self.registers.get_unchecked(reg_idx as usize) };

        res
    }

    #[inline(always)]
    pub fn set_register(&mut self, reg_idx: u32, mut value: u32) -> u32 {
        unsafe {
            core::hint::assert_unchecked(reg_idx < 32);
        }
        if reg_idx == 0 {
            value = 0;
        }
        unsafe {
            let dst = self.registers.get_unchecked_mut(reg_idx as usize);
            let existing = *dst;
            *dst = value;

            existing
        }
    }

    #[inline(always)]
    fn add_marker(&self) {
        #[cfg(feature = "cycle_marker")]
        CYCLE_MARKER.with_borrow_mut(|cm| cm.add_marker(self.cycle_counter as u64))
    }

    #[inline(always)]
    fn add_delegation(id: u32) {
        #[cfg(feature = "cycle_marker")]
        CYCLE_MARKER.with_borrow_mut(|cm| cm.add_delegation(id))
    }

    #[inline(always)]
    fn decoder_step<M: MemorySource, TR: UnrolledTracer<Config>>(
        &mut self,
        memory_source: &mut M,
        tracer: &mut TR,
    ) -> u32 {
        let opcode = opcode_read(self.pc, memory_source);
        let tracing_data = TracingDecoderData {
            pc: self.pc,
            // timestamp: TimestampData::from_scalar(self.timestamp),
        };
        tracer.trace_decoder_step(tracing_data);

        opcode
    }

    pub fn run_cycles<
        M: MemorySource,
        TR: UnrolledTracer<Config>,
        ND: NonDeterminismCSRSource<M>,
        CSR: DelegationCSRProcessor,
    >(
        &mut self,
        memory_source: &mut M,
        tracer: &mut TR,
        non_determinism_source: &mut ND,
        csr_processor: &mut CSR,
        num_cycles: usize,
    ) -> usize {
        for cycle_number in 0..num_cycles {
            tracer.at_cycle_start(&*self);

            // println!("PC = 0x{:08x}", self.pc);
            let opcode = self.decoder_step(memory_source, tracer);

            let rd = get_rd_bits(opcode);
            let formal_rs1 = get_formal_rs1_bits(opcode);
            let formal_rs2 = get_formal_rs2_bits(opcode);
            let op = get_opcode_bits(opcode);
            let funct3 = funct3_bits(opcode);
            let funct7 = funct7_bits(opcode);

            unsafe {
                core::hint::assert_unchecked(formal_rs1 < 32);
                core::hint::assert_unchecked(formal_rs2 < 32);
                core::hint::assert_unchecked(rd < 32);
                core::hint::assert_unchecked(funct3 < 8);
            }
            let pc = self.pc;
            self.pc = self.pc.wrapping_add(4);

            let rs1_value = self.get_register(formal_rs1 as u32);
            let rs2_value = self.get_register(formal_rs2 as u32);
            let rd = rd as u32;

            match op {
                OPCODE_LUI => {
                    // U format
                    report_opcode("LUI");
                    let imm = UTypeOpcode::imm(opcode);
                    let rd_value = imm;

                    let rd_old_value = self.set_register(rd, rd_value);
                    let tracing_data = NonMemoryOpcodeTracingData {
                        initial_pc: pc,
                        opcode,
                        rs1_value,
                        rs2_value,
                        rd_value,
                        new_pc: self.pc,
                        rd_old_value,
                        delegation_type: 0,
                    };
                    tracer.trace_non_mem_step(1, tracing_data);
                }
                OPCODE_AUIPC => {
                    // U format
                    report_opcode("AUIPC");
                    let imm = UTypeOpcode::imm(opcode);
                    let rd_value = pc.wrapping_add(imm);

                    let rd_old_value = self.set_register(rd, rd_value);
                    let tracing_data = NonMemoryOpcodeTracingData {
                        initial_pc: pc,
                        opcode,
                        rs1_value,
                        rs2_value,
                        rd_value,
                        new_pc: self.pc,
                        rd_old_value,
                        delegation_type: 0,
                    };
                    tracer.trace_non_mem_step(1, tracing_data);
                }
                OPCODE_JAL => {
                    report_opcode("JAL");
                    // J format
                    let mut imm: u32 = JTypeOpcode::imm(opcode);
                    sign_extend(&mut imm, 21);
                    let rd_value = self.pc; // already incremented by 4
                    let jmp_addr = pc.wrapping_add(imm); // this one is at this cycle

                    if jmp_addr & 0x3 != 0 {
                        // unaligned PC
                        panic!("Unaligned jump address 0x{:08x}", jmp_addr);
                    } else {
                        self.pc = jmp_addr;
                    }

                    let rd_old_value = self.set_register(rd, rd_value);
                    let tracing_data = NonMemoryOpcodeTracingData {
                        initial_pc: pc,
                        opcode,
                        rs1_value,
                        rs2_value,
                        rd_value,
                        new_pc: self.pc,
                        rd_old_value,
                        delegation_type: 0,
                    };
                    tracer.trace_non_mem_step(2, tracing_data);
                }
                OPCODE_JALR => {
                    report_opcode("JALR");
                    // I format
                    let mut imm: u32 = ITypeOpcode::imm(opcode);
                    // quasi sign extend
                    sign_extend(&mut imm, 12);
                    let rd_value = self.pc; // already incremented by 4
                                            //  The target address is obtained by adding the 12-bit signed I-immediate
                                            // to the register rs1, then setting the least-significant bit of the result to zero
                    let jmp_addr = (rs1_value.wrapping_add(imm) & !0x1);

                    if jmp_addr & 0x3 != 0 {
                        // unaligned PC
                        panic!("Unaligned jump address 0x{:08x}", jmp_addr);
                    } else {
                        self.pc = jmp_addr;
                    }

                    let rd_old_value = self.set_register(rd, rd_value);
                    let tracing_data = NonMemoryOpcodeTracingData {
                        initial_pc: pc,
                        opcode,
                        rs1_value,
                        rs2_value,
                        rd_value,
                        new_pc: self.pc,
                        rd_old_value,
                        delegation_type: 0,
                    };
                    tracer.trace_non_mem_step(2, tracing_data);
                }
                OPCODE_BRANCH => {
                    report_opcode("BRANCH");
                    // B format
                    let mut imm = BTypeOpcode::imm(opcode);
                    sign_extend(&mut imm, 13);
                    let jmp_addr = pc.wrapping_add(imm);

                    let should_jump = match funct3 {
                        0 => rs1_value == rs2_value,
                        1 => rs1_value != rs2_value,
                        4 => (rs1_value as i32) < (rs2_value as i32),
                        5 => (rs1_value as i32) >= (rs2_value as i32),
                        6 => rs1_value < rs2_value,
                        7 => rs1_value >= rs2_value,
                        _ => {
                            panic!("Unknown opcode 0x{:08x}", opcode);
                        }
                    };

                    if should_jump {
                        if jmp_addr & 0x3 != 0 {
                            // unaligned PC
                            panic!("Unaligned jump address 0x{:08x}", jmp_addr);
                        } else {
                            self.pc = jmp_addr;
                        }
                    }

                    // BRANCH doesn't write to RD, and must be masked as-is it did access x0
                    let rd = 0;
                    let rd_old_value = self.get_register(rd);
                    let tracing_data = NonMemoryOpcodeTracingData {
                        initial_pc: pc,
                        opcode,
                        rs1_value,
                        rs2_value,
                        rd_value: 0,
                        new_pc: self.pc,
                        rd_old_value,
                        delegation_type: 0,
                    };
                    tracer.trace_non_mem_step(2, tracing_data);
                }
                OP_IMM_SUBMASK => {
                    let operand_1 = rs1_value;
                    let mut imm = ITypeOpcode::imm(opcode);
                    sign_extend(&mut imm, 12);
                    let operand_2 = imm;
                    let opcode_family;
                    let rd_value = match funct3 {
                        0b000 => {
                            report_opcode("ADD");
                            opcode_family = 1;
                            operand_1.wrapping_add(operand_2)
                        }
                        0b001 if funct7 == SLL_FUNCT7 => {
                            report_opcode("SLL");
                            opcode_family = 3;
                            // shift is encoded in lowest 5 bits
                            operand_1 << (operand_2 & 0x1f)
                        }
                        0b101 if funct7 == SRL_FUNCT7 => {
                            report_opcode("SRL");
                            opcode_family = 3;
                            // shift is encoded in lowest 5 bits
                            operand_1 >> (operand_2 & 0x1f)
                        }
                        0b101 if funct7 == SRA_FUNCT7 => {
                            report_opcode("SRA");
                            opcode_family = 3;
                            // Arithmetic shift right
                            // shift is encoded in lowest 5 bits

                            if Config::SUPPORT_SRA {
                                ((operand_1 as i32) >> (operand_2 & 0x1f)) as u32
                            } else {
                                panic!("Unknown opcode 0x{:08x}", opcode);
                            }
                        }
                        0b101 if funct7 == ROT_FUNCT7 => {
                            report_opcode("ROR");
                            opcode_family = 3;
                            // Arithmetic shift right
                            // shift is encoded in lowest 5 bits

                            if Config::SUPPORT_ROT {
                                operand_1.rotate_right(operand_2 & 0x1f)
                            } else {
                                panic!("Unknown opcode 0x{:08x}", opcode);
                            }
                        }
                        0b010 => {
                            report_opcode("SLT");
                            opcode_family = 2;
                            // Store less than
                            ((operand_1 as i32) < (operand_2 as i32)) as u32
                        }
                        0b011 => {
                            report_opcode("SLTU");
                            opcode_family = 2;
                            // Store less than unsigned
                            (operand_1 < operand_2) as u32
                        }
                        0b100 => {
                            report_opcode("XOR");
                            opcode_family = 3;
                            // XOR
                            operand_1 ^ operand_2
                        }
                        0b110 => {
                            report_opcode("OR");
                            opcode_family = 3;
                            // OR
                            operand_1 | operand_2
                        }
                        0b111 => {
                            report_opcode("AND");
                            opcode_family = 3;
                            // AND
                            operand_1 & operand_2
                        }
                        _ => {
                            panic!("Unknown opcode 0x{:08x}", opcode);
                        }
                    };

                    let rd_old_value = self.set_register(rd, rd_value);
                    let tracing_data = NonMemoryOpcodeTracingData {
                        initial_pc: pc,
                        opcode,
                        rs1_value,
                        rs2_value,
                        rd_value,
                        new_pc: self.pc,
                        rd_old_value,
                        delegation_type: 0,
                    };

                    tracer.trace_non_mem_step(opcode_family, tracing_data);
                }
                OP_SUBMASK => {
                    let is_r_type = op == OP_SUBMASK;
                    let operand_1 = rs1_value;
                    let operand_2 = rs2_value;

                    if funct7 == M_EXT_FUNCT7 {
                        // Multiplication extension
                        let rd_value = match funct3 {
                            0b000 => {
                                report_opcode("MUL");
                                // MUL
                                if Config::SUPPORT_MUL {
                                    (operand_1 as i32).wrapping_mul(operand_2 as i32) as u32
                                } else {
                                    panic!("Unknown opcode 0x{:08x}", opcode);
                                }
                            }
                            0b001 => {
                                report_opcode("MULH");
                                // MULH
                                if Config::SUPPORT_MUL && Config::SUPPORT_SIGNED_MUL {
                                    (((operand_1 as i32) as i64)
                                        .wrapping_mul((operand_2 as i32) as i64)
                                        >> 32) as u32
                                } else {
                                    panic!("Unknown opcode 0x{:08x}", opcode);
                                }
                            }
                            0b010 => {
                                report_opcode("MULSU");
                                // MULHSU
                                if Config::SUPPORT_MUL && Config::SUPPORT_SIGNED_MUL {
                                    (((operand_1 as i32) as i64)
                                        .wrapping_mul(((operand_2 as u32) as u64) as i64)
                                        >> 32) as u32
                                } else {
                                    panic!("Unknown opcode 0x{:08x}", opcode);
                                }
                            }
                            0b011 => {
                                report_opcode("MULHU");
                                // MULHU
                                if Config::SUPPORT_MUL {
                                    ((operand_1 as u64).wrapping_mul(operand_2 as u64) >> 32) as u32
                                } else {
                                    panic!("Unknown opcode 0x{:08x}", opcode);
                                }
                            }
                            0b100 => {
                                report_opcode("DIV");
                                // DIV
                                if Config::SUPPORT_DIV && Config::SUPPORT_SIGNED_DIV {
                                    if operand_2 == 0 {
                                        -1i32 as u32
                                    } else {
                                        if operand_1 as i32 == i32::MIN && operand_2 as i32 == -1 {
                                            operand_1
                                        } else {
                                            ((operand_1 as i32) / (operand_2 as i32)) as u32
                                        }
                                    }
                                } else {
                                    panic!("Unknown opcode 0x{:08x}", opcode);
                                }
                            }
                            0b101 => {
                                report_opcode("DIVU");
                                // DIVU
                                if Config::SUPPORT_DIV {
                                    if operand_2 == 0 {
                                        0xffffffff
                                    } else {
                                        operand_1 / operand_2
                                    }
                                } else {
                                    panic!("Unknown opcode 0x{:08x}", opcode);
                                }
                            }
                            0b110 => {
                                report_opcode("REM");
                                // REM
                                if Config::SUPPORT_DIV && Config::SUPPORT_SIGNED_DIV {
                                    if operand_2 == 0 {
                                        operand_1
                                    } else {
                                        if operand_1 as i32 == i32::MIN && operand_2 as i32 == -1 {
                                            0u32
                                        } else {
                                            ((operand_1 as i32) % (operand_2 as i32)) as u32
                                        }
                                    }
                                } else {
                                    panic!("Unknown opcode 0x{:08x}", opcode);
                                }
                            }
                            0b111 => {
                                report_opcode("REMU");
                                // REMU
                                if Config::SUPPORT_DIV {
                                    if operand_2 == 0 {
                                        operand_1
                                    } else {
                                        operand_1 % operand_2
                                    }
                                } else {
                                    panic!("Unknown opcode 0x{:08x}", opcode);
                                }
                            }
                            _ => unsafe { unreachable_unchecked() },
                        };

                        let rd_old_value = self.set_register(rd, rd_value);
                        let tracing_data = NonMemoryOpcodeTracingData {
                            initial_pc: pc,
                            opcode,
                            rs1_value,
                            rs2_value,
                            rd_value,
                            new_pc: self.pc,
                            rd_old_value,
                            delegation_type: 0,
                        };

                        tracer.trace_non_mem_step(4, tracing_data);
                    } else {
                        // basic set
                        let opcode_family;
                        let rd_value = match funct3 {
                            0b000 if funct7 == 0 => {
                                report_opcode("ADD");
                                opcode_family = 1;
                                operand_1.wrapping_add(operand_2)
                            }
                            0b000 if funct7 == SUB_FUNCT7 => {
                                report_opcode("SUB");
                                opcode_family = 1;
                                operand_1.wrapping_sub(operand_2)
                            }
                            0b001 if funct7 == SLL_FUNCT7 => {
                                report_opcode("SLL");
                                opcode_family = 3;
                                // shift is encoded in lowest 5 bits
                                operand_1 << (operand_2 & 0x1f)
                            }
                            0b001 if funct7 == ROT_FUNCT7 => {
                                report_opcode("ROL");
                                opcode_family = 3;
                                // Arithmetic shift right
                                // shift is encoded in lowest 5 bits

                                if Config::SUPPORT_ROT {
                                    operand_1.rotate_left(operand_2 & 0x1f)
                                } else {
                                    panic!("Unknown opcode 0x{:08x}", opcode);
                                }
                            }
                            0b101 if funct7 == SRL_FUNCT7 => {
                                report_opcode("SRL");
                                opcode_family = 3;
                                // shift is encoded in lowest 5 bits
                                operand_1 >> (operand_2 & 0x1f)
                            }
                            0b101 if funct7 == SRA_FUNCT7 => {
                                report_opcode("SRA");
                                opcode_family = 3;
                                // Arithmetic shift right
                                // shift is encoded in lowest 5 bits

                                if Config::SUPPORT_SRA {
                                    ((operand_1 as i32) >> (operand_2 & 0x1f)) as u32
                                } else {
                                    panic!("Unknown opcode 0x{:08x}", opcode);
                                }
                            }
                            0b101 if funct7 == ROT_FUNCT7 => {
                                report_opcode("ROR");
                                opcode_family = 3;
                                // Arithmetic shift right
                                // shift is encoded in lowest 5 bits

                                if Config::SUPPORT_ROT {
                                    operand_1.rotate_right(operand_2 & 0x1f)
                                } else {
                                    panic!("Unknown opcode 0x{:08x}", opcode);
                                }
                            }
                            0b010 => {
                                report_opcode("SLT");
                                opcode_family = 2;
                                // Store less than
                                ((operand_1 as i32) < (operand_2 as i32)) as u32
                            }
                            0b011 => {
                                report_opcode("SLTU");
                                opcode_family = 2;
                                // Store less than unsigned
                                (operand_1 < operand_2) as u32
                            }
                            0b100 => {
                                report_opcode("XOR");
                                opcode_family = 3;
                                // XOR
                                operand_1 ^ operand_2
                            }
                            0b110 => {
                                report_opcode("OR");
                                opcode_family = 3;
                                // OR
                                operand_1 | operand_2
                            }
                            0b111 => {
                                report_opcode("AND");
                                opcode_family = 3;
                                // AND
                                operand_1 & operand_2
                            }
                            _ => {
                                panic!("Unknown opcode 0x{:08x}", opcode);
                            }
                        };

                        let rd_old_value = self.set_register(rd, rd_value);
                        let tracing_data = NonMemoryOpcodeTracingData {
                            initial_pc: pc,
                            opcode,
                            rs1_value,
                            rs2_value,
                            rd_value,
                            new_pc: self.pc,
                            rd_old_value,
                            delegation_type: 0,
                        };
                        tracer.trace_non_mem_step(opcode_family, tracing_data);
                    }
                }
                OPCODE_LOAD => {
                    let mut imm = ITypeOpcode::imm(opcode);
                    sign_extend(&mut imm, 12);

                    let load_address = rs1_value.wrapping_add(imm);

                    match funct3 {
                        a @ 0 | a @ 1 | a @ 2 | a @ 4 | a @ 5 => {
                            let num_bytes = match a {
                                0 | 4 => 1,
                                1 | 5 => 2,
                                2 => 4,
                                _ => unsafe { unreachable_unchecked() },
                            };
                            // Memory implementation should handle read in full. For now we only use one
                            // that doesn't step over 4 byte boundary ever, meaning even though formal address is not 4 byte aligned,
                            // loads of u8/u16/u32 are still "aligned"
                            let (aligned_ram_read_value, ram_read_value, adjusted_load_address) =
                                mem_read_mask_rom_if_needed::<M, Config>(
                                    memory_source,
                                    load_address as u64,
                                    num_bytes,
                                );
                            let rd_value = if Config::SUPPORT_SIGNED_LOAD {
                                // now depending on the type of load we extend it
                                match a {
                                    0 => {
                                        report_opcode("LB");
                                        sign_extend_8(ram_read_value)
                                    }
                                    1 => {
                                        report_opcode("LH");
                                        sign_extend_16(ram_read_value)
                                    }
                                    2 => {
                                        report_opcode("LW");
                                        ram_read_value
                                    }
                                    4 => {
                                        report_opcode("LBU");
                                        zero_extend_8(ram_read_value)
                                    }
                                    5 => {
                                        report_opcode("LHU");
                                        zero_extend_16(ram_read_value)
                                    }
                                    _ => unsafe { unreachable_unchecked() },
                                }
                            } else {
                                // now depending on the type of load we extend it
                                match a {
                                    0 | 1 => {
                                        panic!("Sign extension not enabled for LOAD");
                                    }
                                    2 => {
                                        report_opcode("LW");
                                        ram_read_value
                                    }
                                    4 => {
                                        report_opcode("LBU");
                                        zero_extend_8(ram_read_value)
                                    }
                                    5 => {
                                        report_opcode("LHU");
                                        zero_extend_16(ram_read_value)
                                    }
                                    _ => unsafe { unreachable_unchecked() },
                                }
                            };

                            let rd_old_value = self.set_register(rd, rd_value);
                            let tracing_data = LoadOpcodeTracingData {
                                initial_pc: pc,
                                opcode,
                                rs1_value,
                                aligned_ram_address: adjusted_load_address & !3,
                                aligned_ram_read_value,
                                rd_value,
                                rd_old_value,
                            };
                            if TR::SPECIAL_CASE_WORD_SIZED_MEM_OPS {
                                if num_bytes == 4 {
                                    tracer.trace_word_sized_mem_load_step(tracing_data);
                                } else {
                                    tracer.trace_mem_load_step(tracing_data);
                                }
                            } else {
                                tracer.trace_mem_load_step(tracing_data);
                            }
                        }
                        _ => {
                            panic!("Unknown opcode 0x{:08x}", opcode);
                        }
                    }
                }
                OPCODE_STORE => {
                    // STORE
                    let mut imm = STypeOpcode::imm(opcode);
                    sign_extend(&mut imm, 12);

                    let store_address = rs1_value.wrapping_add(imm);

                    // store operand rs2

                    // access memory
                    match funct3 {
                        a @ 0 | a @ 1 | a @ 2 => {
                            let store_length = 1 << a;

                            // #[cfg(feature = "opcode_stats")]
                            {
                                match store_length {
                                    1 => {
                                        report_opcode("SB");
                                    }
                                    2 => {
                                        report_opcode("SH");
                                    }
                                    4 => {
                                        report_opcode("SW");
                                    }
                                    _ => unsafe { core::hint::unreachable_unchecked() },
                                }
                            }

                            // memory handles the write in full, whether it's aligned or not, or whatever
                            let (aligned_ram_old_value, aligned_ram_write_value) =
                                mem_write::<M, Config>(
                                    memory_source,
                                    store_address as u64,
                                    rs2_value,
                                    store_length,
                                );

                            let tracing_data = StoreOpcodeTracingData {
                                initial_pc: pc,
                                opcode,
                                rs1_value,
                                aligned_ram_address: store_address & !3,
                                rs2_value,
                                aligned_ram_old_value,
                                aligned_ram_write_value,
                            };
                            if TR::SPECIAL_CASE_WORD_SIZED_MEM_OPS {
                                if store_length == 4 {
                                    tracer.trace_word_sized_mem_store_step(tracing_data);
                                } else {
                                    tracer.trace_mem_store_step(tracing_data);
                                }
                            } else {
                                tracer.trace_mem_store_step(tracing_data);
                            }
                        }
                        _ => {
                            panic!("Unknown opcode 0x{:08x}", opcode);
                        }
                    }
                }
                OPCODE_SYSTEM => {
                    // various control instructions, we implement only a subset
                    const ZICSR_MASK: u8 = 0x3;
                    const ZIMOP_MASK: u8 = 0x4;

                    if funct3 & ZIMOP_MASK == ZIMOP_MASK {
                        const MOP_FUNCT7_TEST: u8 = 0b1000001u8;
                        if Config::SUPPORT_MOPS && funct7 & MOP_FUNCT7_TEST == MOP_FUNCT7_TEST {
                            report_opcode("MOP");

                            use field::{Field, Mersenne31Field};

                            let mop_number = ((funct7 & 0b110) >> 1) | ((funct7 & 0b100000) >> 5);
                            let operand_1 = rs1_value;
                            let operand_2 = rs2_value;
                            let mut operand_1 = Mersenne31Field::from_nonreduced_u32(operand_1);
                            let operand_2 = Mersenne31Field::from_nonreduced_u32(operand_2);
                            match mop_number {
                                0 => {
                                    operand_1.add_assign(&operand_2);
                                }
                                1 => {
                                    operand_1.sub_assign(&operand_2);
                                }
                                2 => {
                                    operand_1.mul_assign(&operand_2);
                                }
                                _ => {
                                    panic!("Unknown opcode 0x{:08x}", opcode);
                                }
                            }
                            let rd_value = operand_1.to_reduced_u32();

                            let rd_old_value = self.set_register(rd, rd_value);
                            let tracing_data = NonMemoryOpcodeTracingData {
                                initial_pc: pc,
                                opcode,
                                rs1_value,
                                rs2_value,
                                rd_value,
                                new_pc: self.pc,
                                rd_old_value,
                                delegation_type: 0,
                            };
                            tracer.trace_non_mem_step(1, tracing_data);
                        }
                    } else if funct3 & ZICSR_MASK != 0 {
                        // We do not support stanard CSRs yet
                        assert!(Config::SUPPORT_STANDARD_CSRS == false);
                        assert!(Config::SUPPORT_ONLY_CSRRW);

                        let csr_number = ITypeOpcode::imm(opcode);
                        let mut rd_value = 0;
                        let mut delegation_type = 0u16;

                        // read
                        match csr_number {
                            NON_DETERMINISM_CSR => {
                                // to imporve oracle usability we can try to avoid read
                                // if we intend to write, so check oracle config
                                rd_value = if ND::SHOULD_MOCK_READS_BEFORE_WRITES {
                                    // all our oracle accesses are implemented via CSRRW
                                    // with either rd == 0 or rs1 == 0, so if we have
                                    // rd == 0 here it's just a read
                                    if rd == 0 {
                                        // we consider main intention to be write into CSR,
                                        // so do NOT perform `read()`
                                        0
                                    } else {
                                        // it's actually intended to read
                                        non_determinism_source.read()
                                    }
                                } else {
                                    non_determinism_source.read()
                                };
                            }
                            MARKER_CSR => {
                                // Do nothing here, we do the work in the write case
                            }
                            delegation_csr => {
                                // we can ignore this pass - it will be resolved below in write section
                                debug_assert!(Config::ALLOWED_DELEGATION_CSRS.contains(&delegation_csr), "Machine {:?} is not configured to support CSR number {} at pc 0x{:08x}", Config::default(), delegation_csr, pc);
                            }
                        }

                        if funct3 != 1 {
                            // not CSRRW
                            panic!("Unknown opcode 0x{:08x}", opcode);
                        }

                        // now write into CSR. We do not use written value,
                        // but some delegations depend on formal write event

                        match csr_number {
                            NON_DETERMINISM_CSR => {
                                delegation_type = NON_DETERMINISM_CSR as u16;
                                if ND::SHOULD_IGNORE_WRITES_AFTER_READS {
                                    // if we have rs1 == 0 then we should ignore write into CSR,
                                    // as our main intension was to read

                                    // index of rs1
                                    if formal_rs1 == 0 {
                                        // do nothing
                                    } else {
                                        non_determinism_source
                                            .write_with_memory_access(&*memory_source, rs1_value);
                                    }
                                } else {
                                    non_determinism_source
                                        .write_with_memory_access(&*memory_source, rs1_value);
                                }
                            }
                            MARKER_CSR => self.add_marker(),
                            delegation_csr => {
                                debug_assert!(
                                    Config::ALLOWED_DELEGATION_CSRS.contains(&delegation_csr),
                                    "Machine {:?} is not configured to support CSR number {}",
                                    Config::default(),
                                    delegation_csr
                                );
                                Self::add_delegation(delegation_csr);
                                csr_processor.process_write(
                                    self,
                                    delegation_csr as u16,
                                    memory_source,
                                    non_determinism_source,
                                    tracer,
                                );
                                delegation_type = delegation_csr as u16;
                            }
                        }

                        if delegation_type != NON_DETERMINISM_CSR as u16 {
                            assert_eq!(rd_value, 0);
                        }

                        let rd_old_value = self.set_register(rd, rd_value);
                        let tracing_data = NonMemoryOpcodeTracingData {
                            initial_pc: pc,
                            opcode,
                            rs1_value,
                            rs2_value,
                            rd_value,
                            new_pc: self.pc,
                            rd_old_value,
                            delegation_type,
                        };
                        tracer.trace_non_mem_step(3, tracing_data);
                    } else {
                        panic!("Unknown opcode 0x{:08x}", opcode);
                    }
                }
                _ => {
                    panic!("Unknown opcode 0x{:08x}", opcode);
                }
            }

            self.timestamp += TIMESTAMP_STEP;
            tracer.at_cycle_end(&*self);

            if pc == self.pc {
                // we are looping, and there are no interrupts
                return cycle_number + 1;
            }
        }

        num_cycles
    }

    // pub fn pretty_dump(&self) {
    //     println!(
    //         "PC = 0x{:08x}, RA = 0x{:08x}, SP = 0x{:08x}, GP = 0x{:08x}",
    //         self.pc, self.registers[1], self.registers[2], self.registers[3]
    //     );
    //     for chunk in self.registers.iter().enumerate().array_chunks::<4>() {
    //         for (idx, reg) in chunk.iter() {
    //             print!("x{:02} = 0x{:08x}, ", idx, reg);
    //         }
    //         println!("");
    //     }
    // }
}
