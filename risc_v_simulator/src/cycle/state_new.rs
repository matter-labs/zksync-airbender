// This simulator follows a paradigm of the unrolled cycle circuits

use std::collections::HashMap;
use std::hint::unreachable_unchecked;

pub use super::decoder_utils::*;
pub use super::utils::*;
use crate::utils::{sign_extend, sign_extend_16, sign_extend_8, zero_extend_16, zero_extend_8};

use crate::abstractions::csr_processor::NoExtraCSRs;
use crate::abstractions::memory::{AccessType, MemorySource};
use crate::abstractions::non_determinism::NonDeterminismCSRSource;
use crate::abstractions::tracer::Tracer;
use crate::cycle::state::report_opcode;
use crate::cycle::state::MARKER_CSR;
use crate::cycle::state::NON_DETERMINISM_CSR;
use crate::cycle::state::NUM_REGISTERS;
#[cfg(feature = "opcode_stats")]
use crate::cycle::state::OPCODES_COUNTER;
#[cfg(feature = "cycle_marker")]
use crate::cycle::state::{CycleMarker, Mark, CYCLE_MARKER};
use crate::cycle::status_registers::TrapReason;
use crate::cycle::IMStandardIsaConfig;
use crate::cycle::MachineConfig;
use crate::mmu::MMUImplementation;

use crate::cycle::opcode_formats::*;

pub trait DelegationCSRProcessor: 'static + Clone + std::fmt::Debug {
    fn process_write<
        M: MemorySource,
        TR: Tracer<C>,
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
        TR: Tracer<C>,
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
        TR: Tracer<C>,
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
        use crate::delegations::unrolled::blake2_round_function_with_compression_mode::*;
        use crate::delegations::unrolled::u256_ops_with_control::*;

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
        CYCLE_MARKER.with_borrow_mut(|cm| cm.add_marker())
    }

    #[inline(always)]
    fn add_delegation(id: u32) {
        #[cfg(feature = "cycle_marker")]
        CYCLE_MARKER.with_borrow_mut(|cm| cm.add_delegation(id))
    }

    #[inline(always)]
    fn count_new_cycle_for_markers(&self) {
        #[cfg(feature = "cycle_marker")]
        CYCLE_MARKER.with_borrow_mut(|cm| cm.incr_cycle_counter())
    }

    #[inline(always)]
    fn decoder_step<M: MemorySource, TR: Tracer<Config>>(
        &mut self,
        memory_source: &mut M,
        tracer: &mut TR,
    ) -> u32 {
        let opcode = opcode_read(self.pc, memory_source);

        opcode
    }

    pub fn run_cycles<
        M: MemorySource,
        TR: Tracer<Config>,
        ND: NonDeterminismCSRSource<M>,
        CSR: DelegationCSRProcessor,
    >(
        &mut self,
        memory_source: &mut M,
        tracer: &mut TR,
        non_determinism_source: &mut ND,
        csr_processor: &mut CSR,
        num_cycles: usize,
    ) -> bool {
        let mut finished_execution = false;

        for _cycle in 0..num_cycles {
            tracer.at_cycle_start_ext(&*self);

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
            tracer.trace_rs1_read(formal_rs1 as u32, rs1_value);
            let rs2_value = if op != OPCODE_LOAD {
                let rs2_value = self.get_register(formal_rs2 as u32);
                tracer.trace_rs2_read(formal_rs2 as u32, rs2_value);

                rs2_value
            } else {
                0
            };

            let rd = rd as u32;

            match op {
                OPCODE_LUI => {
                    // U format
                    report_opcode("LUI");
                    let imm = UTypeOpcode::imm(opcode);
                    let rd_value = imm;

                    let rd_old_value = self.set_register(rd, rd_value);
                    tracer.trace_rd_write(rd, rd_old_value, rd_value);
                }
                OPCODE_AUIPC => {
                    // U format
                    report_opcode("AUIPC");
                    let imm = UTypeOpcode::imm(opcode);
                    let rd_value = pc.wrapping_add(imm);

                    let rd_old_value = self.set_register(rd, rd_value);
                    tracer.trace_rd_write(rd, rd_old_value, rd_value);
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
                    tracer.trace_rd_write(rd, rd_old_value, rd_value);
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
                    tracer.trace_rd_write(rd, rd_old_value, rd_value);
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
                    tracer.trace_rd_write(rd, rd_old_value, 0);
                }
                OP_IMM_SUBMASK => {
                    let operand_1 = rs1_value;
                    let mut imm = ITypeOpcode::imm(opcode);
                    sign_extend(&mut imm, 12);
                    let operand_2 = imm;
                    let rd_value = match funct3 {
                        0b000 => {
                            report_opcode("ADD");
                            operand_1.wrapping_add(operand_2)
                        }
                        0b001 if funct7 == SLL_FUNCT7 => {
                            report_opcode("SLL");
                            // shift is encoded in lowest 5 bits
                            operand_1 << (operand_2 & 0x1f)
                        }
                        0b101 if funct7 == SRL_FUNCT7 => {
                            report_opcode("SRL");
                            // shift is encoded in lowest 5 bits
                            operand_1 >> (operand_2 & 0x1f)
                        }
                        0b101 if funct7 == SRA_FUNCT7 => {
                            report_opcode("SRA");
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
                            // Store less than
                            ((operand_1 as i32) < (operand_2 as i32)) as u32
                        }
                        0b011 => {
                            report_opcode("SLTU");
                            // Store less than unsigned
                            (operand_1 < operand_2) as u32
                        }
                        0b100 => {
                            report_opcode("XOR");
                            // XOR
                            operand_1 ^ operand_2
                        }
                        0b110 => {
                            report_opcode("OR");
                            // OR
                            operand_1 | operand_2
                        }
                        0b111 => {
                            report_opcode("AND");
                            // AND
                            operand_1 & operand_2
                        }
                        _ => {
                            panic!("Unknown opcode 0x{:08x}", opcode);
                        }
                    };

                    let rd_old_value = self.set_register(rd, rd_value);
                    tracer.trace_rd_write(rd, rd_old_value, rd_value);
                }
                OP_SUBMASK => {
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
                        tracer.trace_rd_write(rd, rd_old_value, rd_value);
                    } else {
                        // basic set
                        let rd_value = match funct3 {
                            0b000 if funct7 == 0 => {
                                report_opcode("ADD");
                                operand_1.wrapping_add(operand_2)
                            }
                            0b000 if funct7 == SUB_FUNCT7 => {
                                report_opcode("SUB");
                                operand_1.wrapping_sub(operand_2)
                            }
                            0b001 if funct7 == SLL_FUNCT7 => {
                                report_opcode("SLL");
                                // shift is encoded in lowest 5 bits
                                operand_1 << (operand_2 & 0x1f)
                            }
                            0b001 if funct7 == ROT_FUNCT7 => {
                                report_opcode("ROL");
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
                                // shift is encoded in lowest 5 bits
                                operand_1 >> (operand_2 & 0x1f)
                            }
                            0b101 if funct7 == SRA_FUNCT7 => {
                                report_opcode("SRA");
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
                                // Store less than
                                ((operand_1 as i32) < (operand_2 as i32)) as u32
                            }
                            0b011 => {
                                report_opcode("SLTU");
                                // Store less than unsigned
                                (operand_1 < operand_2) as u32
                            }
                            0b100 => {
                                report_opcode("XOR");
                                // XOR
                                operand_1 ^ operand_2
                            }
                            0b110 => {
                                report_opcode("OR");
                                // OR
                                operand_1 | operand_2
                            }
                            0b111 => {
                                report_opcode("AND");
                                // AND
                                operand_1 & operand_2
                            }
                            _ => {
                                panic!("Unknown opcode 0x{:08x}", opcode);
                            }
                        };

                        let rd_old_value = self.set_register(rd, rd_value);
                        tracer.trace_rd_write(rd, rd_old_value, rd_value);
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
                            let (aligned_ram_read_value, ram_read_value) = mem_read::<M, Config>(
                                memory_source,
                                load_address as u64,
                                num_bytes,
                            );
                            tracer.trace_ram_read(
                                (load_address & !0x3) as u64,
                                aligned_ram_read_value,
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
                            tracer.trace_rd_write(rd, rd_old_value, rd_value);
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

                            #[cfg(feature = "opcode_stats")]
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
                            tracer.trace_ram_read_write(
                                (store_address & !0x3) as u64,
                                aligned_ram_old_value,
                                aligned_ram_write_value,
                            );
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
                    const ZIMOP_FUNCT3: u8 = 0b100;

                    // if funct3 & ZIMOP_MASK == ZIMOP_MASK {
                    if funct3 == ZIMOP_FUNCT3 {
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
                            tracer.trace_rd_write(rd, rd_old_value, rd_value);
                        }
                    } else if funct3 & ZICSR_MASK != 0 {
                        // We do not support standard CSRs yet
                        assert!(Config::SUPPORT_STANDARD_CSRS == false);
                        assert!(Config::SUPPORT_ONLY_CSRRW);

                        let csr_number = ITypeOpcode::imm(opcode);
                        let mut rd_value = 0;
                        let mut delegation_type = 0u16;

                        // read
                        match csr_number {
                            NON_DETERMINISM_CSR => {
                                // to improve oracle usability we can try to avoid read
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
                                tracer.trace_non_determinism_read(rd_value);
                            }
                            MARKER_CSR => {
                                // Do nothing here, we do the work in the write case
                            }
                            delegation_csr => {
                                // we can ignore this pass - it will be resolved below in write section
                                debug_assert!(Config::ALLOWED_DELEGATION_CSRS.contains(&delegation_csr), "Machine {:?} is not configured to support CSR number {} at pc 0x{:08x}", Config::default(), delegation_csr, pc);
                            }
                        }

                        if funct3 != 0b001 {
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
                                tracer.trace_non_determinism_write(rs1_value);
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
                        tracer.trace_rd_write(rd, rd_old_value, rd_value);
                    } else {
                        panic!("Unknown opcode 0x{:08x}", opcode);
                    }
                }
                _ => {
                    panic!("Unknown opcode 0x{:08x}", opcode);
                }
            }

            self.count_new_cycle_for_markers();

            tracer.at_cycle_end_ext(&*self);

            if self.pc == pc {
                finished_execution = true;
            }
        }

        finished_execution
    }
}
