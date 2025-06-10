use std::collections::HashMap;
use std::hint::unreachable_unchecked;

use super::{status_registers::*, MachineConfig};
use crate::abstractions::csr_processor::CustomCSRProcessor;
use crate::abstractions::memory::{AccessType, MemorySource};
use crate::abstractions::non_determinism::NonDeterminismCSRSource;
use crate::abstractions::tracer::Tracer;
use crate::abstractions::{mem_read, mem_write};
use crate::cycle::IMStandardIsaConfig;
use crate::mmu::MMUImplementation;
use crate::utils::*;

#[cfg(feature = "delegation")]
use crate::delegations;

use super::opcode_formats::*;
use cs::definitions::TimestampScalar;
use rand::Rng;

pub const NUM_REGISTERS: usize = 32;
pub const MAX_MEMORY_OPS_PER_CYCLE: u32 = 3;
pub const NON_DETERMINISM_CSR: u32 = 0x7c0;
pub const MARKER_CSR: u32 = 0x7ff;

// static CSR_COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

#[cfg(feature = "opcode_stats")]
thread_local! {

    pub(crate) static OPCODES_COUNTER: std::cell::RefCell<std::collections::HashMap<&'static str, usize>> = std::cell::RefCell::new(std::collections::HashMap::new());
}

#[inline(always)]
pub(crate) fn report_opcode(_opcode: &'static str) {
    #[cfg(feature = "opcode_stats")]
    OPCODES_COUNTER.with_borrow_mut(|el| {
        *el.entry(_opcode).or_default() += 1;
    });
}

#[inline(always)]
pub fn output_opcode_stats() {
    #[cfg(feature = "opcode_stats")]
    {
        let mut keys: Vec<&'static str> =
            OPCODES_COUNTER.with_borrow(|el| el.keys().copied().collect::<Vec<_>>());
        keys.sort();
        for key in keys.into_iter() {
            let value = OPCODES_COUNTER.with_borrow(|el| el[key]);
            println!("Opcode {}: used {} times", key, value);
        }
    }
}

#[cfg(feature = "cycle_marker")]
#[derive(Debug, Default, Clone)]
pub struct Mark {
    pub cycles: u64,
    pub delegations: HashMap<u32, u64>,
}

#[cfg(feature = "cycle_marker")]
impl Mark {
    pub fn diff(&self, before: &Self) -> Self {
        let cycles = self.cycles - before.cycles;
        let mut delegations = HashMap::new();
        for (id, current_count) in self.delegations.iter() {
            match before.delegations.get(&id) {
                Some(previous_count) => {
                    let diff = current_count - previous_count;
                    if diff != 0 {
                        delegations.insert(*id, diff);
                    }
                }
                None => {
                    delegations.insert(*id, *current_count);
                }
            }
        }

        Self {
            cycles,
            delegations,
        }
    }
}

#[cfg(feature = "cycle_marker")]
#[derive(Debug, Default)]
pub struct CycleMarker {
    cycle_counter: u64,
    pub markers: Vec<Mark>,
    pub delegation_counter: HashMap<u32, u64>,
}

#[cfg(feature = "cycle_marker")]
impl CycleMarker {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    #[inline(always)]
    pub(crate) fn add_marker(&mut self) {
        self.markers.push(Mark {
            cycles: self.cycle_counter,
            delegations: self.delegation_counter.clone(),
        })
    }

    #[inline(always)]
    pub(crate) fn add_delegation(&mut self, id: u32) {
        self.delegation_counter
            .entry(id)
            .and_modify(|n| *n += 1)
            .or_insert(1);
    }

    #[inline(always)]
    pub(crate) fn incr_cycle_counter(&mut self) {
        self.cycle_counter += 1
    }
}

#[cfg(feature = "cycle_marker")]
thread_local! {
  pub(crate) static CYCLE_MARKER: std::cell::RefCell<CycleMarker> = std::cell::RefCell::new(CycleMarker::new());
}

#[cfg(feature = "cycle_marker")]
pub fn take_cycle_marker() -> CycleMarker {
    CYCLE_MARKER.with(|cm| std::mem::take(&mut *cm.borrow_mut()))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum Mode {
    User = 0,
    Supervisor = 1,
    Reserved = 2,
    Machine = 3,
}

impl Mode {
    #[must_use]
    #[inline(always)]
    pub const fn as_register_value(self) -> u32 {
        self as u32
    }

    #[must_use]
    #[inline(always)]
    pub const fn from_proper_bit_value(src: u32) -> Self {
        match src {
            i if i == Mode::User as u32 => Mode::User,
            i if i == Mode::Supervisor as u32 => Mode::Supervisor,
            i if i == Mode::Reserved as u32 => Mode::Reserved,
            i if i == Mode::Machine as u32 => Mode::Machine,
            _ => unsafe { unreachable_unchecked() },
        }
    }
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Default, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct TrapStateRegisters {
    pub status: u32, // status register
    pub ie: u32,     // interrupt-enable register
    pub ip: u32,     // interrupt-pending register
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Default, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct TrapSetupRegisters {
    // pub isa: u32, // we will not use it
    // pub edeleg: u32, // we will not use it
    // pub ideleg: u32, // we will not use it
    // pub counteren: u32, // we will not use it
    pub tvec: u32, // trap-handler base address
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Default, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct TrapHandlingRegisters {
    pub scratch: u32, // scratch register for machine trap handlers
    pub epc: u32,     // exception program counter
    pub cause: u32,   // trap cause
    pub tval: u32,    // bad address or instruction
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Default, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct ModeStatusAndTrapRegisters {
    pub state: TrapStateRegisters,
    pub setup: TrapSetupRegisters,
    pub handling: TrapHandlingRegisters,
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Default, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct ExtraFlags(pub u32);

impl ExtraFlags {
    pub const WAIT_FOR_INTERRUPT_BIT: u32 = 2;

    #[must_use]
    #[inline(always)]
    pub const fn get_current_mode(self) -> Mode {
        Mode::from_proper_bit_value(get_bits_and_align_right(self.0, 0, 2))
    }

    #[inline(always)]
    pub const fn set_mode(&mut self, mode: Mode) {
        self.0 = (self.0 & !0x3) | mode.as_register_value();
    }

    #[inline(always)]
    pub const fn set_mode_raw(&mut self, mode_bits: u32) {
        self.0 = (self.0 & !0x3) | mode_bits;
    }

    #[must_use]
    #[inline(always)]
    pub const fn get_wait_for_interrupt(self) -> u32 {
        get_bit_unaligned(self.0, Self::WAIT_FOR_INTERRUPT_BIT)
    }

    #[inline(always)]
    pub const fn set_wait_for_interrupt_bit(&mut self) {
        set_bit(&mut self.0, Self::WAIT_FOR_INTERRUPT_BIT)
    }

    #[inline(always)]
    pub const fn clear_wait_for_interrupt_bit(&mut self) {
        clear_bit(&mut self.0, Self::WAIT_FOR_INTERRUPT_BIT)
    }
}

#[derive(Clone, Debug)]
pub struct StateTracer<C: MachineConfig = IMStandardIsaConfig> {
    tracer: Vec<RiscV32State<C>>,
}

impl<C: MachineConfig> StateTracer<C> {
    pub fn new_for_num_cycles(num_cycles: usize) -> Self {
        Self {
            tracer: Vec::with_capacity(num_cycles + 1),
        }
    }

    pub fn insert(&mut self, idx: usize, state: RiscV32State<C>) {
        assert_eq!(self.tracer.len(), idx, "trying to insert out of order");
        self.tracer.push(state);
    }

    pub fn get(&self, idx: usize) -> Option<&RiscV32State<C>> {
        self.tracer.get(idx)
    }
}

#[deprecated]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct RiscV32State<Config: MachineConfig = IMStandardIsaConfig> {
    pub registers: [u32; NUM_REGISTERS],
    pub pc: u32,
    pub extra_flags: ExtraFlags, // everything that doesn't need full register

    pub timer: u64,
    pub timer_match: u64,

    pub machine_mode_trap_data: ModeStatusAndTrapRegisters,

    pub sapt: u32, // for debugging

    _marker: std::marker::PhantomData<Config>,
}

impl<Config: MachineConfig> RiscV32State<Config> {
    pub fn initial(initial_pc: u32) -> Self {
        // we should start in machine mode, the rest is not important and can be by default
        let registers = [0u32; NUM_REGISTERS];
        let pc = initial_pc;
        let mut extra_flags = ExtraFlags(0u32);
        extra_flags.set_mode(Mode::Machine);

        let cycle_counter = 0usize;
        let timer = 0u64;
        let timer_match = u64::MAX;

        let machine_mode_trap_data = ModeStatusAndTrapRegisters {
            state: TrapStateRegisters {
                status: 0,
                ie: 0,
                ip: 0,
            },
            setup: TrapSetupRegisters { tvec: 0 },
            handling: TrapHandlingRegisters {
                scratch: 0,
                epc: 0,
                cause: 0,
                tval: 0,
            },
        };

        let sapt = 0u32;

        #[cfg(feature = "opcode_stats")]
        OPCODES_COUNTER.with_borrow_mut(|el| el.clear());

        Self {
            registers,
            pc,
            extra_flags,
            timer,
            timer_match,
            machine_mode_trap_data,
            sapt,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn new_random(initial_pc: u32, is_user_mode: bool, is_halted: bool) -> Self {
        let mut rng = rand::thread_rng();

        let mut extra_flags = ExtraFlags(0u32);
        extra_flags.set_mode(if is_user_mode {
            Mode::User
        } else {
            Mode::Machine
        });
        if is_halted {
            extra_flags.set_wait_for_interrupt_bit()
        }

        let cycle_counter = 0usize;
        let timer = 0u64;
        let timer_match = u64::MAX;

        let mut status = rng.gen();
        MStatusRegister::set_mpp_to_machine(&mut status);

        let machine_mode_trap_data = ModeStatusAndTrapRegisters {
            state: TrapStateRegisters {
                status,
                ie: rng.gen(),
                ip: rng.gen(),
            },
            setup: TrapSetupRegisters { tvec: rng.gen() },
            handling: TrapHandlingRegisters {
                scratch: rng.gen(),
                epc: rng.gen::<u32>() & (u32::MAX - 3),
                cause: rng.gen(),
                tval: rng.gen(),
            },
        };

        let state = RiscV32State {
            registers: std::array::from_fn(|i| if i > 0 { rng.gen() } else { 0 }),
            pc: initial_pc,
            extra_flags,

            timer,
            timer_match,

            machine_mode_trap_data,

            sapt: rng.gen(),
            _marker: std::marker::PhantomData,
        };

        state
    }

    #[must_use]
    #[inline(always)]
    pub fn get_first_register<TR: Tracer<Config>>(&self, reg_idx: u32, tracer: &mut TR) -> u32 {
        let res = unsafe { *self.registers.get_unchecked(reg_idx as usize) };
        tracer.trace_rs1_read(reg_idx, res);

        res
    }

    #[must_use]
    #[inline(always)]
    pub fn get_second_register<TR: Tracer<Config>>(&self, reg_idx: u32, tracer: &mut TR) -> u32 {
        let res = unsafe { *self.registers.get_unchecked(reg_idx as usize) };
        tracer.trace_rs2_read(reg_idx, res);

        res
    }

    #[inline(always)]
    pub fn set_register<TR: Tracer<Config>>(
        &mut self,
        reg_idx: u32,
        mut value: u32,
        tracer: &mut TR,
    ) {
        if reg_idx == 0 {
            value = 0;
        }
        let read_value = self.registers[reg_idx as usize];
        self.registers[reg_idx as usize] = value;
        tracer.trace_rd_write(reg_idx, read_value, value);
    }

    pub fn cycle<
        'a,
        M: MemorySource,
        TR: Tracer<Config>,
        ND: NonDeterminismCSRSource<M>,
        MMU: MMUImplementation<M, TR, Config>,
    >(
        &'a mut self,
        memory_source: &'a mut M,
        tracer: &'a mut TR,
        mmu: &'a mut MMU,
        non_determinism_source: &mut ND,
    ) {
        #[cfg(not(feature = "delegation"))]
        {
            use crate::abstractions::csr_processor::NoExtraCSRs;
            self.cycle_ext(
                memory_source,
                tracer,
                mmu,
                non_determinism_source,
                &mut NoExtraCSRs,
            );
        }
        #[cfg(feature = "delegation")]
        {
            use crate::delegations::DelegationsCSRProcessor;
            self.cycle_ext(
                memory_source,
                tracer,
                mmu,
                non_determinism_source,
                &mut DelegationsCSRProcessor,
            );
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

    pub fn cycle_ext<
        'a,
        M: MemorySource,
        TR: Tracer<Config>,
        ND: NonDeterminismCSRSource<M>,
        MMU: MMUImplementation<M, TR, Config>,
        CSR: CustomCSRProcessor,
    >(
        &'a mut self,
        memory_source: &'a mut M,
        tracer: &'a mut TR,
        mmu: &'a mut MMU,
        non_determinism_source: &mut ND,
        csr_processor: &mut CSR,
    ) {
        tracer.at_cycle_start(&*self);

        if self.extra_flags.get_wait_for_interrupt() != 0 {
            tracer.at_cycle_end(&*self);
            return;
        }

        let current_privilege_mode = self.extra_flags.get_current_mode();
        let mut pc = self.pc;
        // println!("PC = 0x{:08x}", pc);
        let mut ret_val: u32 = 0;
        let mut trap = TrapReason::NoTrap;
        let mut instr: u32 = 0;

        'cycle_block: {
            // normal cycle
            // we assume no InstructionAccessFault here
            let instruction_phys_address = mmu.map_virtual_to_physical(
                pc,
                current_privilege_mode,
                AccessType::Instruction,
                memory_source,
                tracer,
                &mut trap,
            );
            if trap.is_a_trap() {
                // error during address translation
                debug_assert_eq!(trap, TrapReason::InstructionPageFault);
                break 'cycle_block;
            }

            instr = mem_read::<_, _, _>(
                memory_source,
                tracer,
                instruction_phys_address,
                4,
                AccessType::Instruction,
                &mut trap,
            );

            if trap.is_a_trap() {
                // error during address translation
                debug_assert_eq!(
                    trap.as_register_value(),
                    TrapReason::InstructionAccessFault.as_register_value()
                );
                break 'cycle_block;
            }

            // decode the instruction and perform cycle
            // destination register
            let mut rd = get_rd(instr);
            // we will ALWAYS read formal rs1 and rs2
            let formal_rs1 = get_formal_rs1(instr);
            let formal_rs2 = get_formal_rs2(instr);

            unsafe {
                core::hint::assert_unchecked(formal_rs1 < 32);
                core::hint::assert_unchecked(formal_rs2 < 32);
                core::hint::assert_unchecked(rd < 32);
            }

            let rs1 = self.get_first_register(formal_rs1, tracer);
            let rs2 = self.get_second_register(formal_rs2, tracer);

            // note on all the PC operations below: if we modify PC in the opcode,
            // we subtract 4 from it, to later on add 4 once at the end of the loop. For MOST
            // of the opcodes it makes sense to shorten the opcode body
            const LOWEST_7_BITS_MASK: u32 = 0x7f;

            match instr & LOWEST_7_BITS_MASK {
                0b0110111 => {
                    report_opcode("LUI");
                    // LUI
                    let imm = UTypeOpcode::imm(instr);

                    ret_val = imm;
                },
                0b0010111 => {
                    report_opcode("AUIPC");
                    // AUIPC
                    let imm = UTypeOpcode::imm(instr);

                    ret_val = pc.wrapping_add(imm);
                },
                0b1101111 => {
                    report_opcode("JAL");
                    // JAL
                    let mut rel_addr: u32 = JTypeOpcode::imm(instr);
                    // quasi-sign-extend
                    sign_extend(&mut rel_addr, 21);
                    ret_val = pc.wrapping_add(4u32);
                    let jmp_addr = pc.wrapping_sub(4u32).wrapping_add(rel_addr);

                    if jmp_addr & 0x3 != 0 {
                        // unaligned PC
                        trap = TrapReason::InstructionAddressMisaligned;
                        break 'cycle_block;
                    } else {
                        pc = jmp_addr;
                    }
                },
                0b1100111 => {
                    report_opcode("JALR");
                    // JALR
                    let mut imm: u32 = ITypeOpcode::imm(instr);
                    // quasi sign extend
                    sign_extend(&mut imm, 12);

                    ret_val = pc.wrapping_add(4u32);
                    //  The target address is obtained by adding the 12-bit signed I-immediate
                    // to the register rs1, then setting the least-significant bit of the result to zero
                    let jmp_addr = (rs1.wrapping_add(imm) & !0x1).wrapping_sub(4u32);

                    if jmp_addr & 0x3 != 0 {
                        // unaligned PC
                        trap = TrapReason::InstructionAddressMisaligned;
                        break 'cycle_block;
                    } else {
                        pc = jmp_addr;
                    }
                }
                0b1100011 => {
                    report_opcode("BRANCH");
                    // BRANCH
                    let mut imm = BTypeOpcode::imm(instr);
                    sign_extend(&mut imm, 13);

                    rd = 0;
                    let dst = pc.wrapping_add(imm).wrapping_sub(4u32);
                    let funct3 = BTypeOpcode::funct3(instr);

                    let should_jump = match funct3 {
                        0 => rs1 == rs2,
                        1 => rs1 != rs2,
                        4 => (rs1 as i32) < (rs2 as i32),
                        5 => (rs1 as i32) >= (rs2 as i32),
                        6 => rs1 < rs2,
                        7 => rs1 >= rs2,
                        _ => {
                            trap = TrapReason::IllegalInstruction;
                            break 'cycle_block;
                        }
                    };

                    if should_jump {
                        if dst & 0x3 != 0 {
                            // unaligned PC
                            trap = TrapReason::InstructionAddressMisaligned;
                            break 'cycle_block;
                        } else {
                            pc = dst;
                        }
                    }
                },
                0b0000011 => {
                    // LOAD

                    // if rd == 0 {
                    //     // Exception raised: loads with a destination of x0 must still raise
                    //     // any exceptions and action any other side effects
                    //     // even though the load value is discarded
                    //     trap = TrapReason::IllegalInstruction;
                    //     break 'cycle_block;
                    // }

                    let mut imm = ITypeOpcode::imm(instr);
                    sign_extend(&mut imm, 12);

                    let virtual_address = rs1.wrapping_add(imm);

                    // println!("Load into x{:02} from 0x{:08x} at PC = 0x{:08x}", rd, virtual_address, pc);

                    // we formally access it once, but most likely full memory access
                    // will be abstracted away into external interface hiding memory translation too
                    let operand_phys_address = mmu.map_virtual_to_physical(
                        virtual_address, current_privilege_mode, AccessType::MemLoad, memory_source,
                        tracer, &mut trap
                    );
                    if trap.is_a_trap() {
                        // error during address translation
                        debug_assert_eq!(trap, TrapReason::LoadPageFault);
                        break 'cycle_block;
                    }

                    let funct3 = ITypeOpcode::funct3(instr);
                    match funct3 {
                        a @ 0 | a @ 1 | a @ 2 | a @ 4 | a @ 5 => {
                            let num_bytes = match a {
                                0 | 4 => 1,
                                1 | 5 => 2,
                                2 => 4,
                                _ => unsafe {unreachable_unchecked()}
                            };
                            // Memory implementation should handle read in full. For now we only use one
                            // that doesn't step over 4 byte boundary ever, meaning even though formal address is not 4 byte aligned,
                            // loads of u8/u16/u32 are still "aligned"
                            let operand = mem_read::<_, _, _ >(
                                memory_source, tracer, operand_phys_address,
                                num_bytes, AccessType::MemLoad, &mut trap
                            );
                            if trap.is_a_trap() {
                                debug_assert_eq!(trap, TrapReason::LoadAddressMisaligned);
                                break 'cycle_block;
                            }
                            if Config::SUPPORT_SIGNED_LOAD {
                                // now depending on the type of load we extend it
                                ret_val = match a {
                                    0 => {
                                        report_opcode("LB");
                                        sign_extend_8(operand)
                                    },
                                    1 => {
                                        report_opcode("LH");
                                        sign_extend_16(operand)
                                    },
                                    2 => {
                                        report_opcode("LW");
                                        operand
                                    },
                                    4 => {
                                        report_opcode("LB");
                                        zero_extend_8(operand)
                                    },
                                    5 => {
                                        report_opcode("LH");
                                        zero_extend_16(operand)
                                    },
                                    _ => unsafe {unreachable_unchecked()}
                                };
                            } else {
                                // now depending on the type of load we extend it
                                ret_val = match a {
                                    0 => {
                                        trap = TrapReason::IllegalInstruction;
                                        break 'cycle_block;
                                    },
                                    1 => {
                                        trap = TrapReason::IllegalInstruction;
                                        break 'cycle_block;
                                    },
                                    2 => {
                                        report_opcode("LW");
                                        operand
                                    },
                                    4 => {
                                        report_opcode("LB");
                                        zero_extend_8(operand)
                                    },
                                    5 => {
                                        report_opcode("LH");
                                        zero_extend_16(operand)
                                    },
                                    _ => unsafe {unreachable_unchecked()}
                                };
                            }

                        },
                        _ => {
                            trap = TrapReason::IllegalInstruction;
                            break 'cycle_block;
                        },
                    }
                },
                0b0100011 => {
                    // STORE
                    let mut imm = STypeOpcode::imm(instr);
                    sign_extend(&mut imm, 12);

                    let virtual_address = imm.wrapping_add(rs1);
                    // it's S-type, that has no RD, so set it to x0
                    rd = 0;

                    // println!("Store of x{:02} = 0x{:08x} into 0x{:08x} at PC = 0x{:08x}", STypeOpcode::rs2(instr), rs2, virtual_address, pc);

                    // store operand rs2

                    // we formally access it once, but most likely full memory access
                    // will be abstracted away into external interface hiding memory translation too
                    let operand_phys_address = mmu.map_virtual_to_physical(
                        virtual_address, current_privilege_mode, AccessType::MemStore, memory_source, tracer, &mut trap
                    );
                    if trap.is_a_trap() {
                        debug_assert_eq!(trap, TrapReason::StoreOrAMOPageFault);
                        break 'cycle_block;
                    }

                    // access memory
                    let funct3 = STypeOpcode::funct3(instr);
                    match funct3 {
                        a @ 0 | a @ 1 | a @ 2 => {
                            let store_length = 1 << a;

                            #[cfg(feature = "opcode_stats")]
                            {
                                match store_length {
                                    1 => {
                                        report_opcode("SB");
                                    },
                                    2 => {
                                        report_opcode("SH");
                                    },
                                    4 => {
                                        report_opcode("SW");
                                    },
                                    _ => {
                                        unreachable!()
                                    }
                                }
                            }

                            // memory handles the write in full, whether it's aligned or not, or whatever
                            mem_write::<_, _, _>(
                                memory_source, tracer, operand_phys_address, rs2, store_length,
                                &mut trap
                            );
                            if trap.is_a_trap() {
                                // error during address translation
                                debug_assert_eq!(trap, TrapReason::StoreOrAMOAddressMisaligned);
                                break 'cycle_block;
                            }
                        },
                        _ => {
                            trap = TrapReason::IllegalInstruction;
                            break 'cycle_block;
                        },
                    }
                },
                0b0010011 | // Op-immediate
                0b0110011 // op
                => {
                    const TEST_REG_REG_MASK: u32 = 0x20;
                    let is_r_type = instr & TEST_REG_REG_MASK != 0;
                    let operand_1 = rs1;
                    let operand_2 = if is_r_type {
                        rs2
                    } else {
                        let mut imm = ITypeOpcode::imm(instr);
                        sign_extend(&mut imm, 12);

                        imm
                    };

                    let funct3 = RTypeOpcode::funct3(instr); // same as IType
                    let funct7 = RTypeOpcode::funct7(instr);
                    if is_r_type && funct7 == 1 {
                        // RV32M - multiplication subset
                        ret_val = match funct3 {
                            0 => {
                                report_opcode("MUL");
                                // MUL
                                if Config::SUPPORT_MUL {
                                    (operand_1 as i32).wrapping_mul(operand_2 as i32) as u32
                                } else {
                                    trap = TrapReason::IllegalInstruction;
                                    break 'cycle_block;
                                }
                            },
                            1 => {
                                report_opcode("MULH");
                                // MULH
                                if Config::SUPPORT_MUL && Config::SUPPORT_SIGNED_MUL {
                                    (((operand_1 as i32) as i64).wrapping_mul((operand_2 as i32) as i64) >> 32) as u32
                                } else {
                                    trap = TrapReason::IllegalInstruction;
                                    break 'cycle_block;
                                }
                            },
                            2 => {
                                report_opcode("MULSU");
                                // MULHSU
                                if Config::SUPPORT_MUL && Config::SUPPORT_SIGNED_MUL {
                                    (((operand_1 as i32) as i64).wrapping_mul(((operand_2 as u32) as u64) as i64) >> 32) as u32
                                } else {
                                    trap = TrapReason::IllegalInstruction;
                                    break 'cycle_block;
                                }
                            },
                            3 => {
                                report_opcode("MULHU");
                                // MULHU
                                if Config::SUPPORT_MUL {
                                    ((operand_1 as u64).wrapping_mul(operand_2 as u64) >> 32) as u32
                                } else {
                                    trap = TrapReason::IllegalInstruction;
                                    break 'cycle_block;
                                }
                            },
                            4 => {
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
                                    trap = TrapReason::IllegalInstruction;
                                    break 'cycle_block;
                                }
                            },
                            5 => {
                                report_opcode("DIVU");
                                // DIVU
                                if Config::SUPPORT_DIV {
                                    if operand_2 == 0 {
                                        0xffffffff
                                    } else {
                                        operand_1 / operand_2
                                    }
                                } else {
                                    trap = TrapReason::IllegalInstruction;
                                    break 'cycle_block;
                                }
                            },
                            6 => {
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
                                    trap = TrapReason::IllegalInstruction;
                                    break 'cycle_block;
                                }
                            },
                            7 => {
                                report_opcode("REMU");
                                // REMU
                                if Config::SUPPORT_DIV {
                                    if operand_2 == 0 {
                                        operand_1
                                    } else {
                                        operand_1 % operand_2
                                    }
                                } else {
                                    trap = TrapReason::IllegalInstruction;
                                    break 'cycle_block;
                                }
                            },
                            _ => unsafe {
                                unreachable_unchecked()
                            },
                        };
                    } else {
                        // basic set
                        const ARITHMETIC_SHIFT_RIGHT_TEST_MASK: u32 = 0x40000000;
                        const SUB_TEST_MASK: u32 = 0x40000000;
                        const ROTATE_MASK: u32 = 0b0110_0000_0000_0000_0000_0000_0000_0000u32;
                        ret_val = match funct3 {
                            0 => {
                                if is_r_type && instr & SUB_TEST_MASK != 0 {
                                    report_opcode("SUB");
                                    operand_1.wrapping_sub(operand_2)
                                } else {
                                    report_opcode("ADD");
                                    operand_1.wrapping_add(operand_2)
                                }
                            },
                            1 => {
                                if instr & ROTATE_MASK != 0 {
                                    report_opcode("ROL");
                                    if Config::SUPPORT_ROT {
                                        operand_1.rotate_left(operand_2 & 0x1f)
                                    } else {
                                        trap = TrapReason::IllegalInstruction;
                                        break 'cycle_block;
                                    }
                                } else {
                                    report_opcode("SLL");
                                    // Shift left
                                    // shift is encoded in lowest 5 bits
                                    operand_1 << (operand_2 & 0x1f)
                                }
                            },
                            2 => {
                                report_opcode("LT");
                                // Signed LT
                                ((operand_1 as i32) < (operand_2 as i32)) as u32
                            },
                            3 => {
                                report_opcode("LTU");
                                // Unsigned LT
                                (operand_1 < operand_2) as u32
                            },
                            4 => {
                                report_opcode("XOR");
                                // XOR
                                operand_1 ^ operand_2
                            },
                            5 => {
                                if instr & ROTATE_MASK == ROTATE_MASK {
                                    report_opcode("ROR");
                                    if Config::SUPPORT_ROT {
                                        operand_1.rotate_right(operand_2 & 0x1f)
                                    } else {
                                        trap = TrapReason::IllegalInstruction;
                                        break 'cycle_block;
                                    }
                                } else {
                                    if instr & ARITHMETIC_SHIFT_RIGHT_TEST_MASK != 0 {
                                        report_opcode("SRA");
                                        // Arithmetic shift right
                                        // shift is encoded in lowest 5 bits

                                        if Config::SUPPORT_SRA {
                                            ((operand_1 as i32) >> (operand_2 & 0x1f)) as u32
                                        } else {
                                            trap = TrapReason::IllegalInstruction;
                                            break 'cycle_block;
                                        }
                                    } else {
                                        report_opcode("SRL");
                                        operand_1  >> (operand_2 & 0x1f)
                                    }
                                }
                            },
                            6 => {
                                report_opcode("OR");
                                // OR
                                operand_1 | operand_2
                            },
                            7 => {
                                report_opcode("AND");
                                // AND
                                operand_1 & operand_2
                            },
                            _ => unsafe {
                                unreachable_unchecked()
                            },
                        };

                        let valid_encoding = if !is_r_type {
                            // the only invalid encodings are in case of SLLI, SRLI, SRAI which require
                            // predetermined funct7

                            // Also allow ROL/ROR/RORI
                            match funct3 {
                                1 => funct7 == 0 || funct7 == 0b0110000,
                                5 => funct7 == 0 || funct7 == 0b0100000 || funct7 == 0b0110000,
                                _ => true
                            }
                        } else {
                            match funct3 {
                                0 | 5 => funct7 == 0 || funct7 == 0b0100000,
                                _ => funct7 == 0,
                            }
                        };

                        if !valid_encoding {
                            trap = TrapReason::IllegalInstruction;
                            break 'cycle_block;
                        };
                    }
                },
                // 0b0001111 => {
                //     // nothing to do in fence, our memory is linear
                //     rd = 0;
                // },
                0b1110011 => {
                    // various control instructions, we implement only a subset
                    const ZICSR_MASK: u32 = 0x3;
                    const ZIMOP_MASK: u32 = 0x4;

                    let funct3 = ITypeOpcode::funct3(instr);
                    let csr_number = ITypeOpcode::imm(instr);

                    // so now we can just use full integer values for csr numbers
                    if funct3 & ZICSR_MASK != 0 {
                        report_opcode("CSR");
                        let csr_privilege_mode = get_bits_and_align_right(csr_number, 8, 2);
                        let csr_privilege_mode = Mode::from_proper_bit_value(csr_privilege_mode);
                        if csr_privilege_mode.as_register_value() > current_privilege_mode.as_register_value() {
                            trap = TrapReason::IllegalInstruction;
                            break 'cycle_block;
                        }
                        let rs1_as_imm = ITypeOpcode::rs1(instr);

                        if Config::SUPPORT_STANDARD_CSRS == false {
                            // read
                            match csr_number {
                                NON_DETERMINISM_CSR => {
                                    // to improve oracle usability we can try to avoid read
                                    // if we intend to write, so check oracle config
                                    ret_val = if ND::SHOULD_MOCK_READS_BEFORE_WRITES {
                                        // all our oracle accesses are implemented via CSRRW
                                        // with either rd == 0 or rs1 == 0, so if we have
                                        // rd == 0 here it's just a read
                                        if rd == 0
                                        {
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
                                    tracer.trace_non_determinism_read(ret_val);
                                }
                                MARKER_CSR => {
                                  // Do nothing here, we do the work in the write case
                                }
                                csr => {
                                    assert!(Config::ALLOWED_DELEGATION_CSRS.contains(&csr), "Machine {:?} is not configured to support CSR number {} at pc 0x{:08x}", Config::default(), csr, pc);
                                    // println!("Custom CSR = 0x{:04x} READ at cycle {}", csr_number, proc_cycle);
                                    csr_processor.process_read(self, memory_source, non_determinism_source, tracer, mmu, csr_number, rs1, rs1_as_imm, &mut ret_val, &mut trap);
                                    if trap.is_a_trap() {
                                        break 'cycle_block;
                                    }
                                }
                            }

                            let write_val;
                            // update
                            if Config::SUPPORT_ONLY_CSRRW == false {
                                match funct3 {
                                    1 => write_val = rs1, //CSRRW
                                    2 => write_val = ret_val | rs1, //CSRRS
                                    3 => write_val = ret_val & !rs1, //CSRRC
                                    5 => write_val = rs1_as_imm, //CSRRWI
                                    6 => write_val = ret_val | rs1_as_imm, //CSRRSI
                                    7 => write_val = ret_val & !rs1_as_imm, //CSRRCI
                                    _ => {
                                        trap = TrapReason::IllegalInstruction;
                                        break 'cycle_block;
                                    }
                                }
                            } else {
                                match funct3 {
                                    1 => write_val = rs1, //CSRRW
                                    _ => {
                                        trap = TrapReason::IllegalInstruction;
                                        break 'cycle_block;
                                    }
                                }
                            }

                            match csr_number {
                                NON_DETERMINISM_CSR => {

                                    if ND::SHOULD_IGNORE_WRITES_AFTER_READS {
                                        // if we have rs1 == 0 then we should ignore write into CSR,
                                        // as our main intension was to read
                                        if rs1_as_imm == 0 // index of rs1
                                        {
                                            // do nothing
                                        } else {
                                            non_determinism_source.write_with_memory_access(&*memory_source, write_val);
                                        }
                                    } else {
                                        non_determinism_source.write_with_memory_access(&*memory_source, write_val);
                                    }
                                }
                                MARKER_CSR => {
                                  self.add_marker()
                                }
                                csr => {
                                    assert!(Config::ALLOWED_DELEGATION_CSRS.contains(&csr), "Machine {:?} is not configured to support CSR number {}", Config::default(), csr);
                                    Self::add_delegation(csr);
                                    // let t = CSR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::AcqRel);
                                    // println!("Custom CSR = 0x{:04x} WRITE at cycle {}, total: {}", csr_number, proc_cycle, t + 1);
                                    csr_processor.process_write(self, memory_source, non_determinism_source, tracer, mmu, csr_number, rs1, rs1_as_imm, &mut trap);
                                    if trap.is_a_trap() {
                                        break 'cycle_block;
                                    }
                                }
                            }
                        } else {
                            // read
                            match csr_number {
                                0x180 => {
                                    // satp
                                    ret_val = mmu.read_sapt(current_privilege_mode, &mut trap);
                                    if trap.is_a_trap() {
                                        break 'cycle_block;
                                    }
                                },
                                0x300 => ret_val = self.machine_mode_trap_data.state.status, // mstatus
                                //0x301 => ret_val = 0b01_00_0000_0001_0000_0001_0001_0000_0000u32, //misa (I + M + usemode)
                                0x304 => ret_val = self.machine_mode_trap_data.state.ie, // mie
                                0x305 => ret_val = self.machine_mode_trap_data.setup.tvec, // mtvec
                                0x340 => ret_val = self.machine_mode_trap_data.handling.scratch, // mscratch
                                0x341 => ret_val = self.machine_mode_trap_data.handling.epc, // mepc
                                0x342 => ret_val = self.machine_mode_trap_data.handling.cause, // mcause
                                0x343 => ret_val = self.machine_mode_trap_data.handling.tval, // mtval
                                0x344 => ret_val = self.machine_mode_trap_data.state.ip, // mip
                                //0xc00 => ret_val = self.cycle_counter as u32, // cycle
                                //0xf11 => ret_val = 0, // vendor ID, will come up later on,
                                NON_DETERMINISM_CSR => {
                                    // to improve oracle usability we can try to avoid read
                                    // if we intend to write, so check oracle config
                                    ret_val = if ND::SHOULD_MOCK_READS_BEFORE_WRITES {
                                        // all our oracle accesses are implemented via CSRRW
                                        // with either rd == 0 or rs1 == 0, so if we have
                                        // rd == 0 here it's just a read
                                        if rd == 0
                                        {
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
                                    tracer.trace_non_determinism_read(ret_val);
                                }
                                MARKER_CSR => {
                                  // Do nothing here
                                }
                                csr => {
                                    assert!(Config::ALLOWED_DELEGATION_CSRS.contains(&csr), "Machine {:?} is not configured to support CSR number {}", Config::default(), csr);
                                    // println!("Custom CSR = 0x{:04x} READ at cycle {}", csr_number, proc_cycle);
                                    csr_processor.process_read(self, memory_source, non_determinism_source, tracer, mmu, csr_number, rs1, rs1_as_imm, &mut ret_val, &mut trap);
                                    if trap.is_a_trap() {
                                        break 'cycle_block;
                                    }
                                }
                            }

                            let write_val;
                            // update
                            if Config::SUPPORT_ONLY_CSRRW == false {
                                match funct3 {
                                    1 => write_val = rs1, //CSRRW
                                    2 => write_val = ret_val | rs1, //CSRRS
                                    3 => write_val = ret_val & !rs1, //CSRRC
                                    5 => write_val = rs1_as_imm, //CSRRWI
                                    6 => write_val = ret_val | rs1_as_imm, //CSRRSI
                                    7 => write_val = ret_val & !rs1_as_imm, //CSRRCI
                                    _ => {
                                        trap = TrapReason::IllegalInstruction;
                                        break 'cycle_block;
                                    }
                                }
                            } else {
                                match funct3 {
                                    1 => write_val = rs1, //CSRRW
                                    _ => {
                                        trap = TrapReason::IllegalInstruction;
                                        break 'cycle_block;
                                    }
                                }
                            }

                            match csr_number {
                                0x180 => {
                                    // satp
                                    mmu.write_sapt(write_val, current_privilege_mode, &mut trap);
                                    if trap.is_a_trap() {
                                        break 'cycle_block;
                                    }
                                },
                                0x300 => self.machine_mode_trap_data.state.status = write_val, // mstatus
                                0x304 => self.machine_mode_trap_data.state.ie = write_val, // mie
                                0x305 => self.machine_mode_trap_data.setup.tvec = write_val, // mtvec
                                0x340 => self.machine_mode_trap_data.handling.scratch = write_val, // mscratch
                                0x341 => self.machine_mode_trap_data.handling.epc = write_val, // mepc
                                0x342 => self.machine_mode_trap_data.handling.cause = write_val, // mcause
                                0x343 => self.machine_mode_trap_data.handling.tval = write_val, // mtval
                                0x344 => self.machine_mode_trap_data.state.ip = write_val, // mip
                                NON_DETERMINISM_CSR => {
                                    if ND::SHOULD_IGNORE_WRITES_AFTER_READS {
                                        // if we have rs1 == 0 then we should ignore write into CSR,
                                        // as our main intension was to read
                                        if rs1_as_imm == 0 // index of rs1
                                        {
                                            // do nothing
                                        } else {
                                            non_determinism_source.write_with_memory_access(&*memory_source, write_val);
                                        }
                                    } else {
                                        non_determinism_source.write_with_memory_access(&*memory_source, write_val);
                                    }
                                }
                                MARKER_CSR => {
                                  self.add_marker()
                                }
                                csr => {
                                    assert!(Config::ALLOWED_DELEGATION_CSRS.contains(&csr), "Machine {:?} is not configured to support CSR number {}", Config::default(), csr);
                                    // let t = CSR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::AcqRel);
                                    Self::add_delegation(csr);
                                    csr_processor.process_write(self, memory_source, non_determinism_source, tracer, mmu, csr_number, rs1, rs1_as_imm, &mut trap);
                                    if trap.is_a_trap() {
                                        break 'cycle_block;
                                    }
                                }
                            }
                        }
                        // and writeback
                    } else if funct3 == 0b000 {
                        // TODO: add to configuration later
                        trap = TrapReason::IllegalInstruction;
                        break 'cycle_block;

                        // // SYSTEM
                        // rd = 0;
                        // // mainly we support WFI, MRET, ECALL and EBREAK
                        // if csr_number == 0x105 {
                        //     println!("WFI: proc_cycle: {:?}, pc = {}, opcode = 0x{:08x}", proc_cycle, pc, instr);
                        //     self.extra_flags.set_wait_for_interrupt_bit();
                        //     self.pc = pc.wrapping_add(4u32);
                        //     return;
                        // } else if csr_number == 0x302 {
                        //     // MRET
                        //     let existing_mstatus = self.machine_mode_trap_data.state.status;
                        //     let previous_privilege = MStatusRegister::mpp(existing_mstatus);
                        //     // MRET then in mstatus/mstatush sets MPV=0, MPP=0,
                        //     // MIE=MPIE, and MPIE=1. Lastly, MRET sets the privilege mode as previously determined, and
                        //     // sets pc=mepc.
                        //     MStatusRegister::clear_mpp(&mut self.machine_mode_trap_data.state.status);
                        //     MStatusRegister::clear_mprv(&mut self.machine_mode_trap_data.state.status);
                        //     let mpie = MStatusRegister::mpie_aligned_bit(self.machine_mode_trap_data.state.status);
                        //     MStatusRegister::set_mie_to_value(&mut self.machine_mode_trap_data.state.status, mpie);
                        //     MStatusRegister::set_mpie(&mut self.machine_mode_trap_data.state.status);

                        //     // set privilege
                        //     self.extra_flags.set_mode_raw(Mode::User.as_register_value() | previous_privilege);
                        //     pc = self.machine_mode_trap_data.handling.epc.wrapping_sub(4u32);
                        // } else {
                        //     match csr_number {
                        //         0 => {
                        //             // ECALL
                        //             trap = match current_privilege_mode {
                        //                 Mode::Machine => TrapReason::EnvironmentCallFromMMode,
                        //                 Mode::User => TrapReason::EnvironmentCallFromUMode,
                        //                 _ => TrapReason::IllegalInstruction,
                        //             };

                        //             break 'cycle_block;
                        //         },
                        //         1 => {
                        //             // EBREAK
                        //             trap = TrapReason::Breakpoint;
                        //             break 'cycle_block;
                        //         },
                        //         _ => {
                        //             trap = TrapReason::IllegalInstruction;
                        //             break 'cycle_block;
                        //         }
                        //     }
                        // }
                    } else if funct3 & ZIMOP_MASK == ZIMOP_MASK {
                        const MOP_FUNCT7_TEST: u32 = 0b1000001u32;
                        let funct7 = RTypeOpcode::funct7(instr);
                        if funct7 & MOP_FUNCT7_TEST == MOP_FUNCT7_TEST {
                            report_opcode("MOP");
                            if Config::SUPPORT_MOPS {
                                use field::{Field, Mersenne31Field};

                                let mop_number = ((funct7 & 0b110) >> 1) | ((funct7 & 0b100000) >> 5);
                                let operand_1 = rs1;
                                let operand_2 = rs2;
                                let mut operand_1 = Mersenne31Field::from_nonreduced_u32(operand_1);
                                let operand_2 = Mersenne31Field::from_nonreduced_u32(operand_2);
                                match mop_number {
                                    0 => {
                                        operand_1.add_assign(&operand_2);
                                    },
                                    1 => {
                                        operand_1.sub_assign(&operand_2);
                                    },
                                    2 => {
                                        operand_1.mul_assign(&operand_2);
                                    }
                                    _ => {
                                        trap = TrapReason::IllegalInstruction;
                                        break 'cycle_block;
                                    }
                                }
                                ret_val = operand_1.to_reduced_u32();
                            } else {
                                trap = TrapReason::IllegalInstruction;
                                break 'cycle_block;
                            }
                        } else {
                            trap = TrapReason::IllegalInstruction;
                            break 'cycle_block;
                        }
                    } else {
                        trap = TrapReason::IllegalInstruction;
                        break 'cycle_block;
                    }
                },
                0b00101111 => {
                    // RV32A, explicitly not supported
                    trap = TrapReason::IllegalInstruction;
                    break 'cycle_block;
                },
                _ => {
                    // any other instruction
                    trap = TrapReason::IllegalInstruction;
                    break 'cycle_block;
                }
            }

            // If there was a trap, do NOT allow register writeback.
            debug_assert_eq!(trap, TrapReason::NoTrap);
            // println!("Set x{:02} = 0x{:08x}", rd, ret_val);
            self.set_register(rd, ret_val, tracer);

            // traps below will update PC themself, so it only happens if we have NO trap
            pc = pc.wrapping_add(4u32);
        }

        // Handle traps and interrupts.
        if trap.is_a_trap() {
            println!("trap: {:?}, pc: {:08x}, instr: {:08x}", trap, pc, instr);

            if Config::HANDLE_EXCEPTIONS == false {
                panic!("Simulator encountered an exception");
            } else {
                let trap = trap.as_register_value();
                if trap & INTERRUPT_MASK != 0 {
                    // interrupt, not a trap. Always machine level in our system
                    self.machine_mode_trap_data.handling.cause = trap;
                    self.machine_mode_trap_data.handling.tval = 0;
                    pc = pc.wrapping_add(4u32); // PC points to where the PC will return!
                } else {
                    self.machine_mode_trap_data.handling.cause = trap;
                    // TODO: here we have a freedom of what to put into tval. We place opcode value now, because PC will be placed into EPC below
                    self.machine_mode_trap_data.handling.tval = instr;
                }
                // println!("Trapping at pc = 0x{:08x} into PC = 0x{:08x}. MECP is set to 0x{:08x}", pc, self.machine_mode_trap_data.setup.tvec, pc);
                // self.pretty_dump();
                // self.stack_dump(memory, mmu);

                self.machine_mode_trap_data.handling.epc = pc;
                // update machine status register to reflect previous privilege

                // On an interrupt, the system moves current MIE into MPIE
                let mie =
                    MStatusRegister::mie_aligned_bit(self.machine_mode_trap_data.state.status);
                MStatusRegister::set_mpie_to_value(
                    &mut self.machine_mode_trap_data.state.status,
                    mie,
                );

                // go to trap vector
                pc = self.machine_mode_trap_data.setup.tvec;

                // Enter machine mode
                self.extra_flags.set_mode(Mode::Machine);
            }
        }

        self.pc = pc;

        // for debugging
        self.sapt = mmu.read_sapt(current_privilege_mode, &mut trap);
        self.count_new_cycle_for_markers();
        tracer.at_cycle_end(&*self);

        //let trap = trap.as_register_value();
        //println!("end of cycle: PC = 0x{:08x}, trap = 0x{:08x}, interrupt = {:?}", self.pc, trap, trap & INTERRUPT_MASK != 0);
    }

    pub fn pretty_dump(&self) {
        println!(
            "PC = 0x{:08x}, RA = 0x{:08x}, SP = 0x{:08x}, GP = 0x{:08x}",
            self.pc, self.registers[1], self.registers[2], self.registers[3]
        );
        for chunk in self.registers.iter().enumerate().array_chunks::<4>() {
            for (idx, reg) in chunk.iter() {
                print!("x{:02} = 0x{:08x}, ", idx, reg);
            }
            println!("");
        }
    }
}
