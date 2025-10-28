use crate::types::Num;
use field::PrimeField;

pub const NUM_INSTRUCTION_TYPES: usize = 6;
pub const CSR_ENCODING_BITLEN: usize = 12;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum InstructionType {
    RType = 0,
    IType,
    SType,
    BType,
    UType,
    JType,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
#[repr(u32)]
pub enum ExecutorOperation {
    INVALID = 0,
    LUI,
    AUIPC,
    JMP,
    BEQ,
    BNE,
    BLT,
    BGE,
    BLTU,
    BGEU,
    BYTEMEM,
    HALFWORDMEM,
    WORDMEM,
    ADD,
    SUB,
    SLT,
    SLTU,
    BINARY,
    SLL,
    SRL,
    SRA,
    NOP,
    ECALLBREAK,
    MRET,
    WFI,
    CSRRW,
    CSRRS,
    CSRRC,
    MUL,
    MULH,
    MULHSU,
    MULHU,
    DIV,
    DIVU,
    REM,
    REMU,
}

pub const NUM_EXECUTOR_OPERATIONS: usize = const { (ExecutorOperation::REMU as u32 + 1) as usize };

pub const NUM_OF_CSR: usize = 11;
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
#[repr(u32)]
pub enum CsrRegisters {
    Invalid = 0,
    Satp,
    Mstatus,
    Mie,
    Mtvec,
    Mscratch,
    Mepc,
    Mcause,
    Mtval,
    Mip,
    Mcustom,
}

impl CsrRegisters {
    pub fn to_encoding_variable<F: PrimeField>(&self) -> Num<F> {
        let encoding: u64 = match self {
            Self::Satp => 0x180,
            Self::Mstatus => 0x300,
            Self::Mie => 0x304,
            Self::Mtvec => 0x305,
            Self::Mscratch => 0x340,
            Self::Mepc => 0x341,
            Self::Mcause => 0x342,
            Self::Mtval => 0x343,
            Self::Mip => 0x344,
            Self::Mcustom => 0x7c0,
            Self::Invalid => 0x00,
        };

        Num::Constant(F::from_u64(encoding as u64).unwrap())
    }

    pub fn from_encoding(num: u32) -> Self {
        match num {
            0x180 => Self::Satp,
            0x300 => Self::Mstatus,
            0x304 => Self::Mie,
            0x305 => Self::Mtvec,
            0x340 => Self::Mscratch,
            0x341 => Self::Mepc,
            0x342 => Self::Mcause,
            0x343 => Self::Mtval,
            0x344 => Self::Mip,
            0x7c0 => Self::Mcustom,
            _ => Self::Invalid,
        }
    }

    pub fn get_rw_mode(&self) -> CsrRwMode {
        CsrRwMode::RW
    }

    pub fn get_privilege_mode(&self) -> Mode {
        match self {
            CsrRegisters::Satp => Mode::Supervisor,
            _ => Mode::Machine,
        }
    }
}

// 10 bit of csr:
// 1 - RO
// 0 - RW
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CsrRwMode {
    RO,
    RW,
}

// 8 & 9 bits of csr
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum Mode {
    User = 0,
    Supervisor = 1,
    Reserved = 2,
    Machine = 3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum InterruptReason {
    Reserved = 0,
    SupervisorSoftwareInterrupt = 1,
    MachineSoftwareInterrupt = 3,
    SupervisorTimerInterrupt = 5,
    MachineTimerInterrupt = 7,
    SupervisorExternalInterrupt = 9,
    MachineExternalInterrupt = 11,
}

impl InterruptReason {
    #[inline(always)]
    pub const fn as_register_value(self) -> u32 {
        self as u32
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum TrapReason {
    InstructionAddressMisaligned = 0,
    InstructionAccessFault = 1,
    IllegalInstruction = 2,
    Breakpoint = 3,
    LoadAddressMisaligned = 4,
    LoadAccessFault = 5,
    StoreOrAMOAddressMisaligned = 6,
    StoreOrAMOAccessFault = 7,
    EnvironmentCallFromUMode = 8,
    EnvironmentCallFromSMode = 9,
    EnvironmentCallFromMMode = 11,
    InstructionPageFault = 12,
    LoadPageFault = 13,
    StoreOrAMOPageFault = 15,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum MStatusRegister {
    Sie = 1,
    Mie = 3,
    Spie = 5,
    Ube = 6,
    Mpie = 7,
    Spp = 8,
    Vs = 9,   //2 bits
    Mpp = 11, //2 bits
    Fs = 13,  //2 bits
    Cs = 15,  //xs? //2 bits
    Mprv = 17,
    Sum = 18,
    Mxr = 19,
    Tvm = 20,
    Tw = 21,
    Tsr = 22,
    Sd = 31,
}
