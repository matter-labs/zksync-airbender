#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
#[non_exhaustive]
pub enum DelegationType {
    Blake = 0,
    BigInt,
    Keccak,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
#[non_exhaustive]
pub enum InstructionName {
    Illegal = 0, // Important
    Lui,
    Auipc,
    Jal,
    Jalr,
    Addi,
    Slli,
    Srli,
    Srai,
    Slti,
    Sltiu,
    Xori,
    Ori,
    Andi,
    Mul,
    Mulh,
    Mulhsu,
    Mulhu,
    Div,
    Divu,
    Rem,
    Remu,
    Add,
    Sub,
    Sll,
    Rol,
    Srl,
    Sra,
    Ror,
    Slt,
    Sltu,
    Xor,
    Or,
    And,
    Branch,
    Lhu,
    Lbu,
    Lw,
    Lh,
    Lb,
    Sb,
    Sh,
    Sw,
    ZimopAdd,
    ZimopSub,
    ZimopMul,
    ZicsrDelegation,
    ZicsrMarkerCsr,
    ZicsrNonDeterminismRead,
    ZicsrNonDeterminismWrite,
    FormalEnd,
}

pub const NUM_OPCODE_HANDLERS: usize = InstructionName::FormalEnd as u8 as usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C, align(8))]
pub struct Instruction {
    pub name: InstructionName,
    pub rs1: u8,
    pub rs2: u8,
    pub rd: u8,
    pub imm: u32, // or delegation type
}

impl Instruction {
    #[inline(always)]
    const fn as_byte_slice(&self) -> &[u8; 8] {
        unsafe { core::mem::transmute::<_, _>(self) }
    }

    pub fn new(name: InstructionName, rs1: u8, rs2: u8, rd: u8, imm: u32) -> Self {
        Self {
            name,
            rs1,
            rs2,
            rd,
            imm,
        }
    }

    pub fn emit(&self, dst: &mut impl std::io::Write) -> Result<usize, String> {
        dst.write_all(self.as_byte_slice())
            .map(|_| core::mem::size_of::<Self>())
            .map_err(|x| x.to_string())
    }

    pub fn from_imm(name: InstructionName, rs1: u8, rs2: u8, rd: u8, imm: u32) -> Self {
        Self {
            name,
            rs1,
            rs2,
            rd,
            imm,
        }
    }
}
