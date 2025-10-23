pub const OP_IMM_SUBMASK: u8 = 0b0010011;
pub const OP_SUBMASK: u8 = 0b0110011;

pub const OPCODE_LUI: u8 = 0b0110111;
pub const OPCODE_AUIPC: u8 = 0b0010111;
pub const OPCODE_JAL: u8 = 0b1101111;
pub const OPCODE_JALR: u8 = 0b1100111;
pub const OPCODE_BRANCH: u8 = 0b1100011;
pub const OPCODE_LOAD: u8 = 0b0000011;
pub const OPCODE_STORE: u8 = 0b0100011;
pub const OPCODE_SYSTEM: u8 = 0b1110011;

pub const GROUP_IMM_ADD: u8 = 0b000;
pub const GROUP_IMM_SLL: u8 = 0b001;
pub const GROUP_IMM_SLT: u8 = 0b010;
pub const GROUP_IMM_SLTU: u8 = 0b011;
pub const GROUP_IMM_XOR: u8 = 0b100;
pub const GROUP_IMM_SRL: u8 = 0b101;
pub const GROUP_IMM_SRA: u8 = 0b101;
pub const GROUP_IMM_ROR: u8 = 0b101;
pub const GROUP_IMM_OR: u8 = 0b110;
pub const GROUP_IMM_AND: u8 = 0b111;

pub(crate) const SUB_FUNCT7: u8 = 0b0100000;
pub(crate) const SLL_FUNCT7: u8 = 0;
pub(crate) const SRL_FUNCT7: u8 = 0;
pub(crate) const SRA_FUNCT7: u8 = 0b0100000;
pub(crate) const ROT_FUNCT7: u8 = 0b0110000;
pub(crate) const M_EXT_FUNCT7: u8 = 0b0000001;
