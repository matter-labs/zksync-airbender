mod decode;
mod encoding_types;
mod instr_stream;
mod instructions;

use self::decode::*;
use self::encoding_types::*;
pub use self::instr_stream::*;
use self::instructions::*;

pub const CYCLE_CSR_INDEX: u32 = 3072;

#[must_use]
#[inline(always)]
pub const fn funct3_bits(src: u32) -> u8 {
    ((src >> 12) & 0b111) as u8
}

#[must_use]
#[inline(always)]
pub const fn funct7_bits(src: u32) -> u8 {
    ((src >> 25) & 0b1111111) as u8
}

#[must_use]
#[inline(always)]
pub const fn get_opcode_bits(src: u32) -> u8 {
    (src & 0b01111111) as u8 // opcode is always lowest 7 bits
}

#[must_use]
#[inline(always)]
pub const fn get_rd_bits(src: u32) -> u8 {
    ((src >> 7) & 0b00011111) as u8
}

#[must_use]
#[inline(always)]
pub const fn get_formal_rs1_bits(src: u32) -> u8 {
    ((src >> 15) & 0b00011111) as u8
}

#[must_use]
#[inline(always)]
pub const fn get_formal_rs2_bits(src: u32) -> u8 {
    ((src >> 20) & 0b00011111) as u8
}

pub trait DecodingOptions: 'static + Sized {
    const SUPPORT_SUBWORD_MEM_ACCESS: bool;
    const SUPPORT_MUL_DIV: bool;
    const SUPPORT_SIGNED_MUL_DIV: bool;
    const SUPPORT_MOP: bool;
}

pub fn decode<OPT: DecodingOptions>(opcode: u32) -> Instruction {
    let rd = get_rd_bits(opcode);
    let formal_rs1 = get_formal_rs1_bits(opcode);
    let formal_rs2 = get_formal_rs2_bits(opcode);
    let op = get_opcode_bits(opcode);
    let funct3 = funct3_bits(opcode);
    let funct7 = funct7_bits(opcode);

    let instruction = match op {
        OPCODE_LUI => {
            // U format
            let imm = UTypeOpcode::imm(opcode);

            Instruction::from_imm(InstructionName::Lui, formal_rs1, formal_rs2, rd, imm)
        }
        OPCODE_AUIPC => {
            // U format
            let imm = UTypeOpcode::imm(opcode);

            Instruction::from_imm(InstructionName::Auipc, formal_rs1, formal_rs2, rd, imm)
        }
        OPCODE_JAL => {
            // J format
            let mut imm: u32 = JTypeOpcode::imm(opcode);
            sign_extend(&mut imm, 21);

            Instruction::from_imm(InstructionName::Jal, formal_rs1, formal_rs2, rd, imm)
        }
        OPCODE_JALR => {
            // I format
            let mut imm: u32 = ITypeOpcode::imm(opcode);
            // quasi sign extend
            sign_extend(&mut imm, 12);
            Instruction::from_imm(InstructionName::Jalr, formal_rs1, formal_rs2, rd, imm)
        }
        OPCODE_BRANCH => {
            // B format
            let mut imm = BTypeOpcode::imm(opcode);
            sign_extend(&mut imm, 13);

            // NOTE: branch instructions do not write, and we always model it as RD = 0 and write of 0 for tracing purposes.
            // And we will put funct3 into rd here to reduce code size
            match funct3 {
                0 | 1 | 4 | 5 | 6 | 7 => {}
                _ => {
                    panic!("Unknown opcode 0x{:08x}", opcode);
                }
            };

            Instruction::from_imm(InstructionName::Branch, formal_rs1, formal_rs2, funct3, imm)
        }
        OP_IMM_SUBMASK => {
            let mut imm = ITypeOpcode::imm(opcode);
            sign_extend(&mut imm, 12);

            let instr = match funct3 {
                GROUP_IMM_ADD => {
                    Instruction::from_imm(InstructionName::Addi, formal_rs1, formal_rs2, rd, imm)
                }
                GROUP_IMM_SLL if funct7 == SLL_FUNCT7 => {
                    // Shift is encoded in the lowest 5 bits
                    Instruction::from_imm(
                        InstructionName::Slli,
                        formal_rs1,
                        formal_rs2,
                        rd,
                        imm & 0x1f,
                    )
                }
                GROUP_IMM_SRL if funct7 == SRL_FUNCT7 => {
                    // Shift is encoded in the lowest 5 bits
                    Instruction::from_imm(
                        InstructionName::Srli,
                        formal_rs1,
                        formal_rs2,
                        rd,
                        imm & 0x1f,
                    )
                }
                GROUP_IMM_SRA if funct7 == SRA_FUNCT7 => {
                    // Shift is encoded in the lowest 5 bits
                    Instruction::from_imm(
                        InstructionName::Srai,
                        formal_rs1,
                        formal_rs2,
                        rd,
                        imm & 0x1f,
                    )
                }
                0b101 if funct7 == ROT_FUNCT7 => {
                    panic!("not supporting rotate family")
                    // Arithmetic shift right
                    // shift is encoded in lowest 5 bits

                    // if Config::SUPPORT_ROT {
                    //     operand_1.rotate_right(operand_2 & 0x1f)
                    // } else {
                    //     panic!("Unknown opcode 0x{:08x}", opcode);
                    // }
                }
                GROUP_IMM_SLT => {
                    Instruction::from_imm(InstructionName::Slti, formal_rs1, formal_rs2, rd, imm)
                }
                GROUP_IMM_SLTU => {
                    Instruction::from_imm(InstructionName::Sltiu, formal_rs1, formal_rs2, rd, imm)
                }
                GROUP_IMM_XOR => {
                    Instruction::from_imm(InstructionName::Xori, formal_rs1, formal_rs2, rd, imm)
                }
                GROUP_IMM_OR => {
                    Instruction::from_imm(InstructionName::Ori, formal_rs1, formal_rs2, rd, imm)
                }
                GROUP_IMM_AND => {
                    Instruction::from_imm(InstructionName::Andi, formal_rs1, formal_rs2, rd, imm)
                }
                _ => {
                    panic!("Unknown opcode 0x{:08x}", opcode);
                }
            };

            instr
        }
        OP_SUBMASK => {
            if funct7 == M_EXT_FUNCT7 {
                // Multiplication extension
                match funct3 {
                    0b000 => {
                        if OPT::SUPPORT_MUL_DIV {
                            Instruction::from_imm(
                                InstructionName::Mul,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        } else {
                            Instruction::from_imm(
                                InstructionName::Illegal,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        }
                    }
                    0b001 => {
                        if OPT::SUPPORT_MUL_DIV && OPT::SUPPORT_SIGNED_MUL_DIV {
                            Instruction::from_imm(
                                InstructionName::Mulh,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        } else {
                            Instruction::from_imm(
                                InstructionName::Illegal,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        }
                    }
                    0b010 => {
                        if OPT::SUPPORT_MUL_DIV && OPT::SUPPORT_SIGNED_MUL_DIV {
                            Instruction::from_imm(
                                InstructionName::Mulhsu,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        } else {
                            Instruction::from_imm(
                                InstructionName::Illegal,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        }
                    }
                    0b011 => {
                        if OPT::SUPPORT_MUL_DIV {
                            Instruction::from_imm(
                                InstructionName::Mulhu,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        } else {
                            Instruction::from_imm(
                                InstructionName::Illegal,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        }
                    }
                    0b100 => {
                        if OPT::SUPPORT_MUL_DIV && OPT::SUPPORT_SIGNED_MUL_DIV {
                            Instruction::from_imm(
                                InstructionName::Div,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        } else {
                            Instruction::from_imm(
                                InstructionName::Illegal,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        }
                    }
                    0b101 => {
                        if OPT::SUPPORT_MUL_DIV {
                            Instruction::from_imm(
                                InstructionName::Divu,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        } else {
                            Instruction::from_imm(
                                InstructionName::Illegal,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        }
                    }
                    0b110 => {
                        if OPT::SUPPORT_MUL_DIV && OPT::SUPPORT_SIGNED_MUL_DIV {
                            Instruction::from_imm(
                                InstructionName::Rem,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        } else {
                            Instruction::from_imm(
                                InstructionName::Illegal,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        }
                    }
                    0b111 => {
                        if OPT::SUPPORT_MUL_DIV {
                            Instruction::from_imm(
                                InstructionName::Remu,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        } else {
                            Instruction::from_imm(
                                InstructionName::Illegal,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        }
                    }

                    _ => unreachable!(),
                }
            } else {
                // basic set
                match funct3 {
                    0b000 if funct7 == 0 => {
                        Instruction::from_imm(InstructionName::Add, formal_rs1, formal_rs2, rd, 0)
                    }
                    0b000 if funct7 == SUB_FUNCT7 => {
                        Instruction::from_imm(InstructionName::Sub, formal_rs1, formal_rs2, rd, 0)
                    }
                    0b001 if funct7 == SLL_FUNCT7 => {
                        Instruction::from_imm(InstructionName::Sll, formal_rs1, formal_rs2, rd, 0)
                    }
                    0b001 if funct7 == ROT_FUNCT7 => {
                        panic!("ROL is not supported");
                        // Instruction::from_imm(InstructionName::Rol, formal_rs1, formal_rs2, rd, 0)
                    }
                    0b101 if funct7 == SRL_FUNCT7 => {
                        Instruction::from_imm(InstructionName::Srl, formal_rs1, formal_rs2, rd, 0)
                    }
                    0b101 if funct7 == SRA_FUNCT7 => {
                        Instruction::from_imm(InstructionName::Sra, formal_rs1, formal_rs2, rd, 0)
                    }
                    0b101 if funct7 == ROT_FUNCT7 => {
                        panic!("ROR is not supported");
                        // Instruction::from_imm(InstructionName::Ror, formal_rs1, formal_rs2, rd, 0)
                    }
                    0b010 => {
                        Instruction::from_imm(InstructionName::Slt, formal_rs1, formal_rs2, rd, 0)
                    }
                    0b011 => {
                        Instruction::from_imm(InstructionName::Sltu, formal_rs1, formal_rs2, rd, 0)
                    }
                    0b100 => {
                        Instruction::from_imm(InstructionName::Xor, formal_rs1, formal_rs2, rd, 0)
                    }
                    0b110 => {
                        Instruction::from_imm(InstructionName::Or, formal_rs1, formal_rs2, rd, 0)
                    }
                    0b111 => {
                        Instruction::from_imm(InstructionName::And, formal_rs1, formal_rs2, rd, 0)
                    }
                    _ => {
                        panic!("Unknown opcode 0x{:08x}", opcode);
                    }
                }
            }
        }
        OPCODE_LOAD => {
            let mut imm = ITypeOpcode::imm(opcode);
            sign_extend(&mut imm, 12);

            match funct3 {
                a @ 0 | a @ 1 | a @ 2 | a @ 4 | a @ 5 => {
                    let instr = match a {
                        0 => {
                            if OPT::SUPPORT_SUBWORD_MEM_ACCESS {
                                Instruction::from_imm(
                                    InstructionName::Lb,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    imm,
                                )
                            } else {
                                Instruction::from_imm(
                                    InstructionName::Illegal,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    imm,
                                )
                            }
                        }
                        1 => {
                            if OPT::SUPPORT_SUBWORD_MEM_ACCESS {
                                Instruction::from_imm(
                                    InstructionName::Lh,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    imm,
                                )
                            } else {
                                Instruction::from_imm(
                                    InstructionName::Illegal,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    imm,
                                )
                            }
                        }
                        2 => Instruction::from_imm(
                            InstructionName::Lw,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            imm,
                        ),
                        4 => {
                            if OPT::SUPPORT_SUBWORD_MEM_ACCESS {
                                Instruction::from_imm(
                                    InstructionName::Lbu,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    imm,
                                )
                            } else {
                                Instruction::from_imm(
                                    InstructionName::Illegal,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    imm,
                                )
                            }
                        }
                        5 => {
                            if OPT::SUPPORT_SUBWORD_MEM_ACCESS {
                                Instruction::from_imm(
                                    InstructionName::Lhu,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    imm,
                                )
                            } else {
                                Instruction::from_imm(
                                    InstructionName::Illegal,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    imm,
                                )
                            }
                        }
                        _ => unreachable!(),
                    };

                    instr
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

            // access memory
            match funct3 {
                a @ 0 | a @ 1 | a @ 2 => {
                    let store_length = 1 << a;

                    match store_length {
                        1 => {
                            if OPT::SUPPORT_SUBWORD_MEM_ACCESS {
                                Instruction::from_imm(
                                    InstructionName::Sb,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    imm,
                                )
                            } else {
                                Instruction::from_imm(
                                    InstructionName::Illegal,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    imm,
                                )
                            }
                        }
                        2 => {
                            if OPT::SUPPORT_SUBWORD_MEM_ACCESS {
                                Instruction::from_imm(
                                    InstructionName::Sh,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    imm,
                                )
                            } else {
                                Instruction::from_imm(
                                    InstructionName::Illegal,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    imm,
                                )
                            }
                        }
                        4 => Instruction::from_imm(
                            InstructionName::Sw,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            imm,
                        ),
                        _ => unsafe { core::hint::unreachable_unchecked() },
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
            const ZIMOP_FUNCT3: u8 = 0b100;

            // if funct3 & ZIMOP_MASK == ZIMOP_MASK {
            let instr = if funct3 == ZIMOP_FUNCT3 {
                const MOP_FUNCT7_TEST: u8 = 0b1000001u8;

                if funct7 & MOP_FUNCT7_TEST == MOP_FUNCT7_TEST {
                    let mop_number = ((funct7 & 0b110) >> 1) | ((funct7 & 0b100000) >> 5);
                    match mop_number {
                        0 => {
                            if OPT::SUPPORT_MOP {
                                Instruction::from_imm(
                                    InstructionName::ZimopAdd,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    0,
                                )
                            } else {
                                Instruction::from_imm(
                                    InstructionName::Illegal,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    0,
                                )
                            }
                        }
                        1 => {
                            if OPT::SUPPORT_MOP {
                                Instruction::from_imm(
                                    InstructionName::ZimopSub,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    0,
                                )
                            } else {
                                Instruction::from_imm(
                                    InstructionName::Illegal,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    0,
                                )
                            }
                        }
                        2 => {
                            if OPT::SUPPORT_MOP {
                                Instruction::from_imm(
                                    InstructionName::ZimopMul,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    0,
                                )
                            } else {
                                Instruction::from_imm(
                                    InstructionName::Illegal,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    0,
                                )
                            }
                        }
                        _ => {
                            panic!("Unknown MOP number {}", mop_number);
                        }
                    }
                } else {
                    panic!();
                }
            } else if funct3 & ZICSR_MASK != 0 {
                let csr_number = ITypeOpcode::imm(opcode);

                // read
                let instr = match csr_number {
                    common_constants::NON_DETERMINISM_CSR => {
                        assert!(formal_rs1 == 0 || rd == 0, "Non-determinism CSR access should be readonly or write only, but is 0x{:08x}", opcode);
                        if formal_rs1 == 0 {
                            // we have rd != 0, so we read from source and write to rd
                            Instruction::from_imm(
                                InstructionName::ZicsrNonDeterminismRead,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        } else {
                            Instruction::from_imm(
                                InstructionName::ZicsrNonDeterminismWrite,
                                formal_rs1,
                                formal_rs2,
                                rd,
                                0,
                            )
                        }
                    }
                    common_constants::BLAKE2S_DELEGATION_CSR_REGISTER => {
                        assert_eq!(formal_rs1, 0);
                        assert_eq!(rd, 0);
                        Instruction::from_imm(
                            InstructionName::ZicsrDelegation,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            DelegationType::Blake as u32,
                        )
                    }
                    common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER => {
                        assert_eq!(formal_rs1, 0);
                        assert_eq!(rd, 0);
                        Instruction::from_imm(
                            InstructionName::ZicsrDelegation,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            DelegationType::BigInt as u32,
                        )
                    }
                    common_constants::KECCAK_SPECIAL5_CSR_REGISTER => {
                        assert_eq!(formal_rs1, 0);
                        assert_eq!(rd, 0);
                        Instruction::from_imm(
                            InstructionName::ZicsrDelegation,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            DelegationType::Keccak as u32,
                        )
                    }
                    CYCLE_CSR_INDEX => Instruction::from_imm(
                        InstructionName::Illegal,
                        formal_rs1,
                        formal_rs2,
                        rd,
                        0,
                    ),
                    _ => {
                        panic!("Unknown CSR number 0x{:04x}", csr_number);
                    }
                };

                if funct3 != 0b001 {
                    // not CSRRW
                    panic!("Unknown opcode 0x{:08x}", opcode);
                }

                instr
            } else {
                panic!("Unknown system funct3 enc 0x{:08x}", funct3);
            };

            instr
        }
        _ => {
            panic!("Unknown opcode 0x{:08x}", opcode);
        }
    };

    instruction
}

pub struct FullMachineDecoderConfig;

impl DecodingOptions for FullMachineDecoderConfig {
    const SUPPORT_MOP: bool = false;
    const SUPPORT_MUL_DIV: bool = true;
    const SUPPORT_SIGNED_MUL_DIV: bool = true;
    const SUPPORT_SUBWORD_MEM_ACCESS: bool = true;
}

pub struct FullUnsignedMachineDecoderConfig;

impl DecodingOptions for FullUnsignedMachineDecoderConfig {
    const SUPPORT_MOP: bool = false;
    const SUPPORT_MUL_DIV: bool = true;
    const SUPPORT_SIGNED_MUL_DIV: bool = false;
    const SUPPORT_SUBWORD_MEM_ACCESS: bool = true;
}

pub struct ReducedMachineDecoderConfig;

impl DecodingOptions for ReducedMachineDecoderConfig {
    const SUPPORT_MOP: bool = true;
    const SUPPORT_MUL_DIV: bool = false;
    const SUPPORT_SIGNED_MUL_DIV: bool = false;
    const SUPPORT_SUBWORD_MEM_ACCESS: bool = false;
}
