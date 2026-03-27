use crate::ir::decode::*;
use crate::ir::encoding_types::*;
use crate::ir::instructions::*;
use crate::ir::DecodingOptions;
use common_constants::CYCLE_CSR_INDEX;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
#[non_exhaustive]
pub enum DelegationType {
    Blake = common_constants::BLAKE2S_DELEGATION_CSR_REGISTER,
    BigInt = common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER,
    Keccak = common_constants::KECCAK_SPECIAL5_CSR_REGISTER,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
#[non_exhaustive]
pub enum InstructionName {
    Illegal = 0, // Important

    // add-like
    Nop, // marker for pure instructions that use rd == 0
    Add, // includes immediate variant and LUI
    Sub,
    Auipc,
    ZimopAdd,
    ZimopSub,
    ZimopMul,
    // Comparison and branch-like
    Slt,
    Sltu,
    Jal,
    Jalr,
    Branch,
    // Binary ops and shifts
    Sll,
    Srl,
    Sra,
    Rol,
    Ror,
    Xor,
    Or,
    And,
    // Multiplication and division
    Mul,
    Mulh,
    Mulhsu,
    Mulhu,
    Div,
    Divu,
    Rem,
    Remu,
    // Word sized memory access
    Lw,
    Sw,
    // Subword sized memory access
    Lhu,
    Lbu,
    Lh,
    Lb,
    Sb,
    Sh,
    // VM specific instructions
    ZicsrDelegation,
    ZicsrNonDeterminismRead,
    ZicsrNonDeterminismWrite,
    // Aux instructions
    ZicsrMarkerCsr,
    // End
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

    pub const fn from_imm(name: InstructionName, rs1: u8, rs2: u8, rd: u8, imm: u32) -> Self {
        Self {
            name,
            rs1,
            rs2,
            rd,
            imm,
        }
    }

    pub const fn pure_from_imm(name: InstructionName, rs1: u8, rs2: u8, rd: u8, imm: u32) -> Self {
        if rd == 0 {
            Self::nop()
        } else {
            Self {
                name,
                rs1,
                rs2,
                rd,
                imm,
            }
        }
    }

    pub const fn nop() -> Self {
        Self {
            name: InstructionName::Nop,
            rs1: 0,
            rs2: 0,
            rd: 0,
            imm: 0,
        }
    }
}

pub fn preprocess_bytecode<
    OPT: DecodingOptions,
    const PROTECT_AGAINST_MID_DELEGATION_JUMPS: bool,
>(
    bytecode: &[u32],
) -> Vec<Instruction> {
    let mut i = 0;

    let illegal_instr = Instruction::from_imm(InstructionName::Illegal, 0, 0, 0, 0);

    let mut instructions = vec![illegal_instr; bytecode.len()];

    while i < bytecode.len() {
        let opcode = bytecode[i];

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
                // Modeled as addition
                Instruction::pure_from_imm(InstructionName::Add, 0, 0, rd, imm)
            }
            OPCODE_AUIPC => {
                // U format
                let imm = UTypeOpcode::imm(opcode);

                Instruction::pure_from_imm(InstructionName::Auipc, 0, 0, rd, imm)
            }
            OPCODE_JAL => {
                // J format
                let mut imm: u32 = JTypeOpcode::imm(opcode);
                sign_extend(&mut imm, 21);

                Instruction::from_imm(InstructionName::Jal, 0, 0, rd, imm)
            }
            OPCODE_JALR => {
                // I format
                let mut imm: u32 = ITypeOpcode::imm(opcode);
                // quasi sign extend
                sign_extend(&mut imm, 12);
                Instruction::from_imm(InstructionName::Jalr, formal_rs1, 0, rd, imm)
            }
            OPCODE_BRANCH => {
                // B format
                let mut imm = BTypeOpcode::imm(opcode);
                sign_extend(&mut imm, 13);

                // NOTE: branch instructions do not write, and we always model it as RD = 0 and write of 0 for tracing purposes.
                // And we will put funct3 into rd here to reduce struct size
                match funct3 {
                    0 | 1 | 4 | 5 | 6 | 7 => {}
                    _ => {
                        panic!(
                            "Unknown BRANCH-like opcode 0x{:08x} at PC = 0x{:08x}",
                            opcode,
                            i * 4
                        );
                    }
                };

                Instruction::from_imm(InstructionName::Branch, formal_rs1, formal_rs2, funct3, imm)
            }
            OP_IMM_SUBMASK => {
                let mut imm = ITypeOpcode::imm(opcode);
                sign_extend(&mut imm, 12);

                let instr = match funct3 {
                    GROUP_IMM_ADD => {
                        Instruction::pure_from_imm(InstructionName::Add, formal_rs1, 0, rd, imm)
                    }
                    GROUP_IMM_SLL if funct7 == SLL_FUNCT7 => {
                        // Shift is encoded in the lowest 5 bits
                        Instruction::pure_from_imm(
                            InstructionName::Sll,
                            formal_rs1,
                            0,
                            rd,
                            imm & 0x1f,
                        )
                    }
                    GROUP_IMM_SRL if funct7 == SRL_FUNCT7 => {
                        // Shift is encoded in the lowest 5 bits
                        Instruction::pure_from_imm(
                            InstructionName::Srl,
                            formal_rs1,
                            0,
                            rd,
                            imm & 0x1f,
                        )
                    }
                    GROUP_IMM_SRA if funct7 == SRA_FUNCT7 => {
                        // Shift is encoded in the lowest 5 bits
                        Instruction::pure_from_imm(
                            InstructionName::Sra,
                            formal_rs1,
                            0,
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
                        Instruction::pure_from_imm(InstructionName::Slt, formal_rs1, 0, rd, imm)
                    }
                    GROUP_IMM_SLTU => {
                        Instruction::pure_from_imm(InstructionName::Sltu, formal_rs1, 0, rd, imm)
                    }
                    GROUP_IMM_XOR => {
                        Instruction::pure_from_imm(InstructionName::Xor, formal_rs1, 0, rd, imm)
                    }
                    GROUP_IMM_OR => {
                        Instruction::pure_from_imm(InstructionName::Or, formal_rs1, 0, rd, imm)
                    }
                    GROUP_IMM_AND => {
                        Instruction::pure_from_imm(InstructionName::And, formal_rs1, 0, rd, imm)
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
                                Instruction::pure_from_imm(
                                    InstructionName::Mul,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    0,
                                )
                            } else {
                                illegal_instr
                            }
                        }
                        0b001 => {
                            if OPT::SUPPORT_MUL_DIV && OPT::SUPPORT_SIGNED_MUL_DIV {
                                Instruction::pure_from_imm(
                                    InstructionName::Mulh,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    0,
                                )
                            } else {
                                illegal_instr
                            }
                        }
                        0b010 => {
                            if OPT::SUPPORT_MUL_DIV && OPT::SUPPORT_SIGNED_MUL_DIV {
                                Instruction::pure_from_imm(
                                    InstructionName::Mulhsu,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    0,
                                )
                            } else {
                                illegal_instr
                            }
                        }
                        0b011 => {
                            if OPT::SUPPORT_MUL_DIV {
                                Instruction::pure_from_imm(
                                    InstructionName::Mulhu,
                                    formal_rs1,
                                    formal_rs2,
                                    rd,
                                    0,
                                )
                            } else {
                                illegal_instr
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
                                illegal_instr
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
                                illegal_instr
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
                                illegal_instr
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
                                illegal_instr
                            }
                        }

                        _ => unreachable!(),
                    }
                } else {
                    // basic set
                    match funct3 {
                        0b000 if funct7 == 0 => Instruction::pure_from_imm(
                            InstructionName::Add,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            0,
                        ),
                        0b000 if funct7 == SUB_FUNCT7 => Instruction::pure_from_imm(
                            InstructionName::Sub,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            0,
                        ),
                        0b001 if funct7 == SLL_FUNCT7 => Instruction::pure_from_imm(
                            InstructionName::Sll,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            0,
                        ),
                        0b001 if funct7 == ROT_FUNCT7 => {
                            panic!("ROL is not supported");
                            // Instruction::from_imm(InstructionName::Rol, formal_rs1, formal_rs2, rd, 0)
                        }
                        0b101 if funct7 == SRL_FUNCT7 => Instruction::pure_from_imm(
                            InstructionName::Srl,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            0,
                        ),
                        0b101 if funct7 == SRA_FUNCT7 => Instruction::pure_from_imm(
                            InstructionName::Sra,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            0,
                        ),
                        0b101 if funct7 == ROT_FUNCT7 => {
                            panic!("ROR is not supported");
                            // Instruction::from_imm(InstructionName::Ror, formal_rs1, formal_rs2, rd, 0)
                        }
                        0b010 => Instruction::pure_from_imm(
                            InstructionName::Slt,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            0,
                        ),
                        0b011 => Instruction::pure_from_imm(
                            InstructionName::Sltu,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            0,
                        ),
                        0b100 => Instruction::pure_from_imm(
                            InstructionName::Xor,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            0,
                        ),
                        0b110 => Instruction::pure_from_imm(
                            InstructionName::Or,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            0,
                        ),
                        0b111 => Instruction::pure_from_imm(
                            InstructionName::And,
                            formal_rs1,
                            formal_rs2,
                            rd,
                            0,
                        ),
                        _ => {
                            panic!("Unknown opcode 0x{:08x}", opcode);
                        }
                    }
                }
            }
            OPCODE_LOAD => {
                // NOTE: we WILL model all loads as pure - eventual unaligned load into x0
                // doesn't really change behavior, and we do have any memory regions that forbid
                // access
                let mut imm = ITypeOpcode::imm(opcode);
                sign_extend(&mut imm, 12);

                match funct3 {
                    a @ 0 | a @ 1 | a @ 2 | a @ 4 | a @ 5 => {
                        let instr = match a {
                            0 => {
                                if OPT::SUPPORT_SUBWORD_MEM_ACCESS {
                                    Instruction::pure_from_imm(
                                        InstructionName::Lb,
                                        formal_rs1,
                                        0,
                                        rd,
                                        imm,
                                    )
                                } else {
                                    illegal_instr
                                }
                            }
                            1 => {
                                if OPT::SUPPORT_SUBWORD_MEM_ACCESS {
                                    Instruction::pure_from_imm(
                                        InstructionName::Lh,
                                        formal_rs1,
                                        0,
                                        rd,
                                        imm,
                                    )
                                } else {
                                    illegal_instr
                                }
                            }
                            2 => Instruction::pure_from_imm(
                                InstructionName::Lw,
                                formal_rs1,
                                0,
                                rd,
                                imm,
                            ),
                            4 => {
                                if OPT::SUPPORT_SUBWORD_MEM_ACCESS {
                                    Instruction::pure_from_imm(
                                        InstructionName::Lbu,
                                        formal_rs1,
                                        0,
                                        rd,
                                        imm,
                                    )
                                } else {
                                    illegal_instr
                                }
                            }
                            5 => {
                                if OPT::SUPPORT_SUBWORD_MEM_ACCESS {
                                    Instruction::pure_from_imm(
                                        InstructionName::Lhu,
                                        formal_rs1,
                                        0,
                                        rd,
                                        imm,
                                    )
                                } else {
                                    illegal_instr
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

                // NOTE: we model stored as they write to x0

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
                                        0,
                                        imm,
                                    )
                                } else {
                                    illegal_instr
                                }
                            }
                            2 => {
                                if OPT::SUPPORT_SUBWORD_MEM_ACCESS {
                                    Instruction::from_imm(
                                        InstructionName::Sh,
                                        formal_rs1,
                                        formal_rs2,
                                        0,
                                        imm,
                                    )
                                } else {
                                    illegal_instr
                                }
                            }
                            4 => Instruction::from_imm(
                                InstructionName::Sw,
                                formal_rs1,
                                formal_rs2,
                                0,
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
                                    Instruction::pure_from_imm(
                                        InstructionName::ZimopAdd,
                                        formal_rs1,
                                        formal_rs2,
                                        rd,
                                        0,
                                    )
                                } else {
                                    illegal_instr
                                }
                            }
                            1 => {
                                if OPT::SUPPORT_MOP {
                                    Instruction::pure_from_imm(
                                        InstructionName::ZimopSub,
                                        formal_rs1,
                                        formal_rs2,
                                        rd,
                                        0,
                                    )
                                } else {
                                    illegal_instr
                                }
                            }
                            2 => {
                                if OPT::SUPPORT_MOP {
                                    Instruction::pure_from_imm(
                                        InstructionName::ZimopMul,
                                        formal_rs1,
                                        formal_rs2,
                                        rd,
                                        0,
                                    )
                                } else {
                                    illegal_instr
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
                                // NOTE: non-deteminism READ will be modeled as special opcode in circuits,
                                // that basically has no requirements on the rd value
                                assert_ne!(rd, 0);
                                // we have rd != 0, so we read from source and write to rd
                                Instruction::from_imm(
                                    InstructionName::ZicsrNonDeterminismRead,
                                    0,
                                    0,
                                    rd,
                                    0,
                                )
                            } else {
                                // NOTE: non-deteminism WRITE will be modeled as NOP in circuits
                                assert_eq!(rd, 0);
                                Instruction::from_imm(
                                    InstructionName::ZicsrNonDeterminismWrite,
                                    formal_rs1,
                                    0,
                                    0,
                                    0,
                                )
                            }
                        }
                        // NOTE on all delegations below - we will eventually model them via
                        // just NOP-like read from CSR index IN CIRCUIT (or replayer), but simulator
                        // will just dispatch it internally as it wants
                        common_constants::BLAKE2S_DELEGATION_CSR_REGISTER => {
                            assert_eq!(formal_rs1, 0);
                            assert_eq!(rd, 0);

                            // here we will peek into next instructions and issue only one call
                            // we should expect 7 or 10 calls
                            let mut num_calls = 0;
                            for j in 1..=10 {
                                if bytecode[i + j] == opcode {
                                    continue;
                                } else {
                                    num_calls = j;
                                    break;
                                }
                            }
                            assert!(num_calls == 7 || num_calls == 10);

                            let instr = Instruction::from_imm(
                                InstructionName::ZicsrDelegation,
                                0,
                                0,
                                0,
                                DelegationType::Blake as u32,
                            );

                            if PROTECT_AGAINST_MID_DELEGATION_JUMPS {
                                instructions[i] = instr;
                            } else {
                                for j in 0..num_calls {
                                    instructions[i + j] = instr;
                                }
                            }
                            i += num_calls;
                            // short-cut
                            continue;
                        }
                        common_constants::BIGINT_OPS_WITH_CONTROL_CSR_REGISTER => {
                            // Bigint instructions are issued one by one
                            assert_eq!(formal_rs1, 0);
                            assert_eq!(rd, 0);
                            Instruction::from_imm(
                                InstructionName::ZicsrDelegation,
                                0,
                                0,
                                0,
                                DelegationType::BigInt as u32,
                            )
                        }
                        common_constants::KECCAK_SPECIAL5_CSR_REGISTER => {
                            assert_eq!(formal_rs1, 0);
                            assert_eq!(rd, 0);
                            use common_constants::NUM_DELEGATION_CALLS_FOR_KECCAK_F1600;

                            let mut num_calls = 0;
                            for j in 1..=NUM_DELEGATION_CALLS_FOR_KECCAK_F1600 {
                                if bytecode[i + j] == opcode {
                                    continue;
                                } else {
                                    num_calls = j;
                                    break;
                                }
                            }
                            assert_eq!(num_calls, NUM_DELEGATION_CALLS_FOR_KECCAK_F1600);

                            let instr = Instruction::from_imm(
                                InstructionName::ZicsrDelegation,
                                0,
                                0,
                                0,
                                DelegationType::Keccak as u32,
                            );

                            if PROTECT_AGAINST_MID_DELEGATION_JUMPS {
                                instructions[i] = instr;
                            } else {
                                for j in 0..num_calls {
                                    instructions[i + j] = instr;
                                }
                            }
                            i += num_calls;
                            // short-cut
                            continue;
                        }
                        common_constants::internal_features::TRANSPILER_MARKER_CSR => {
                            // We only support the write-only marker form
                            // `csrrw x0, 0x7ff, x0`.
                            assert_eq!(rd, 0);
                            assert_eq!(formal_rs1, 0);
                            Instruction::from_imm(
                                InstructionName::ZicsrMarkerCsr,
                                formal_rs1,
                                0,
                                0,
                                0,
                            )
                        }
                        CYCLE_CSR_INDEX => {
                            // It is canonical CSR to encode UNIMP instruction
                            illegal_instr
                        }
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
                // just some opcode of unknown nature, may be padding or whatever. Just invalid
                illegal_instr
            }
        };

        instructions[i] = instruction;
        i += 1;
    }

    instructions
}
