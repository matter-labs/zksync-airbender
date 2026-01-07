use field::Mersenne31Field;

use super::*;
use crate::machine::machine_configurations::BasicFlagsSource;
use crate::types::Boolean;

const UPDATE_RD_BIT: usize = 0; // = r_insn || i_insn || j_insn || u_insn
const USE_RS2_BIT: usize = 1; // = r_insn || s_insn || b_insn
const B_INST_BIT: usize = 2;
const FLAGS_SOURCE_OFFSET: usize = 3;
// const RS2_QUERY_IS_REGISTER: usize = 3;
// const RD_QUERY_IS_REGISTER: usize = 4;
// const FLAGS_SOURCE_OFFSET: usize = 5;

#[derive(Clone, Copy, Debug)]
pub struct ReducedMachineCircuitMask {
    inner: [Boolean; REDUCED_MACHINE_NUM_FLAGS],
}

impl ReducedMachineCircuitMask {
    pub fn get_flag_source(&self) -> BasicFlagsSource {
        use crate::machine::machine_configurations::minimal_no_exceptions_with_delegation::MinimalMachineNoExceptionHandlingWithDelegation;
        use crate::machine::Machine;

        let keys = <MinimalMachineNoExceptionHandlingWithDelegation as Machine<Mersenne31Field>>::all_decoder_keys();
        BasicFlagsSource::new(keys, self.inner[FLAGS_SOURCE_OFFSET..].to_vec())
    }

    pub fn get_update_rd_flag(&self) -> Boolean {
        self.inner[UPDATE_RD_BIT]
    }

    pub fn get_use_rs2_flag(&self) -> Boolean {
        self.inner[USE_RS2_BIT]
    }

    pub fn get_b_instruction_flag(&self) -> Boolean {
        self.inner[B_INST_BIT]
    }

    // pub fn get_rs2_query_is_register_flag(&self) -> Boolean {
    //     self.inner[RS2_QUERY_IS_REGISTER]
    // }

    // pub fn get_rd_query_is_register_flag(&self) -> Boolean {
    //     self.inner[RD_QUERY_IS_REGISTER]
    // }
}

impl InstructionFamilyBitmaskCircuitParser for ReducedMachineCircuitMask {
    fn parse<F: PrimeField, CS: Circuit<F>>(cs: &mut CS, input: Variable) -> Self {
        let inner =
            Boolean::split_into_bitmask::<_, _, REDUCED_MACHINE_NUM_FLAGS>(cs, Num::Var(input));
        Self { inner }
    }
}

#[derive(Debug)]
pub struct ReducedMachineDecoder {
    cached_all_opcodes: Vec<Box<dyn crate::machine::DecodableMachineOp>>,
    cached_all_keys: crate::machine::DecoderOutputExtraKeysHolder,
    major_keys: Vec<crate::machine::DecoderMajorInstructionFamilyKey>,
    max_minor_keys: usize,
}

impl ReducedMachineDecoder {
    pub fn new() -> Self {
        use crate::machine::machine_configurations::minimal_no_exceptions_with_delegation::MinimalMachineNoExceptionHandlingWithDelegation;
        use crate::machine::Machine;

        let all_keys = <MinimalMachineNoExceptionHandlingWithDelegation as Machine<
            Mersenne31Field,
        >>::all_decoder_keys();
        let major_keys = all_keys.all_major_keys();
        let max_minor_keys = all_keys.max_minor_keys();

        Self {
            cached_all_opcodes: <MinimalMachineNoExceptionHandlingWithDelegation as Machine<
                Mersenne31Field,
            >>::all_supported_opcodes(),
            cached_all_keys: all_keys,
            major_keys,
            max_minor_keys,
        }
    }
}

impl OpcodeFamilyDecoder for ReducedMachineDecoder {
    type BitmaskCircuitParser = ReducedMachineCircuitMask;

    fn instruction_family_index(&self) -> u8 {
        REDUCED_MACHINE_CIRCUIT_FAMILY_IDX
    }

    fn define_decoder_subspace(
        &self,
        opcode: u32,
    ) -> Result<ExecutorFamilyDecoderExtendedData, ()> {
        // let mut repr = 0u32;
        let op = get_opcode_bits(opcode);
        let func3 = funct3_bits(opcode);
        let func7 = funct7_bits(opcode);
        let (mut rs1_index, mut rs2_index, mut rd_index) =
            formally_parse_rs1_rs2_rd_props_for_tracer(opcode);

        let major_key_offset = FLAGS_SOURCE_OFFSET;
        let minor_key_offset = major_key_offset + self.major_keys.len();
        assert_eq!(
            REDUCED_MACHINE_NUM_FLAGS,
            minor_key_offset + self.max_minor_keys
        );

        let mut result = ExecutorFamilyDecoderExtendedData {
            data: ExecutorFamilyDecoderData::default(),
            instruction_format: InstructionType::RType,
            validate_csr_index_in_immediate: false,
        };

        let mut validate_csr = false;
        let mut avoid_sign_ext_immedaite = false;

        for supported_opcode in self.cached_all_opcodes.iter() {
            if let Ok((instr_format, major_key, minor_keys)) =
                supported_opcode.define_decoder_subspace(op, func3, func7)
            {
                if op == OPERATION_SYSTEM && func3 == 0b001 {
                    // CSRRW only in system space, not MOP one
                    // only if opcode is supported
                    avoid_sign_ext_immedaite = true;
                    validate_csr = true;
                }

                let imm = instr_format.parse_imm(opcode, avoid_sign_ext_immedaite);

                let mut mask = 0u32;

                match instr_format {
                    InstructionType::IType => {
                        rs2_index = 0;
                    }
                    InstructionType::BType => {
                        rd_index = 0;
                    }
                    InstructionType::JType => {
                        rs1_index = 0;
                        rs2_index = 0;
                    }
                    InstructionType::UType => {
                        rs1_index = 0;
                        rs2_index = 0;
                    }
                    InstructionType::SType => {
                        rd_index = 0;
                    }
                    _ => {}
                }

                // extra flags
                if instr_format == InstructionType::RType
                    || instr_format == InstructionType::IType
                    || instr_format == InstructionType::JType
                    || instr_format == InstructionType::UType
                {
                    mask |= 1 << UPDATE_RD_BIT;
                }

                if instr_format == InstructionType::RType
                    || instr_format == InstructionType::SType
                    || instr_format == InstructionType::BType
                {
                    mask |= 1 << USE_RS2_BIT;
                }

                if instr_format == InstructionType::BType {
                    mask |= 1 << B_INST_BIT;
                }

                // if opcode != OPERATION_LOAD {
                //     mask |= 1 << RS2_QUERY_IS_REGISTER;
                // }

                // if instr_format != InstructionType::SType {
                //     mask |= 1 << RD_QUERY_IS_REGISTER;
                // }

                // flags source
                let major_index = self.cached_all_keys.get_major_index(&major_key);
                mask |= (1 << major_index as u32) << major_key_offset;

                for minor in minor_keys.iter() {
                    let (_major_index, minor_index) =
                        self.cached_all_keys.get_index_set(&major_key, minor);
                    assert_eq!(_major_index, major_index);
                    mask |= (1 << minor_index as u64) << minor_key_offset;
                }

                result.data = ExecutorFamilyDecoderData {
                    imm,
                    rs1_index,
                    rs2_index,
                    rd_index,
                    rd_is_zero: rd_index == 0,
                    funct3: func3,
                    funct7: None,
                    opcode_family_bits: mask,
                };
                result.instruction_format = instr_format;
                result.validate_csr_index_in_immediate = validate_csr;

                return Ok(result);
            } else {
                // continue to next supported opcode
            }
        }

        Err(())
    }
}

#[test]
fn create_decoder_table_for_reduced_machine() {
    let binary = std::fs::read("../tools/verifier/recursion_layer.bin").unwrap();
    assert!(binary.len() % 4 == 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let family = Box::new(ReducedMachineDecoder::new()) as Box<dyn OpcodeFamilyDecoder>;

    use crate::machine::*;
    use std::alloc::Global;

    let _result = preprocess_bytecode::<Mersenne31Field, Global>(
        &binary,
        1 << 20,
        &family,
        &[NON_DETERMINISM_CSR, BLAKE2S_DELEGATION_CSR_REGISTER as u16],
    );
}
