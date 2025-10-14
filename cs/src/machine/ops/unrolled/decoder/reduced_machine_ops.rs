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

#[derive(Clone, Copy, Debug)]
pub struct ReducedMachineDecoder;

impl OpcodeFamilyDecoder for ReducedMachineDecoder {
    type BitmaskCircuitParser = ReducedMachineCircuitMask;

    fn instruction_family_index(&self) -> u8 {
        REDUCED_MACHINE_CIRCUIT_FAMILY_IDX
    }

    fn define_decoder_subspace(
        &self,
        opcode: u8,
        func3: u8,
        func7: u8,
    ) -> (
        bool, // is valid instruction or not
        InstructionType,
        InstructionFamilyBitmaskRepr, // Instruction specific data
    ) {
        use crate::machine::machine_configurations::minimal_no_exceptions_with_delegation::MinimalMachineNoExceptionHandlingWithDelegation;
        use crate::machine::Machine;

        let all_opcodes = <MinimalMachineNoExceptionHandlingWithDelegation as Machine<
            Mersenne31Field,
        >>::all_supported_opcodes();
        let all_keys = <MinimalMachineNoExceptionHandlingWithDelegation as Machine<
            Mersenne31Field,
        >>::all_decoder_keys();
        let major_keys = all_keys.all_major_keys();
        let max_minor_keys = all_keys.max_minor_keys();

        let major_key_offset = FLAGS_SOURCE_OFFSET;
        let minor_key_offset = major_key_offset + major_keys.len();
        assert_eq!(REDUCED_MACHINE_NUM_FLAGS, minor_key_offset + max_minor_keys);

        let mut result = INVALID_OPCODE_DEFAULTS;

        for supported_opcode in all_opcodes.iter() {
            if let Ok((instr_format, major_key, minor_keys)) =
                supported_opcode.define_decoder_subspace(opcode, func3, func7)
            {
                result.0 = true; // valid instruction
                result.1 = instr_format;

                let mut mask = 0u32;

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
                let major_index = all_keys.get_major_index(&major_key);
                mask |= (1 << major_index as u32) << major_key_offset;

                for minor in minor_keys.iter() {
                    let (_major_index, minor_index) = all_keys.get_index_set(&major_key, minor);
                    assert_eq!(_major_index, major_index);
                    mask |= (1 << minor_index as u64) << minor_key_offset;
                }

                result.2 = mask;
                break;
            } else {
                // continue to next supported opcode
            }
        }

        result
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

    let family = Box::new(ReducedMachineDecoder) as Box<dyn OpcodeFamilyDecoder>;

    use crate::machine::*;
    use std::alloc::Global;

    let _result = preprocess_bytecode::<Mersenne31Field, Global>(
        &binary,
        1 << 20,
        &family,
        &[NON_DETERMINISM_CSR, BLAKE2S_DELEGATION_CSR_REGISTER as u16],
    );
}
