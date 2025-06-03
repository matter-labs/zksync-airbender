use self::utils::*;
use super::*;
use crate::constraint::*;
use crate::cs::circuit::*;
use crate::cs::placeholder::Placeholder;
use crate::definitions::*;
use crate::devices::diffs::CommonDiffs;
use crate::devices::optimization_context::OptimizationContext;
use crate::devices::risc_v_types::InstructionType;
use crate::devices::risc_v_types::TrapReason;
use crate::machine::instruction_decoding_data::*;
use crate::tables::TableDriver;
use crate::tables::TableType;
use crate::types::*;
use field::PrimeField;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt::Debug;
use tables::key_for_continuous_log2_range;
use tables::LookupTable;
use tables::LookupWrapper;

pub mod decoder;
pub mod instruction_decoding_data;
pub mod machine_configurations;
pub mod ops;
pub mod utils;

pub const NON_DETERMINISM_CSR: u16 = 0x7c0;
pub const UNIMP_OPCODE: u32 = 0xc0001073;
pub const UNIMP_OPCODE_LOW: u16 = UNIMP_OPCODE as u16;
pub const UNIMP_OPCODE_HIGH: u16 = (UNIMP_OPCODE >> 16) as u16;

pub trait TyEq<T> {
    fn rw(self) -> T;
    fn rwi(x: T) -> Self;
}

impl<T> TyEq<T> for T {
    fn rw(self) -> T {
        self
    }
    fn rwi(x: T) -> Self {
        x
    }
}

pub fn basic_invalid_bitmask() -> u64 {
    let mut basic_invalid_bitmask = 0u64;
    basic_invalid_bitmask |= 1; // unknown instruction flag
    basic_invalid_bitmask |= (1 << InstructionType::BType as u64) << 1;

    basic_invalid_bitmask
}

pub trait RegisterValueSource<F: PrimeField>: 'static + Clone {
    fn get_register(&self) -> Register<F>;
    fn get_register_with_decomposition(&self) -> RegisterDecomposition<F>;
    fn get_register_with_decomposition_and_sign(&self) -> Option<RegisterDecompositionWithSign<F>>;
    fn get_sign_bit(&self) -> Option<Boolean>;
}

impl<F: PrimeField> RegisterValueSource<F> for RegisterDecomposition<F> {
    fn get_register(&self) -> Register<F> {
        self.into_register()
    }
    fn get_register_with_decomposition(&self) -> RegisterDecomposition<F> {
        *self
    }
    fn get_register_with_decomposition_and_sign(&self) -> Option<RegisterDecompositionWithSign<F>> {
        None
    }
    fn get_sign_bit(&self) -> Option<Boolean> {
        None
    }
}

impl<F: PrimeField> RegisterValueSource<F> for RegisterDecompositionWithSign<F> {
    fn get_register(&self) -> Register<F> {
        self.clone().into_register()
    }
    fn get_register_with_decomposition(&self) -> RegisterDecomposition<F> {
        todo!();
    }
    fn get_register_with_decomposition_and_sign(&self) -> Option<RegisterDecompositionWithSign<F>> {
        Some(self.clone())
    }
    fn get_sign_bit(&self) -> Option<Boolean> {
        Some(self.sign_bit)
    }
}

pub trait DecoderOutputSource<F: PrimeField, RS: RegisterValueSource<F>>: 'static + Clone {
    fn get_rs1_or_equivalent(&self) -> RS;
    fn get_rs2_or_equivalent(&self) -> RS;
    fn get_imm(&self) -> Register<F>;
    fn get_pc_next(&self) -> Register<F>;
    fn get_rs2_index(&self) -> Constraint<F>;
    fn funct3(&self) -> Num<F>;
    fn funct12(&self) -> Constraint<F>;
}

pub trait AbstractMachineState<F: PrimeField>: 'static + Clone {
    fn set_size() -> usize;
    fn append_into_variables_set(&self, dst: &mut Vec<Variable>);
}

impl<F: PrimeField> AbstractMachineState<F> for Register<F> {
    fn set_size() -> usize {
        REGISTER_SIZE
    }

    fn append_into_variables_set(&self, dst: &mut Vec<Variable>) {
        dst.push(self.0[0].get_variable());
        dst.push(self.0[1].get_variable());
    }
}

pub struct CSRUseProperties {
    // assume all are RW and M-mode for now
    pub standard_csrs: Vec<u16>,
    pub allow_non_determinism_csr: bool,
    pub support_mstatus: bool,
}

pub trait BaseMachineState<F: PrimeField>: AbstractMachineState<F> {
    fn opcodes_are_in_rom() -> bool;
    fn get_pc(&self) -> &Register<F>;
    fn get_pc_mut(&mut self) -> &mut Register<F>;

    fn csr_use_props() -> CSRUseProperties;
    fn all_csrs(&self) -> BTreeMap<u16, Register<F>>;
}

pub trait IndexableBooleanSet: 'static + Clone {
    fn get_major_flag(&self, major: DecoderMajorInstructionFamilyKey) -> Boolean;
    fn get_minor_flag(
        &self,
        major: DecoderMajorInstructionFamilyKey,
        minor: DecoderInstructionVariantsKey,
    ) -> Boolean;
}

pub trait DecodableMachineOp: 'static + Debug {
    fn define_decoder_subspace(
        &self,
        opcode: u8,
        func3: u8,
        func7: u8,
    ) -> Result<
        (
            InstructionType,
            DecoderMajorInstructionFamilyKey,
            &'static [DecoderInstructionVariantsKey],
        ),
        (),
    >;
}

// abstract op needs to be able to describe an opcode space of self,
// then access some indexed flags and operands source, and produce output
pub trait MachineOp<
    F: PrimeField,
    ST: BaseMachineState<F>,
    RS: RegisterValueSource<F>,
    DE: DecoderOutputSource<F, RS>,
    BS: IndexableBooleanSet,
>: DecodableMachineOp + Clone
{
    fn define_used_tables() -> Vec<TableType> {
        vec![]
    }

    fn apply<CS: Circuit<F>, const ASSUME_TRUSTED_CODE: bool, const OUTPUT_EXACT_EXCEPTIONS: bool>(
        cs: &mut CS,
        machine_state: &ST,
        inputs: &DE,
        boolean_set: &BS,
        opt_ctx: &mut OptimizationContext<F, CS>,
    ) -> CommonDiffs<F>;
}

pub trait Machine<F: PrimeField>: 'static + Clone + Default {
    const ASSUME_TRUSTED_CODE: bool;
    const OUTPUT_EXACT_EXCEPTIONS: bool;
    const USE_ROM_FOR_BYTECODE: bool;

    type State: BaseMachineState<F>;

    fn all_supported_opcodes() -> Vec<Box<dyn DecodableMachineOp>>;

    fn define_used_tables() -> BTreeSet<TableType>;
    fn define_additional_tables(&self) -> Vec<(TableType, LookupWrapper<F>)> {
        vec![]
    }

    fn all_decoder_keys() -> DecoderOutputExtraKeysHolder {
        let all_opcodes = Self::all_supported_opcodes();
        let mut all_keys = DecoderOutputExtraKeysHolder::new();
        let mut formats = Vec::with_capacity(1 << (7 + 3 + 7));
        for opcode in 0..(1u8 << 7) {
            for funct3 in 0..(1u8 << 3) {
                for funct7 in 0..(1u8 << 7) {
                    let mut found = false;
                    'inner: for supported_opcode in all_opcodes.iter() {
                        if let Ok((instr_format, major_key, minor_keys)) =
                            supported_opcode.define_decoder_subspace(opcode, funct3, funct7)
                        {
                            // there is some opcode that supports it, so just continue now
                            formats.push((false, instr_format));
                            all_keys.collect(major_key, minor_keys);
                            found = true;
                            break 'inner;
                        } else {
                            // continue to next supported opcode
                        }
                    }
                    // none of the opcodes could process such combination,
                    // so we degrade to default one
                    if found == false {
                        formats.push((true, InstructionType::RType));
                    }
                }
            }
        }

        assert_eq!(formats.len(), 1 << (7 + 3 + 7));

        all_keys
    }

    fn create_decoder_table(id: u32) -> LookupTable<F, 3> {
        use crate::tables::first_key_index_gen_fn;

        let ([first_word_bits, second_word_bits], stub_values) = Self::produce_decoder_table_stub();

        assert_eq!(stub_values.len(), 1 << (7 + 3 + 7));
        assert!(first_word_bits < F::CHAR_BITS);
        assert!(second_word_bits < F::CHAR_BITS);

        let mask_first_word: u64 = (1u64 << first_word_bits) - 1;
        let _mask_second_word: u64 = (1u64 << second_word_bits) - 1;

        let keys = key_for_continuous_log2_range(7 + 3 + 7);
        const TABLE_NAME: &'static str = "Decoder table";
        LookupTable::<F, 3>::create_table_from_key_and_key_generation_closure(
            &keys,
            TABLE_NAME.to_string(),
            1,
            move |key| {
                let input = key[0].as_u64_reduced();
                assert!(input < (1u64 << 17));
                let bitmask = stub_values[input as usize];
                let first_word = bitmask & mask_first_word;
                let second_word = bitmask >> first_word_bits;

                let mut result = [F::ZERO; 3];
                result[0] = F::from_u64_unchecked(first_word as u64);
                result[1] = F::from_u64_unchecked(second_word as u64);

                (input as usize, result)
            },
            Some(first_key_index_gen_fn::<F, 3>),
            id,
        )
    }

    fn produce_decoder_table_stub() -> ([usize; 2], Vec<u64>) {
        // we want to walk over full subspace of u7 x u3 x u7 to collect:
        // - instruction format bits
        // - basic decoder properties bits
        // - bits that define full approach to bytecode execution for our subset

        let all_opcodes = Self::all_supported_opcodes();
        let all_keys = Self::all_decoder_keys();
        let major_keys = all_keys.all_major_keys();
        let max_minor_keys = all_keys.max_minor_keys();

        // now we can properly form a bitmask
        let mut total_used_bits = 0usize;
        // invalid flag
        total_used_bits += 1;
        // encode format
        let opcode_format_offset = total_used_bits;
        total_used_bits += NUM_INSTRUCTION_TYPES_IN_DECODE_BITS;
        let major_key_offset = total_used_bits;
        // and then - from all possible keys used by all the opcodes
        total_used_bits += major_keys.len();
        let minor_key_offset = total_used_bits;
        // and then - maximum number of minor keys
        total_used_bits += max_minor_keys;
        // assert that we fit
        let field_capacity = F::CHAR_BITS - 1;
        assert!(total_used_bits <= field_capacity * 2);
        let mut splitting = [0usize; 2];
        let first_chunk = std::cmp::min(total_used_bits, field_capacity);
        splitting[0] = first_chunk;
        let second_chunk = total_used_bits - first_chunk;
        splitting[1] = second_chunk;

        let basic_invalid_bitmask = basic_invalid_bitmask();
        let mut result = vec![basic_invalid_bitmask; 1 << (7 + 3 + 7)];
        // walk over opcodes again, but now arrange the keys into bitmask
        for opcode in 0..(1u8 << 7) {
            for funct3 in 0..(1u8 << 3) {
                for funct7 in 0..(1u8 << 7) {
                    let concatenated_key =
                        opcode as u32 + ((funct3 as u32) << 7) + ((funct7 as u32) << 10);
                    'inner: for supported_opcode in all_opcodes.iter() {
                        if let Ok((instr_format, major_key, minor_keys)) =
                            supported_opcode.define_decoder_subspace(opcode, funct3, funct7)
                        {
                            // there is some opcode that supports it, so just continue now
                            let mut mask = 0u64;
                            // not_invalid
                            mask |= 0;
                            // opcode format
                            mask |= (1 << instr_format as u64) << opcode_format_offset;

                            let major_index = all_keys.get_major_index(&major_key);
                            mask |= (1 << major_index as u64) << major_key_offset;

                            for minor in minor_keys.iter() {
                                let (_major_index, minor_index) =
                                    all_keys.get_index_set(&major_key, minor);
                                assert_eq!(_major_index, major_index);
                                mask |= (1 << minor_index as u64) << minor_key_offset;
                            }

                            result[concatenated_key as usize] = mask;
                            break 'inner;
                        } else {
                            // continue to next supported opcode
                        }
                    }
                    // none of the opcodes could process such combination,
                    // so we degrade to default one
                }
            }
        }

        assert_eq!(result.len(), 1 << (7 + 3 + 7));

        (splitting, result)
    }

    fn verify_bytecode_base(bytecode: &[u32]) -> Vec<(usize, u32)> {
        let all_opcodes = Self::all_supported_opcodes();
        let mut unsupported_opcodes = Vec::new();
        for (pos, &opcode) in bytecode.iter().enumerate() {
            let op = opcode & 0b111_1111;
            let funct3 = (opcode >> 12) & 0b111;
            let funct7 = (opcode >> 25) & 0b111_1111;
            let mut supported = false;
            for supported_op in all_opcodes.iter() {
                if let Ok(_) =
                    supported_op.define_decoder_subspace(op as u8, funct3 as u8, funct7 as u8)
                {
                    supported = true;
                    break;
                }
            }

            if supported == false {
                unsupported_opcodes.push((pos, opcode));
            }
        }

        unsupported_opcodes
    }

    fn describe_state_transition<CS: Circuit<F>, const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize>(
        circuit: &mut CS,
    ) -> (Self::State, Self::State)
    where
        [(); { <Self as Machine<F>>::ASSUME_TRUSTED_CODE } as usize]:,
        [(); { <Self as Machine<F>>::OUTPUT_EXACT_EXCEPTIONS } as usize]:;

    fn run_single_cycle<const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize>(
        bytecode: &[u32],
        cs: &mut impl Circuit<F>,
        csr_table: Option<LookupWrapper<F>>,
    ) -> (Self::State, Self::State)
    where
        [(); { <Self as Machine<F>>::ASSUME_TRUSTED_CODE } as usize]:,
        [(); { <Self as Machine<F>>::OUTPUT_EXACT_EXCEPTIONS } as usize]:,
    {
        let machine = Self::default();
        use machine_configurations::{create_table_driver_into_cs, create_table_for_rom_image};
        create_table_driver_into_cs::<_, _, _, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(cs, machine);
        let rom_table = create_table_for_rom_image::<_, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(
            &bytecode,
            TableType::RomRead.to_table_id(),
        );
        cs.add_table_with_content(TableType::RomRead, LookupWrapper::Dimensional3(rom_table));
        if let Some(csr_table) = csr_table {
            cs.add_table_with_content(TableType::SpecialCSRProperties, csr_table);
        }
        let (prev_state, next_state) =
            Self::describe_state_transition::<_, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(cs);
        // assert!(cs.is_satisfied());

        (prev_state, next_state)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::machine::machine_configurations::minimal_no_exceptions::MinimalMachineNoExceptionHandling;
    use disc_v::{decode_inst, format_inst, rv_isa};
    use field::Mersenne31Field;
    type F = Mersenne31Field;

    #[test]
    fn touch_base_machine() {
        let (splitting, _) =
            <MinimalMachineNoExceptionHandling as Machine<F>>::produce_decoder_table_stub();
        dbg!(splitting);
    }

    #[ignore = "depends on ZKsync OS"]
    #[test]
    fn check_binary() {
        let path = "../../zksync-os/zksync_os/app.text";
        let binary = std::fs::read(path).unwrap();
        let isa = rv_isa::rv32;
        assert!(binary.len() % 4 == 0);
        let binary: Vec<_> = binary
            .array_chunks::<4>()
            .map(|el| u32::from_le_bytes(*el))
            .collect();
        let unsupported_places =
            <MinimalMachineNoExceptionHandling as Machine<F>>::verify_bytecode_base(&binary);
        let num_unsupported = unsupported_places.len();
        for (pos, opcode) in unsupported_places.into_iter() {
            let instr = decode_inst(isa, pos as u64, opcode as u64);
            println!(
                "Can not support opcode 0x{:08x} at offset {}: {}",
                opcode,
                pos,
                format_inst(32, &instr)
            );
        }
        println!("Total unsupported places: {}", num_unsupported);
    }
}
