use crate::cs::{
    cs_reference::BasicAssembly, witness_placer::graph_description::WitnessGraphCreator,
};

use super::*;

pub mod full_isa_no_exceptions;
pub mod full_isa_with_delegation_no_exceptions;
pub mod full_isa_with_delegation_no_exceptions_no_signed_mul_div;
pub mod minimal_no_exceptions;
pub mod minimal_no_exceptions_with_delegation;
pub mod minimal_state;
pub mod state_transition_parts;

#[derive(Clone, Debug)]
pub struct BasicFlagsSource {
    keys: DecoderOutputExtraKeysHolder,
    values: Vec<Boolean>,
}

impl BasicFlagsSource {
    pub fn new(keys: DecoderOutputExtraKeysHolder, values: Vec<Boolean>) -> Self {
        assert_eq!(keys.num_major_keys() + keys.max_minor_keys(), values.len());

        Self { keys, values }
    }
}

impl IndexableBooleanSet for BasicFlagsSource {
    #[track_caller]
    fn get_major_flag(&self, major: DecoderMajorInstructionFamilyKey) -> Boolean {
        let major_index = self.keys.get_major_index(&major);
        self.values[major_index]
    }

    #[track_caller]
    fn get_minor_flag(
        &self,
        major: DecoderMajorInstructionFamilyKey,
        minor: DecoderInstructionVariantsKey,
    ) -> Boolean {
        let (_major_index, minor_index) = self.keys.get_index_set(&major, &minor);
        let offset = self.keys.num_major_keys();
        self.values[offset..][minor_index]
    }
}

#[derive(Clone, Debug)]
pub struct BasicDecodingResultWithoutSigns<F: PrimeField> {
    pub pc_next: Register<F>,
    pub src1: RegisterDecomposition<F>,
    pub src2: RegisterDecomposition<F>,
    pub rs2_index: Constraint<F>,
    pub imm: Register<F>,
    pub funct3: Num<F>,
    pub funct12: Constraint<F>,
}

impl<F: PrimeField> DecoderOutputSource<F, RegisterDecomposition<F>>
    for BasicDecodingResultWithoutSigns<F>
{
    fn get_pc_next(&self) -> Register<F> {
        self.pc_next
    }
    fn funct3(&self) -> Num<F> {
        self.funct3
    }
    fn get_rs2_index(&self) -> Constraint<F> {
        self.rs2_index.clone()
    }
    fn funct12(&self) -> Constraint<F> {
        self.funct12.clone()
    }
    fn get_imm(&self) -> Register<F> {
        self.imm
    }
    fn get_rs1_or_equivalent(&self) -> RegisterDecomposition<F> {
        self.src1
    }
    fn get_rs2_or_equivalent(&self) -> RegisterDecomposition<F> {
        self.src2
    }
}

#[derive(Clone, Debug)]
pub struct BasicDecodingResultWithSigns<F: PrimeField> {
    pub pc_next: Register<F>,
    pub src1: RegisterDecompositionWithSign<F>,
    pub src2: RegisterDecompositionWithSign<F>,
    pub imm: Register<F>,
    pub rs2_index: Constraint<F>,
    pub funct3: Num<F>,
    pub funct12: Constraint<F>,
}

impl<F: PrimeField> DecoderOutputSource<F, RegisterDecompositionWithSign<F>>
    for BasicDecodingResultWithSigns<F>
{
    fn get_pc_next(&self) -> Register<F> {
        self.pc_next
    }
    fn funct3(&self) -> Num<F> {
        self.funct3
    }
    fn get_rs2_index(&self) -> Constraint<F> {
        self.rs2_index.clone()
    }
    fn funct12(&self) -> Constraint<F> {
        self.funct12.clone()
    }
    fn get_imm(&self) -> Register<F> {
        self.imm
    }
    fn get_rs1_or_equivalent(&self) -> RegisterDecompositionWithSign<F> {
        self.src1.clone()
    }
    fn get_rs2_or_equivalent(&self) -> RegisterDecompositionWithSign<F> {
        self.src2.clone()
    }
}

pub fn pad_bytecode<const ROM_ADDRESS_SPACE_BOUND: u32>(bytecode: &mut Vec<u32>) {
    assert!(ROM_ADDRESS_SPACE_BOUND.is_power_of_two());
    assert!(bytecode.len() as u32 <= ROM_ADDRESS_SPACE_BOUND / 4);
    bytecode.resize((ROM_ADDRESS_SPACE_BOUND / 4) as usize, UNIMP_OPCODE);
}

/// Creating a table with ROM (program) data.
/// The table will have a constant size (ROM_ADDRESS_SPACE_BOUND / 4), and look like this:
/// (0, image bytes 0..2, image bytes 2..4)
/// (4, image bytes 4..6, image bytes 6..8)
// We have to do this his way, as our prime field is a little bit smaller than 32 bits.
// All the entries larger than the image will be filled with UNIMP_OPCODE.
pub fn create_table_for_rom_image<
    F: PrimeField,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    image: &[u32],
    id: u32,
) -> LookupTable<F, 3> {
    assert!(ROM_ADDRESS_SPACE_SECOND_WORD_BITS > 0);

    assert!(
        image.len() * 4 <= 1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
        "ROM size can be at most {} bytes ({} words), but input is {} words",
        1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
        (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4,
        image.len()
    );

    let mut keys = Vec::with_capacity(1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS - 2));
    for i in 0..1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS - 2) {
        let mut key = [F::ZERO; 3];
        let address = i * 4;
        key[0] = F::from_u64_unchecked(address as u64);
        keys.push(key);
    }

    assert_eq!(
        keys.len(),
        1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS - 2)
    );
    const TABLE_NAME: &'static str = "ROM table";
    let image = image.to_vec();
    LookupTable::<F, 3>::create_table_from_key_and_key_generation_closure(
        &keys,
        TABLE_NAME.to_string(),
        1,
        move |key| {
            let pc = key[0].as_u64_reduced();
            assert!(
                pc < 1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS) as u64,
                "PC = {} is too large for ROM bound {} bytes",
                pc,
                1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)
            );
            assert!(pc % 4 == 0, "PC = {} is not aligned", pc);
            let index = (pc as usize) / 4;
            let opcode = if index < image.len() {
                let opcode = image[index];

                opcode
            } else {
                // UNIMP opcodes
                UNIMP_OPCODE
            };
            let low = opcode as u16;
            let high = (opcode >> 16) as u16;

            let mut result = [F::ZERO; 3];
            result[0] = F::from_u64_unchecked(low as u64);
            result[1] = F::from_u64_unchecked(high as u64);

            ((pc / 4) as usize, result)
        },
        Some(|keys| {
            let pc = keys[0].as_u64_reduced();
            assert!(
                pc < 1u64 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS),
                "PC = {} is too large for ROM bound {}",
                pc,
                1u64 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)
            );
            assert!(pc % 4 == 0, "PC = {} is not aligned", pc);
            let index = (pc / 4) as usize;

            index
        }),
        id,
    )
}

pub fn create_csr_table_for_delegation<F: PrimeField>(
    allow_non_determinism: bool,
    allowed_delegation_csrs: &[u32],
    id: u32,
) -> LookupTable<F, 3> {
    use crate::csr_properties::create_special_csr_properties_table;
    create_special_csr_properties_table(id, allow_non_determinism, allowed_delegation_csrs)
}

// Use this function if you need CS-detached table driver, e.g. in proving or setup
pub fn create_table_driver<
    F: PrimeField,
    M: Machine<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    machine: M,
) -> TableDriver<F> {
    // materialize all tables
    let used_tables = M::define_used_tables();
    assert!(
        used_tables.contains(&TableType::ZeroEntry) == false,
        "machine must not define zero entry table as used"
    );
    assert!(
        used_tables.contains(&TableType::OpTypeBitmask) == false,
        "machine must not define decoder table"
    );
    assert!(
        used_tables.contains(&TableType::CsrBitmask) == false,
        "machine must not define CSR support table"
    );
    assert!(
        used_tables.contains(&TableType::RangeCheckSmall) == false,
        "machine must not define 8-bit range check table"
    );

    let extra_tables = machine.define_additional_tables();
    for (table, _) in extra_tables.iter() {
        assert!(used_tables.contains(table) == false);
    }

    let mut table_driver = TableDriver::new();

    for table in used_tables.into_iter() {
        table_driver.materialize_table(table);
    }

    for (table, content) in extra_tables.into_iter() {
        table_driver.add_table_with_content(table, content);
    }

    table_driver.materialize_table(TableType::And);
    table_driver.materialize_table(TableType::ZeroEntry);
    table_driver.materialize_table(TableType::QuickDecodeDecompositionCheck4x4x4);
    table_driver.materialize_table(TableType::QuickDecodeDecompositionCheck7x3x6);
    table_driver.materialize_table(TableType::U16GetSignAndHighByte);
    table_driver.materialize_table(TableType::RangeCheckSmall);

    let decoder_table = M::create_decoder_table(TableType::OpTypeBitmask.to_table_id());
    table_driver.add_table_with_content(
        TableType::OpTypeBitmask,
        LookupWrapper::Dimensional3(decoder_table),
    );

    // let csr_support_table = M::create_csr_support_table(TableType::CsrBitmask.to_table_id());
    // table_driver.add_table_with_content(
    //     TableType::CsrBitmask,
    //     LookupWrapper::Dimensional3(csr_support_table),
    // );

    if M::USE_ROM_FOR_BYTECODE {
        // manual call here, to later on easily control address bits
        let id = TableType::RomAddressSpaceSeparator.to_table_id();
        use crate::tables::create_rom_separator_table;
        let table = LookupWrapper::Dimensional3(create_rom_separator_table::<
            F,
            ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
        >(id));
        table_driver.add_table_with_content(TableType::RomAddressSpaceSeparator, table);
    }

    table_driver
}

pub fn create_table_driver_into_cs<
    F: PrimeField,
    CS: Circuit<F>,
    M: Machine<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    cs: &mut CS,
    machine: M,
) {
    // materialize all tables
    let used_tables = M::define_used_tables();
    assert!(
        used_tables.contains(&TableType::ZeroEntry) == false,
        "machine must not define zero entry table as used"
    );
    assert!(
        used_tables.contains(&TableType::OpTypeBitmask) == false,
        "machine must not define decoder table"
    );
    assert!(
        used_tables.contains(&TableType::CsrBitmask) == false,
        "machine must not define CSR support table"
    );
    assert!(
        used_tables.contains(&TableType::RangeCheckSmall) == false,
        "machine must not define 8-bit range check table"
    );

    let extra_tables = machine.define_additional_tables();
    for (table, _) in extra_tables.iter() {
        assert!(used_tables.contains(table) == false);
    }

    for table in used_tables.into_iter() {
        cs.materialize_table(table);
    }

    for (table, content) in extra_tables.into_iter() {
        cs.add_table_with_content(table, content);
    }

    cs.materialize_table(TableType::And);
    cs.materialize_table(TableType::ZeroEntry);
    cs.materialize_table(TableType::QuickDecodeDecompositionCheck4x4x4);
    cs.materialize_table(TableType::QuickDecodeDecompositionCheck7x3x6);
    cs.materialize_table(TableType::U16GetSignAndHighByte);
    cs.materialize_table(TableType::RangeCheckSmall);

    let decoder_table = M::create_decoder_table(TableType::OpTypeBitmask.to_table_id());
    cs.add_table_with_content(
        TableType::OpTypeBitmask,
        LookupWrapper::Dimensional3(decoder_table),
    );

    if M::USE_ROM_FOR_BYTECODE {
        // manual call here, to later on easily control address bits
        let id = TableType::RomAddressSpaceSeparator.to_table_id();
        use crate::tables::create_rom_separator_table;
        let table = LookupWrapper::Dimensional3(create_rom_separator_table::<
            F,
            ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
        >(id));
        cs.add_table_with_content(TableType::RomAddressSpaceSeparator, table);
    }
}

pub fn compile_machine<
    F: PrimeField,
    C: Circuit<F>,
    M: Machine<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    machine: M,
) -> CircuitOutput<F>
where
    [(); { <M as Machine<F>>::ASSUME_TRUSTED_CODE } as usize]:,
    [(); { <M as Machine<F>>::OUTPUT_EXACT_EXCEPTIONS } as usize]:,
{
    let mut cs = C::new();

    create_table_driver_into_cs::<F, C, M, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(&mut cs, machine);

    let (initial_state, final_state) =
        M::describe_state_transition::<_, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(&mut cs);

    let mut initial_state_vars = vec![];
    initial_state.append_into_variables_set(&mut initial_state_vars);

    let mut final_state_vars = vec![];
    final_state.append_into_variables_set(&mut final_state_vars);

    let (mut output, _) = cs.finalize();
    output.state_input = initial_state_vars;
    output.state_output = final_state_vars;

    output
}

pub fn dump_wintess_graph<
    F: PrimeField,
    M: Machine<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    _machine: M,
) -> WitnessGraphCreator<F>
where
    [(); { <M as Machine<F>>::ASSUME_TRUSTED_CODE } as usize]:,
    [(); { <M as Machine<F>>::OUTPUT_EXACT_EXCEPTIONS } as usize]:,
{
    let mut cs = BasicAssembly::<F, WitnessGraphCreator<F>>::new();
    cs.witness_placer = Some(WitnessGraphCreator::<F>::new());
    let _ = M::describe_state_transition::<_, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(&mut cs);
    let (_, witness_placer) = cs.finalize();

    witness_placer.unwrap()
}

pub fn dump_ssa_witness_eval_form<
    F: PrimeField,
    M: Machine<F>,
    const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize,
>(
    machine: M,
) -> Vec<Vec<crate::cs::witness_placer::graph_description::RawExpression<F>>>
where
    [(); { <M as Machine<F>>::ASSUME_TRUSTED_CODE } as usize]:,
    [(); { <M as Machine<F>>::OUTPUT_EXACT_EXCEPTIONS } as usize]:,
{
    let graph = dump_wintess_graph::<_, _, ROM_ADDRESS_SPACE_SECOND_WORD_BITS>(machine);
    let (_resolution_order, ssa_forms) = graph.compute_resolution_order();

    ssa_forms
}

#[cfg(test)]
mod tests {
    use field::Mersenne31Field;

    use super::*;

    #[test]
    fn rom_table_test() {
        let image = [100_000, 200_000, 0];
        let table = create_table_for_rom_image::<Mersenne31Field, 16>(&image, 15);

        // Now table should have entries:
        // 0 -- 0x86a0 0x1
        // 4 -- 0xd40 0x3
        // 8 -- 0x0 0x0
        // 12 -- 0xc0001073  (UNIMP)
        assert_eq!(
            table.lookup_value::<2>(&[Mersenne31Field::new(0)]),
            [Mersenne31Field::new(0x86a0), Mersenne31Field::new(0x1)]
        );
        assert_eq!(
            table.lookup_value::<2>(&[Mersenne31Field::new(4)]),
            [Mersenne31Field::new(0xd40), Mersenne31Field::new(0x3)]
        );
        assert_eq!(
            table.lookup_value::<2>(&[Mersenne31Field::new(8)]),
            [Mersenne31Field::new(0x0), Mersenne31Field::new(0x0)]
        );
        assert_eq!(
            table.lookup_value::<2>(&[Mersenne31Field::new(12)]),
            [Mersenne31Field::new(0x1073), Mersenne31Field::new(0xc000)]
        );
    }
}
