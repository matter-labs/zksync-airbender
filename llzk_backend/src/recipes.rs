use std::collections::BTreeMap;
use std::collections::BTreeSet;

use anyhow::Result;
use prover::common_constants;
use prover::cs::cs::circuit::Circuit;
use prover::cs::cs::circuit::CircuitOutput;
use prover::cs::cs::circuit::IndirectAccessType;
use prover::cs::cs::circuit::PicusExpr;
use prover::cs::cs::circuit::PicusStructuredConstraint;
use prover::cs::cs::circuit::RegisterAccessType;
use prover::cs::cs::circuit::RegisterAndIndirectAccesses;
use prover::cs::cs::circuit::ShuffleRamMemQuery;
use prover::cs::cs::circuit::ShuffleRamQueryType;
use prover::cs::cs::cs_reference::BasicAssembly;
use prover::cs::cs::placeholder::Placeholder;
use prover::cs::cs::witness_placer::graph_description::RawExpression;
use prover::cs::cs::witness_placer::graph_description::WitnessGraphCreator;
use prover::cs::definitions::TableType;
use prover::cs::definitions::Variable;
use prover::cs::delegation::dump_ssa_witness_eval_form_for_delegation;
use prover::cs::devices::diffs::CommonDiffs;
use prover::cs::devices::diffs::NextPcValue;
use prover::cs::devices::optimization_context::OptimizationContext;
use prover::cs::machine::instruction_decoding_data::DecoderInstructionVariantsKey;
use prover::cs::machine::instruction_decoding_data::DecoderMajorInstructionFamilyKey;
use prover::cs::machine::machine_configurations::minimal_state::MinimalStateRegistersInMemory;
use prover::cs::machine::machine_configurations::BasicDecodingResultWithSigns;
use prover::cs::machine::ops::add_sub::AddOp;
use prover::cs::machine::ops::add_sub::SubOp;
use prover::cs::machine::ops::add_sub::ADD_OP_KEY;
use prover::cs::machine::ops::add_sub::SUB_OP_KEY;
use prover::cs::machine::ops::binops::BinaryOp;
use prover::cs::machine::ops::binops::BINOP_COMMON_OP_KEY;
use prover::cs::machine::ops::common_impls::csr::apply_non_determinism_csr_only_assuming_no_unimp;
use prover::cs::machine::ops::conditional::ConditionalOp;
use prover::cs::machine::ops::conditional::CONDITIONAL_COMMON_OP_KEY;
use prover::cs::machine::ops::csr::CSR_COMMON_OP_KEY;
use prover::cs::machine::ops::jump::JumpOp;
use prover::cs::machine::ops::jump::JAL_OP_KEY;
use prover::cs::machine::ops::jump::JUMP_COMMON_OP_KEY;
use prover::cs::machine::ops::load::LoadOp;
use prover::cs::machine::ops::load::LOAD_COMMON_OP_KEY;
use prover::cs::machine::ops::load::LOAD_HALF_WORD_OP_KEY;
use prover::cs::machine::ops::load::LOAD_WORD_OP_KEY;
use prover::cs::machine::ops::lui_auipc::AuiPc;
use prover::cs::machine::ops::lui_auipc::LuiOp;
use prover::cs::machine::ops::lui_auipc::AUIPC_OP_KEY;
use prover::cs::machine::ops::lui_auipc::LUI_OP_KEY;
use prover::cs::machine::ops::mop::MopOp;
use prover::cs::machine::ops::mop::ADDMOD_OP_KEY;
use prover::cs::machine::ops::mop::MOP_OP_KEY;
use prover::cs::machine::ops::mop::MULMOD_OP_KEY;
use prover::cs::machine::ops::mop::SUBMOD_OP_KEY;
use prover::cs::machine::ops::mul_div::DivRemOp;
use prover::cs::machine::ops::mul_div::MulOp;
use prover::cs::machine::ops::mul_div::DIVREM_COMMON_OP_KEY;
use prover::cs::machine::ops::mul_div::DIVU_OP_KEY;
use prover::cs::machine::ops::mul_div::DIV_OP_KEY;
use prover::cs::machine::ops::mul_div::MULHSU_OP_KEY;
use prover::cs::machine::ops::mul_div::MULH_OP_KEY;
use prover::cs::machine::ops::mul_div::MUL_COMMON_OP_KEY;
use prover::cs::machine::ops::mul_div::MUL_OP_KEY;
use prover::cs::machine::ops::mul_div::REM_OP_KEY;
use prover::cs::machine::ops::shift::ShiftOp;
use prover::cs::machine::ops::shift::SHIFT_COMMON_OP_KEY;
use prover::cs::machine::ops::shift::SHIFT_RIGHT_ALGEBRAIC_KEY;
use prover::cs::machine::ops::shift::SHIFT_RIGHT_KEY;
use prover::cs::machine::ops::store::StoreOp;
use prover::cs::machine::ops::store::STORE_COMMON_OP_KEY;
use prover::cs::machine::ops::store::STORE_HALF_WORD_OP_KEY;
use prover::cs::machine::ops::store::STORE_WORD_OP_KEY;
use prover::cs::machine::ops::RS2_LOAD_LOCAL_TIMESTAMP;
use prover::cs::machine::utils::calculate_pc_next_no_overflows;
use prover::cs::machine::utils::form_mem_op_for_register_only;
use prover::cs::machine::IndexableBooleanSet;
use prover::cs::machine::MachineOp;
use prover::cs::tables::LookupWrapper;
use prover::cs::types::Boolean;
use prover::cs::types::Num;
use prover::cs::types::Register;
use prover::field::Mersenne31Field;
use prover::field::PrimeField;

use crate::codegen::ExtractedVariable;
use crate::codegen::LlzkBoundarySpec;

pub const DEFAULT_TRACE_LEN_LOG2: usize = 20;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircuitBuildKind {
    ExecutorPreprocessedBytecode {
        bytecode_size: usize,
        trace_len_log2: usize,
    },
    PlainCircuit {
        trace_len_log2: usize,
    },
    Delegation {
        trace_len_log2: usize,
    },
}

#[derive(Clone, Debug)]
pub struct BuiltCircuit {
    pub circuit_output: CircuitOutput<Mersenne31Field>,
    pub boundary_spec: Option<LlzkBoundarySpec>,
    pub witness_ssa: Vec<Vec<RawExpression<Mersenne31Field>>>,
}

#[derive(Clone, Copy)]
pub struct CircuitRecipe {
    pub name: &'static str,
    pub build_kind: CircuitBuildKind,
    pub build: fn() -> Result<BuiltCircuit>,
}

#[derive(Clone, Debug)]
struct ExplicitFlagSource {
    default_false: Boolean,
    majors: BTreeMap<DecoderMajorInstructionFamilyKey, Boolean>,
    minors: BTreeMap<
        (
            DecoderMajorInstructionFamilyKey,
            DecoderInstructionVariantsKey,
        ),
        Boolean,
    >,
}

impl ExplicitFlagSource {
    fn new(default_false: Boolean) -> Self {
        Self {
            default_false,
            majors: BTreeMap::new(),
            minors: BTreeMap::new(),
        }
    }

    fn with_major(mut self, key: DecoderMajorInstructionFamilyKey, value: Boolean) -> Self {
        self.majors.insert(key, value);
        self
    }

    fn with_minor(
        mut self,
        major: DecoderMajorInstructionFamilyKey,
        minor: DecoderInstructionVariantsKey,
        value: Boolean,
    ) -> Self {
        self.minors.insert((major, minor), value);
        self
    }
}

impl IndexableBooleanSet for ExplicitFlagSource {
    fn get_major_flag(&self, major: DecoderMajorInstructionFamilyKey) -> Boolean {
        self.majors
            .get(&major)
            .copied()
            .unwrap_or(self.default_false)
    }

    fn get_minor_flag(
        &self,
        major: DecoderMajorInstructionFamilyKey,
        minor: DecoderInstructionVariantsKey,
    ) -> Boolean {
        self.minors
            .get(&(major, minor))
            .copied()
            .unwrap_or(self.default_false)
    }
}

#[derive(Clone, Copy, Debug)]
enum BinopVariant {
    Xor,
    Or,
    And,
}

#[derive(Clone, Copy, Debug)]
enum ShiftVariant {
    Sll,
    Srl,
    Sra,
}

#[derive(Clone, Copy, Debug)]
enum MopVariant {
    AddMod,
    SubMod,
    MulMod,
}

#[derive(Clone, Copy, Debug)]
enum MulVariant {
    Signed,
    UnsignedOnly,
}

#[derive(Clone, Copy, Debug)]
enum DivRemVariant {
    Signed,
    UnsignedOnly,
}

fn finalize_build<T>(
    build: impl FnOnce(&mut BasicAssembly<Mersenne31Field>) -> T,
) -> (CircuitOutput<Mersenne31Field>, T) {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    let metadata = build(&mut cs);
    let (circuit_output, _) = cs.finalize();
    (circuit_output, metadata)
}

fn dump_ssa_for_build(
    externally_assigned: impl IntoIterator<Item = Variable>,
    build: impl FnOnce(&mut BasicAssembly<Mersenne31Field, WitnessGraphCreator<Mersenne31Field>>),
) -> Vec<Vec<RawExpression<Mersenne31Field>>> {
    let mut cs = BasicAssembly::<Mersenne31Field, WitnessGraphCreator<Mersenne31Field>>::new();
    cs.witness_placer = Some(WitnessGraphCreator::<Mersenne31Field>::new());
    build(&mut cs);
    let externally_assigned = externally_assigned.into_iter().collect::<Vec<_>>();
    if !externally_assigned.is_empty() {
        let assume_boundary_inputs = move |placer: &mut <BasicAssembly<
            Mersenne31Field,
            WitnessGraphCreator<Mersenne31Field>,
        > as Circuit<Mersenne31Field>>::WitnessPlacer| {
            use prover::cs::cs::witness_placer::WitnessPlacer;

            for variable in externally_assigned.iter().copied() {
                placer.assume_assigned(variable);
            }
        };
        cs.set_values(assume_boundary_inputs);
    }
    let (_, witness_placer) = cs.finalize();
    let graph = witness_placer.unwrap();
    let (_resolution_order, ssa_forms) = graph.compute_resolution_order();
    ssa_forms
}

fn build_executor_family(
    bytecode_size: usize,
    synthesis: impl FnOnce(&mut BasicAssembly<Mersenne31Field>),
    witness_ssa_fn: fn(&[u32]) -> Vec<Vec<RawExpression<Mersenne31Field>>>,
) -> Result<BuiltCircuit> {
    let bytecode = vec![0u32; bytecode_size];
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    synthesis(&mut cs);
    let (circuit_output, _) = cs.finalize();
    Ok(BuiltCircuit {
        circuit_output,
        boundary_spec: None,
        witness_ssa: witness_ssa_fn(&bytecode),
    })
}

fn build_plain_family(
    circuit_name: &'static str,
    build: impl FnOnce(&mut BasicAssembly<Mersenne31Field>) -> LlzkBoundarySpec,
    witness_build: impl FnOnce(
        &mut BasicAssembly<Mersenne31Field, WitnessGraphCreator<Mersenne31Field>>,
    ),
) -> Result<BuiltCircuit> {
    let (circuit_output, boundary_spec) = finalize_build(build);
    let witness_ssa = dump_ssa_for_build(
        boundary_input_variables(&circuit_output, &boundary_spec, circuit_name),
        witness_build,
    );
    Ok(BuiltCircuit {
        circuit_output,
        boundary_spec: Some(boundary_spec),
        witness_ssa,
    })
}

fn build_delegation_family(
    build: impl FnOnce(&mut BasicAssembly<Mersenne31Field>),
    boundary_from_output: impl FnOnce(&CircuitOutput<Mersenne31Field>) -> Result<LlzkBoundarySpec>,
    witness_build: impl Fn(&mut BasicAssembly<Mersenne31Field, WitnessGraphCreator<Mersenne31Field>>),
) -> Result<BuiltCircuit> {
    let (circuit_output, ()) = finalize_build(build);
    let boundary_spec = boundary_from_output(&circuit_output)?;
    let witness_ssa =
        dump_ssa_witness_eval_form_for_delegation::<Mersenne31Field, _>(witness_build);
    Ok(BuiltCircuit {
        circuit_output,
        boundary_spec: Some(boundary_spec),
        witness_ssa,
    })
}

fn signal_vars(values: impl IntoIterator<Item = ExtractedVariable>) -> BTreeSet<Variable> {
    let mut set = BTreeSet::new();
    for value in values {
        match value {
            ExtractedVariable::Register { low, high } => {
                set.insert(low);
                set.insert(high);
            }
            ExtractedVariable::Scalar(variable) => {
                set.insert(variable);
            }
        }
    }
    set
}

fn make_boundary_spec(
    inputs: Vec<ExtractedVariable>,
    outputs: Vec<ExtractedVariable>,
    include_shuffle_ram_io: bool,
) -> LlzkBoundarySpec {
    let mut spec = LlzkBoundarySpec::new(inputs.clone(), outputs.clone())
        .with_signal_vars(signal_vars(inputs.into_iter().chain(outputs.clone())));
    if include_shuffle_ram_io {
        spec = spec.with_shuffle_ram_io();
    }
    spec
}

fn variables_in_extracted_value(value: ExtractedVariable) -> impl Iterator<Item = Variable> {
    let vars = match value {
        ExtractedVariable::Register { low, high } => [Some(low), Some(high)],
        ExtractedVariable::Scalar(variable) => [Some(variable), None],
    };
    vars.into_iter().flatten()
}

fn boundary_input_variables<F: PrimeField>(
    circuit_output: &CircuitOutput<F>,
    boundary_spec: &LlzkBoundarySpec,
    circuit_name: &str,
) -> BTreeSet<Variable> {
    let mut inputs = boundary_spec
        .inputs
        .iter()
        .copied()
        .flat_map(variables_in_extracted_value)
        .collect::<BTreeSet<_>>();

    let use_legacy_query2_input = boundary_spec.use_legacy_query2_input
        || (boundary_spec.include_shuffle_ram_io && circuit_name == "unified_reduced_machine");

    if boundary_spec.include_shuffle_ram_io {
        for (query_index, query) in circuit_output.shuffle_ram_queries.iter().enumerate() {
            inputs.extend(query.read_value);
            if !query.is_readonly() && use_legacy_query2_input && query_index == 2 {
                inputs.extend(query.write_value);
            }
            if let ShuffleRamQueryType::RegisterOrRam { address, .. } = query.query_type {
                inputs.extend(address);
            }
        }
    }

    inputs
}

fn fixed_boolean<CS: Circuit<Mersenne31Field>>(cs: &mut CS, value: bool) -> Boolean {
    let var = cs.add_boolean_variable();
    let var_id = var.get_variable().unwrap();
    let expected = if value { 1u64 } else { 0u64 };
    cs.add_constraint_allow_explicit_linear(
        prover::cs::constraint::Constraint::from(var_id)
            - prover::cs::constraint::Term::from(expected),
    );
    cs.add_picus_parallel_constraint(PicusStructuredConstraint::Eq {
        lhs: PicusExpr::Variable(var_id),
        rhs: PicusExpr::Constant(Mersenne31Field::from_u64_unchecked(expected)),
    });
    cs.set_values(move |placer: &mut CS::WitnessPlacer| {
        use prover::cs::cs::witness_placer::WitnessMask;
        use prover::cs::cs::witness_placer::WitnessPlacer;
        use prover::cs::cs::witness_placer::WitnessTypeSet;

        let mask = <<<CS as Circuit<Mersenne31Field>>::WitnessPlacer as WitnessTypeSet<
            Mersenne31Field,
        >>::Mask as WitnessMask>::constant(value);
        placer.assign_mask(var_id, &mask);
    });

    var
}

fn fixed_num<CS: Circuit<Mersenne31Field>>(cs: &mut CS, value: u64) -> Num<Mersenne31Field> {
    let var = cs.add_variable();
    cs.add_constraint_allow_explicit_linear(
        prover::cs::constraint::Constraint::from(var) - prover::cs::constraint::Term::from(value),
    );
    cs.add_picus_parallel_constraint(PicusStructuredConstraint::Eq {
        lhs: PicusExpr::Variable(var),
        rhs: PicusExpr::Constant(Mersenne31Field::from_u64_unchecked(value)),
    });
    cs.set_values(move |placer: &mut CS::WitnessPlacer| {
        use prover::cs::cs::witness_placer::WitnessComputationalField;
        use prover::cs::cs::witness_placer::WitnessPlacer;
        use prover::cs::cs::witness_placer::WitnessTypeSet;

        let field = <<<CS as Circuit<Mersenne31Field>>::WitnessPlacer as WitnessTypeSet<
            Mersenne31Field,
        >>::Field as WitnessComputationalField<Mersenne31Field>>::constant(
            Mersenne31Field::from_u64_unchecked(value),
        );
        placer.assign_field(var, &field);
    });
    Num::Var(var)
}

fn fixed_register<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    value: u32,
) -> Register<Mersenne31Field> {
    let reg = Register::new(cs);
    let low = (value & 0xffff) as u64;
    let high = (value >> 16) as u64;
    cs.add_constraint_allow_explicit_linear(
        prover::cs::constraint::Constraint::from(reg.0[0].get_variable())
            - prover::cs::constraint::Term::from(low),
    );
    cs.add_constraint_allow_explicit_linear(
        prover::cs::constraint::Constraint::from(reg.0[1].get_variable())
            - prover::cs::constraint::Term::from(high),
    );
    cs.add_picus_parallel_constraint(PicusStructuredConstraint::Eq {
        lhs: PicusExpr::Variable(reg.0[0].get_variable()),
        rhs: PicusExpr::Constant(Mersenne31Field::from_u64_unchecked(low)),
    });
    cs.add_picus_parallel_constraint(PicusStructuredConstraint::Eq {
        lhs: PicusExpr::Variable(reg.0[1].get_variable()),
        rhs: PicusExpr::Constant(Mersenne31Field::from_u64_unchecked(high)),
    });
    let low_u16 = low as u16;
    let high_u16 = high as u16;
    let variables = [reg.0[0].get_variable(), reg.0[1].get_variable()];
    cs.set_values(move |placer: &mut CS::WitnessPlacer| {
        use prover::cs::cs::witness_placer::WitnessComputationalInteger;
        use prover::cs::cs::witness_placer::WitnessPlacer;
        use prover::cs::cs::witness_placer::WitnessTypeSet;

        let low = <<<CS as Circuit<Mersenne31Field>>::WitnessPlacer as WitnessTypeSet<
            Mersenne31Field,
        >>::U16 as WitnessComputationalInteger<u16>>::constant(low_u16);
        let high = <<<CS as Circuit<Mersenne31Field>>::WitnessPlacer as WitnessTypeSet<
            Mersenne31Field,
        >>::U16 as WitnessComputationalInteger<u16>>::constant(high_u16);
        placer.assign_u16(variables[0], &low);
        placer.assign_u16(variables[1], &high);
    });
    reg
}

/// The standalone harnesses often expose an encoded mode/funct3 scalar as an LLZK
/// input while the underlying op implementation consumes boolean flag bits. The
/// witness graph cannot infer those decomposition bits from constraints alone, so we
/// assign them explicitly from the scalar boundary input.
fn assign_scalar_u8_bits<CS: Circuit<Mersenne31Field>, const N: usize>(
    cs: &mut CS,
    scalar: Variable,
    bit_vars: [Variable; N],
) {
    cs.set_values(move |placer: &mut CS::WitnessPlacer| {
        use prover::cs::cs::witness_placer::WitnessComputationalInteger;
        use prover::cs::cs::witness_placer::WitnessPlacer;

        let value = placer.get_u8(scalar);
        for (bit_idx, bit_var) in bit_vars.into_iter().enumerate() {
            let bit = value.get_bit(bit_idx as u32);
            placer.assign_mask(bit_var, &bit);
        }
    });
}

fn rs1_shuffle_ram_query<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    reg_encoding: Num<Mersenne31Field>,
    bytecode_is_in_rom_only: bool,
) -> (Register<Mersenne31Field>, ShuffleRamMemQuery) {
    let mut local_timestamp_in_cycle = 0;
    if !bytecode_is_in_rom_only {
        local_timestamp_in_cycle += 1;
    }
    // Standalone LLZK recipes expose register-read values explicitly through the
    // boundary, so these query values must be ordinary input-backed registers rather
    // than oracle-backed placeholders.
    let value = Register::new(cs);
    let query = form_mem_op_for_register_only(local_timestamp_in_cycle, reg_encoding, value, value);
    (value, query)
}

fn rs2_shuffle_ram_query<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    reg_encoding: Num<Mersenne31Field>,
    bytecode_is_in_rom_only: bool,
) -> (Register<Mersenne31Field>, ShuffleRamMemQuery) {
    let mut local_timestamp_in_cycle = RS2_LOAD_LOCAL_TIMESTAMP;
    if !bytecode_is_in_rom_only {
        local_timestamp_in_cycle += 1;
    }
    let value = Register::new(cs);
    let query = form_mem_op_for_register_only(local_timestamp_in_cycle, reg_encoding, value, value);
    (value, query)
}

fn rd_shuffle_ram_query<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    reg_encoding: Num<Mersenne31Field>,
    write_value: Register<Mersenne31Field>,
    bytecode_is_in_rom_only: bool,
) -> ShuffleRamMemQuery {
    let local_timestamp_in_cycle = if bytecode_is_in_rom_only { 2 } else { 3 };
    // Standalone load/store recipes expose shuffle-RAM IO directly through the LLZK boundary.
    // Keep the synthetic RD prior-value slot input-backed too, otherwise witness SSA sees the
    // same variables as both externally assigned and internally placeholder-assigned.
    let read_value = Register::new_unchecked(cs);
    form_mem_op_for_register_only(
        local_timestamp_in_cycle,
        reg_encoding,
        read_value,
        write_value,
    )
}

fn add_standalone_rom_tables<CS: Circuit<Mersenne31Field>>(cs: &mut CS) {
    use prover::cs::machine::machine_configurations::create_table_for_rom_image;
    use prover::cs::tables::create_rom_separator_table;

    let rom_separator =
        LookupWrapper::Dimensional3(create_rom_separator_table::<
            Mersenne31Field,
            { common_constants::rom::ROM_SECOND_WORD_BITS },
        >(TableType::RomAddressSpaceSeparator.to_table_id()));
    cs.add_table_with_content(TableType::RomAddressSpaceSeparator, rom_separator);

    let rom_read = LookupWrapper::Dimensional3(create_table_for_rom_image::<
        Mersenne31Field,
        { common_constants::rom::ROM_SECOND_WORD_BITS },
    >(&[], TableType::RomRead.to_table_id()));
    cs.add_table_with_content(TableType::RomRead, rom_read);
}

fn register_input(reg: Register<Mersenne31Field>) -> ExtractedVariable {
    ExtractedVariable::register([reg.0[0].get_variable(), reg.0[1].get_variable()])
}

fn register_output(reg: [Variable; 2]) -> ExtractedVariable {
    ExtractedVariable::register(reg)
}

fn scalar_output(variable: Variable) -> ExtractedVariable {
    ExtractedVariable::scalar(variable)
}

fn delegation_register_write(
    access: &RegisterAndIndirectAccesses,
) -> Result<([Variable; 2], [Variable; 2])> {
    match access.register_access {
        RegisterAccessType::Write {
            read_value,
            write_value,
        } => Ok((read_value, write_value)),
        RegisterAccessType::Read { .. } => anyhow::bail!(
            "delegation register access x{} expected a write",
            access.register_index
        ),
    }
}

fn delegation_indirect_reads(access: &RegisterAndIndirectAccesses) -> Result<Vec<[Variable; 2]>> {
    access
        .indirect_accesses
        .iter()
        .map(|indirect| match indirect {
            IndirectAccessType::Read { read_value, .. } => Ok(*read_value),
            IndirectAccessType::Write { .. } => anyhow::bail!(
                "delegation indirect access for x{} expected a read",
                access.register_index
            ),
        })
        .collect()
}

fn delegation_indirect_writes(
    access: &RegisterAndIndirectAccesses,
) -> Result<Vec<([Variable; 2], [Variable; 2])>> {
    access
        .indirect_accesses
        .iter()
        .map(|indirect| match indirect {
            IndirectAccessType::Write {
                read_value,
                write_value,
                ..
            } => Ok((*read_value, *write_value)),
            IndirectAccessType::Read { .. } => anyhow::bail!(
                "delegation indirect access for x{} expected a write",
                access.register_index
            ),
        })
        .collect()
}

fn bigint_with_control_boundary_from_output(
    circuit_output: &CircuitOutput<Mersenne31Field>,
) -> Result<LlzkBoundarySpec> {
    let accesses = &circuit_output.register_and_indirect_memory_accesses;
    if accesses.len() != 3 {
        anyhow::bail!(
            "bigint delegation expected 3 register/indirect access bundles, found {}",
            accesses.len()
        );
    }

    let x10_writes = delegation_indirect_writes(&accesses[0])?;
    let x11_reads = delegation_indirect_reads(&accesses[1])?;
    let (x12_read, x12_write) = delegation_register_write(&accesses[2])?;
    if accesses[0].register_index != 10
        || accesses[1].register_index != 11
        || accesses[2].register_index != 12
    {
        anyhow::bail!("bigint delegation register access layout changed unexpectedly");
    }
    if x10_writes.len() != 8 || x11_reads.len() != 8 {
        anyhow::bail!("bigint delegation indirect access layout changed unexpectedly");
    }

    let mut inputs = x10_writes
        .iter()
        .map(|(read_value, _)| register_output(*read_value))
        .collect::<Vec<_>>();
    inputs.extend(x11_reads.into_iter().map(register_output));
    inputs.push(ExtractedVariable::scalar(x12_read[0]));

    let mut outputs = x10_writes
        .into_iter()
        .map(|(_, write_value)| register_output(write_value))
        .collect::<Vec<_>>();
    outputs.push(register_output(x12_write));

    Ok(make_boundary_spec(inputs, outputs, false))
}

fn blake2_with_extended_control_boundary_from_output(
    circuit_output: &CircuitOutput<Mersenne31Field>,
) -> Result<LlzkBoundarySpec> {
    let accesses = &circuit_output.register_and_indirect_memory_accesses;
    if accesses.len() != 3 {
        anyhow::bail!(
            "blake2 delegation expected 3 register/indirect access bundles, found {}",
            accesses.len()
        );
    }

    let x10_writes = delegation_indirect_writes(&accesses[0])?;
    let x11_reads = delegation_indirect_reads(&accesses[1])?;
    let (x12_read, x12_write) = delegation_register_write(&accesses[2])?;
    if accesses[0].register_index != 10
        || accesses[1].register_index != 11
        || accesses[2].register_index != 12
    {
        anyhow::bail!("blake2 delegation register access layout changed unexpectedly");
    }
    if x10_writes.len() != 24 || x11_reads.len() != 16 {
        anyhow::bail!("blake2 delegation indirect access layout changed unexpectedly");
    }

    let mut inputs = x10_writes[..8]
        .iter()
        .map(|(read_value, _)| register_output(*read_value))
        .collect::<Vec<_>>();
    inputs.extend(
        x10_writes[8..]
            .iter()
            .map(|(read_value, _)| register_output(*read_value)),
    );
    inputs.extend(x11_reads.into_iter().map(register_output));
    inputs.push(ExtractedVariable::scalar(x12_read[1]));

    let mut outputs = x10_writes[..8]
        .iter()
        .map(|(_, write_value)| register_output(*write_value))
        .collect::<Vec<_>>();
    outputs.extend(
        x10_writes[8..]
            .iter()
            .map(|(_, write_value)| register_output(*write_value)),
    );
    outputs.push(register_output(x12_write));

    Ok(make_boundary_spec(inputs, outputs, false))
}

fn keccak_special5_boundary_from_output(
    circuit_output: &CircuitOutput<Mersenne31Field>,
) -> Result<LlzkBoundarySpec> {
    let accesses = &circuit_output.register_and_indirect_memory_accesses;
    if accesses.len() != 2 {
        anyhow::bail!(
            "keccak delegation expected 2 register/indirect access bundles, found {}",
            accesses.len()
        );
    }

    if accesses[0].register_index != 10 || accesses[1].register_index != 11 {
        anyhow::bail!("keccak delegation register access layout changed unexpectedly");
    }

    let (x10_read, x10_write) = delegation_register_write(&accesses[0])?;
    let x11_read = match accesses[1].register_access {
        RegisterAccessType::Read { read_value } => read_value,
        RegisterAccessType::Write { .. } => {
            anyhow::bail!("keccak delegation x11 access unexpectedly became a write")
        }
    };
    let state_writes = delegation_indirect_writes(&accesses[1])?;
    if state_writes.len() != 12 {
        anyhow::bail!(
            "keccak delegation expected 12 indirect state writes, found {}",
            state_writes.len()
        );
    }

    let mut inputs = vec![
        ExtractedVariable::scalar(x10_read[0]),
        register_output(x11_read),
    ];
    inputs.extend(
        state_writes
            .iter()
            .map(|(read_value, _)| register_output(*read_value)),
    );

    let mut outputs = vec![ExtractedVariable::scalar(x10_write[0])];
    outputs.extend(
        state_writes
            .into_iter()
            .map(|(_, write_value)| register_output(write_value)),
    );

    Ok(make_boundary_spec(inputs, outputs, false))
}

fn build_binary_like_decoder_output<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    rs1: Register<Mersenne31Field>,
    rs2: Register<Mersenne31Field>,
    imm: Register<Mersenne31Field>,
    funct3: Num<Mersenne31Field>,
) -> BasicDecodingResultWithSigns<Mersenne31Field> {
    // Signed register decomposition uses the fixed `U16GetSignAndHighByte` lookup. Logical LLZK
    // can tolerate an uninitialized table driver here, but the one-row compiler cannot.
    cs.materialize_table(TableType::U16GetSignAndHighByte);
    BasicDecodingResultWithSigns {
        pc_next: Register::new_from_constant(0),
        src1: prover::cs::types::RegisterDecompositionWithSign::parse_reg(cs, rs1),
        src2: prover::cs::types::RegisterDecompositionWithSign::parse_reg(cs, rs2),
        imm,
        rs2_index: prover::cs::constraint::Constraint::from(0u64),
        funct3,
        funct12: prover::cs::constraint::Constraint::from(0u64),
    }
}

fn materialize_constraint_output<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    mut constraint: prover::cs::constraint::Constraint<Mersenne31Field>,
) -> Variable {
    constraint.normalize();
    if constraint.is_empty() {
        return match fixed_num(cs, 0) {
            Num::Var(var) => var,
            Num::Constant(_) => unreachable!("fixed_num always materializes a variable"),
        };
    } else if constraint.terms.iter().all(|term| term.is_constant()) {
        let value = constraint.as_constant().as_u64_reduced();
        return match fixed_num(cs, value) {
            Num::Var(var) => var,
            Num::Constant(_) => unreachable!("fixed_num always materializes a variable"),
        };
    } else {
        let parallel_constraint = constraint.clone();
        let var = cs.add_variable_from_constraint_allow_explicit_linear(constraint);
        cs.add_picus_parallel_constraint(PicusStructuredConstraint::Eq {
            lhs: PicusExpr::Variable(var),
            rhs: prover::cs::cs::circuit::picus_expr_from_constraint(&parallel_constraint),
        });
        return var;
    }
}

fn materialize_register_outputs<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    reg: Register<Mersenne31Field>,
) -> [Variable; 2] {
    reg.0.map(|word| match word {
        Num::Var(var) => var,
        Num::Constant(value) => materialize_constraint_output(
            cs,
            prover::cs::constraint::Constraint::from(value.as_u64_reduced()),
        ),
    })
}

fn materialize_rd_outputs<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    diffs: CommonDiffs<Mersenne31Field>,
) -> [Variable; 2] {
    let selected = CommonDiffs::select_final_rd_value(cs, &[diffs]);
    materialize_register_outputs(cs, selected)
}

fn materialize_next_pc_outputs<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    diffs: &CommonDiffs<Mersenne31Field>,
    default_pc: Register<Mersenne31Field>,
) -> [Variable; 2] {
    match &diffs.new_pc_value {
        NextPcValue::Default => materialize_register_outputs(cs, default_pc),
        NextPcValue::Custom(reg) => materialize_register_outputs(cs, *reg),
    }
}

fn materialize_trap_outputs<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    diffs: &CommonDiffs<Mersenne31Field>,
) -> Option<[Variable; 2]> {
    match (&diffs.trapped, &diffs.trap_reason) {
        (Some(trapped), Some(trap_reason)) => {
            let trapped_var = materialize_constraint_output(
                cs,
                prover::cs::constraint::Constraint::from(*trapped),
            );
            let trap_reason_var = match trap_reason {
                Num::Var(var) => *var,
                Num::Constant(value) => materialize_constraint_output(
                    cs,
                    prover::cs::constraint::Constraint::from(value.as_u64_reduced()),
                ),
            };
            Some([trapped_var, trap_reason_var])
        }
        (None, None) => None,
        _ => panic!("trap outputs must be either fully present or absent"),
    }
}

fn add_sub_harness<CS: Circuit<Mersenne31Field>>(cs: &mut CS, is_sub: bool) -> LlzkBoundarySpec {
    let false_flag = fixed_boolean(cs, false);
    let true_flag = fixed_boolean(cs, true);
    let rs1 = Register::new(cs);
    let rs2 = Register::new(cs);
    let zero_reg = fixed_register(cs, 0);
    let zero_funct3 = fixed_num(cs, 0);
    let decoder_output = build_binary_like_decoder_output(cs, rs1, rs2, zero_reg, zero_funct3);
    let initial_pc = fixed_register(cs, 0);
    let initial_state = MinimalStateRegistersInMemory { pc: initial_pc };
    let flags = if is_sub {
        ExplicitFlagSource::new(false_flag).with_major(SUB_OP_KEY, true_flag)
    } else {
        ExplicitFlagSource::new(false_flag).with_major(ADD_OP_KEY, true_flag)
    };
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = if is_sub {
        SubOp::apply::<_, true, false>(cs, &initial_state, &decoder_output, &flags, &mut opt_ctx)
    } else {
        AddOp::apply::<_, true, false>(cs, &initial_state, &decoder_output, &flags, &mut opt_ctx)
    };
    let rd_outputs = materialize_rd_outputs(cs, diffs.clone());
    let next_pc = fixed_register(cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(cs, &diffs, next_pc);
    opt_ctx.enforce_all(cs);
    make_boundary_spec(
        vec![register_input(rs1), register_input(rs2)],
        vec![
            register_output(rd_outputs),
            register_output(next_pc_outputs),
        ],
        false,
    )
}

fn lui_harness<CS: Circuit<Mersenne31Field>>(cs: &mut CS) -> LlzkBoundarySpec {
    let false_flag = fixed_boolean(cs, false);
    let true_flag = fixed_boolean(cs, true);
    let imm = Register::new(cs);
    let zero = fixed_register(cs, 0);
    let zero_reg = fixed_register(cs, 0);
    let zero_funct3 = fixed_num(cs, 0);
    let decoder_output = build_binary_like_decoder_output(cs, zero, zero_reg, imm, zero_funct3);
    let initial_pc = fixed_register(cs, 0);
    let initial_state = MinimalStateRegistersInMemory { pc: initial_pc };
    let flags = ExplicitFlagSource::new(false_flag).with_major(LUI_OP_KEY, true_flag);
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs =
        LuiOp::apply::<_, true, false>(cs, &initial_state, &decoder_output, &flags, &mut opt_ctx);
    let rd_outputs = materialize_rd_outputs(cs, diffs.clone());
    let next_pc = fixed_register(cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(cs, &diffs, next_pc);
    opt_ctx.enforce_all(cs);
    make_boundary_spec(
        vec![register_input(imm)],
        vec![
            register_output(rd_outputs),
            register_output(next_pc_outputs),
        ],
        false,
    )
}

fn auipc_harness<CS: Circuit<Mersenne31Field>>(cs: &mut CS) -> LlzkBoundarySpec {
    let false_flag = fixed_boolean(cs, false);
    let true_flag = fixed_boolean(cs, true);
    let pc = Register::new(cs);
    let imm = Register::new(cs);
    let zero = fixed_register(cs, 0);
    let zero_reg = fixed_register(cs, 0);
    let zero_funct3 = fixed_num(cs, 0);
    let decoder_output = build_binary_like_decoder_output(cs, zero, zero_reg, imm, zero_funct3);
    let initial_state = MinimalStateRegistersInMemory { pc };
    let pc_next = calculate_pc_next_no_overflows(cs, pc);
    let flags = ExplicitFlagSource::new(false_flag).with_major(AUIPC_OP_KEY, true_flag);
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs =
        AuiPc::apply::<_, true, false>(cs, &initial_state, &decoder_output, &flags, &mut opt_ctx);
    let rd_outputs = materialize_rd_outputs(cs, diffs.clone());
    let next_pc_outputs = materialize_next_pc_outputs(cs, &diffs, pc_next);
    opt_ctx.enforce_all(cs);
    make_boundary_spec(
        vec![register_input(pc), register_input(imm)],
        vec![
            register_output(rd_outputs),
            register_output(next_pc_outputs),
        ],
        false,
    )
}

fn binop_harness<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    variant: BinopVariant,
) -> LlzkBoundarySpec {
    for table in [TableType::Xor, TableType::Or, TableType::And] {
        cs.materialize_table(table);
    }
    let false_flag = fixed_boolean(cs, false);
    let true_flag = fixed_boolean(cs, true);
    let rs1 = Register::new(cs);
    let rs2 = Register::new(cs);
    let funct3 = match variant {
        BinopVariant::Xor => fixed_num(cs, 0b100),
        BinopVariant::Or => fixed_num(cs, 0b110),
        BinopVariant::And => fixed_num(cs, 0b111),
    };
    let zero_reg = fixed_register(cs, 0);
    let decoder_output = build_binary_like_decoder_output(cs, rs1, rs2, zero_reg, funct3);
    let initial_pc = fixed_register(cs, 0);
    let initial_state = MinimalStateRegistersInMemory { pc: initial_pc };
    let flags = ExplicitFlagSource::new(false_flag).with_major(BINOP_COMMON_OP_KEY, true_flag);
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = BinaryOp::apply::<_, true, false>(
        cs,
        &initial_state,
        &decoder_output,
        &flags,
        &mut opt_ctx,
    );
    let rd_outputs = materialize_rd_outputs(cs, diffs.clone());
    let next_pc = fixed_register(cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(cs, &diffs, next_pc);
    opt_ctx.enforce_all(cs);
    make_boundary_spec(
        vec![register_input(rs1), register_input(rs2)],
        vec![
            register_output(rd_outputs),
            register_output(next_pc_outputs),
        ],
        false,
    )
}

fn shift_harness<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    variant: ShiftVariant,
) -> LlzkBoundarySpec {
    for table in [
        TableType::ShiftImplementation,
        TableType::TruncateShiftAmount,
        TableType::SRASignFiller,
    ] {
        cs.materialize_table(table);
    }
    let false_flag = fixed_boolean(cs, false);
    let shift_major_true = fixed_boolean(cs, true);
    let rs1 = Register::new(cs);
    let rs2 = Register::new(cs);
    let zero_reg = fixed_register(cs, 0);
    let zero_funct3 = fixed_num(cs, 0);
    let flags = match variant {
        ShiftVariant::Sll => {
            ExplicitFlagSource::new(false_flag).with_major(SHIFT_COMMON_OP_KEY, shift_major_true)
        }
        ShiftVariant::Srl => ExplicitFlagSource::new(false_flag)
            .with_major(SHIFT_COMMON_OP_KEY, shift_major_true)
            .with_minor(
                SHIFT_COMMON_OP_KEY,
                SHIFT_RIGHT_KEY,
                fixed_boolean(cs, true),
            ),
        ShiftVariant::Sra => ExplicitFlagSource::new(false_flag)
            .with_major(SHIFT_COMMON_OP_KEY, shift_major_true)
            .with_minor(
                SHIFT_COMMON_OP_KEY,
                SHIFT_RIGHT_KEY,
                fixed_boolean(cs, true),
            )
            .with_minor(
                SHIFT_COMMON_OP_KEY,
                SHIFT_RIGHT_ALGEBRAIC_KEY,
                fixed_boolean(cs, true),
            ),
    };
    let decoder_output = build_binary_like_decoder_output(cs, rs1, rs2, zero_reg, zero_funct3);
    let initial_pc = fixed_register(cs, 0);
    let initial_state = MinimalStateRegistersInMemory { pc: initial_pc };
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = ShiftOp::<true, false>::apply::<_, true, false>(
        cs,
        &initial_state,
        &decoder_output,
        &flags,
        &mut opt_ctx,
    );
    let rd_outputs = materialize_rd_outputs(cs, diffs.clone());
    let next_pc = fixed_register(cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(cs, &diffs, next_pc);
    opt_ctx.enforce_all(cs);
    make_boundary_spec(
        vec![register_input(rs1), register_input(rs2)],
        vec![
            register_output(rd_outputs),
            register_output(next_pc_outputs),
        ],
        false,
    )
}

fn mop_harness<CS: Circuit<Mersenne31Field>>(cs: &mut CS, variant: MopVariant) -> LlzkBoundarySpec {
    cs.set_picus_parallel_constraints_enabled(true);
    let false_flag = fixed_boolean(cs, false);
    let mop_major_true = fixed_boolean(cs, true);
    let rs1 = Register::new(cs);
    let rs2 = Register::new(cs);
    let zero_reg = fixed_register(cs, 0);
    let zero_funct3 = fixed_num(cs, 0);
    let flags = match variant {
        MopVariant::AddMod => ExplicitFlagSource::new(false_flag)
            .with_major(MOP_OP_KEY, mop_major_true)
            .with_minor(MOP_OP_KEY, ADDMOD_OP_KEY, fixed_boolean(cs, true)),
        MopVariant::SubMod => ExplicitFlagSource::new(false_flag)
            .with_major(MOP_OP_KEY, mop_major_true)
            .with_minor(MOP_OP_KEY, SUBMOD_OP_KEY, fixed_boolean(cs, true)),
        MopVariant::MulMod => ExplicitFlagSource::new(false_flag)
            .with_major(MOP_OP_KEY, mop_major_true)
            .with_minor(MOP_OP_KEY, MULMOD_OP_KEY, fixed_boolean(cs, true)),
    };
    let decoder_output = build_binary_like_decoder_output(cs, rs1, rs2, zero_reg, zero_funct3);
    let initial_pc = fixed_register(cs, 0);
    let initial_state = MinimalStateRegistersInMemory { pc: initial_pc };
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs =
        MopOp::apply::<_, true, false>(cs, &initial_state, &decoder_output, &flags, &mut opt_ctx);
    let rd_outputs = materialize_rd_outputs(cs, diffs.clone());
    let next_pc = fixed_register(cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(cs, &diffs, next_pc);
    opt_ctx.enforce_all(cs);
    make_boundary_spec(
        vec![register_input(rs1), register_input(rs2)],
        vec![
            register_output(rd_outputs),
            register_output(next_pc_outputs),
        ],
        false,
    )
}

fn conditional_harness<CS: Circuit<Mersenne31Field>>(cs: &mut CS) -> LlzkBoundarySpec {
    cs.set_picus_parallel_constraints_enabled(true);
    for table in [
        TableType::JumpCleanupOffset,
        TableType::ConditionalOpAllConditionsResolver,
        TableType::U16GetSignAndHighByte,
    ] {
        cs.materialize_table(table);
    }

    let false_flag = fixed_boolean(cs, false);
    let true_flag = fixed_boolean(cs, true);
    let rs1 = Register::new(cs);
    let rs2 = Register::new(cs);
    let pc = Register::new(cs);
    let imm = Register::new(cs);
    let funct3: Num<Mersenne31Field> = Num::Var(cs.add_variable());
    let funct3_bit0 = cs.add_boolean_variable();
    let funct3_bit1 = cs.add_boolean_variable();
    let funct3_bit2 = cs.add_boolean_variable();
    let funct3_bit0_var = funct3_bit0.get_variable().unwrap();
    let funct3_bit1_var = funct3_bit1.get_variable().unwrap();
    let funct3_bit2_var = funct3_bit2.get_variable().unwrap();
    cs.add_constraint_allow_explicit_linear(
        prover::cs::constraint::Constraint::from(funct3.get_variable())
            - prover::cs::constraint::Term::from(funct3_bit0_var)
            - prover::cs::constraint::Term::from((
                Mersenne31Field::from_u64_unchecked(2),
                funct3_bit1_var,
            ))
            - prover::cs::constraint::Term::from((
                Mersenne31Field::from_u64_unchecked(4),
                funct3_bit2_var,
            )),
    );
    cs.add_picus_parallel_constraint(PicusStructuredConstraint::Eq {
        lhs: PicusExpr::Variable(funct3.get_variable()),
        rhs: PicusExpr::Variable(funct3_bit0_var)
            + (PicusExpr::Constant(Mersenne31Field::from_u64_unchecked(2))
                * PicusExpr::Variable(funct3_bit1_var))
            + (PicusExpr::Constant(Mersenne31Field::from_u64_unchecked(4))
                * PicusExpr::Variable(funct3_bit2_var)),
    });
    assign_scalar_u8_bits(
        cs,
        funct3.get_variable(),
        [funct3_bit0_var, funct3_bit1_var, funct3_bit2_var],
    );
    let pc_next = calculate_pc_next_no_overflows(cs, pc);
    let decoder_output = BasicDecodingResultWithSigns {
        pc_next,
        src1: prover::cs::types::RegisterDecompositionWithSign::parse_reg(cs, rs1),
        src2: prover::cs::types::RegisterDecompositionWithSign::parse_reg(cs, rs2),
        imm,
        rs2_index: prover::cs::constraint::Constraint::from(0u64),
        funct3,
        funct12: prover::cs::constraint::Constraint::from(0u64),
    };
    let initial_state = MinimalStateRegistersInMemory { pc };
    let flags =
        ExplicitFlagSource::new(false_flag).with_major(CONDITIONAL_COMMON_OP_KEY, true_flag);
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = ConditionalOp::<true>::apply::<_, true, false>(
        cs,
        &initial_state,
        &decoder_output,
        &flags,
        &mut opt_ctx,
    );
    let rd_outputs = materialize_rd_outputs(cs, diffs.clone());
    let next_pc_outputs = materialize_next_pc_outputs(cs, &diffs, pc_next);
    opt_ctx.enforce_all(cs);
    make_boundary_spec(
        vec![
            register_input(rs1),
            register_input(rs2),
            register_input(pc),
            register_input(imm),
            ExtractedVariable::scalar(funct3.get_variable()),
        ],
        vec![
            register_output(rd_outputs),
            register_output(next_pc_outputs),
        ],
        false,
    )
}

fn jump_harness<CS: Circuit<Mersenne31Field>, const ASSUME_TRUSTED_CODE: bool>(
    cs: &mut CS,
) -> LlzkBoundarySpec {
    cs.set_picus_parallel_constraints_enabled(true);
    cs.materialize_table(TableType::JumpCleanupOffset);
    cs.materialize_table(TableType::U16GetSignAndHighByte);

    let false_flag = fixed_boolean(cs, false);
    let true_flag = fixed_boolean(cs, true);
    let is_jal = cs.add_boolean_variable();
    let rs1 = Register::new(cs);
    let pc = Register::new(cs);
    let imm = Register::new(cs);
    let zero_reg = fixed_register(cs, 0);
    let zero_funct3 = fixed_num(cs, 0);
    let pc_next = calculate_pc_next_no_overflows(cs, pc);
    let decoder_output = BasicDecodingResultWithSigns {
        pc_next,
        src1: prover::cs::types::RegisterDecompositionWithSign::parse_reg(cs, rs1),
        src2: prover::cs::types::RegisterDecompositionWithSign::parse_reg(cs, zero_reg),
        imm,
        rs2_index: prover::cs::constraint::Constraint::from(0u64),
        funct3: zero_funct3,
        funct12: prover::cs::constraint::Constraint::from(0u64),
    };
    let initial_state = MinimalStateRegistersInMemory { pc };
    let flags = ExplicitFlagSource::new(false_flag)
        .with_major(JUMP_COMMON_OP_KEY, true_flag)
        .with_minor(JUMP_COMMON_OP_KEY, JAL_OP_KEY, is_jal);
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = JumpOp::apply::<_, ASSUME_TRUSTED_CODE, false>(
        cs,
        &initial_state,
        &decoder_output,
        &flags,
        &mut opt_ctx,
    );
    let rd_outputs = materialize_rd_outputs(cs, diffs.clone());
    let next_pc_outputs = materialize_next_pc_outputs(cs, &diffs, pc_next);
    let trap_outputs = materialize_trap_outputs(cs, &diffs);
    opt_ctx.enforce_all(cs);

    let mut outputs = vec![
        register_output(rd_outputs),
        register_output(next_pc_outputs),
    ];
    if let Some([trapped, trap_reason]) = trap_outputs {
        outputs.push(scalar_output(trapped));
        outputs.push(scalar_output(trap_reason));
    }
    make_boundary_spec(
        vec![
            register_input(rs1),
            register_input(pc),
            register_input(imm),
            ExtractedVariable::scalar(is_jal.get_variable().unwrap()),
        ],
        outputs,
        false,
    )
}

fn mul_harness<CS: Circuit<Mersenne31Field>>(cs: &mut CS, variant: MulVariant) -> LlzkBoundarySpec {
    cs.materialize_table(TableType::U16GetSignAndHighByte);
    cs.materialize_table(TableType::RangeCheckSmall);
    let false_flag = fixed_boolean(cs, false);
    let true_flag = fixed_boolean(cs, true);
    let rs1 = Register::new(cs);
    let rs2 = Register::new(cs);
    let zero_reg = fixed_register(cs, 0);
    let zero_funct3 = fixed_num(cs, 0);
    let mode: Num<Mersenne31Field> = Num::Var(cs.add_variable());
    let mode_bit0 = cs.add_boolean_variable();
    let mode_bit0_var = mode_bit0.get_variable().unwrap();
    let mut mode_bit_vars = vec![mode_bit0_var];
    let flags = match variant {
        MulVariant::Signed => {
            let mode_bit1 = cs.add_boolean_variable();
            let mode_bit1_var = mode_bit1.get_variable().unwrap();
            mode_bit_vars.push(mode_bit1_var);
            cs.add_constraint_allow_explicit_linear(
                prover::cs::constraint::Constraint::from(mode.get_variable())
                    - prover::cs::constraint::Term::from(mode_bit0_var)
                    - prover::cs::constraint::Term::from((
                        Mersenne31Field::from_u64_unchecked(2),
                        mode_bit1_var,
                    )),
            );
            let mode_is_0 = Boolean::and(&mode_bit0.toggle(), &mode_bit1.toggle(), cs);
            let mode_is_1 = Boolean::and(&mode_bit0, &mode_bit1.toggle(), cs);
            let mode_is_2 = Boolean::and(&mode_bit0.toggle(), &mode_bit1, cs);
            ExplicitFlagSource::new(false_flag)
                .with_major(MUL_COMMON_OP_KEY, true_flag)
                .with_minor(MUL_COMMON_OP_KEY, MUL_OP_KEY, mode_is_0)
                .with_minor(MUL_COMMON_OP_KEY, MULH_OP_KEY, mode_is_1)
                .with_minor(MUL_COMMON_OP_KEY, MULHSU_OP_KEY, mode_is_2)
        }
        MulVariant::UnsignedOnly => {
            cs.add_constraint_allow_explicit_linear(
                prover::cs::constraint::Constraint::from(mode.get_variable())
                    - prover::cs::constraint::Term::from(mode_bit0_var),
            );
            ExplicitFlagSource::new(false_flag)
                .with_major(MUL_COMMON_OP_KEY, true_flag)
                .with_minor(MUL_COMMON_OP_KEY, MUL_OP_KEY, mode_bit0.toggle())
        }
    };
    match mode_bit_vars.as_slice() {
        [bit0] => assign_scalar_u8_bits(cs, mode.get_variable(), [*bit0]),
        [bit0, bit1] => assign_scalar_u8_bits(cs, mode.get_variable(), [*bit0, *bit1]),
        _ => unreachable!("mul harness only uses one or two mode bits"),
    }
    let decoder_output = build_binary_like_decoder_output(cs, rs1, rs2, zero_reg, zero_funct3);
    let initial_pc = fixed_register(cs, 0);
    let initial_state = MinimalStateRegistersInMemory { pc: initial_pc };
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = match variant {
        MulVariant::Signed => MulOp::<true>::apply::<_, true, false>(
            cs,
            &initial_state,
            &decoder_output,
            &flags,
            &mut opt_ctx,
        ),
        MulVariant::UnsignedOnly => MulOp::<false>::apply::<_, true, false>(
            cs,
            &initial_state,
            &decoder_output,
            &flags,
            &mut opt_ctx,
        ),
    };
    let rd_outputs = materialize_rd_outputs(cs, diffs.clone());
    let next_pc = fixed_register(cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(cs, &diffs, next_pc);
    opt_ctx.enforce_all(cs);
    make_boundary_spec(
        vec![
            register_input(rs1),
            register_input(rs2),
            ExtractedVariable::scalar(mode.get_variable()),
        ],
        vec![
            register_output(rd_outputs),
            register_output(next_pc_outputs),
        ],
        false,
    )
}

fn divrem_harness<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    variant: DivRemVariant,
) -> LlzkBoundarySpec {
    cs.materialize_table(TableType::U16GetSignAndHighByte);
    cs.materialize_table(TableType::RangeCheckSmall);
    let false_flag = fixed_boolean(cs, false);
    let true_flag = fixed_boolean(cs, true);
    let rs1 = Register::new(cs);
    let rs2 = Register::new(cs);
    let zero_reg = fixed_register(cs, 0);
    let zero_funct3 = fixed_num(cs, 0);
    let mode: Num<Mersenne31Field> = Num::Var(cs.add_variable());
    let mode_bit0 = cs.add_boolean_variable();
    let mode_bit0_var = mode_bit0.get_variable().unwrap();
    let mut mode_bit_vars = vec![mode_bit0_var];
    let flags = match variant {
        DivRemVariant::Signed => {
            let mode_bit1 = cs.add_boolean_variable();
            let mode_bit1_var = mode_bit1.get_variable().unwrap();
            mode_bit_vars.push(mode_bit1_var);
            cs.add_constraint_allow_explicit_linear(
                prover::cs::constraint::Constraint::from(mode.get_variable())
                    - prover::cs::constraint::Term::from(mode_bit0_var)
                    - prover::cs::constraint::Term::from((
                        Mersenne31Field::from_u64_unchecked(2),
                        mode_bit1_var,
                    )),
            );
            let mode_is_0 = Boolean::and(&mode_bit0.toggle(), &mode_bit1.toggle(), cs);
            let mode_is_1 = Boolean::and(&mode_bit0, &mode_bit1.toggle(), cs);
            let mode_is_2 = Boolean::and(&mode_bit0.toggle(), &mode_bit1, cs);
            ExplicitFlagSource::new(false_flag)
                .with_major(DIVREM_COMMON_OP_KEY, true_flag)
                .with_minor(DIVREM_COMMON_OP_KEY, DIV_OP_KEY, mode_is_0)
                .with_minor(DIVREM_COMMON_OP_KEY, DIVU_OP_KEY, mode_is_1)
                .with_minor(DIVREM_COMMON_OP_KEY, REM_OP_KEY, mode_is_2)
        }
        DivRemVariant::UnsignedOnly => {
            cs.add_constraint_allow_explicit_linear(
                prover::cs::constraint::Constraint::from(mode.get_variable())
                    - prover::cs::constraint::Term::from(mode_bit0_var),
            );
            ExplicitFlagSource::new(false_flag)
                .with_major(DIVREM_COMMON_OP_KEY, true_flag)
                .with_minor(DIVREM_COMMON_OP_KEY, DIVU_OP_KEY, mode_bit0.toggle())
        }
    };
    match mode_bit_vars.as_slice() {
        [bit0] => assign_scalar_u8_bits(cs, mode.get_variable(), [*bit0]),
        [bit0, bit1] => assign_scalar_u8_bits(cs, mode.get_variable(), [*bit0, *bit1]),
        _ => unreachable!("div/rem harness only uses one or two mode bits"),
    }
    let decoder_output = build_binary_like_decoder_output(cs, rs1, rs2, zero_reg, zero_funct3);
    let initial_pc = fixed_register(cs, 0);
    let initial_state = MinimalStateRegistersInMemory { pc: initial_pc };
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = match variant {
        DivRemVariant::Signed => DivRemOp::<true>::apply::<_, true, false>(
            cs,
            &initial_state,
            &decoder_output,
            &flags,
            &mut opt_ctx,
        ),
        DivRemVariant::UnsignedOnly => DivRemOp::<false>::apply::<_, true, false>(
            cs,
            &initial_state,
            &decoder_output,
            &flags,
            &mut opt_ctx,
        ),
    };
    let rd_outputs = materialize_rd_outputs(cs, diffs.clone());
    let next_pc = fixed_register(cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(cs, &diffs, next_pc);
    opt_ctx.enforce_all(cs);
    make_boundary_spec(
        vec![
            register_input(rs1),
            register_input(rs2),
            ExtractedVariable::scalar(mode.get_variable()),
        ],
        vec![
            register_output(rd_outputs),
            register_output(next_pc_outputs),
        ],
        false,
    )
}

fn csrrw_harness<CS: Circuit<Mersenne31Field>>(cs: &mut CS) -> LlzkBoundarySpec {
    cs.materialize_table(TableType::U16GetSignAndHighByte);
    let false_flag = fixed_boolean(cs, false);
    let true_flag = fixed_boolean(cs, true);
    let rs1 = Register::new(cs);
    let pc = Register::new(cs);
    let zero_reg = fixed_register(cs, 0);
    let zero_num = fixed_num(cs, 0);
    let pc_next = calculate_pc_next_no_overflows(cs, pc);
    let decoder_output = BasicDecodingResultWithSigns {
        pc_next,
        src1: prover::cs::types::RegisterDecompositionWithSign::parse_reg(cs, rs1),
        src2: prover::cs::types::RegisterDecompositionWithSign::parse_reg(cs, zero_reg),
        imm: zero_reg,
        rs2_index: prover::cs::constraint::Constraint::from(0u64),
        funct3: zero_num,
        funct12: prover::cs::constraint::Constraint::from(0u64),
    };
    let initial_state = MinimalStateRegistersInMemory { pc };
    let flags = ExplicitFlagSource::new(false_flag).with_major(CSR_COMMON_OP_KEY, true_flag);
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = apply_non_determinism_csr_only_assuming_no_unimp::<
        _,
        _,
        _,
        _,
        _,
        _,
        false,
        false,
        false,
        true,
        false,
    >(cs, &initial_state, &decoder_output, &flags, &mut opt_ctx);
    let rd_outputs = materialize_rd_outputs(cs, diffs.clone());
    let next_pc_outputs = materialize_next_pc_outputs(cs, &diffs, pc_next);
    opt_ctx.enforce_all(cs);
    make_boundary_spec(
        vec![register_input(rs1), register_input(pc)],
        vec![
            register_output(rd_outputs),
            register_output(next_pc_outputs),
        ],
        false,
    )
}

fn load_boundary_spec(
    rs1_index: Variable,
    rs2_index: Variable,
    pc: Register<Mersenne31Field>,
    imm: Register<Mersenne31Field>,
    funct3: Variable,
    rd_outputs: [Variable; 2],
    next_pc_outputs: [Variable; 2],
) -> LlzkBoundarySpec {
    make_boundary_spec(
        vec![
            ExtractedVariable::scalar(rs1_index),
            ExtractedVariable::scalar(rs2_index),
            register_input(pc),
            register_input(imm),
            ExtractedVariable::scalar(funct3),
        ],
        vec![
            register_output(rd_outputs),
            register_output(next_pc_outputs),
        ],
        true,
    )
}

fn build_load_mode_flags<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    false_flag: Boolean,
) -> (Num<Mersenne31Field>, ExplicitFlagSource, Variable, Variable) {
    let funct3: Num<Mersenne31Field> = Num::Var(cs.add_variable());
    let bit0 = cs.add_boolean_variable();
    let bit1 = cs.add_boolean_variable();
    let bit2 = cs.add_boolean_variable();
    let bit0_var = bit0.get_variable().unwrap();
    let bit1_var = bit1.get_variable().unwrap();
    let bit2_var = bit2.get_variable().unwrap();
    cs.add_constraint_allow_explicit_linear(
        prover::cs::constraint::Constraint::from(funct3.get_variable())
            - prover::cs::constraint::Term::from(bit0_var)
            - prover::cs::constraint::Term::from((
                Mersenne31Field::from_u64_unchecked(2),
                bit1_var,
            ))
            - prover::cs::constraint::Term::from((
                Mersenne31Field::from_u64_unchecked(4),
                bit2_var,
            )),
    );
    // Valid load funct3 encodings are {000, 001, 010, 100, 101}. The only cases
    // with bit1 = 1 should be `010`, so both `(bit1 && bit0)` and `(bit1 && bit2)`
    // must be forbidden. Keep this quadratic so the standalone harness stays within
    // the circuit system's max degree.
    cs.add_constraint(
        prover::cs::constraint::Term::from(bit1_var) * prover::cs::constraint::Term::from(bit0_var),
    );
    cs.add_constraint(
        prover::cs::constraint::Term::from(bit2_var) * prover::cs::constraint::Term::from(bit1_var),
    );
    let full_word = Boolean::and(&bit2.toggle(), &Boolean::and(&bit1, &bit0.toggle(), cs), cs);
    let half_word = Boolean::and(&bit1.toggle(), &bit0, cs);
    let flags = ExplicitFlagSource::new(false_flag)
        .with_major(LOAD_COMMON_OP_KEY, fixed_boolean(cs, true))
        .with_minor(LOAD_COMMON_OP_KEY, LOAD_WORD_OP_KEY, full_word)
        .with_minor(LOAD_COMMON_OP_KEY, LOAD_HALF_WORD_OP_KEY, half_word);
    assign_scalar_u8_bits(cs, funct3.get_variable(), [bit0_var, bit1_var, bit2_var]);
    (funct3, flags, bit1_var, bit2_var)
}

fn load_query<CS: Circuit<Mersenne31Field>>(cs: &mut CS) -> ShuffleRamMemQuery {
    let true_flag = fixed_boolean(cs, true);
    let is_register = cs.add_variable_from_constraint_allow_explicit_linear(
        prover::cs::constraint::Constraint::from(1u64)
            - prover::cs::constraint::Term::from(true_flag.get_variable().unwrap()),
    );
    let query_type = ShuffleRamQueryType::RegisterOrRam {
        is_register: Boolean::Is(is_register),
        address: [cs.add_variable(), cs.add_variable()],
    };
    let read_value = [cs.add_variable(), cs.add_variable()];
    let query = ShuffleRamMemQuery {
        query_type,
        local_timestamp_in_cycle: RS2_LOAD_LOCAL_TIMESTAMP,
        read_value,
        write_value: read_value,
    };
    cs.add_shuffle_ram_query(query);
    query
}

fn store_query<CS: Circuit<Mersenne31Field>>(cs: &mut CS) -> ShuffleRamMemQuery {
    let true_flag = fixed_boolean(cs, true);
    let is_register = cs.add_variable_from_constraint_allow_explicit_linear(
        prover::cs::constraint::Constraint::from(1u64)
            - prover::cs::constraint::Term::from(true_flag.get_variable().unwrap()),
    );
    let query_type = ShuffleRamQueryType::RegisterOrRam {
        is_register: Boolean::Is(is_register),
        address: [cs.add_variable(), cs.add_variable()],
    };
    let read_value = [cs.add_variable(), cs.add_variable()];
    let write_value = [cs.add_variable(), cs.add_variable()];
    let query = ShuffleRamMemQuery {
        query_type,
        local_timestamp_in_cycle: 2,
        read_value,
        write_value,
    };
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        use prover::cs::cs::witness_placer::WitnessPlacer;
        placer.assume_assigned(write_value[0]);
        placer.assume_assigned(write_value[1]);
        if prover::cs::cs::cs_reference::RESOLVE_WITNESS {
            let value = placer.get_oracle_u32(Placeholder::WriteRegMemWriteValue);
            placer.assign_u32_from_u16_parts(write_value, &value);
        }
    };
    cs.set_values(value_fn);
    cs.add_shuffle_ram_query(query);
    query
}

fn load_harness<CS: Circuit<Mersenne31Field>>(cs: &mut CS) -> LlzkBoundarySpec {
    for table in [
        TableType::MemoryOffsetGetBits,
        TableType::ExtendLoadedValue,
        TableType::U16GetSignAndHighByte,
    ] {
        cs.materialize_table(table);
    }
    add_standalone_rom_tables(cs);
    let false_flag = fixed_boolean(cs, false);
    let (funct3, flags, _bit1_var, _bit2_var) = build_load_mode_flags(cs, false_flag);
    let rs1_index = cs.add_variable();
    let rs2_index = cs.add_variable();
    let pc = Register::new(cs);
    let imm = Register::new(cs);
    let (rs1_reg, rs1_query) = rs1_shuffle_ram_query(cs, Num::Var(rs1_index), true);
    cs.add_shuffle_ram_query(rs1_query);
    let load_query = load_query(cs);
    let pc_next = calculate_pc_next_no_overflows(cs, pc);
    let zero_reg = fixed_register(cs, 0);
    let decoder_output = BasicDecodingResultWithSigns {
        pc_next,
        src1: prover::cs::types::RegisterDecompositionWithSign::parse_reg(cs, rs1_reg),
        src2: prover::cs::types::RegisterDecompositionWithSign::parse_reg(cs, zero_reg),
        imm,
        rs2_index: prover::cs::constraint::Constraint::from(rs2_index),
        funct3,
        funct12: prover::cs::constraint::Constraint::from(0u64),
    };
    let initial_state = MinimalStateRegistersInMemory { pc };
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = LoadOp::<true, true>::spec_apply::<_, _, _, _, _, _, true, false>(
        cs,
        &initial_state,
        &decoder_output,
        &flags,
        &mut { load_query.clone() },
        &mut opt_ctx,
    );
    let rd_outputs = materialize_rd_outputs(cs, diffs.clone());
    // The chunked-memory one-row compiler assumes the executor-style memory-query shape:
    // RS1 read, RS2/load read, then RD/store writeback. Standalone loads only need the first
    // two queries semantically, so we synthesize the RD writeback query here from the explicit
    // boundary-backed destination register index and the already-materialized RD result.
    let rd_write_query = rd_shuffle_ram_query(
        cs,
        Num::Var(rs2_index),
        Register(rd_outputs.map(Num::Var)),
        true,
    );
    cs.add_shuffle_ram_query(rd_write_query);
    let next_pc_outputs = materialize_next_pc_outputs(cs, &diffs, pc_next);
    opt_ctx.enforce_all(cs);
    load_boundary_spec(
        rs1_index,
        rs2_index,
        pc,
        imm,
        funct3.get_variable(),
        rd_outputs,
        next_pc_outputs,
    )
}

fn build_store_mode_flags<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    false_flag: Boolean,
) -> (ExplicitFlagSource, Variable) {
    let funct3 = cs.add_variable();
    let bit0 = cs.add_boolean_variable();
    let bit1 = cs.add_boolean_variable();
    let bit0_var = bit0.get_variable().unwrap();
    let bit1_var = bit1.get_variable().unwrap();
    cs.add_constraint_allow_explicit_linear(
        prover::cs::constraint::Constraint::from(funct3)
            - prover::cs::constraint::Term::from(bit0_var)
            - prover::cs::constraint::Term::from((
                Mersenne31Field::from_u64_unchecked(2),
                bit1_var,
            )),
    );
    cs.add_constraint(
        prover::cs::constraint::Term::from(bit0_var) * prover::cs::constraint::Term::from(bit1_var),
    );
    let full_word = Boolean::and(&bit1, &bit0.toggle(), cs);
    let half_word = Boolean::and(&bit1.toggle(), &bit0, cs);
    let flags = ExplicitFlagSource::new(false_flag)
        .with_major(STORE_COMMON_OP_KEY, fixed_boolean(cs, true))
        .with_minor(STORE_COMMON_OP_KEY, STORE_WORD_OP_KEY, full_word)
        .with_minor(STORE_COMMON_OP_KEY, STORE_HALF_WORD_OP_KEY, half_word);
    assign_scalar_u8_bits(cs, funct3, [bit0_var, bit1_var]);
    (flags, funct3)
}

fn store_harness<CS: Circuit<Mersenne31Field>>(cs: &mut CS) -> LlzkBoundarySpec {
    for table in [
        TableType::MemoryOffsetGetBits,
        TableType::StoreByteSourceContribution,
        TableType::StoreByteExistingContribution,
        TableType::U16GetSignAndHighByte,
    ] {
        cs.materialize_table(table);
    }
    add_standalone_rom_tables(cs);
    let false_flag = fixed_boolean(cs, false);
    let (flags, funct3) = build_store_mode_flags(cs, false_flag);
    let rs1_index = cs.add_variable();
    let rs2_index = cs.add_variable();
    let pc = Register::new(cs);
    let imm = Register::new(cs);
    let (rs1_reg, rs1_query) = rs1_shuffle_ram_query(cs, Num::Var(rs1_index), true);
    cs.add_shuffle_ram_query(rs1_query);
    let (rs2_reg, rs2_query) = rs2_shuffle_ram_query(cs, Num::Var(rs2_index), true);
    cs.add_shuffle_ram_query(rs2_query);
    let mut store_query = store_query(cs);
    let pc_next = calculate_pc_next_no_overflows(cs, pc);
    let decoder_output = BasicDecodingResultWithSigns {
        pc_next,
        src1: prover::cs::types::RegisterDecompositionWithSign::parse_reg(cs, rs1_reg),
        src2: prover::cs::types::RegisterDecompositionWithSign::parse_reg(cs, rs2_reg),
        imm,
        rs2_index: prover::cs::constraint::Constraint::from(rs2_index),
        funct3: Num::Var(funct3),
        funct12: prover::cs::constraint::Constraint::from(0u64),
    };
    let initial_state = MinimalStateRegistersInMemory { pc };
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = StoreOp::<true>::spec_apply::<_, _, _, _, _, _, true, false>(
        cs,
        &initial_state,
        &decoder_output,
        &flags,
        &mut store_query,
        &mut opt_ctx,
    );
    let next_pc_outputs = materialize_next_pc_outputs(cs, &diffs, pc_next);
    opt_ctx.enforce_all(cs);
    make_boundary_spec(
        vec![
            ExtractedVariable::scalar(rs1_index),
            ExtractedVariable::scalar(rs2_index),
            register_input(pc),
            register_input(imm),
            ExtractedVariable::scalar(funct3),
        ],
        vec![register_output(next_pc_outputs)],
        true,
    )
}

fn build_add_op() -> Result<BuiltCircuit> {
    build_plain_family(
        "add_op",
        |cs| add_sub_harness(cs, false),
        |cs| {
            let _ = add_sub_harness(cs, false);
        },
    )
}

fn build_sub_op() -> Result<BuiltCircuit> {
    build_plain_family(
        "sub_op",
        |cs| add_sub_harness(cs, true),
        |cs| {
            let _ = add_sub_harness(cs, true);
        },
    )
}

fn build_lui_op() -> Result<BuiltCircuit> {
    build_plain_family("lui_op", lui_harness, |cs| {
        let _ = lui_harness(cs);
    })
}

fn build_auipc_op() -> Result<BuiltCircuit> {
    build_plain_family("auipc_op", auipc_harness, |cs| {
        let _ = auipc_harness(cs);
    })
}

fn build_xor_op() -> Result<BuiltCircuit> {
    build_plain_family(
        "xor_op",
        |cs| binop_harness(cs, BinopVariant::Xor),
        |cs| {
            let _ = binop_harness(cs, BinopVariant::Xor);
        },
    )
}

fn build_or_op() -> Result<BuiltCircuit> {
    build_plain_family(
        "or_op",
        |cs| binop_harness(cs, BinopVariant::Or),
        |cs| {
            let _ = binop_harness(cs, BinopVariant::Or);
        },
    )
}

fn build_and_op() -> Result<BuiltCircuit> {
    build_plain_family(
        "and_op",
        |cs| binop_harness(cs, BinopVariant::And),
        |cs| {
            let _ = binop_harness(cs, BinopVariant::And);
        },
    )
}

fn build_sll_op() -> Result<BuiltCircuit> {
    build_plain_family(
        "sll_op",
        |cs| shift_harness(cs, ShiftVariant::Sll),
        |cs| {
            let _ = shift_harness(cs, ShiftVariant::Sll);
        },
    )
}

fn build_srl_op() -> Result<BuiltCircuit> {
    build_plain_family(
        "srl_op",
        |cs| shift_harness(cs, ShiftVariant::Srl),
        |cs| {
            let _ = shift_harness(cs, ShiftVariant::Srl);
        },
    )
}

fn build_sra_op() -> Result<BuiltCircuit> {
    build_plain_family(
        "sra_op",
        |cs| shift_harness(cs, ShiftVariant::Sra),
        |cs| {
            let _ = shift_harness(cs, ShiftVariant::Sra);
        },
    )
}

fn build_addmod_op() -> Result<BuiltCircuit> {
    build_plain_family(
        "addmod_op",
        |cs| mop_harness(cs, MopVariant::AddMod),
        |cs| {
            let _ = mop_harness(cs, MopVariant::AddMod);
        },
    )
}

fn build_submod_op() -> Result<BuiltCircuit> {
    build_plain_family(
        "submod_op",
        |cs| mop_harness(cs, MopVariant::SubMod),
        |cs| {
            let _ = mop_harness(cs, MopVariant::SubMod);
        },
    )
}

fn build_mulmod_op() -> Result<BuiltCircuit> {
    build_plain_family(
        "mulmod_op",
        |cs| mop_harness(cs, MopVariant::MulMod),
        |cs| {
            let _ = mop_harness(cs, MopVariant::MulMod);
        },
    )
}

fn build_conditional_op() -> Result<BuiltCircuit> {
    build_plain_family("conditional_op", conditional_harness, |cs| {
        let _ = conditional_harness(cs);
    })
}

fn build_jump_op_trusted() -> Result<BuiltCircuit> {
    build_plain_family("jump_op_trusted", jump_harness::<_, true>, |cs| {
        let _ = jump_harness::<_, true>(cs);
    })
}

fn build_jump_op_untrusted() -> Result<BuiltCircuit> {
    build_plain_family("jump_op_untrusted", jump_harness::<_, false>, |cs| {
        let _ = jump_harness::<_, false>(cs);
    })
}

fn build_mul_op_signed() -> Result<BuiltCircuit> {
    build_plain_family(
        "mul_op_signed",
        |cs| mul_harness(cs, MulVariant::Signed),
        |cs| {
            let _ = mul_harness(cs, MulVariant::Signed);
        },
    )
}

fn build_mul_op_unsigned_only() -> Result<BuiltCircuit> {
    build_plain_family(
        "mul_op_unsigned_only",
        |cs| mul_harness(cs, MulVariant::UnsignedOnly),
        |cs| {
            let _ = mul_harness(cs, MulVariant::UnsignedOnly);
        },
    )
}

fn build_divrem_op_signed() -> Result<BuiltCircuit> {
    build_plain_family(
        "divrem_op_signed",
        |cs| divrem_harness(cs, DivRemVariant::Signed),
        |cs| {
            let _ = divrem_harness(cs, DivRemVariant::Signed);
        },
    )
}

fn build_divrem_op_unsigned_only() -> Result<BuiltCircuit> {
    build_plain_family(
        "divrem_op_unsigned_only",
        |cs| divrem_harness(cs, DivRemVariant::UnsignedOnly),
        |cs| {
            let _ = divrem_harness(cs, DivRemVariant::UnsignedOnly);
        },
    )
}

fn build_csrrw_op() -> Result<BuiltCircuit> {
    build_plain_family("csrrw_op", csrrw_harness, |cs| {
        let _ = csrrw_harness(cs);
    })
}

fn build_load_op() -> Result<BuiltCircuit> {
    build_plain_family("load_op", load_harness, |cs| {
        let _ = load_harness(cs);
    })
}

fn build_store_op() -> Result<BuiltCircuit> {
    build_plain_family("store_op", store_harness, |cs| {
        let _ = store_harness(cs);
    })
}

fn optimized_decoder_boundary_spec(
    instruction: Register<Mersenne31Field>,
    invalid_opcode: Variable,
    outputs: [Variable; 8],
) -> LlzkBoundarySpec {
    let mut extracted_outputs = vec![scalar_output(invalid_opcode)];
    extracted_outputs.extend(outputs.into_iter().map(scalar_output));
    make_boundary_spec(vec![register_input(instruction)], extracted_outputs, false)
}

fn build_optimized_decoder() -> Result<BuiltCircuit> {
    let (circuit_output, instruction, invalid_opcode, outputs) =
        picus_frontend::build_optimized_decoder_circuit_output(true);
    let boundary_spec = optimized_decoder_boundary_spec(instruction, invalid_opcode, outputs);
    let witness_ssa = picus_frontend::dump_optimized_decoder_witness_eval_form();
    Ok(BuiltCircuit {
        circuit_output,
        boundary_spec: Some(boundary_spec),
        witness_ssa,
    })
}

fn build_bigint_with_control_delegation() -> Result<BuiltCircuit> {
    use prover::cs::delegation::bigint_with_control::define_u256_ops_extended_control_delegation_circuit_for_translation;

    build_delegation_family(
        |cs| {
            define_u256_ops_extended_control_delegation_circuit_for_translation(cs);
        },
        bigint_with_control_boundary_from_output,
        |cs| {
            define_u256_ops_extended_control_delegation_circuit_for_translation(cs);
        },
    )
}

fn build_blake2_with_extended_control_delegation() -> Result<BuiltCircuit> {
    use prover::cs::delegation::blake2_round_with_extended_control::define_blake2_with_extended_control_delegation_circuit_for_translation;

    build_delegation_family(
        |cs| {
            define_blake2_with_extended_control_delegation_circuit_for_translation(cs);
        },
        blake2_with_extended_control_boundary_from_output,
        |cs| {
            define_blake2_with_extended_control_delegation_circuit_for_translation(cs);
        },
    )
}

fn build_keccak_special5_delegation() -> Result<BuiltCircuit> {
    use prover::cs::delegation::keccak_special5::define_keccak_special5_delegation_circuit;

    build_delegation_family(
        |cs| {
            define_keccak_special5_delegation_circuit::<_, _, false>(cs);
        },
        keccak_special5_boundary_from_output,
        |cs| {
            define_keccak_special5_delegation_circuit::<_, _, false>(cs);
        },
    )
}

fn build_add_sub_lui_auipc_mop_executor() -> Result<BuiltCircuit> {
    use add_sub_lui_auipc_mop::dump_ssa_form;
    use add_sub_lui_auipc_mop::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    use prover::cs::machine::ops::unrolled::add_sub_lui_auipc_mop::add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode;
    use prover::cs::machine::ops::unrolled::add_sub_lui_auipc_mop::add_sub_lui_auipc_mop_table_addition_fn;
    let bytecode_size = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
    build_executor_family(
        bytecode_size,
        |cs| {
            add_sub_lui_auipc_mop_table_addition_fn(cs);
            add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode(cs);
        },
        dump_ssa_form,
    )
}

fn build_jump_branch_slt_executor() -> Result<BuiltCircuit> {
    use jump_branch_slt::dump_ssa_form;
    use jump_branch_slt::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    use prover::cs::machine::ops::unrolled::jump_branch_slt::jump_branch_slt_circuit_with_preprocessed_bytecode;
    use prover::cs::machine::ops::unrolled::jump_branch_slt::jump_branch_slt_table_addition_fn;
    let bytecode_size = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
    build_executor_family(
        bytecode_size,
        |cs| {
            jump_branch_slt_table_addition_fn(cs);
            jump_branch_slt_circuit_with_preprocessed_bytecode::<_, _, true>(cs);
        },
        dump_ssa_form,
    )
}

fn build_load_store_subword_only_executor() -> Result<BuiltCircuit> {
    use load_store_subword_only::dump_ssa_form;
    use load_store_subword_only::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    use prover::cs::machine::ops::unrolled::load_store_subword_only::subword_only_load_store_circuit_with_preprocessed_bytecode;
    use prover::cs::machine::ops::unrolled::load_store_subword_only::subword_only_load_store_table_addition_fn;
    let bytecode_size = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
    build_executor_family(
        bytecode_size,
        |cs| {
            subword_only_load_store_table_addition_fn(cs);
            subword_only_load_store_circuit_with_preprocessed_bytecode::<
                _,
                _,
                { common_constants::ROM_SECOND_WORD_BITS },
            >(cs);
        },
        dump_ssa_form,
    )
}

fn build_load_store_word_only_executor() -> Result<BuiltCircuit> {
    use load_store_word_only::dump_ssa_form;
    use load_store_word_only::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    use prover::cs::machine::ops::unrolled::load_store_word_only::word_only_load_store_circuit_with_preprocessed_bytecode;
    use prover::cs::machine::ops::unrolled::load_store_word_only::word_only_load_store_table_addition_fn;
    let bytecode_size = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
    build_executor_family(
        bytecode_size,
        |cs| {
            word_only_load_store_table_addition_fn(cs);
            word_only_load_store_circuit_with_preprocessed_bytecode::<
                _,
                _,
                { common_constants::ROM_SECOND_WORD_BITS },
            >(cs);
        },
        dump_ssa_form,
    )
}

fn build_mul_div_executor() -> Result<BuiltCircuit> {
    use mul_div::dump_ssa_form;
    use mul_div::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    use prover::cs::machine::ops::unrolled::mul_div::mul_div_circuit_with_preprocessed_bytecode;
    use prover::cs::machine::ops::unrolled::mul_div::mul_div_table_addition_fn;
    let bytecode_size = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
    build_executor_family(
        bytecode_size,
        |cs| {
            mul_div_table_addition_fn(cs);
            mul_div_circuit_with_preprocessed_bytecode::<_, _, true>(cs);
        },
        dump_ssa_form,
    )
}

fn build_shift_binary_csr_executor() -> Result<BuiltCircuit> {
    use prover::cs::machine::machine_configurations::create_csr_table_for_delegation;
    use prover::cs::machine::ops::unrolled::shift_binary_csr::shift_binop_csrrw_circuit_with_preprocessed_bytecode;
    use prover::cs::machine::ops::unrolled::shift_binary_csr::shift_binop_csrrw_table_addition_fn;
    use shift_binary_csr::dump_ssa_form;
    use shift_binary_csr::ALLOWED_DELEGATION_CSRS;
    use shift_binary_csr::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    let bytecode_size = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
    build_executor_family(
        bytecode_size,
        |cs| {
            let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
                true,
                ALLOWED_DELEGATION_CSRS,
                TableType::SpecialCSRProperties.to_table_id(),
            );
            shift_binop_csrrw_table_addition_fn(cs);
            cs.add_table_with_content(
                TableType::SpecialCSRProperties,
                LookupWrapper::Dimensional3(csr_table),
            );
            shift_binop_csrrw_circuit_with_preprocessed_bytecode(cs);
        },
        dump_ssa_form,
    )
}

fn build_unified_reduced_machine_executor() -> Result<BuiltCircuit> {
    use prover::cs::machine::machine_configurations::create_csr_table_for_delegation;
    use prover::cs::machine::ops::unrolled::reduced_machine_ops::reduced_machine_circuit_with_preprocessed_bytecode;
    use prover::cs::machine::ops::unrolled::reduced_machine_ops::reduced_machine_table_addition_fn;
    use unified_reduced_machine::dump_ssa_form;
    use unified_reduced_machine::ALLOWED_DELEGATION_CSRS;
    use unified_reduced_machine::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    let bytecode_size = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
    build_executor_family(
        bytecode_size,
        |cs| {
            let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
                true,
                ALLOWED_DELEGATION_CSRS,
                TableType::SpecialCSRProperties.to_table_id(),
            );
            reduced_machine_table_addition_fn(cs);
            cs.add_table_with_content(
                TableType::SpecialCSRProperties,
                LookupWrapper::Dimensional3(csr_table),
            );
            reduced_machine_circuit_with_preprocessed_bytecode::<
                _,
                _,
                { common_constants::ROM_SECOND_WORD_BITS },
            >(cs);
        },
        dump_ssa_form,
    )
}

pub fn add_sub_lui_auipc_mop_recipe() -> CircuitRecipe {
    use add_sub_lui_auipc_mop::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    use add_sub_lui_auipc_mop::TRACE_LEN_LOG2;
    CircuitRecipe {
        name: "add_sub_lui_auipc_mop",
        build_kind: CircuitBuildKind::ExecutorPreprocessedBytecode {
            bytecode_size: (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4,
            trace_len_log2: TRACE_LEN_LOG2 as usize,
        },
        build: build_add_sub_lui_auipc_mop_executor,
    }
}

pub fn jump_branch_slt_recipe() -> CircuitRecipe {
    use jump_branch_slt::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    use jump_branch_slt::TRACE_LEN_LOG2;
    CircuitRecipe {
        name: "jump_branch_slt",
        build_kind: CircuitBuildKind::ExecutorPreprocessedBytecode {
            bytecode_size: (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4,
            trace_len_log2: TRACE_LEN_LOG2 as usize,
        },
        build: build_jump_branch_slt_executor,
    }
}

pub fn load_store_subword_only_recipe() -> CircuitRecipe {
    use load_store_subword_only::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    use load_store_subword_only::TRACE_LEN_LOG2;
    CircuitRecipe {
        name: "load_store_subword_only",
        build_kind: CircuitBuildKind::ExecutorPreprocessedBytecode {
            bytecode_size: (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4,
            trace_len_log2: TRACE_LEN_LOG2 as usize,
        },
        build: build_load_store_subword_only_executor,
    }
}

pub fn load_store_word_only_recipe() -> CircuitRecipe {
    use load_store_word_only::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    use load_store_word_only::TRACE_LEN_LOG2;
    CircuitRecipe {
        name: "load_store_word_only",
        build_kind: CircuitBuildKind::ExecutorPreprocessedBytecode {
            bytecode_size: (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4,
            trace_len_log2: TRACE_LEN_LOG2 as usize,
        },
        build: build_load_store_word_only_executor,
    }
}

pub fn mul_div_recipe() -> CircuitRecipe {
    use mul_div::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    use mul_div::TRACE_LEN_LOG2;
    CircuitRecipe {
        name: "mul_div",
        build_kind: CircuitBuildKind::ExecutorPreprocessedBytecode {
            bytecode_size: (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4,
            trace_len_log2: TRACE_LEN_LOG2 as usize,
        },
        build: build_mul_div_executor,
    }
}

pub fn shift_binary_csr_recipe() -> CircuitRecipe {
    use shift_binary_csr::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    use shift_binary_csr::TRACE_LEN_LOG2;
    CircuitRecipe {
        name: "shift_binary_csr",
        build_kind: CircuitBuildKind::ExecutorPreprocessedBytecode {
            bytecode_size: (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4,
            trace_len_log2: TRACE_LEN_LOG2 as usize,
        },
        build: build_shift_binary_csr_executor,
    }
}

pub fn unified_reduced_machine_recipe() -> CircuitRecipe {
    use unified_reduced_machine::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;
    use unified_reduced_machine::TRACE_LEN_LOG2;
    CircuitRecipe {
        name: "unified_reduced_machine",
        build_kind: CircuitBuildKind::ExecutorPreprocessedBytecode {
            bytecode_size: (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4,
            trace_len_log2: TRACE_LEN_LOG2 as usize,
        },
        build: build_unified_reduced_machine_executor,
    }
}

pub fn add_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "add_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_add_op,
    }
}

pub fn sub_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "sub_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_sub_op,
    }
}

pub fn lui_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "lui_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_lui_op,
    }
}

pub fn auipc_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "auipc_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_auipc_op,
    }
}

pub fn xor_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "xor_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_xor_op,
    }
}

pub fn or_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "or_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_or_op,
    }
}

pub fn and_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "and_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_and_op,
    }
}

pub fn sll_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "sll_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_sll_op,
    }
}

pub fn srl_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "srl_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_srl_op,
    }
}

pub fn sra_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "sra_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_sra_op,
    }
}

pub fn addmod_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "addmod_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_addmod_op,
    }
}

pub fn submod_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "submod_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_submod_op,
    }
}

pub fn mulmod_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "mulmod_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_mulmod_op,
    }
}

pub fn conditional_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "conditional_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_conditional_op,
    }
}

pub fn jump_op_trusted_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "jump_op_trusted",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_jump_op_trusted,
    }
}

pub fn jump_op_untrusted_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "jump_op_untrusted",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_jump_op_untrusted,
    }
}

pub fn mul_op_signed_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "mul_op_signed",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_mul_op_signed,
    }
}

pub fn mul_op_unsigned_only_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "mul_op_unsigned_only",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_mul_op_unsigned_only,
    }
}

pub fn divrem_op_signed_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "divrem_op_signed",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_divrem_op_signed,
    }
}

pub fn divrem_op_unsigned_only_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "divrem_op_unsigned_only",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_divrem_op_unsigned_only,
    }
}

pub fn csrrw_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "csrrw_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_csrrw_op,
    }
}

pub fn load_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "load_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_load_op,
    }
}

pub fn store_op_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "store_op",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_store_op,
    }
}

pub fn optimized_decoder_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "optimized_decoder",
        build_kind: CircuitBuildKind::PlainCircuit {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_optimized_decoder,
    }
}

pub fn bigint_with_control_delegation_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "bigint_with_control_delegation",
        build_kind: CircuitBuildKind::Delegation {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_bigint_with_control_delegation,
    }
}

pub fn blake2_with_extended_control_delegation_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "blake2_with_extended_control_delegation",
        build_kind: CircuitBuildKind::Delegation {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_blake2_with_extended_control_delegation,
    }
}

pub fn keccak_special5_delegation_recipe() -> CircuitRecipe {
    CircuitRecipe {
        name: "keccak_special5_delegation",
        build_kind: CircuitBuildKind::Delegation {
            trace_len_log2: DEFAULT_TRACE_LEN_LOG2,
        },
        build: build_keccak_special5_delegation,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn standalone_arithmetic_recipe_uses_plain_build_kind() {
        let recipe = add_op_recipe();
        assert_eq!(recipe.name, "add_op");
        assert!(matches!(
            recipe.build_kind,
            CircuitBuildKind::PlainCircuit {
                trace_len_log2: DEFAULT_TRACE_LEN_LOG2
            }
        ));
    }

    #[test]
    fn delegation_recipe_uses_delegation_build_kind() {
        let recipe = bigint_with_control_delegation_recipe();
        assert_eq!(recipe.name, "bigint_with_control_delegation");
        assert!(matches!(
            recipe.build_kind,
            CircuitBuildKind::Delegation {
                trace_len_log2: DEFAULT_TRACE_LEN_LOG2
            }
        ));
    }

    #[test]
    fn add_op_boundary_spec_exposes_expected_inputs_and_outputs() {
        let mut cs = BasicAssembly::<Mersenne31Field>::new();
        let boundary_spec = add_sub_harness(&mut cs, false);

        assert_eq!(boundary_spec.inputs.len(), 2);
        assert_eq!(boundary_spec.outputs.len(), 2);
        assert!(boundary_spec.proof_system_signal_vars.len() >= 8);
        assert!(!boundary_spec.include_shuffle_ram_io);
    }

    #[test]
    fn load_op_boundary_spec_includes_shuffle_ram_io() {
        let mut cs = BasicAssembly::<Mersenne31Field>::new();
        let rs1_index = cs.add_variable();
        let rs2_index = cs.add_variable();
        let pc = Register::new(&mut cs);
        let imm = Register::new(&mut cs);
        let funct3 = cs.add_variable();
        let rd_outputs = [cs.add_variable(), cs.add_variable()];
        let next_pc_outputs = [cs.add_variable(), cs.add_variable()];
        let boundary_spec = load_boundary_spec(
            rs1_index,
            rs2_index,
            pc,
            imm,
            funct3,
            rd_outputs,
            next_pc_outputs,
        );

        assert!(boundary_spec.include_shuffle_ram_io);
        assert_eq!(boundary_spec.inputs.len(), 5);
        assert_eq!(boundary_spec.outputs.len(), 2);
    }
}
