#![allow(type_alias_bounds)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(iter_advance_by)]
#![feature(option_zip)]
#![feature(allocator_api)]

use cs::constraint::Constraint;
use cs::constraint::Term;
use cs::cs::circuit::Circuit;
use cs::cs::circuit::CircuitOutput;
use cs::cs::circuit::LookupQuery;
use cs::cs::circuit::LookupQueryTableType;
use cs::cs::circuit::PicusExpr as CircuitPicusExpr;
use cs::cs::circuit::PicusStructuredConstraint as CircuitPicusStructuredConstraint;
use cs::cs::circuit::ShuffleRamMemQuery;
use cs::cs::cs_reference::BasicAssembly;
use cs::cs::witness_placer::graph_description::RawExpression;
use cs::cs::witness_placer::graph_description::WitnessGraphCreator;
use cs::definitions::OpcodeFamilyCircuitState;
use cs::definitions::TableType;
use cs::definitions::Variable;
use cs::definitions::ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS;
use cs::definitions::JUMP_SLT_BRANCH_FAMILY_NUM_BITS;
use cs::definitions::MEMORY_FAMILY_NUM_FLAGS;
use cs::definitions::MUL_DIV_FAMILY_NUM_FLAGS;
use cs::definitions::REDUCED_MACHINE_NUM_FLAGS;
use cs::definitions::SHIFT_BINARY_CSRRW_FAMILY_NUM_FLAGS;
use cs::definitions::SUBWORD_ONLY_MEMORY_FAMILY_NUM_FLAGS;
use cs::delegation::bigint_with_control::define_u256_ops_extended_control_delegation_circuit_with_metadata;
use cs::delegation::bigint_with_control::BigintDelegationPicusMetadata;
use cs::delegation::blake2_round_with_extended_control::define_blake2_with_extended_control_delegation_circuit_with_metadata;
use cs::delegation::blake2_round_with_extended_control::Blake2WithExtendedControlDelegationPicusMetadata;
use cs::devices::diffs::CommonDiffs;
use cs::devices::diffs::NextPcValue;
use cs::devices::optimization_context::OptimizationContext;
use cs::devices::risc_v_types::InstructionType;
use cs::machine::decoder::decode_optimized_must_handle_csr::OptimizedDecoder;
use cs::machine::decoder::DecoderInput;
use cs::machine::instruction_decoding_data::DecoderInstructionVariantsKey;
use cs::machine::instruction_decoding_data::DecoderMajorInstructionFamilyKey;
use cs::machine::machine_configurations::create_csr_table_for_delegation;
use cs::machine::machine_configurations::full_isa_no_exceptions::FullIsaMachineNoExceptionHandling;
use cs::machine::machine_configurations::minimal_no_exceptions_with_delegation::MinimalMachineNoExceptionHandlingWithDelegation;
use cs::machine::machine_configurations::minimal_state::MinimalStateRegistersInMemory;
use cs::machine::machine_configurations::BasicDecodingResultWithSigns;
use cs::machine::ops::add_sub::AddOp;
use cs::machine::ops::add_sub::SubOp;
use cs::machine::ops::add_sub::ADD_OP_KEY;
use cs::machine::ops::add_sub::SUB_OP_KEY;
use cs::machine::ops::binops::BinaryOp;
use cs::machine::ops::binops::BINOP_COMMON_OP_KEY;
use cs::machine::ops::conditional::ConditionalOp;
use cs::machine::ops::conditional::CONDITIONAL_COMMON_OP_KEY;
use cs::machine::ops::csr::CSR_COMMON_OP_KEY;
use cs::machine::ops::jump::JumpOp;
use cs::machine::ops::jump::JAL_OP_KEY;
use cs::machine::ops::jump::JUMP_COMMON_OP_KEY;
use cs::machine::ops::lui_auipc::AuiPc;
use cs::machine::ops::lui_auipc::LuiOp;
use cs::machine::ops::lui_auipc::AUIPC_OP_KEY;
use cs::machine::ops::lui_auipc::LUI_OP_KEY;
use cs::machine::ops::mop::MopOp;
use cs::machine::ops::mop::ADDMOD_OP_KEY;
use cs::machine::ops::mop::MOP_OP_KEY;
use cs::machine::ops::mop::MULMOD_OP_KEY;
use cs::machine::ops::mop::SUBMOD_OP_KEY;
use cs::machine::ops::mul_div::DivRemOp;
use cs::machine::ops::mul_div::MulOp;
use cs::machine::ops::mul_div::DIVREM_COMMON_OP_KEY;
use cs::machine::ops::mul_div::DIVU_OP_KEY;
use cs::machine::ops::mul_div::DIV_OP_KEY;
use cs::machine::ops::mul_div::MULHSU_OP_KEY;
use cs::machine::ops::mul_div::MULH_OP_KEY;
use cs::machine::ops::mul_div::MUL_COMMON_OP_KEY;
use cs::machine::ops::mul_div::MUL_OP_KEY;
use cs::machine::ops::mul_div::REM_OP_KEY;
use cs::machine::ops::shift::ShiftOp;
use cs::machine::ops::shift::SHIFT_COMMON_OP_KEY;
use cs::machine::ops::shift::SHIFT_RIGHT_ALGEBRAIC_KEY;
use cs::machine::ops::shift::SHIFT_RIGHT_KEY;
use cs::machine::ops::unrolled::add_sub_lui_auipc_mop::add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode;
use cs::machine::ops::unrolled::add_sub_lui_auipc_mop::add_sub_lui_auipc_mop_table_addition_fn;
use cs::machine::ops::unrolled::decoder::describe_decoder_cycle_from_opcode_with_metadata;
use cs::machine::ops::unrolled::decoder::UnrolledDecoderPicusMetadata;
use cs::machine::ops::unrolled::jump_branch_slt::jump_branch_slt_circuit_with_preprocessed_bytecode;
use cs::machine::ops::unrolled::jump_branch_slt::jump_branch_slt_table_addition_fn;
use cs::machine::ops::unrolled::load_store::create_load_store_special_tables;
use cs::machine::ops::unrolled::load_store::load_store_circuit_with_preprocessed_bytecode;
use cs::machine::ops::unrolled::load_store::load_store_table_addition_fn;
use cs::machine::ops::unrolled::load_store_subword_only::subword_only_load_store_circuit_with_preprocessed_bytecode;
use cs::machine::ops::unrolled::load_store_subword_only::subword_only_load_store_table_addition_fn;
#[cfg(test)]
use cs::machine::ops::unrolled::load_store_word_only::create_word_only_load_store_special_tables;
#[cfg(test)]
use cs::machine::ops::unrolled::load_store_word_only::word_only_load_store_circuit_with_preprocessed_bytecode;
#[cfg(test)]
use cs::machine::ops::unrolled::load_store_word_only::word_only_load_store_table_addition_fn;
use cs::machine::ops::unrolled::mul_div::mul_div_circuit_with_preprocessed_bytecode;
use cs::machine::ops::unrolled::mul_div::mul_div_table_addition_fn;
use cs::machine::ops::unrolled::reduced_machine_ops::create_reduced_machine_special_tables;
use cs::machine::ops::unrolled::reduced_machine_ops::reduced_machine_circuit_with_preprocessed_bytecode;
use cs::machine::ops::unrolled::reduced_machine_ops::reduced_machine_table_addition_fn;
use cs::machine::ops::unrolled::shift_binary_csr::shift_binop_csrrw_circuit_with_preprocessed_bytecode;
use cs::machine::ops::unrolled::shift_binary_csr::shift_binop_csrrw_table_addition_fn;
use cs::machine::ops::RS1_LOAD_LOCAL_TIMESTAMP;
use cs::machine::ops::RS2_LOAD_LOCAL_TIMESTAMP;
use cs::machine::IndexableBooleanSet;
use cs::machine::Machine;
use cs::machine::MachineOp;
use cs::tables::LookupWrapper;
use cs::types::Boolean;
use cs::types::Num;
use cs::types::Register;
use field::Mersenne31Field;
use field::PrimeField;
use picus::PicusConstraint;
use picus::PicusExpr;
use picus::PicusModule;
use picus::PicusProgram;
use std::collections::BTreeMap;

mod lookups;
use lookups::add_disjunctive_lookup_constraints;
use lookups::add_lookup_constraints;

const U16_BOUND: u64 = 1 << 16;

#[derive(Clone, Debug)]
struct SpecializationCase {
    name_suffix: Option<String>,
    assignments: BTreeMap<usize, u64>,
}

#[derive(Clone, Debug)]
pub struct DecoderSpecialization {
    cases: Vec<SpecializationCase>,
}

impl DecoderSpecialization {
    fn from_named_assignments(cases: Vec<(String, BTreeMap<usize, u64>)>) -> Self {
        Self {
            cases: cases
                .into_iter()
                .map(|(name_suffix, assignments)| SpecializationCase {
                    name_suffix: Some(sanitize_module_label(&name_suffix)),
                    assignments,
                })
                .collect(),
        }
    }
}

fn sanitize_module_label(raw: &str) -> String {
    let mut sanitized = String::with_capacity(raw.len());
    let mut last_was_underscore = false;

    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() {
            sanitized.push(ch.to_ascii_lowercase());
            last_was_underscore = false;
        } else if !last_was_underscore {
            sanitized.push('_');
            last_was_underscore = true;
        }
    }

    let sanitized = sanitized.trim_matches('_');
    if sanitized.is_empty() {
        "case".to_string()
    } else {
        sanitized.to_string()
    }
}

#[cfg(test)]
fn specialization_for_single_bit_named(
    bit_var_id: usize,
    false_name: &str,
    true_name: &str,
) -> DecoderSpecialization {
    let mut cases = Vec::with_capacity(2);
    for (value, name) in [(0u64, false_name), (1u64, true_name)] {
        let mut env = BTreeMap::new();
        env.insert(bit_var_id, value);
        cases.push((name.to_string(), env));
    }

    DecoderSpecialization::from_named_assignments(cases)
}

fn specialization_for_flat_one_hot_named(
    decoded_bits: &[usize],
    labels: &[&str],
) -> DecoderSpecialization {
    assert_eq!(
        decoded_bits.len(),
        labels.len(),
        "one-hot specialization labels must match decoded bit count"
    );

    let mut cases = Vec::with_capacity(decoded_bits.len());
    for (active_bit, label) in labels.iter().enumerate() {
        let mut env = BTreeMap::new();
        for (idx, bit_var_id) in decoded_bits.iter().copied().enumerate() {
            let value = if idx == active_bit { 1 } else { 0 };
            env.insert(bit_var_id, value);
        }
        cases.push(((*label).to_string(), env));
    }

    DecoderSpecialization::from_named_assignments(cases)
}

fn specialization_for_mul_div_signed(decoded_bits: &[usize]) -> DecoderSpecialization {
    let [is_division, div_vs_divu, rs1_signed, rs2_signed] = decoded_bits else {
        panic!("signed mul/div specialization expects exactly four decoded bits");
    };
    let bit_ids = [*is_division, *div_vs_divu, *rs1_signed, *rs2_signed];
    // Mul/div is not flat one-hot: the bits encode a small decision tree, so we
    // specialize over the real instruction environments instead of per-bit cases.
    let cases = [
        [1, 1, 1, 1], // DIV
        [1, 1, 0, 0], // DIVU
        [1, 0, 1, 1], // REM
        [1, 0, 0, 0], // REMU
        [0, 1, 1, 1], // MUL
        [0, 0, 1, 1], // MULH
        [0, 0, 1, 0], // MULHSU
        [0, 0, 0, 0], // MULHU
    ];
    let labels = [
        "div", "divu", "rem", "remu", "mul", "mulh", "mulhsu", "mulhu",
    ];

    DecoderSpecialization::from_named_assignments(
        labels
            .into_iter()
            .zip(cases)
            .map(|(label, values)| (label.to_string(), bit_ids.into_iter().zip(values).collect()))
            .collect(),
    )
}

fn specialization_for_mul_div_unsigned_only(decoded_bits: &[usize]) -> DecoderSpecialization {
    let [is_division, mul_vs_divu, ..] = decoded_bits else {
        panic!("unsigned-only mul/div specialization expects mul/div family bits");
    };
    let bit_ids = [*is_division, *mul_vs_divu];
    let cases = [
        [0, 0], // MULHU
        [0, 1], // MUL
        [1, 0], // REMU
        [1, 1], // DIVU
    ];
    let labels = ["mulhu", "mul", "remu", "divu"];

    DecoderSpecialization::from_named_assignments(
        labels
            .into_iter()
            .zip(cases)
            .map(|(label, values)| (label.to_string(), bit_ids.into_iter().zip(values).collect()))
            .collect(),
    )
}

fn specialization_for_mul_div<const SUPPORT_SIGNED: bool>(
    decoded_bits: &[usize],
) -> DecoderSpecialization {
    if SUPPORT_SIGNED {
        specialization_for_mul_div_signed(decoded_bits)
    } else {
        specialization_for_mul_div_unsigned_only(decoded_bits)
    }
}

fn specialization_for_shift_binop_csrrw(
    decoded_bits: &[usize],
    funct3_var_id: usize,
) -> DecoderSpecialization {
    let [sll, srl, sra, binary_op, csrrw, use_imm] = decoded_bits else {
        panic!("shift/binop/csrrw specialization expects exactly six decoded bits");
    };
    let bit_ids = [*sll, *srl, *sra, *binary_op, *csrrw, *use_imm];
    // This family is not flat one-hot because `use_imm` refines the top-level
    // operation bit. The binary-op path also depends on funct3, so the harness
    // must specialize to decoder-consistent funct3 values instead of leaving it
    // unconstrained.
    let mk_env = |values: [u64; 6], funct3: u64| {
        let mut env: BTreeMap<usize, u64> = bit_ids.into_iter().zip(values).collect();
        env.insert(funct3_var_id, funct3);
        env
    };

    DecoderSpecialization::from_named_assignments(vec![
        ("sll".to_string(), mk_env([1, 0, 0, 0, 0, 0], 0b001)),
        ("srl".to_string(), mk_env([0, 1, 0, 0, 0, 0], 0b101)),
        ("sra".to_string(), mk_env([0, 0, 1, 0, 0, 0], 0b101)),
        ("xor".to_string(), mk_env([0, 0, 0, 1, 0, 0], 0b100)),
        ("or".to_string(), mk_env([0, 0, 0, 1, 0, 0], 0b110)),
        ("and".to_string(), mk_env([0, 0, 0, 1, 0, 0], 0b111)),
        ("csrrw".to_string(), mk_env([0, 0, 0, 0, 1, 0], 0b001)),
        ("slli".to_string(), mk_env([1, 0, 0, 0, 0, 1], 0b001)),
        ("srli".to_string(), mk_env([0, 1, 0, 0, 0, 1], 0b101)),
        ("srai".to_string(), mk_env([0, 0, 1, 0, 0, 1], 0b101)),
        ("xori".to_string(), mk_env([0, 0, 0, 1, 0, 1], 0b100)),
        ("ori".to_string(), mk_env([0, 0, 0, 1, 0, 1], 0b110)),
        ("andi".to_string(), mk_env([0, 0, 0, 1, 0, 1], 0b111)),
    ])
}

fn specialization_from_named_bitmasks(
    decoded_bits: &[usize],
    named_masks: impl IntoIterator<Item = (String, u32)>,
) -> DecoderSpecialization {
    let cases = named_masks
        .into_iter()
        .map(|(label, mask)| {
            let assignments = decoded_bits
                .iter()
                .copied()
                .enumerate()
                .map(|(idx, bit_var_id)| {
                    let value = ((mask >> idx) & 1) as u64;
                    (bit_var_id, value)
                })
                .collect();
            (label, assignments)
        })
        .collect();

    DecoderSpecialization::from_named_assignments(cases)
}

fn specialization_with_fixed_assignment(
    specialization: DecoderSpecialization,
    var_id: usize,
    value: u64,
) -> DecoderSpecialization {
    let cases = specialization
        .cases
        .into_iter()
        .map(|mut case| {
            case.assignments.insert(var_id, value);
            case
        })
        .collect();

    DecoderSpecialization { cases }
}

fn reduced_machine_instruction_type_label(instr_type: InstructionType) -> &'static str {
    match instr_type {
        InstructionType::RType => "rtype",
        InstructionType::IType => "itype",
        InstructionType::SType => "stype",
        InstructionType::BType => "btype",
        InstructionType::UType => "utype",
        InstructionType::JType => "jtype",
    }
}

fn reduced_machine_case_label(
    instruction_type: InstructionType,
    major_key: DecoderMajorInstructionFamilyKey,
    minor_keys: &[DecoderInstructionVariantsKey],
) -> String {
    let mut parts = vec![
        reduced_machine_instruction_type_label(instruction_type).to_string(),
        sanitize_module_label(major_key.0),
    ];
    parts.extend(minor_keys.iter().map(|key| sanitize_module_label(key.0)));
    parts.join("_")
}

fn named_reduced_machine_masks() -> Vec<(String, u32)> {
    use cs::machine::Machine;

    let all_keys =
        <MinimalMachineNoExceptionHandlingWithDelegation as Machine<Mersenne31Field>>::all_decoder_keys();
    let all_opcodes = <MinimalMachineNoExceptionHandlingWithDelegation as Machine<
        Mersenne31Field,
    >>::all_supported_opcodes();

    let major_key_offset = 3usize;
    let minor_key_offset = major_key_offset + all_keys.num_major_keys();
    let csr_major_bit = 1u32 << (major_key_offset + all_keys.get_major_index(&CSR_COMMON_OP_KEY));
    let mut named_masks = BTreeMap::new();

    for opcode in 0u8..=0x7f {
        for funct3 in 0u8..=0x7 {
            for funct7 in 0u8..=0x7f {
                for supported_opcode in all_opcodes.iter() {
                    if let Ok((instruction_type, major_key, minor_keys)) =
                        supported_opcode.define_decoder_subspace(opcode, funct3, funct7)
                    {
                        let mut mask = 0u32;
                        match instruction_type {
                            InstructionType::RType
                            | InstructionType::IType
                            | InstructionType::JType
                            | InstructionType::UType => mask |= 1 << 0,
                            InstructionType::SType | InstructionType::BType => {}
                        }
                        match instruction_type {
                            InstructionType::RType
                            | InstructionType::SType
                            | InstructionType::BType => mask |= 1 << 1,
                            InstructionType::IType
                            | InstructionType::UType
                            | InstructionType::JType => {}
                        }
                        if instruction_type == InstructionType::BType {
                            mask |= 1 << 2;
                        }

                        let major_index = all_keys.get_major_index(&major_key);
                        mask |= 1u32 << (major_key_offset + major_index);
                        for minor in minor_keys.iter() {
                            let (_, minor_index) = all_keys.get_index_set(&major_key, minor);
                            mask |= 1u32 << (minor_key_offset + minor_index);
                        }

                        if (mask & csr_major_bit) == 0 {
                            let label =
                                reduced_machine_case_label(instruction_type, major_key, minor_keys);
                            if let Some(existing) = named_masks.get(&mask) {
                                assert_eq!(
                                    existing, &label,
                                    "same reduced-machine mask maps to multiple labels"
                                );
                            } else {
                                named_masks.insert(mask, label);
                            }
                        }
                        break;
                    }
                }
            }
        }
    }

    named_masks
        .into_iter()
        .map(|(mask, label)| (label, mask))
        .collect()
}

#[cfg(test)]
fn valid_reduced_machine_masks() -> Vec<u32> {
    named_reduced_machine_masks()
        .into_iter()
        .map(|(_, mask)| mask)
        .collect()
}

fn executor_machine_state<F: PrimeField>(
    circuit_output: &CircuitOutput<F>,
) -> OpcodeFamilyCircuitState<F> {
    *circuit_output
        .executor_machine_state
        .as_ref()
        .expect("executor machine state must be present in executor circuit")
}

fn power_of_two_bit_index(value: u64) -> Option<usize> {
    if value != 0 && value.is_power_of_two() {
        Some(value.trailing_zeros() as usize)
    } else {
        None
    }
}

fn recover_split_bitmask_variables<F: PrimeField>(
    circuit_output: &CircuitOutput<F>,
    full_bitmask_var: Variable,
    width: usize,
) -> Vec<usize> {
    let negative_one = F::CHARACTERISTICS - 1;
    let mut recovered = None;

    for (constraint, _) in &circuit_output.constraints {
        let mut constraint = constraint.clone();
        constraint.normalize();

        if constraint.degree() != 1 || constraint.terms.len() != width + 1 {
            continue;
        }

        let mut bits = vec![None; width];
        let mut saw_full_bitmask = false;
        let mut valid = true;

        for term in &constraint.terms {
            let Term::Expression {
                coeff,
                inner,
                degree,
            } = *term
            else {
                valid = false;
                break;
            };

            if degree != 1 {
                valid = false;
                break;
            }

            let variable = inner[0];
            let coeff = coeff.as_u64_reduced();
            if variable == full_bitmask_var {
                if saw_full_bitmask || coeff != negative_one {
                    valid = false;
                    break;
                }
                saw_full_bitmask = true;
            } else if let Some(bit_idx) = power_of_two_bit_index(coeff) {
                if bit_idx >= width || bits[bit_idx].is_some() {
                    valid = false;
                    break;
                }
                bits[bit_idx] = Some(variable.0 as usize);
            } else {
                valid = false;
                break;
            }
        }

        if valid && saw_full_bitmask && bits.iter().all(Option::is_some) {
            let bits: Vec<_> = bits.into_iter().map(Option::unwrap).collect();
            if let Some(existing) = &recovered {
                assert_eq!(
                    existing, &bits,
                    "found multiple inconsistent bitmask decompositions for variable {:?}",
                    full_bitmask_var
                );
            }
            recovered = Some(bits);
        }
    }

    recovered.unwrap_or_else(|| {
        panic!(
            "failed to recover {}-bit decomposition for variable {:?}",
            width, full_bitmask_var
        )
    })
}

fn recover_direct_mask_variable(circuit_output: &CircuitOutput<Mersenne31Field>) -> usize {
    executor_machine_state(circuit_output)
        .decoder_data
        .circuit_family_extra_mask
        .0 as usize
}

fn variable_to_picus_expr(var: Variable) -> PicusExpr {
    PicusExpr::Var(var.0 as usize)
}

fn boolean_to_picus_expr(value: Boolean) -> PicusExpr {
    match value {
        Boolean::Is(var) => variable_to_picus_expr(var),
        Boolean::Not(var) => PicusExpr::Const(1) - variable_to_picus_expr(var),
        Boolean::Constant(value) => PicusExpr::Const(value as u64),
    }
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

struct StandaloneHarness {
    circuit_output: CircuitOutput<Mersenne31Field>,
    extra_inputs: Vec<PicusExpr>,
    extra_outputs: Vec<PicusExpr>,
}

fn fixed_boolean<CS: Circuit<Mersenne31Field>>(cs: &mut CS, value: bool) -> Boolean {
    let var = cs.add_boolean_variable();
    let var_id = var.get_variable().unwrap();
    let expected = if value { 1u64 } else { 0u64 };
    cs.add_constraint_allow_explicit_linear(Constraint::from(var_id) - Term::from(expected));
    cs.add_picus_parallel_constraint(CircuitPicusStructuredConstraint::Eq {
        lhs: CircuitPicusExpr::Variable(var_id),
        rhs: CircuitPicusExpr::Constant(Mersenne31Field::from_u64_unchecked(expected)),
    });

    var
}

fn fixed_num<CS: Circuit<Mersenne31Field>>(cs: &mut CS, value: u64) -> Num<Mersenne31Field> {
    let var = cs.add_variable();
    cs.add_constraint_allow_explicit_linear(Constraint::from(var) - Term::from(value));
    cs.add_picus_parallel_constraint(CircuitPicusStructuredConstraint::Eq {
        lhs: CircuitPicusExpr::Variable(var),
        rhs: CircuitPicusExpr::Constant(Mersenne31Field::from_u64_unchecked(value)),
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
        Constraint::from(reg.0[0].get_variable()) - Term::from(low),
    );
    cs.add_constraint_allow_explicit_linear(
        Constraint::from(reg.0[1].get_variable()) - Term::from(high),
    );
    cs.add_picus_parallel_constraint(CircuitPicusStructuredConstraint::Eq {
        lhs: CircuitPicusExpr::Variable(reg.0[0].get_variable()),
        rhs: CircuitPicusExpr::Constant(Mersenne31Field::from_u64_unchecked(low)),
    });
    cs.add_picus_parallel_constraint(CircuitPicusStructuredConstraint::Eq {
        lhs: CircuitPicusExpr::Variable(reg.0[1].get_variable()),
        rhs: CircuitPicusExpr::Constant(Mersenne31Field::from_u64_unchecked(high)),
    });
    reg
}

fn register_as_inputs(reg: Register<Mersenne31Field>) -> Vec<PicusExpr> {
    reg.0
        .into_iter()
        .map(|el| variable_to_picus_expr(el.get_variable()))
        .collect()
}

fn word_pairs_to_picus_exprs(words: &[[Variable; 2]]) -> Vec<PicusExpr> {
    words
        .iter()
        .flat_map(|word| word.iter().copied().map(variable_to_picus_expr))
        .collect()
}

fn materialize_rd_outputs<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    diffs: CommonDiffs<Mersenne31Field>,
) -> [Variable; 2] {
    assert_eq!(
        diffs.rd_value.len(),
        1,
        "standalone op harness must produce exactly one RD value"
    );
    let (rd_value, _flag) = diffs.rd_value.into_iter().next().unwrap();

    rd_value.map(|constraint| materialize_constraint_output(cs, constraint))
}

fn materialize_constraint_output<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    mut constraint: Constraint<Mersenne31Field>,
) -> Variable {
    constraint.normalize();
    let var = cs.add_variable();
    if constraint.is_empty() {
        cs.add_constraint_allow_explicit_linear(Constraint::from(var));
        cs.add_picus_parallel_constraint(CircuitPicusStructuredConstraint::Eq {
            lhs: CircuitPicusExpr::Variable(var),
            rhs: CircuitPicusExpr::Constant(Mersenne31Field::from_u64_unchecked(0)),
        });
    } else if constraint.terms.iter().all(|term| term.is_constant()) {
        let value = constraint.as_constant().as_u64_reduced();
        cs.add_constraint_allow_explicit_linear(Constraint::from(var) - Term::from(value));
        cs.add_picus_parallel_constraint(CircuitPicusStructuredConstraint::Eq {
            lhs: CircuitPicusExpr::Variable(var),
            rhs: CircuitPicusExpr::Constant(Mersenne31Field::from_u64_unchecked(value)),
        });
    } else {
        let parallel_constraint = constraint.clone();
        cs.add_constraint_allow_explicit_linear(Constraint::from(var) - constraint);
        cs.add_picus_parallel_constraint(CircuitPicusStructuredConstraint::Eq {
            lhs: CircuitPicusExpr::Variable(var),
            rhs: cs::cs::circuit::picus_expr_from_constraint(&parallel_constraint),
        });
    }

    var
}

fn materialize_register_outputs<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    reg: Register<Mersenne31Field>,
) -> [Variable; 2] {
    reg.0.map(|word| match word {
        Num::Var(var) => var,
        Num::Constant(value) => {
            materialize_constraint_output(cs, Constraint::from(value.as_u64_reduced()))
        }
    })
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
            let trapped_var = materialize_constraint_output(cs, Constraint::from(*trapped));
            let trap_reason_var = match trap_reason {
                Num::Var(var) => *var,
                Num::Constant(value) => {
                    materialize_constraint_output(cs, Constraint::from(value.as_u64_reduced()))
                }
            };
            Some([trapped_var, trap_reason_var])
        }
        (None, None) => None,
        _ => panic!("trap outputs must be either fully present or absent"),
    }
}

fn build_standalone_program(harness_name: &str, harness: StandaloneHarness) -> PicusProgram {
    let module = build_picus_module_from_circuit_output(
        harness_name,
        &harness.circuit_output,
        None,
        &harness.extra_inputs,
        &harness.extra_outputs,
        &[],
    );

    let mut modules = BTreeMap::new();
    modules.insert(module.name.clone(), module);
    let mut program = PicusProgram::new(Mersenne31Field::CHARACTERISTICS);
    program.add_modules(&mut modules);
    program
}

fn build_binary_like_decoder_output<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    rs1: Register<Mersenne31Field>,
    rs2: Register<Mersenne31Field>,
    imm: Register<Mersenne31Field>,
    funct3: Num<Mersenne31Field>,
) -> BasicDecodingResultWithSigns<Mersenne31Field> {
    BasicDecodingResultWithSigns {
        pc_next: Register::new_from_constant(0),
        src1: cs::types::RegisterDecompositionWithSign::parse_reg(cs, rs1),
        src2: cs::types::RegisterDecompositionWithSign::parse_reg(cs, rs2),
        imm,
        rs2_index: Constraint::from(0u64),
        funct3,
        funct12: Constraint::from(0u64),
    }
}

fn build_add_sub_harness(is_sub: bool) -> StandaloneHarness {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    let false_flag = fixed_boolean(&mut cs, false);
    let true_flag = fixed_boolean(&mut cs, true);
    let rs1 = Register::new(&mut cs);
    let rs2 = Register::new(&mut cs);
    let zero_reg = fixed_register(&mut cs, 0);
    let zero_funct3 = fixed_num(&mut cs, 0);
    let decoder_output = build_binary_like_decoder_output(&mut cs, rs1, rs2, zero_reg, zero_funct3);
    let initial_state = MinimalStateRegistersInMemory {
        pc: fixed_register(&mut cs, 0),
    };
    let flags = if is_sub {
        ExplicitFlagSource::new(false_flag).with_major(SUB_OP_KEY, true_flag)
    } else {
        ExplicitFlagSource::new(false_flag).with_major(ADD_OP_KEY, true_flag)
    };
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = if is_sub {
        SubOp::apply::<_, true, false>(
            &mut cs,
            &initial_state,
            &decoder_output,
            &flags,
            &mut opt_ctx,
        )
    } else {
        AddOp::apply::<_, true, false>(
            &mut cs,
            &initial_state,
            &decoder_output,
            &flags,
            &mut opt_ctx,
        )
    };
    let rd_outputs = materialize_rd_outputs(&mut cs, diffs.clone());
    let default_pc = fixed_register(&mut cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(&mut cs, &diffs, default_pc);
    opt_ctx.enforce_all(&mut cs);
    let (circuit_output, _) = cs.finalize();

    StandaloneHarness {
        circuit_output,
        extra_inputs: [register_as_inputs(rs1), register_as_inputs(rs2)].concat(),
        extra_outputs: rd_outputs
            .into_iter()
            .chain(next_pc_outputs)
            .map(variable_to_picus_expr)
            .collect(),
    }
}

fn build_lui_harness() -> StandaloneHarness {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    let false_flag = fixed_boolean(&mut cs, false);
    let true_flag = fixed_boolean(&mut cs, true);
    let imm = Register::new(&mut cs);
    let zero = fixed_register(&mut cs, 0);
    let zero_reg = fixed_register(&mut cs, 0);
    let zero_funct3 = fixed_num(&mut cs, 0);
    let decoder_output =
        build_binary_like_decoder_output(&mut cs, zero, zero_reg, imm, zero_funct3);
    let initial_state = MinimalStateRegistersInMemory {
        pc: fixed_register(&mut cs, 0),
    };
    let flags = ExplicitFlagSource::new(false_flag).with_major(LUI_OP_KEY, true_flag);
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = LuiOp::apply::<_, true, false>(
        &mut cs,
        &initial_state,
        &decoder_output,
        &flags,
        &mut opt_ctx,
    );
    let rd_outputs = materialize_rd_outputs(&mut cs, diffs.clone());
    let default_pc = fixed_register(&mut cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(&mut cs, &diffs, default_pc);
    opt_ctx.enforce_all(&mut cs);
    let (circuit_output, _) = cs.finalize();

    StandaloneHarness {
        circuit_output,
        extra_inputs: register_as_inputs(imm),
        extra_outputs: rd_outputs
            .into_iter()
            .chain(next_pc_outputs)
            .map(variable_to_picus_expr)
            .collect(),
    }
}

fn build_auipc_harness() -> StandaloneHarness {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    let false_flag = fixed_boolean(&mut cs, false);
    let true_flag = fixed_boolean(&mut cs, true);
    let pc = Register::new(&mut cs);
    let imm = Register::new(&mut cs);
    let zero = fixed_register(&mut cs, 0);
    let zero_reg = fixed_register(&mut cs, 0);
    let zero_funct3 = fixed_num(&mut cs, 0);
    let decoder_output =
        build_binary_like_decoder_output(&mut cs, zero, zero_reg, imm, zero_funct3);
    let initial_state = MinimalStateRegistersInMemory { pc };
    let pc_next = cs::machine::utils::calculate_pc_next_no_overflows(&mut cs, pc);
    let flags = ExplicitFlagSource::new(false_flag).with_major(AUIPC_OP_KEY, true_flag);
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = AuiPc::apply::<_, true, false>(
        &mut cs,
        &initial_state,
        &decoder_output,
        &flags,
        &mut opt_ctx,
    );
    let rd_outputs = materialize_rd_outputs(&mut cs, diffs.clone());
    let next_pc_outputs = materialize_next_pc_outputs(&mut cs, &diffs, pc_next);
    opt_ctx.enforce_all(&mut cs);
    let (circuit_output, _) = cs.finalize();

    StandaloneHarness {
        circuit_output,
        extra_inputs: [register_as_inputs(pc), register_as_inputs(imm)].concat(),
        extra_outputs: rd_outputs
            .into_iter()
            .chain(next_pc_outputs)
            .map(variable_to_picus_expr)
            .collect(),
    }
}

fn build_binop_harness(variant: BinopVariant) -> StandaloneHarness {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    for table in [TableType::Xor, TableType::Or, TableType::And] {
        cs.materialize_table(table);
    }
    let false_flag = fixed_boolean(&mut cs, false);
    let true_flag = fixed_boolean(&mut cs, true);
    let rs1 = Register::new(&mut cs);
    let rs2 = Register::new(&mut cs);
    let funct3 = match variant {
        BinopVariant::Xor => fixed_num(&mut cs, 0b100),
        BinopVariant::Or => fixed_num(&mut cs, 0b110),
        BinopVariant::And => fixed_num(&mut cs, 0b111),
    };
    let zero_reg = fixed_register(&mut cs, 0);
    let decoder_output = build_binary_like_decoder_output(&mut cs, rs1, rs2, zero_reg, funct3);
    let initial_state = MinimalStateRegistersInMemory {
        pc: fixed_register(&mut cs, 0),
    };
    let flags = ExplicitFlagSource::new(false_flag).with_major(BINOP_COMMON_OP_KEY, true_flag);
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = BinaryOp::apply::<_, true, false>(
        &mut cs,
        &initial_state,
        &decoder_output,
        &flags,
        &mut opt_ctx,
    );
    let rd_outputs = materialize_rd_outputs(&mut cs, diffs.clone());
    let default_pc = fixed_register(&mut cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(&mut cs, &diffs, default_pc);
    opt_ctx.enforce_all(&mut cs);
    let (circuit_output, _) = cs.finalize();

    StandaloneHarness {
        circuit_output,
        extra_inputs: [register_as_inputs(rs1), register_as_inputs(rs2)].concat(),
        extra_outputs: rd_outputs
            .into_iter()
            .chain(next_pc_outputs)
            .map(variable_to_picus_expr)
            .collect(),
    }
}

fn build_shift_harness(variant: ShiftVariant) -> StandaloneHarness {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    for table in [
        TableType::ShiftImplementation,
        TableType::TruncateShiftAmount,
        TableType::SRASignFiller,
    ] {
        cs.materialize_table(table);
    }
    let false_flag = fixed_boolean(&mut cs, false);
    let shift_major_true = fixed_boolean(&mut cs, true);
    let rs1 = Register::new(&mut cs);
    let rs2 = Register::new(&mut cs);
    let zero_reg = fixed_register(&mut cs, 0);
    let zero_funct3 = fixed_num(&mut cs, 0);
    let flags = match variant {
        ShiftVariant::Sll => {
            ExplicitFlagSource::new(false_flag).with_major(SHIFT_COMMON_OP_KEY, shift_major_true)
        }
        ShiftVariant::Srl => ExplicitFlagSource::new(false_flag)
            .with_major(SHIFT_COMMON_OP_KEY, shift_major_true)
            .with_minor(
                SHIFT_COMMON_OP_KEY,
                SHIFT_RIGHT_KEY,
                fixed_boolean(&mut cs, true),
            ),
        ShiftVariant::Sra => ExplicitFlagSource::new(false_flag)
            .with_major(SHIFT_COMMON_OP_KEY, shift_major_true)
            .with_minor(
                SHIFT_COMMON_OP_KEY,
                SHIFT_RIGHT_KEY,
                fixed_boolean(&mut cs, true),
            )
            .with_minor(
                SHIFT_COMMON_OP_KEY,
                SHIFT_RIGHT_ALGEBRAIC_KEY,
                fixed_boolean(&mut cs, true),
            ),
    };
    let decoder_output = build_binary_like_decoder_output(&mut cs, rs1, rs2, zero_reg, zero_funct3);
    let initial_state = MinimalStateRegistersInMemory {
        pc: fixed_register(&mut cs, 0),
    };
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = ShiftOp::<true, false>::apply::<_, true, false>(
        &mut cs,
        &initial_state,
        &decoder_output,
        &flags,
        &mut opt_ctx,
    );
    let rd_outputs = materialize_rd_outputs(&mut cs, diffs.clone());
    let default_pc = fixed_register(&mut cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(&mut cs, &diffs, default_pc);
    opt_ctx.enforce_all(&mut cs);
    let (circuit_output, _) = cs.finalize();

    StandaloneHarness {
        circuit_output,
        extra_inputs: [register_as_inputs(rs1), register_as_inputs(rs2)].concat(),
        extra_outputs: rd_outputs
            .into_iter()
            .chain(next_pc_outputs)
            .map(variable_to_picus_expr)
            .collect(),
    }
}

fn build_mop_harness(variant: MopVariant) -> StandaloneHarness {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    cs.set_picus_parallel_constraints_enabled(true);
    let false_flag = fixed_boolean(&mut cs, false);
    let mop_major_true = fixed_boolean(&mut cs, true);
    let rs1 = Register::new(&mut cs);
    let rs2 = Register::new(&mut cs);
    let zero_reg = fixed_register(&mut cs, 0);
    let zero_funct3 = fixed_num(&mut cs, 0);
    let flags = match variant {
        MopVariant::AddMod => ExplicitFlagSource::new(false_flag)
            .with_major(MOP_OP_KEY, mop_major_true)
            .with_minor(MOP_OP_KEY, ADDMOD_OP_KEY, fixed_boolean(&mut cs, true)),
        MopVariant::SubMod => ExplicitFlagSource::new(false_flag)
            .with_major(MOP_OP_KEY, mop_major_true)
            .with_minor(MOP_OP_KEY, SUBMOD_OP_KEY, fixed_boolean(&mut cs, true)),
        MopVariant::MulMod => ExplicitFlagSource::new(false_flag)
            .with_major(MOP_OP_KEY, mop_major_true)
            .with_minor(MOP_OP_KEY, MULMOD_OP_KEY, fixed_boolean(&mut cs, true)),
    };
    let decoder_output = build_binary_like_decoder_output(&mut cs, rs1, rs2, zero_reg, zero_funct3);
    let initial_state = MinimalStateRegistersInMemory {
        pc: fixed_register(&mut cs, 0),
    };
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = MopOp::apply::<_, true, false>(
        &mut cs,
        &initial_state,
        &decoder_output,
        &flags,
        &mut opt_ctx,
    );
    let rd_outputs = materialize_rd_outputs(&mut cs, diffs.clone());
    let default_pc = fixed_register(&mut cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(&mut cs, &diffs, default_pc);
    opt_ctx.enforce_all(&mut cs);
    let (circuit_output, _) = cs.finalize();

    StandaloneHarness {
        circuit_output,
        extra_inputs: [register_as_inputs(rs1), register_as_inputs(rs2)].concat(),
        extra_outputs: rd_outputs
            .into_iter()
            .chain(next_pc_outputs)
            .map(variable_to_picus_expr)
            .collect(),
    }
}

fn build_conditional_harness() -> StandaloneHarness {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    cs.set_picus_parallel_constraints_enabled(true);
    for table in [
        TableType::JumpCleanupOffset,
        TableType::ConditionalOpAllConditionsResolver,
        TableType::U16GetSignAndHighByte,
    ] {
        cs.materialize_table(table);
    }

    let false_flag = fixed_boolean(&mut cs, false);
    let true_flag = fixed_boolean(&mut cs, true);
    let rs1 = Register::new(&mut cs);
    let rs2 = Register::new(&mut cs);
    let pc = Register::new(&mut cs);
    let imm = Register::new(&mut cs);
    let funct3 = Num::Var(cs.add_variable());
    let funct3_bit0 = cs.add_boolean_variable();
    let funct3_bit1 = cs.add_boolean_variable();
    let funct3_bit2 = cs.add_boolean_variable();
    let funct3_bit0_var = funct3_bit0.get_variable().unwrap();
    let funct3_bit1_var = funct3_bit1.get_variable().unwrap();
    let funct3_bit2_var = funct3_bit2.get_variable().unwrap();
    cs.add_constraint_allow_explicit_linear(
        Constraint::from(funct3.get_variable())
            - Term::from(funct3_bit0_var)
            - Term::from((Mersenne31Field::from_u64_unchecked(2), funct3_bit1_var))
            - Term::from((Mersenne31Field::from_u64_unchecked(4), funct3_bit2_var)),
    );
    cs.add_picus_parallel_constraint(CircuitPicusStructuredConstraint::Eq {
        lhs: CircuitPicusExpr::Variable(funct3.get_variable()),
        rhs: CircuitPicusExpr::Variable(funct3_bit0_var)
            + (CircuitPicusExpr::Constant(Mersenne31Field::from_u64_unchecked(2))
                * CircuitPicusExpr::Variable(funct3_bit1_var))
            + (CircuitPicusExpr::Constant(Mersenne31Field::from_u64_unchecked(4))
                * CircuitPicusExpr::Variable(funct3_bit2_var)),
    });
    let pc_next = cs::machine::utils::calculate_pc_next_no_overflows(&mut cs, pc);
    let decoder_output = BasicDecodingResultWithSigns {
        pc_next,
        src1: cs::types::RegisterDecompositionWithSign::parse_reg(&mut cs, rs1),
        src2: cs::types::RegisterDecompositionWithSign::parse_reg(&mut cs, rs2),
        imm,
        rs2_index: Constraint::from(0u64),
        funct3,
        funct12: Constraint::from(0u64),
    };
    let initial_state = MinimalStateRegistersInMemory { pc };
    let flags =
        ExplicitFlagSource::new(false_flag).with_major(CONDITIONAL_COMMON_OP_KEY, true_flag);
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = ConditionalOp::<true>::apply::<_, true, false>(
        &mut cs,
        &initial_state,
        &decoder_output,
        &flags,
        &mut opt_ctx,
    );
    let rd_outputs = materialize_rd_outputs(&mut cs, diffs.clone());
    let next_pc_outputs = materialize_next_pc_outputs(&mut cs, &diffs, pc_next);
    opt_ctx.enforce_all(&mut cs);
    let (circuit_output, _) = cs.finalize();

    let mut extra_inputs = [
        register_as_inputs(rs1),
        register_as_inputs(rs2),
        register_as_inputs(pc),
        register_as_inputs(imm),
    ]
    .concat();
    extra_inputs.push(variable_to_picus_expr(funct3.get_variable()));

    let extra_outputs = rd_outputs
        .into_iter()
        .chain(next_pc_outputs)
        .map(variable_to_picus_expr)
        .collect();

    StandaloneHarness {
        circuit_output,
        extra_inputs,
        extra_outputs,
    }
}

fn build_jump_harness<const ASSUME_TRUSTED_CODE: bool>() -> StandaloneHarness {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    cs.set_picus_parallel_constraints_enabled(true);
    cs.materialize_table(TableType::JumpCleanupOffset);

    let false_flag = fixed_boolean(&mut cs, false);
    let true_flag = fixed_boolean(&mut cs, true);
    let is_jal = cs.add_boolean_variable();
    let rs1 = Register::new(&mut cs);
    let pc = Register::new(&mut cs);
    let imm = Register::new(&mut cs);
    let zero_reg = fixed_register(&mut cs, 0);
    let zero_funct3 = fixed_num(&mut cs, 0);
    let pc_next = cs::machine::utils::calculate_pc_next_no_overflows(&mut cs, pc);
    let decoder_output = BasicDecodingResultWithSigns {
        pc_next,
        src1: cs::types::RegisterDecompositionWithSign::parse_reg(&mut cs, rs1),
        src2: cs::types::RegisterDecompositionWithSign::parse_reg(&mut cs, zero_reg),
        imm,
        rs2_index: Constraint::from(0u64),
        funct3: zero_funct3,
        funct12: Constraint::from(0u64),
    };
    let initial_state = MinimalStateRegistersInMemory { pc };
    let flags = ExplicitFlagSource::new(false_flag)
        .with_major(JUMP_COMMON_OP_KEY, true_flag)
        .with_minor(JUMP_COMMON_OP_KEY, JAL_OP_KEY, is_jal);
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = JumpOp::apply::<_, ASSUME_TRUSTED_CODE, false>(
        &mut cs,
        &initial_state,
        &decoder_output,
        &flags,
        &mut opt_ctx,
    );
    let rd_outputs = materialize_rd_outputs(&mut cs, diffs.clone());
    let next_pc_outputs = materialize_next_pc_outputs(&mut cs, &diffs, pc_next);
    let trap_outputs = materialize_trap_outputs(&mut cs, &diffs);
    opt_ctx.enforce_all(&mut cs);
    let (circuit_output, _) = cs.finalize();

    let mut extra_inputs = [
        register_as_inputs(rs1),
        register_as_inputs(pc),
        register_as_inputs(imm),
    ]
    .concat();
    extra_inputs.push(boolean_to_picus_expr(is_jal));

    let mut extra_outputs: Vec<_> = rd_outputs
        .into_iter()
        .chain(next_pc_outputs)
        .map(variable_to_picus_expr)
        .collect();
    if let Some(trap_outputs) = trap_outputs {
        extra_outputs.extend(trap_outputs.into_iter().map(variable_to_picus_expr));
    }

    StandaloneHarness {
        circuit_output,
        extra_inputs,
        extra_outputs,
    }
}

fn build_mul_harness(variant: MulVariant) -> StandaloneHarness {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    cs.materialize_table(TableType::U16GetSignAndHighByte);

    let false_flag = fixed_boolean(&mut cs, false);
    let true_flag = fixed_boolean(&mut cs, true);
    let rs1 = Register::new(&mut cs);
    let rs2 = Register::new(&mut cs);
    let zero_reg = fixed_register(&mut cs, 0);
    let zero_funct3 = fixed_num(&mut cs, 0);
    let mode: Num<Mersenne31Field> = Num::Var(cs.add_variable());
    let mode_bit0 = cs.add_boolean_variable();
    let mode_bit0_var = mode_bit0.get_variable().unwrap();

    let flags = match variant {
        MulVariant::Signed => {
            let mode_bit1 = cs.add_boolean_variable();
            let mode_bit1_var = mode_bit1.get_variable().unwrap();
            cs.add_constraint_allow_explicit_linear(
                Constraint::from(mode.get_variable())
                    - Term::from(mode_bit0_var)
                    - Term::from((Mersenne31Field::from_u64_unchecked(2), mode_bit1_var)),
            );

            let mode_is_0 = Boolean::and(&mode_bit0.toggle(), &mode_bit1.toggle(), &mut cs);
            let mode_is_1 = Boolean::and(&mode_bit0, &mode_bit1.toggle(), &mut cs);
            let mode_is_2 = Boolean::and(&mode_bit0.toggle(), &mode_bit1, &mut cs);

            ExplicitFlagSource::new(false_flag)
                .with_major(MUL_COMMON_OP_KEY, true_flag)
                .with_minor(MUL_COMMON_OP_KEY, MUL_OP_KEY, mode_is_0)
                .with_minor(MUL_COMMON_OP_KEY, MULH_OP_KEY, mode_is_1)
                .with_minor(MUL_COMMON_OP_KEY, MULHSU_OP_KEY, mode_is_2)
        }
        MulVariant::UnsignedOnly => {
            cs.add_constraint_allow_explicit_linear(
                Constraint::from(mode.get_variable()) - Term::from(mode_bit0_var),
            );

            ExplicitFlagSource::new(false_flag)
                .with_major(MUL_COMMON_OP_KEY, true_flag)
                .with_minor(MUL_COMMON_OP_KEY, MUL_OP_KEY, mode_bit0.toggle())
        }
    };

    let decoder_output = build_binary_like_decoder_output(&mut cs, rs1, rs2, zero_reg, zero_funct3);
    let initial_state = MinimalStateRegistersInMemory {
        pc: fixed_register(&mut cs, 0),
    };
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = match variant {
        MulVariant::Signed => MulOp::<true>::apply::<_, true, false>(
            &mut cs,
            &initial_state,
            &decoder_output,
            &flags,
            &mut opt_ctx,
        ),
        MulVariant::UnsignedOnly => MulOp::<false>::apply::<_, true, false>(
            &mut cs,
            &initial_state,
            &decoder_output,
            &flags,
            &mut opt_ctx,
        ),
    };
    let rd_outputs = materialize_rd_outputs(&mut cs, diffs.clone());
    let default_pc = fixed_register(&mut cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(&mut cs, &diffs, default_pc);
    opt_ctx.enforce_all(&mut cs);
    let (circuit_output, _) = cs.finalize();

    let mut extra_inputs = [register_as_inputs(rs1), register_as_inputs(rs2)].concat();
    extra_inputs.push(variable_to_picus_expr(mode.get_variable()));

    StandaloneHarness {
        circuit_output,
        extra_inputs,
        extra_outputs: rd_outputs
            .into_iter()
            .chain(next_pc_outputs)
            .map(variable_to_picus_expr)
            .collect(),
    }
}

fn build_divrem_harness(variant: DivRemVariant) -> StandaloneHarness {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    cs.materialize_table(TableType::U16GetSignAndHighByte);

    let false_flag = fixed_boolean(&mut cs, false);
    let true_flag = fixed_boolean(&mut cs, true);
    let rs1 = Register::new(&mut cs);
    let rs2 = Register::new(&mut cs);
    let zero_reg = fixed_register(&mut cs, 0);
    let zero_funct3 = fixed_num(&mut cs, 0);
    let mode: Num<Mersenne31Field> = Num::Var(cs.add_variable());
    let mode_bit0 = cs.add_boolean_variable();
    let mode_bit0_var = mode_bit0.get_variable().unwrap();

    let flags = match variant {
        DivRemVariant::Signed => {
            let mode_bit1 = cs.add_boolean_variable();
            let mode_bit1_var = mode_bit1.get_variable().unwrap();
            cs.add_constraint_allow_explicit_linear(
                Constraint::from(mode.get_variable())
                    - Term::from(mode_bit0_var)
                    - Term::from((Mersenne31Field::from_u64_unchecked(2), mode_bit1_var)),
            );

            let mode_is_0 = Boolean::and(&mode_bit0.toggle(), &mode_bit1.toggle(), &mut cs);
            let mode_is_1 = Boolean::and(&mode_bit0, &mode_bit1.toggle(), &mut cs);
            let mode_is_2 = Boolean::and(&mode_bit0.toggle(), &mode_bit1, &mut cs);

            ExplicitFlagSource::new(false_flag)
                .with_major(DIVREM_COMMON_OP_KEY, true_flag)
                .with_minor(DIVREM_COMMON_OP_KEY, DIV_OP_KEY, mode_is_0)
                .with_minor(DIVREM_COMMON_OP_KEY, DIVU_OP_KEY, mode_is_1)
                .with_minor(DIVREM_COMMON_OP_KEY, REM_OP_KEY, mode_is_2)
        }
        DivRemVariant::UnsignedOnly => {
            cs.add_constraint_allow_explicit_linear(
                Constraint::from(mode.get_variable()) - Term::from(mode_bit0_var),
            );

            ExplicitFlagSource::new(false_flag)
                .with_major(DIVREM_COMMON_OP_KEY, true_flag)
                .with_minor(DIVREM_COMMON_OP_KEY, DIVU_OP_KEY, mode_bit0.toggle())
        }
    };

    let decoder_output = build_binary_like_decoder_output(&mut cs, rs1, rs2, zero_reg, zero_funct3);
    let initial_state = MinimalStateRegistersInMemory {
        pc: fixed_register(&mut cs, 0),
    };
    let mut opt_ctx = OptimizationContext::<Mersenne31Field, _>::new();
    let diffs = match variant {
        DivRemVariant::Signed => DivRemOp::<true>::apply::<_, true, false>(
            &mut cs,
            &initial_state,
            &decoder_output,
            &flags,
            &mut opt_ctx,
        ),
        DivRemVariant::UnsignedOnly => DivRemOp::<false>::apply::<_, true, false>(
            &mut cs,
            &initial_state,
            &decoder_output,
            &flags,
            &mut opt_ctx,
        ),
    };
    let rd_outputs = materialize_rd_outputs(&mut cs, diffs.clone());
    let default_pc = fixed_register(&mut cs, 4);
    let next_pc_outputs = materialize_next_pc_outputs(&mut cs, &diffs, default_pc);
    opt_ctx.enforce_all(&mut cs);
    let (circuit_output, _) = cs.finalize();

    let mut extra_inputs = [register_as_inputs(rs1), register_as_inputs(rs2)].concat();
    extra_inputs.push(variable_to_picus_expr(mode.get_variable()));

    StandaloneHarness {
        circuit_output,
        extra_inputs,
        extra_outputs: rd_outputs
            .into_iter()
            .chain(next_pc_outputs)
            .map(variable_to_picus_expr)
            .collect(),
    }
}

fn add_unrolled_decoder_op_type_semantics(
    module: &mut PicusModule,
    metadata: &UnrolledDecoderPicusMetadata,
) {
    let packed_opcode = variable_to_picus_expr(metadata.packed_opcode_var);
    let det_packed_opcode = PicusConstraint::new_det(packed_opcode);

    module.constraints.push(PicusConstraint::Implies(
        Box::new(det_packed_opcode.clone()),
        Box::new(PicusConstraint::new_det(boolean_to_picus_expr(
            metadata.is_invalid,
        ))),
    ));

    for bit in metadata.opcode_formats_except_r {
        module.constraints.push(PicusConstraint::Implies(
            Box::new(det_packed_opcode.clone()),
            Box::new(PicusConstraint::new_det(boolean_to_picus_expr(bit))),
        ));
    }
}

fn neg_expr(expr: PicusExpr) -> PicusExpr {
    PicusExpr::Sub(Box::new(PicusExpr::Const(0)), Box::new(expr))
}

fn term_to_picus_expr<F: PrimeField>(term: &Term<F>) -> PicusExpr {
    match term {
        Term::Constant(c) => {
            let coeff = c.as_u64_reduced();
            let coeff_opp = F::CHARACTERISTICS - coeff;
            if coeff < coeff_opp {
                PicusExpr::Const(coeff)
            } else {
                neg_expr(PicusExpr::Const(coeff_opp))
            }
        }
        Term::Expression {
            coeff,
            inner,
            degree,
        } => {
            let coeff = coeff.as_u64_reduced();
            let coeff_opp = F::CHARACTERISTICS - coeff;
            let mut monomial = PicusExpr::Const(1);
            for var in inner.iter().take(*degree) {
                monomial = monomial * variable_to_picus_expr(*var);
            }

            if coeff < coeff_opp {
                if coeff == 1 {
                    monomial
                } else {
                    PicusExpr::Const(coeff) * monomial
                }
            } else if coeff_opp == 1 {
                neg_expr(monomial)
            } else {
                neg_expr(PicusExpr::Const(coeff_opp) * monomial)
            }
        }
    }
}

fn constraint_to_picus_constraint<F: PrimeField>(constraint: &Constraint<F>) -> PicusConstraint {
    PicusConstraint::Eq(Box::new(constraint_to_picus_expr(constraint)))
}

fn constraint_to_picus_expr<F: PrimeField>(constraint: &Constraint<F>) -> PicusExpr {
    let expr = constraint
        .terms
        .iter()
        .map(term_to_picus_expr::<F>)
        .fold(PicusExpr::Const(0), |acc, term_expr| acc + term_expr);

    expr
}

fn circuit_picus_expr_to_pcl_expr<F: PrimeField>(expr: &CircuitPicusExpr<F>) -> PicusExpr {
    match expr {
        CircuitPicusExpr::Variable(var) => variable_to_picus_expr(*var),
        CircuitPicusExpr::Constant(c) => PicusExpr::Const(c.as_u64_reduced()),
        CircuitPicusExpr::Add(lhs, rhs) => {
            circuit_picus_expr_to_pcl_expr(lhs) + circuit_picus_expr_to_pcl_expr(rhs)
        }
        CircuitPicusExpr::Sub(lhs, rhs) => {
            circuit_picus_expr_to_pcl_expr(lhs) - circuit_picus_expr_to_pcl_expr(rhs)
        }
        CircuitPicusExpr::Mul(lhs, rhs) => {
            circuit_picus_expr_to_pcl_expr(lhs) * circuit_picus_expr_to_pcl_expr(rhs)
        }
    }
}

fn circuit_picus_constraint_to_pcl_constraint<F: PrimeField>(
    constraint: &CircuitPicusStructuredConstraint<F>,
) -> PicusConstraint {
    match constraint {
        CircuitPicusStructuredConstraint::Eq { lhs, rhs } => PicusConstraint::new_equality(
            circuit_picus_expr_to_pcl_expr(lhs),
            circuit_picus_expr_to_pcl_expr(rhs),
        ),
    }
}

fn lookup_input_to_picus_expr<F: PrimeField>(input: &cs::definitions::LookupInput<F>) -> PicusExpr {
    match input {
        cs::definitions::LookupInput::Variable(variable) => variable_to_picus_expr(*variable),
        cs::definitions::LookupInput::Expression {
            linear_terms,
            constant_coeff,
        } => linear_terms.iter().fold(
            PicusExpr::Const(constant_coeff.as_u64_reduced()),
            |acc, (coeff, variable)| {
                acc + (PicusExpr::Const(coeff.as_u64_reduced()) * variable_to_picus_expr(*variable))
            },
        ),
    }
}

fn fresh_picus_var_expr(next_fresh_var_id: &mut usize) -> PicusExpr {
    let var = PicusExpr::Var(*next_fresh_var_id);
    *next_fresh_var_id += 1;
    var
}

pub fn add_circuit_input_and_outputs<F: PrimeField>(
    module: &mut PicusModule,
    ram_queries: &[ShuffleRamMemQuery],
) {
    for query in ram_queries {
        for val in query.read_value {
            let picus_var = variable_to_picus_expr(val);
            module.inputs.push(picus_var.clone());
            module.constraints.push(PicusConstraint::Lt(
                Box::new(picus_var),
                Box::new(PicusExpr::Const(U16_BOUND)),
            ));
        }
        if query.local_timestamp_in_cycle != RS1_LOAD_LOCAL_TIMESTAMP
            && query.local_timestamp_in_cycle != RS2_LOAD_LOCAL_TIMESTAMP
        {
            for val in query.write_value {
                let picus_var = variable_to_picus_expr(val);
                module.outputs.push(picus_var.clone());
            }
        }
    }
}

fn build_picus_module_from_circuit_output<F: PrimeField>(
    module_name: impl Into<String>,
    circuit_output: &CircuitOutput<F>,
    circuit_state: Option<&OpcodeFamilyCircuitState<F>>,
    extra_inputs: &[PicusExpr],
    extra_outputs: &[PicusExpr],
    extra_constraints: &[PicusConstraint],
) -> PicusModule {
    let module_name = module_name.into();
    let mut module = PicusModule::new(module_name.clone());
    add_circuit_input_and_outputs::<F>(&mut module, &circuit_output.shuffle_ram_queries);
    if circuit_output
        .picus_extraction_metadata
        .parallel_constraints_enabled
    {
        let parallel_constraints: Vec<PicusConstraint> = circuit_output
            .picus_extraction_metadata
            .parallel_constraints
            .iter()
            .map(circuit_picus_constraint_to_pcl_constraint::<F>)
            .collect();
        module.constraints.extend_from_slice(&parallel_constraints);
    } else {
        let parsed_constraints: Vec<PicusConstraint> = circuit_output
            .constraints
            .iter()
            .map(|(constraint, _prevent_optimization)| constraint_to_picus_constraint(constraint))
            .collect();
        module.constraints.extend_from_slice(&parsed_constraints);
    }
    let mut next_fresh_var_id = circuit_output.num_of_variables;
    add_lookup_constraints(&mut module, &circuit_output.lookups, &mut next_fresh_var_id);
    add_disjunctive_lookup_constraints(
        &mut module,
        &circuit_output.picus_extraction_metadata.disjunctive_lookups,
        &mut next_fresh_var_id,
    );

    for boolean_var in &circuit_output.boolean_vars {
        let picus_expr = variable_to_picus_expr(*boolean_var);
        module
            .constraints
            .push(PicusConstraint::new_bit(picus_expr));
    }

    for range_check_query in &circuit_output.range_check_expressions {
        let lookup_val = lookup_input_to_picus_expr(&range_check_query.input);
        let bound = 1u64
            .checked_shl(range_check_query.width as u32)
            .expect("range check width must be less than 64");
        module.constraints.push(PicusConstraint::Lt(
            Box::new(lookup_val),
            Box::new(PicusExpr::Const(bound)),
        ));
    }

    if let Some(cs) = circuit_state {
        let rd_is_zero_picus = variable_to_picus_expr(cs.decoder_data.rd_is_zero);
        let funct3_picus = variable_to_picus_expr(cs.decoder_data.funct3);
        let rs1_idx_picus = variable_to_picus_expr(cs.decoder_data.rs1_index);
        let rs2_idx_picus = variable_to_picus_expr(cs.decoder_data.rs2_index);
        let rd_idx_picus = variable_to_picus_expr(cs.decoder_data.rd_index);
        let [rd_imm_low_var, rd_imm_high_var] =
            cs.decoder_data.imm.map(|v| variable_to_picus_expr(v));
        let [pc_low, pc_high] = cs.cycle_start_state.pc.map(|v| variable_to_picus_expr(v));
        let [next_pc_low, next_pc_high] = cs.cycle_end_state.pc.map(|v| variable_to_picus_expr(v));
        module.inputs.push(rd_is_zero_picus.clone());
        module.inputs.push(rd_imm_low_var.clone());
        module.inputs.push(rd_imm_high_var.clone());
        module.inputs.push(funct3_picus.clone());
        module.inputs.push(rs1_idx_picus.clone());
        module.inputs.push(rs2_idx_picus.clone());
        module.inputs.push(rd_idx_picus.clone());
        module
            .constraints
            .push(PicusConstraint::new_lt(funct3_picus.clone(), 8.into()));
        if let Some(funct_7) = cs.decoder_data.funct7 {
            let funct7_picus = variable_to_picus_expr(funct_7);
            module.inputs.push(funct7_picus.clone());
            module
                .constraints
                .push(PicusConstraint::new_lt(funct7_picus.clone(), 128.into()));
        }
        module.inputs.extend_from_slice(
            &cs.cycle_start_state
                .timestamp
                .map(|v| variable_to_picus_expr(v)),
        );
        module.outputs.push(next_pc_low.clone());
        module.outputs.push(next_pc_high.clone());
        module
            .inputs
            .extend_from_slice(&[pc_low.clone(), pc_high.clone()]);
        module
            .constraints
            .push(PicusConstraint::new_bit(rd_is_zero_picus.clone()));
        module
            .constraints
            .push(PicusConstraint::new_lt(rd_imm_low_var, U16_BOUND.into()));
        module
            .constraints
            .push(PicusConstraint::new_lt(rd_imm_high_var, U16_BOUND.into()));
        module
            .constraints
            .push(PicusConstraint::new_lt(pc_low, U16_BOUND.into()));
        module
            .constraints
            .push(PicusConstraint::new_lt(pc_high, U16_BOUND.into()));
    }
    module.inputs.extend_from_slice(extra_inputs);
    module.outputs.extend_from_slice(extra_outputs);
    module.constraints.extend_from_slice(extra_constraints);
    module
}

pub fn circuit_output_to_picus_program<F: PrimeField>(
    module_name: impl Into<String>,
    circuit_output: &CircuitOutput<F>,
    circuit_state: Option<&OpcodeFamilyCircuitState<F>>,
    specialization: Option<&DecoderSpecialization>,
) -> PicusProgram {
    let module_name = module_name.into();
    let module = build_picus_module_from_circuit_output(
        module_name.clone(),
        circuit_output,
        circuit_state,
        &[],
        &[],
        &[],
    );
    let mut modules = BTreeMap::new();
    if let Some(specialization) = specialization {
        for case in specialization.cases.iter() {
            let mut specialized = module.partial_eval(&case.assignments);
            if let Some(name_suffix) = &case.name_suffix {
                specialized.name = format!("{}_{}", module_name, name_suffix);
            }
            let previous = modules.insert(specialized.name.clone(), specialized);
            assert!(
                previous.is_none(),
                "duplicate specialized module name emitted for {}",
                module_name
            );
        }
    } else {
        modules.insert(module_name, module);
    }

    let mut program = PicusProgram::new(F::CHARACTERISTICS);
    program.add_modules(&mut modules);
    program
}

/// Build the standalone optimized-decoder harness inside an arbitrary circuit builder.
///
/// This is factored over `CS` so the exact same harness can be instantiated in two modes:
/// - `BasicAssembly`, which produces the finalized `CircuitOutput` used by Picus and LLZK; and
/// - `BasicAssembly<_, WitnessGraphCreator<_>>`, which records the SSA witness graph used for LLZK
///   `@compute` lowering.
///
/// Keeping the harness body in one place avoids drift between the finalized logical circuit and
/// the witness-graph extraction path. The split wrapper functions below only add the mode-specific
/// finishing steps (`finalize()` vs. `compute_resolution_order()` plus externally-assigned inputs).
fn build_optimized_decoder_circuit_output_with_cs<CS: Circuit<Mersenne31Field>>(
    cs: &mut CS,
    enable_parallel_constraints: bool,
) -> (Register<Mersenne31Field>, Variable, [Variable; 8]) {
    cs.set_picus_parallel_constraints_enabled(enable_parallel_constraints);
    cs.materialize_table(TableType::QuickDecodeDecompositionCheck4x4x4);
    cs.materialize_table(TableType::QuickDecodeDecompositionCheck7x3x6);
    let decoder_table =
        <FullIsaMachineNoExceptionHandling as Machine<Mersenne31Field>>::create_decoder_table(
            TableType::OpTypeBitmask.to_table_id(),
        );
    cs.add_table_with_content(
        TableType::OpTypeBitmask,
        LookupWrapper::Dimensional3(decoder_table),
    );

    let instruction = Register::new(cs);
    let input = DecoderInput { instruction };
    let (splitting, _) =
        <FullIsaMachineNoExceptionHandling as Machine<Mersenne31Field>>::produce_decoder_table_stub(
        );
    let (invalid_opcode, decoder_output, _opcode_format_bits, _other_bits) =
        OptimizedDecoder::decode::<Mersenne31Field, _>(&input, cs, splitting);

    let invalid_opcode_var = match invalid_opcode {
        Boolean::Is(var) => var,
        _ => panic!("optimized decoder invalid opcode flag must be a variable"),
    };
    let rs1_var = match decoder_output.rs1 {
        Num::Var(var) => var,
        Num::Constant(_) => panic!("optimized decoder rs1 must be a variable"),
    };
    let rs2_var = cs.add_variable_from_constraint_allow_explicit_linear(decoder_output.rs2.clone());
    cs.add_picus_parallel_constraint(CircuitPicusStructuredConstraint::Eq {
        lhs: cs::cs::circuit::picus_expr_from_constraint(&decoder_output.rs2),
        rhs: CircuitPicusExpr::Variable(rs2_var),
    });
    let rd_var = cs.add_variable_from_constraint_allow_explicit_linear(decoder_output.rd.clone());
    cs.add_picus_parallel_constraint(CircuitPicusStructuredConstraint::Eq {
        lhs: cs::cs::circuit::picus_expr_from_constraint(&decoder_output.rd),
        rhs: CircuitPicusExpr::Variable(rd_var),
    });
    let imm_low_var = match decoder_output.imm.0[0] {
        Num::Var(var) => var,
        Num::Constant(_) => panic!("optimized decoder imm low must be a variable"),
    };
    let imm_high_var = match decoder_output.imm.0[1] {
        Num::Var(var) => var,
        Num::Constant(_) => panic!("optimized decoder imm high must be a variable"),
    };
    let funct3_var = match decoder_output.funct3 {
        Num::Var(var) => var,
        Num::Constant(_) => panic!("optimized decoder funct3 must be a variable"),
    };
    let funct7_var =
        cs.add_variable_from_constraint_allow_explicit_linear(decoder_output.funct7.clone());
    cs.add_picus_parallel_constraint(CircuitPicusStructuredConstraint::Eq {
        lhs: cs::cs::circuit::picus_expr_from_constraint(&decoder_output.funct7),
        rhs: CircuitPicusExpr::Variable(funct7_var),
    });
    let funct12_var =
        cs.add_variable_from_constraint_allow_explicit_linear(decoder_output.funct12.clone());
    cs.add_picus_parallel_constraint(CircuitPicusStructuredConstraint::Eq {
        lhs: cs::cs::circuit::picus_expr_from_constraint(&decoder_output.funct12),
        rhs: CircuitPicusExpr::Variable(funct12_var),
    });
    (
        instruction,
        invalid_opcode_var,
        [
            rs1_var,
            rs2_var,
            rd_var,
            imm_low_var,
            imm_high_var,
            funct3_var,
            funct7_var,
            funct12_var,
        ],
    )
}

/// Build the finalized standalone optimized-decoder circuit output plus its explicit LLZK boundary.
///
/// The returned tuple mirrors the standalone Picus harness:
/// - the finalized `CircuitOutput`
/// - the symbolic instruction register input
/// - the invalid-opcode flag
/// - the eight decoded scalar outputs
///
/// `llzk_backend` consumes this helper directly rather than re-implementing the decoder harness,
/// which keeps the LLZK translation aligned with the Picus-facing standalone program.
pub fn build_optimized_decoder_circuit_output(
    enable_parallel_constraints: bool,
) -> (
    CircuitOutput<Mersenne31Field>,
    Register<Mersenne31Field>,
    Variable,
    [Variable; 8],
) {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    let (instruction, invalid_opcode_var, outputs) =
        build_optimized_decoder_circuit_output_with_cs(&mut cs, enable_parallel_constraints);
    let (circuit_output, _) = cs.finalize();

    (circuit_output, instruction, invalid_opcode_var, outputs)
}

pub fn build_optimized_decoder_picus_program(enable_parallel_constraints: bool) -> PicusProgram {
    let (circuit_output, instruction, invalid_opcode, outputs) =
        build_optimized_decoder_circuit_output(enable_parallel_constraints);
    let instruction_vars = instruction.0.map(|num| match num {
        Num::Var(var) => var,
        Num::Constant(_) => panic!("decoder instruction input must be variable-backed"),
    });
    let extra_inputs = instruction_vars
        .into_iter()
        .map(variable_to_picus_expr)
        .collect::<Vec<_>>();
    let mut extra_outputs = vec![variable_to_picus_expr(invalid_opcode)];
    extra_outputs.extend(outputs.into_iter().map(variable_to_picus_expr));

    let module = build_picus_module_from_circuit_output(
        "optimized_decoder",
        &circuit_output,
        None,
        &extra_inputs,
        &extra_outputs,
        &[],
    );

    let mut modules = BTreeMap::new();
    modules.insert(module.name.clone(), module);
    let mut program = PicusProgram::new(Mersenne31Field::CHARACTERISTICS);
    program.add_modules(&mut modules);
    program
}

/// Dump witness SSA for the standalone optimized-decoder harness.
///
/// The decoder input register is modeled as an external LLZK boundary input, so the witness graph
/// must be told that those limbs are already assigned before resolution order is computed.
/// Without that step, `WitnessGraphCreator` treats the instruction limbs as missing assignments
/// and panics while building the SSA form.
///
/// This helper reuses [`build_optimized_decoder_circuit_output_with_cs`] so the SSA graph is
/// extracted from the exact same harness that produces the finalized logical circuit.
pub fn dump_optimized_decoder_witness_eval_form() -> Vec<Vec<RawExpression<Mersenne31Field>>> {
    let mut cs = BasicAssembly::<Mersenne31Field, WitnessGraphCreator<Mersenne31Field>>::new();
    cs.witness_placer = Some(WitnessGraphCreator::<Mersenne31Field>::new());
    let (instruction, _invalid_opcode_var, _outputs) =
        build_optimized_decoder_circuit_output_with_cs(&mut cs, true);
    let instruction_vars = instruction.0.map(|num| match num {
        Num::Var(var) => var,
        Num::Constant(_) => panic!("decoder instruction input must be variable-backed"),
    });
    cs.set_values(
        move |placer: &mut <BasicAssembly<
            Mersenne31Field,
            WitnessGraphCreator<Mersenne31Field>,
        > as Circuit<Mersenne31Field>>::WitnessPlacer| {
            use cs::cs::witness_placer::WitnessPlacer;

            for variable in instruction_vars {
                placer.assume_assigned(variable);
            }
        },
    );
    let (_output, witness_placer) = cs.finalize();
    let graph = witness_placer.unwrap();
    let (_resolution_order, ssa_forms) = graph.compute_resolution_order();
    ssa_forms
}

pub fn build_unrolled_decoder_circuit_output(
    enable_parallel_constraints: bool,
) -> (
    CircuitOutput<Mersenne31Field>,
    Register<Mersenne31Field>,
    UnrolledDecoderPicusMetadata,
) {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    cs.set_picus_parallel_constraints_enabled(enable_parallel_constraints);
    cs.materialize_table(TableType::QuickDecodeDecompositionCheck4x4x4);
    cs.materialize_table(TableType::QuickDecodeDecompositionCheck7x3x6);
    let decoder_table =
        <FullIsaMachineNoExceptionHandling as Machine<Mersenne31Field>>::create_decoder_table(
            TableType::OpTypeBitmask.to_table_id(),
        );
    cs.add_table_with_content(
        TableType::OpTypeBitmask,
        LookupWrapper::Dimensional3(decoder_table),
    );

    // This harness extracts the decoder core, so the fetched opcode is modeled as
    // a direct Picus input instead of going through a concrete ROM image lookup.
    let opcode = Register::new(&mut cs);
    let metadata = describe_decoder_cycle_from_opcode_with_metadata(&mut cs, opcode);
    let (circuit_output, _) = cs.finalize();
    (circuit_output, opcode, metadata)
}

pub fn build_unrolled_decoder_picus_program(enable_parallel_constraints: bool) -> PicusProgram {
    let (circuit_output, opcode, metadata) =
        build_unrolled_decoder_circuit_output(enable_parallel_constraints);
    let decoder_machine_state = circuit_output
        .decoder_machine_state
        .as_ref()
        .expect("decoder machine state must be present in unrolled decoder circuit");

    let opcode_vars = opcode.0.map(|num| match num {
        Num::Var(var) => var,
        Num::Constant(_) => panic!("unrolled decoder opcode input must be variable-backed"),
    });
    let extra_inputs = opcode_vars
        .into_iter()
        .map(variable_to_picus_expr)
        .collect::<Vec<_>>();

    let decoder_data = &decoder_machine_state.decoder_data;
    let mut extra_outputs = vec![
        variable_to_picus_expr(decoder_data.decoder_data.rs1_index),
        variable_to_picus_expr(decoder_data.decoder_data.rs2_index),
        variable_to_picus_expr(decoder_data.decoder_data.rd_index),
        variable_to_picus_expr(decoder_data.decoder_data.rd_is_zero),
        variable_to_picus_expr(decoder_data.decoder_data.imm[0]),
        variable_to_picus_expr(decoder_data.decoder_data.imm[1]),
        variable_to_picus_expr(decoder_data.decoder_data.funct3),
        variable_to_picus_expr(decoder_data.circuit_family),
        variable_to_picus_expr(decoder_data.decoder_data.circuit_family_extra_mask),
    ];
    if let Some(funct7) = decoder_data.decoder_data.funct7 {
        extra_outputs.push(variable_to_picus_expr(funct7));
    }

    let mut module = build_picus_module_from_circuit_output(
        "unrolled_decoder",
        &circuit_output,
        None,
        &extra_inputs,
        &extra_outputs,
        &[],
    );
    add_unrolled_decoder_op_type_semantics(&mut module, &metadata);

    let mut modules = BTreeMap::new();
    modules.insert(module.name.clone(), module);
    let mut program = PicusProgram::new(Mersenne31Field::CHARACTERISTICS);
    program.add_modules(&mut modules);
    program
}

pub fn build_add_sub_lui_auipc_mop_circuit_output() -> CircuitOutput<Mersenne31Field> {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    add_sub_lui_auipc_mop_table_addition_fn(&mut cs);
    add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode(&mut cs);
    let (circuit_output, _) = cs.finalize();
    circuit_output
}

fn build_jump_branch_slt_mop_circuit_output() -> CircuitOutput<Mersenne31Field> {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    jump_branch_slt_table_addition_fn(&mut cs);
    jump_branch_slt_circuit_with_preprocessed_bytecode::<_, _, true>(&mut cs);
    let (circuit_output, _) = cs.finalize();
    circuit_output
}

fn build_load_store_subword_only_circuit_output() -> CircuitOutput<Mersenne31Field> {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    subword_only_load_store_table_addition_fn(&mut cs);
    let extra_tables =
        create_load_store_special_tables::<_, { common_constants::ROM_SECOND_WORD_BITS }>(&[]);
    for (table_type, table) in extra_tables {
        cs.add_table_with_content(table_type, table);
    }
    subword_only_load_store_circuit_with_preprocessed_bytecode::<
        _,
        _,
        { common_constants::ROM_SECOND_WORD_BITS },
    >(&mut cs);
    let (circuit_output, _) = cs.finalize();
    circuit_output
}

#[cfg(test)]
fn build_load_store_word_only_circuit_output() -> CircuitOutput<Mersenne31Field> {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    word_only_load_store_table_addition_fn(&mut cs);
    let extra_tables = create_word_only_load_store_special_tables::<
        _,
        { common_constants::ROM_SECOND_WORD_BITS },
    >(&[]);
    for (table_type, table) in extra_tables {
        cs.add_table_with_content(table_type, table);
    }
    word_only_load_store_circuit_with_preprocessed_bytecode::<
        _,
        _,
        { common_constants::ROM_SECOND_WORD_BITS },
    >(&mut cs);
    let (circuit_output, _) = cs.finalize();
    circuit_output
}

fn build_load_store_circuit_output() -> CircuitOutput<Mersenne31Field> {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    load_store_table_addition_fn(&mut cs);
    let extra_tables =
        create_load_store_special_tables::<_, { common_constants::ROM_SECOND_WORD_BITS }>(&[]);
    for (table_type, table) in extra_tables {
        cs.add_table_with_content(table_type, table);
    }
    load_store_circuit_with_preprocessed_bytecode::<_, _, { common_constants::ROM_SECOND_WORD_BITS }>(
        &mut cs,
    );
    let (circuit_output, _) = cs.finalize();
    circuit_output
}

fn build_mul_div_circuit_output<const SUPPORT_SIGNED: bool>(
    enable_parallel_constraints: bool,
) -> CircuitOutput<Mersenne31Field> {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    cs.set_picus_parallel_constraints_enabled(enable_parallel_constraints);
    mul_div_table_addition_fn(&mut cs);
    mul_div_circuit_with_preprocessed_bytecode::<_, _, SUPPORT_SIGNED>(&mut cs);
    let (circuit_output, _) = cs.finalize();
    circuit_output
}

fn build_shift_binop_csrrw_circuit_output() -> CircuitOutput<Mersenne31Field> {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    shift_binop_csrrw_table_addition_fn(&mut cs);
    let csr_table = create_csr_table_for_delegation::<Mersenne31Field>(
        true,
        &[],
        TableType::SpecialCSRProperties.to_table_id(),
    );
    cs.add_table_with_content(
        TableType::SpecialCSRProperties,
        LookupWrapper::Dimensional3(csr_table),
    );
    shift_binop_csrrw_circuit_with_preprocessed_bytecode(&mut cs);
    let (circuit_output, _) = cs.finalize();
    circuit_output
}

fn build_reduced_machine_circuit_output() -> CircuitOutput<Mersenne31Field> {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    reduced_machine_table_addition_fn(&mut cs);
    let extra_tables = create_reduced_machine_special_tables::<
        _,
        { common_constants::ROM_SECOND_WORD_BITS },
    >(&[], &[]);
    for (table_type, table) in extra_tables {
        cs.add_table_with_content(table_type, table);
    }
    reduced_machine_circuit_with_preprocessed_bytecode::<
        _,
        _,
        { common_constants::ROM_SECOND_WORD_BITS },
    >(&mut cs);
    let (circuit_output, _) = cs.finalize();
    circuit_output
}

pub fn build_add_sub_lui_auipc_mop_circuit_output_with_decoded_bits() -> (
    CircuitOutput<Mersenne31Field>,
    OpcodeFamilyCircuitState<Mersenne31Field>,
    [usize; ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS],
) {
    let circuit_output = build_add_sub_lui_auipc_mop_circuit_output();
    let input = executor_machine_state(&circuit_output);
    let decoded_mask_bits = recover_split_bitmask_variables(
        &circuit_output,
        input.decoder_data.circuit_family_extra_mask,
        ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS,
    );
    (
        circuit_output,
        input,
        decoded_mask_bits
            .try_into()
            .expect("add/sub/lui/auipc/mop decomposition must have the expected width"),
    )
}

pub fn build_jump_branch_slt_mop_circuit_output_with_decoded_bits() -> (
    CircuitOutput<Mersenne31Field>,
    OpcodeFamilyCircuitState<Mersenne31Field>,
    [usize; JUMP_SLT_BRANCH_FAMILY_NUM_BITS],
) {
    let circuit_output = build_jump_branch_slt_mop_circuit_output();
    let input = executor_machine_state(&circuit_output);
    let decoded_mask_bits = recover_split_bitmask_variables(
        &circuit_output,
        input.decoder_data.circuit_family_extra_mask,
        JUMP_SLT_BRANCH_FAMILY_NUM_BITS,
    );
    (
        circuit_output,
        input,
        decoded_mask_bits
            .try_into()
            .expect("jump/branch/slt decomposition must have the expected width"),
    )
}

pub fn build_load_store_subword_only_circuit_output_with_decoded_bits() -> (
    CircuitOutput<Mersenne31Field>,
    OpcodeFamilyCircuitState<Mersenne31Field>,
    [usize; SUBWORD_ONLY_MEMORY_FAMILY_NUM_FLAGS],
) {
    let circuit_output = build_load_store_subword_only_circuit_output();
    let input = executor_machine_state(&circuit_output);
    let decoded_mask_bit = recover_direct_mask_variable(&circuit_output);
    (circuit_output, input, [decoded_mask_bit])
}

pub fn build_load_store_circuit_output_with_decoded_bits() -> (
    CircuitOutput<Mersenne31Field>,
    OpcodeFamilyCircuitState<Mersenne31Field>,
    [usize; MEMORY_FAMILY_NUM_FLAGS],
) {
    let circuit_output = build_load_store_circuit_output();
    let input = executor_machine_state(&circuit_output);
    let decoded_mask_bit = recover_direct_mask_variable(&circuit_output);
    (circuit_output, input, [decoded_mask_bit])
}

pub fn build_mul_div_circuit_output_with_decoded_bits() -> (
    CircuitOutput<Mersenne31Field>,
    OpcodeFamilyCircuitState<Mersenne31Field>,
    Vec<usize>,
) {
    build_mul_div_circuit_output_with_decoded_bits_and_parallel_constraints::<true>(true)
}

pub fn build_mul_div_unsigned_only_circuit_output_with_decoded_bits() -> (
    CircuitOutput<Mersenne31Field>,
    OpcodeFamilyCircuitState<Mersenne31Field>,
    Vec<usize>,
) {
    build_mul_div_circuit_output_with_decoded_bits_and_parallel_constraints::<false>(true)
}

pub fn build_mul_div_circuit_output_with_decoded_bits_and_parallel_constraints<
    const SUPPORT_SIGNED: bool,
>(
    enable_parallel_constraints: bool,
) -> (
    CircuitOutput<Mersenne31Field>,
    OpcodeFamilyCircuitState<Mersenne31Field>,
    Vec<usize>,
) {
    let circuit_output =
        build_mul_div_circuit_output::<SUPPORT_SIGNED>(enable_parallel_constraints);
    let input = executor_machine_state(&circuit_output);
    let decoded_mask_bits = recover_split_bitmask_variables(
        &circuit_output,
        input.decoder_data.circuit_family_extra_mask,
        if SUPPORT_SIGNED {
            MUL_DIV_FAMILY_NUM_FLAGS
        } else {
            2
        },
    );
    (circuit_output, input, decoded_mask_bits)
}

pub fn build_shift_binop_csrrw_circuit_output_with_decoded_bits() -> (
    CircuitOutput<Mersenne31Field>,
    OpcodeFamilyCircuitState<Mersenne31Field>,
    [usize; SHIFT_BINARY_CSRRW_FAMILY_NUM_FLAGS],
) {
    let circuit_output = build_shift_binop_csrrw_circuit_output();
    let input = executor_machine_state(&circuit_output);
    let decoded_mask_bits = recover_split_bitmask_variables(
        &circuit_output,
        input.decoder_data.circuit_family_extra_mask,
        SHIFT_BINARY_CSRRW_FAMILY_NUM_FLAGS,
    );
    (
        circuit_output,
        input,
        decoded_mask_bits
            .try_into()
            .expect("shift/binop/csrrw decomposition must have the expected width"),
    )
}

pub fn build_reduced_machine_circuit_output_with_decoded_bits() -> (
    CircuitOutput<Mersenne31Field>,
    OpcodeFamilyCircuitState<Mersenne31Field>,
    [usize; REDUCED_MACHINE_NUM_FLAGS],
) {
    let circuit_output = build_reduced_machine_circuit_output();
    let input = executor_machine_state(&circuit_output);
    let decoded_mask_bits = recover_split_bitmask_variables(
        &circuit_output,
        input.decoder_data.circuit_family_extra_mask,
        REDUCED_MACHINE_NUM_FLAGS,
    );
    (
        circuit_output,
        input,
        decoded_mask_bits
            .try_into()
            .expect("reduced-machine decomposition must have the expected width"),
    )
}

pub fn build_add_sub_lui_auipc_mop_picus_program() -> PicusProgram {
    let (circuit_output, input, decoded_bits) =
        build_add_sub_lui_auipc_mop_circuit_output_with_decoded_bits();
    let specialization = specialization_for_flat_one_hot_named(
        decoded_bits.as_slice(),
        &[
            "add", "addi", "sub", "lui", "auipc", "addmod", "submod", "mulmod",
        ],
    );
    circuit_output_to_picus_program(
        "add_sub_lui_auipc_mop",
        &circuit_output,
        Some(&input),
        Some(&specialization),
    )
}

pub fn build_add_op_picus_program() -> PicusProgram {
    build_standalone_program("add_op", build_add_sub_harness(false))
}

pub fn build_sub_op_picus_program() -> PicusProgram {
    build_standalone_program("sub_op", build_add_sub_harness(true))
}

pub fn build_lui_op_picus_program() -> PicusProgram {
    build_standalone_program("lui_op", build_lui_harness())
}

pub fn build_auipc_op_picus_program() -> PicusProgram {
    build_standalone_program("auipc_op", build_auipc_harness())
}

pub fn build_xor_op_picus_program() -> PicusProgram {
    build_standalone_program("xor_op", build_binop_harness(BinopVariant::Xor))
}

pub fn build_or_op_picus_program() -> PicusProgram {
    build_standalone_program("or_op", build_binop_harness(BinopVariant::Or))
}

pub fn build_and_op_picus_program() -> PicusProgram {
    build_standalone_program("and_op", build_binop_harness(BinopVariant::And))
}

pub fn build_sll_op_picus_program() -> PicusProgram {
    build_standalone_program("sll_op", build_shift_harness(ShiftVariant::Sll))
}

pub fn build_srl_op_picus_program() -> PicusProgram {
    build_standalone_program("srl_op", build_shift_harness(ShiftVariant::Srl))
}

pub fn build_sra_op_picus_program() -> PicusProgram {
    build_standalone_program("sra_op", build_shift_harness(ShiftVariant::Sra))
}

pub fn build_addmod_op_picus_program() -> PicusProgram {
    build_standalone_program("addmod_op", build_mop_harness(MopVariant::AddMod))
}

pub fn build_submod_op_picus_program() -> PicusProgram {
    build_standalone_program("submod_op", build_mop_harness(MopVariant::SubMod))
}

pub fn build_mulmod_op_picus_program() -> PicusProgram {
    build_standalone_program("mulmod_op", build_mop_harness(MopVariant::MulMod))
}

pub fn build_mul_op_signed_picus_program() -> PicusProgram {
    build_standalone_program("mul_op_signed", build_mul_harness(MulVariant::Signed))
}

pub fn build_mul_op_unsigned_only_picus_program() -> PicusProgram {
    build_standalone_program(
        "mul_op_unsigned_only",
        build_mul_harness(MulVariant::UnsignedOnly),
    )
}

pub fn build_divrem_op_signed_picus_program() -> PicusProgram {
    build_standalone_program(
        "divrem_op_signed",
        build_divrem_harness(DivRemVariant::Signed),
    )
}

pub fn build_divrem_op_unsigned_only_picus_program() -> PicusProgram {
    build_standalone_program(
        "divrem_op_unsigned_only",
        build_divrem_harness(DivRemVariant::UnsignedOnly),
    )
}

pub fn build_conditional_op_picus_program() -> PicusProgram {
    build_standalone_program("conditional_op", build_conditional_harness())
}

pub fn build_jump_op_trusted_picus_program() -> PicusProgram {
    build_standalone_program("jump_op_trusted", build_jump_harness::<true>())
}

pub fn build_jump_op_untrusted_picus_program() -> PicusProgram {
    build_standalone_program("jump_op_untrusted", build_jump_harness::<false>())
}

pub fn build_mul_div_picus_program() -> PicusProgram {
    build_mul_div_picus_program_with_parallel_constraints::<true>(false)
}

pub fn build_mul_div_unsigned_only_picus_program() -> PicusProgram {
    build_mul_div_picus_program_with_parallel_constraints::<false>(false)
}

pub fn build_mul_div_picus_program_with_parallel_constraints<const SUPPORT_SIGNED: bool>(
    enable_parallel_constraints: bool,
) -> PicusProgram {
    let (circuit_output, input, decoded_bits) =
        build_mul_div_circuit_output_with_decoded_bits_and_parallel_constraints::<SUPPORT_SIGNED>(
            enable_parallel_constraints,
        );
    let specialization = specialization_for_mul_div::<SUPPORT_SIGNED>(decoded_bits.as_slice());
    circuit_output_to_picus_program(
        if SUPPORT_SIGNED {
            "mul_div"
        } else {
            "mul_div_unsigned_only"
        },
        &circuit_output,
        Some(&input),
        Some(&specialization),
    )
}

pub fn build_shift_binop_csrrw_picus_program() -> PicusProgram {
    let (circuit_output, input, decoded_bits) =
        build_shift_binop_csrrw_circuit_output_with_decoded_bits();
    let specialization = specialization_for_shift_binop_csrrw(
        decoded_bits.as_slice(),
        input.decoder_data.funct3.0 as usize,
    );
    circuit_output_to_picus_program(
        "shift_binop_csrrw",
        &circuit_output,
        Some(&input),
        Some(&specialization),
    )
}

pub fn build_reduced_machine_picus_program() -> PicusProgram {
    let (circuit_output, input, decoded_bits) =
        build_reduced_machine_circuit_output_with_decoded_bits();
    let specialization = specialization_with_fixed_assignment(
        specialization_from_named_bitmasks(decoded_bits.as_slice(), named_reduced_machine_masks()),
        input.execute.0 as usize,
        1,
    );
    circuit_output_to_picus_program(
        "reduced_machine",
        &circuit_output,
        Some(&input),
        Some(&specialization),
    )
}

pub fn build_blake2_with_extended_control_delegation_picus_program() -> PicusProgram {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    let (_, _, metadata) =
        define_blake2_with_extended_control_delegation_circuit_with_metadata(&mut cs);
    let (circuit_output, _) = cs.finalize();

    let Blake2WithExtendedControlDelegationPicusMetadata {
        input_state,
        input_extended_state,
        input_words,
        x12_read_vars,
        output_state,
        output_extended_state,
        x12_write_vars,
    } = metadata;

    let mut extra_inputs = word_pairs_to_picus_exprs(&input_state);
    extra_inputs.extend(word_pairs_to_picus_exprs(&input_extended_state));
    extra_inputs.extend(word_pairs_to_picus_exprs(&input_words));
    extra_inputs.push(variable_to_picus_expr(x12_read_vars[1]));

    let mut extra_outputs = word_pairs_to_picus_exprs(&output_state);
    extra_outputs.extend(word_pairs_to_picus_exprs(&output_extended_state));
    extra_outputs.extend(x12_write_vars.into_iter().map(variable_to_picus_expr));

    let module = build_picus_module_from_circuit_output(
        "blake2_with_extended_control_delegation",
        &circuit_output,
        None,
        &extra_inputs,
        &extra_outputs,
        &[],
    );

    let mut modules = BTreeMap::new();
    modules.insert(module.name.clone(), module);
    let mut program = PicusProgram::new(Mersenne31Field::CHARACTERISTICS);
    program.add_modules(&mut modules);
    program
}

pub fn build_bigint_with_control_delegation_picus_program() -> PicusProgram {
    let mut cs = BasicAssembly::<Mersenne31Field>::new();
    let (_, _, metadata) =
        define_u256_ops_extended_control_delegation_circuit_with_metadata(&mut cs);
    let (circuit_output, _) = cs.finalize();

    let BigintDelegationPicusMetadata {
        a_words,
        b_words,
        control_mask,
        output_state,
        x12_write_vars,
    } = metadata;

    let mut extra_inputs = word_pairs_to_picus_exprs(&a_words);
    extra_inputs.extend(word_pairs_to_picus_exprs(&b_words));
    extra_inputs.push(variable_to_picus_expr(control_mask[0]));

    let mut extra_outputs = word_pairs_to_picus_exprs(&output_state);
    extra_outputs.extend(x12_write_vars.into_iter().map(variable_to_picus_expr));

    let module = build_picus_module_from_circuit_output(
        "bigint_with_control_delegation",
        &circuit_output,
        None,
        &extra_inputs,
        &extra_outputs,
        &[],
    );

    let mut modules = BTreeMap::new();
    modules.insert(module.name.clone(), module);
    let mut program = PicusProgram::new(Mersenne31Field::CHARACTERISTICS);
    program.add_modules(&mut modules);
    program
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::PathBuf;

    fn write_extracted_program(test_name: &str, dumped: &str) {
        let mut out_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        out_dir.push("picus_extracted_modules");
        fs::create_dir_all(&out_dir).expect("failed to create Picus extraction output directory");
        out_dir.push(format!("{test_name}.picus"));
        fs::write(&out_dir, dumped).expect("failed to write Picus extraction output");
    }

    #[test]
    fn add_sub_lui_auipc_mop_translation_smoke_test() {
        let circuit_output = build_add_sub_lui_auipc_mop_circuit_output();
        let program =
            circuit_output_to_picus_program("add_sub_lui_auipc_mop", &circuit_output, None, None);
        let dumped = program.to_string();
        write_extracted_program("add_sub_lui_auipc_mop_translation_smoke_test", &dumped);
        assert!(dumped.contains("(begin-module add_sub_lui_auipc_mop)"));
        assert!(dumped.contains("(prime-number"));
    }

    #[test]
    fn standalone_scalar_op_translation_smoke_tests() {
        let programs = [
            ("add_op", build_add_op_picus_program()),
            ("sub_op", build_sub_op_picus_program()),
            ("lui_op", build_lui_op_picus_program()),
            ("auipc_op", build_auipc_op_picus_program()),
            ("xor_op", build_xor_op_picus_program()),
            ("or_op", build_or_op_picus_program()),
            ("and_op", build_and_op_picus_program()),
            ("sll_op", build_sll_op_picus_program()),
            ("srl_op", build_srl_op_picus_program()),
            ("sra_op", build_sra_op_picus_program()),
            ("addmod_op", build_addmod_op_picus_program()),
            ("submod_op", build_submod_op_picus_program()),
            ("mulmod_op", build_mulmod_op_picus_program()),
            ("mul_op_signed", build_mul_op_signed_picus_program()),
            (
                "mul_op_unsigned_only",
                build_mul_op_unsigned_only_picus_program(),
            ),
            ("divrem_op_signed", build_divrem_op_signed_picus_program()),
            (
                "divrem_op_unsigned_only",
                build_divrem_op_unsigned_only_picus_program(),
            ),
            ("conditional_op", build_conditional_op_picus_program()),
            ("jump_op_trusted", build_jump_op_trusted_picus_program()),
            ("jump_op_untrusted", build_jump_op_untrusted_picus_program()),
        ];

        for (name, program) in programs {
            let dumped = program.to_string();
            write_extracted_program(name, &dumped);
            assert!(dumped.contains(&format!("(begin-module {name})")));
            assert!(dumped.contains("(prime-number"));
        }
    }

    #[test]
    fn optimized_decoder_translation_smoke_test() {
        let program = build_optimized_decoder_picus_program(true);
        let dumped = program.to_string();
        write_extracted_program("optimized_decoder", &dumped);
        assert!(dumped.contains("(begin-module optimized_decoder)"));
        assert!(dumped.contains("(prime-number"));
    }

    #[test]
    fn unrolled_decoder_translation_smoke_test() {
        let program = build_unrolled_decoder_picus_program(true);
        let dumped = program.to_string();
        write_extracted_program("unrolled_decoder", &dumped);
        assert!(dumped.contains("(begin-module unrolled_decoder)"));
        assert!(dumped.contains("(prime-number"));
    }

    #[test]
    fn add_sub_lui_auipc_mop_one_hot_specialization_emits_one_module_per_bit() {
        let (circuit_output, input, decoded_bits) =
            build_add_sub_lui_auipc_mop_circuit_output_with_decoded_bits();
        let specialization = specialization_for_flat_one_hot_named(
            decoded_bits.as_slice(),
            &[
                "add", "addi", "sub", "lui", "auipc", "addmod", "submod", "mulmod",
            ],
        );
        let program = circuit_output_to_picus_program(
            "add_sub_lui_auipc_mop",
            &circuit_output,
            Some(&input),
            Some(&specialization),
        );
        let dumped = program.to_string();
        write_extracted_program("add_sub_lui_auipc_mop", &dumped);
        let module_count = dumped.matches("(begin-module ").count();
        assert_eq!(module_count, ADD_SUB_LUI_AUIPC_MOP_FAMILY_NUM_FLAGS);
    }

    #[test]
    fn jump_branch_slt_one_hot_specialization_emits_one_module_per_bit() {
        let (circuit_output, input, decoded_bits) =
            build_jump_branch_slt_mop_circuit_output_with_decoded_bits();
        let specialization = specialization_for_flat_one_hot_named(
            decoded_bits.as_slice(),
            &["branch", "slti", "slt", "jal", "jalr"],
        );
        let program = circuit_output_to_picus_program(
            "jump_branch_slt",
            &circuit_output,
            Some(&input),
            Some(&specialization),
        );
        let dumped = program.to_string();
        write_extracted_program("jump_branch_slt", &dumped);
    }

    #[test]
    fn load_store_subword_only_one_hot_specialization_emits_one_module_per_bit() {
        let (circuit_output, input, decoded_bits) =
            build_load_store_subword_only_circuit_output_with_decoded_bits();
        let specialization = specialization_for_single_bit_named(decoded_bits[0], "load", "store");
        let program = circuit_output_to_picus_program(
            "load_store_subword_only",
            &circuit_output,
            Some(&input),
            Some(&specialization),
        );
        let dumped = program.to_string();
        write_extracted_program("load_store_subword_only", &dumped);
    }

    #[test]
    fn load_store_word_only_one_hot_specialization_emits_one_module_per_bit() {
        let (circuit_output, input, decoded_bits) = {
            let circuit_output = build_load_store_word_only_circuit_output();
            let input = executor_machine_state(&circuit_output);
            let decoded_mask_bit = recover_direct_mask_variable(&circuit_output);
            (circuit_output, input, [decoded_mask_bit])
        };
        let specialization = specialization_for_single_bit_named(decoded_bits[0], "load", "store");
        let program = circuit_output_to_picus_program(
            "load_store_word_only",
            &circuit_output,
            Some(&input),
            Some(&specialization),
        );
        let dumped = program.to_string();
        write_extracted_program("load_store_word_only", &dumped);
    }

    #[test]
    fn load_store_one_hot_specialization_emits_one_module_per_bit() {
        let (circuit_output, input, decoded_bits) =
            build_load_store_circuit_output_with_decoded_bits();
        let specialization = specialization_for_single_bit_named(decoded_bits[0], "load", "store");
        let program = circuit_output_to_picus_program(
            "load_store",
            &circuit_output,
            Some(&input),
            Some(&specialization),
        );
        let dumped = program.to_string();
        write_extracted_program("load_store", &dumped);
    }

    #[test]
    fn mul_div_specialization_emits_one_module_per_valid_pattern() {
        let (circuit_output, input, decoded_bits) =
            build_mul_div_circuit_output_with_decoded_bits();
        let specialization = specialization_for_mul_div::<true>(decoded_bits.as_slice());
        let program = circuit_output_to_picus_program(
            "mul_div",
            &circuit_output,
            Some(&input),
            Some(&specialization),
        );
        let dumped = program.to_string();
        write_extracted_program("mul_div", &dumped);
    }

    #[test]
    fn mul_div_unsigned_only_specialization_emits_one_module_per_valid_pattern() {
        let (circuit_output, input, decoded_bits) =
            build_mul_div_unsigned_only_circuit_output_with_decoded_bits();
        let specialization = specialization_for_mul_div::<false>(decoded_bits.as_slice());
        let program = circuit_output_to_picus_program(
            "mul_div_unsigned_only",
            &circuit_output,
            Some(&input),
            Some(&specialization),
        );
        let dumped = program.to_string();
        write_extracted_program("mul_div_unsigned_only", &dumped);
    }

    #[test]
    fn shift_binop_csrrw_specialization_emits_one_module_per_valid_pattern() {
        let (circuit_output, input, decoded_bits) =
            build_shift_binop_csrrw_circuit_output_with_decoded_bits();
        let specialization = specialization_for_shift_binop_csrrw(
            decoded_bits.as_slice(),
            input.decoder_data.funct3.0 as usize,
        );
        let program = circuit_output_to_picus_program(
            "shift_binop_csrrw",
            &circuit_output,
            Some(&input),
            Some(&specialization),
        );
        let dumped = program.to_string();
        write_extracted_program("shift_binop_csrrw", &dumped);
        let module_count = dumped.matches("(begin-module ").count();
        assert_eq!(module_count, 13);
    }

    #[test]
    fn reduced_machine_specialization_emits_one_module_per_valid_mask() {
        let (circuit_output, input, decoded_bits) =
            build_reduced_machine_circuit_output_with_decoded_bits();
        let valid_masks = valid_reduced_machine_masks();
        let specialization = specialization_with_fixed_assignment(
            specialization_from_named_bitmasks(
                decoded_bits.as_slice(),
                named_reduced_machine_masks(),
            ),
            input.execute.0 as usize,
            1,
        );
        let program = circuit_output_to_picus_program(
            "reduced_machine",
            &circuit_output,
            Some(&input),
            Some(&specialization),
        );
        let dumped = program.to_string();
        write_extracted_program("reduced_machine", &dumped);
        let module_count = dumped.matches("(begin-module ").count();
        assert_eq!(module_count, valid_masks.len());
    }

    #[test]
    fn blake2_with_extended_control_delegation_translation_smoke_test() {
        let program = build_blake2_with_extended_control_delegation_picus_program();
        let dumped = program.to_string();
        write_extracted_program("blake2_with_extended_control_delegation", &dumped);
        assert!(dumped.contains("(begin-module blake2_with_extended_control_delegation)"));
        assert!(dumped.contains("(prime-number"));
    }

    #[test]
    fn bigint_with_control_delegation_translation_smoke_test() {
        let program = build_bigint_with_control_delegation_picus_program();
        let dumped = program.to_string();
        write_extracted_program("bigint_with_control_delegation", &dumped);
        assert!(dumped.contains("(begin-module bigint_with_control_delegation)"));
        assert!(dumped.contains("(prime-number"));
    }

    #[test]
    fn load_store_lookup_handlers_emit_constraints() {
        let mk_row = |base: u64| {
            [
                cs::definitions::LookupInput::Variable(Variable(base)),
                cs::definitions::LookupInput::Variable(Variable(base + 1)),
                cs::definitions::LookupInput::Variable(Variable(base + 2)),
            ]
        };

        let lookups = vec![
            LookupQuery {
                row: mk_row(0),
                table: LookupQueryTableType::Constant(TableType::AlignedRomRead),
            },
            LookupQuery {
                row: mk_row(10),
                table: LookupQueryTableType::Constant(TableType::MemoryLoadHalfwordOrByte),
            },
            LookupQuery {
                row: mk_row(20),
                table: LookupQueryTableType::Constant(TableType::MemStoreClearOriginalRamValueLimb),
            },
            LookupQuery {
                row: mk_row(30),
                table: LookupQueryTableType::Constant(TableType::RomAddressSpaceSeparator),
            },
            LookupQuery {
                row: mk_row(40),
                table: LookupQueryTableType::Constant(TableType::MemoryGetOffsetAndMaskWithTrap),
            },
        ];

        let mut module = PicusModule::new("load_store_lookup_handlers".to_owned());
        let mut next_fresh_var_id = 128;
        add_lookup_constraints::<Mersenne31Field>(&mut module, &lookups, &mut next_fresh_var_id);
        assert!(!module.constraints.is_empty());
    }
}
