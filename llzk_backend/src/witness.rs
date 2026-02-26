//! Witness SSA extraction and lowering for LLZK `@compute`.
//!
//! The existing constraint lowering path only needs the finalized [`CircuitOutput`], but witness
//! lowering needs one extra layer of compiler metadata:
//! - the one-row compiler's variable-to-column mapping, so we know which SSA writes belong in the
//!   returned struct and which only touch transient memory columns; and
//! - the witness placer's SSA blocks, so we can replay the same evaluation order inside LLZK.
//!
//! The extraction flow implemented here mirrors the Rust witness generator closely:
//! 1. walk each SSA block in order;
//! 2. cache every subexpression by its SSA index;
//! 3. lower writes that target witness or scratch columns into struct member updates;
//! 4. canonicalize placeholder-based witness reads back to explicit LLZK inputs whenever the same
//!    logical machine-state value is already part of the `@compute` boundary; and
//! 5. lower remaing ROM and memory-subtree accesses as explicit runtime hooks.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::ops::Deref;

use anyhow::anyhow;
use anyhow::bail;
use anyhow::Result;
use llzk::dialect::bool;
use llzk::dialect::felt;
use llzk::prelude::*;
use prover::common_constants;
use prover::cs::cs::placeholder::Placeholder;
use prover::cs::cs::witness_placer::graph_description::BoolNodeExpression;
use prover::cs::cs::witness_placer::graph_description::Expression;
use prover::cs::cs::witness_placer::graph_description::FieldNodeExpression;
use prover::cs::cs::witness_placer::graph_description::FixedWidthIntegerNodeExpression;
use prover::cs::cs::witness_placer::graph_description::RawExpression;
use prover::cs::definitions::ColumnAddress;
use prover::cs::definitions::LookupSetDescription;
use prover::cs::definitions::TableIndex;
use prover::cs::definitions::Variable;
use prover::cs::definitions::COMMON_TABLE_WIDTH;
use prover::cs::one_row_compiler::CompiledCircuitArtifact;
use prover::cs::tables::TableType;

use crate::builder::ModuleEnv;
use crate::builder::OpsBuilder;
use crate::builder::SemanticLocation;
use crate::codegen::SpecialCsrPropertiesMetadata;
use crate::codegen::StructVars;
use crate::field::FieldInfo;
use crate::keccak_tables::keccak_permutation_indices_outputs;

const U8_MODULUS: u64 = 1 << 8;
const U16_MODULUS: u64 = 1 << 16;

// Function names for oracle calls.
const READ_FROM_ROM_EXTERN: &str = "read_from_rom";
const READ_FROM_MEMORY_SUBTREE_EXTERN: &str = "read_from_memory_subtree";
const WRITE_TO_MEMORY_SUBTREE_EXTERN: &str = "write_to_memory_subtree";
const READ_ORACLE_FIELD_EXTERN: &str = "read_oracle_field";
const READ_ORACLE_BOOL_EXTERN: &str = "read_oracle_bool";
const READ_ORACLE_U8_EXTERN: &str = "read_oracle_u8";
const READ_ORACLE_U16_EXTERN: &str = "read_oracle_u16";
const READ_ORACLE_U32_EXTERN: &str = "read_oracle_u32";
const READ_OP_TYPE_BITMASK_EXTERN: &str = "read_op_type_bitmask";

#[derive(Clone, Copy)]
enum ComputeRuntimeHookKind {
    MemoryRead,
    MemoryWrite,
    OracleField,
    OracleBool,
    OracleU8,
    OracleU16,
    OracleU32,
    DecoderBitmask,
    RomRead,
}

impl ComputeRuntimeHookKind {
    /// Virtual path segment used for descriptive `llzk://compute/runtime/...` debug locations.
    const fn debug_path(self) -> &'static str {
        match self {
            Self::MemoryRead => "llzk://compute/runtime/memory_read",
            Self::MemoryWrite => "llzk://compute/runtime/memory_write",
            Self::OracleField => "llzk://compute/runtime/oracle_field",
            Self::OracleBool => "llzk://compute/runtime/oracle_bool",
            Self::OracleU8 => "llzk://compute/runtime/oracle_u8",
            Self::OracleU16 => "llzk://compute/runtime/oracle_u16",
            Self::OracleU32 => "llzk://compute/runtime/oracle_u32",
            Self::DecoderBitmask => "llzk://compute/runtime/decoder_bitmask",
            Self::RomRead => "llzk://compute/runtime/rom_read",
        }
    }
}

/// An encoding for a witness placeholder (from [`Placeholder`]), but encoded for easy
/// emission to LLZK in a fixed format that is consistent across all placeholder types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct EncodedOraclePlaceholder {
    kind: u64,
    arg0: u64,
    arg1: u64,
}

/// Convert a witness placeholder into the fixed-width format used by LLZK oracle hooks.
fn encode_oracle_placeholder(placeholder: Placeholder) -> EncodedOraclePlaceholder {
    use Placeholder::*;

    let kind = match placeholder {
        XregsInit => 0,
        XregsFin => 1,
        XregInit(_) => 2,
        XregFin(_) => 3,
        Instruction => 4,
        MemSlot => 5,
        PcInit => 6,
        PcFin => 7,
        StatusInit => 8,
        StatusFin => 9,
        IeInit => 10,
        IeFin => 11,
        IpInit => 12,
        IpFin => 13,
        TvecInit => 14,
        TvecFin => 15,
        ScratchInit => 16,
        ScratchFin => 17,
        EpcInit => 18,
        EpcFin => 19,
        CauseInit => 20,
        CauseFin => 21,
        TvalInit => 22,
        TvalFin => 23,
        ModeInit => 24,
        ModeFin => 25,
        MemorySaptInit => 26,
        MemorySaptFin => 27,
        ContinueExecutionInit => 28,
        ContinueExecutionFin => 29,
        ExternalOracle => 30,
        Trapped => 31,
        InvalidEncoding => 32,
        FirstRegMem => 33,
        SecondRegMem => 34,
        WriteRegMemReadWitness => 35,
        WriteRegMemWriteValue => 36,
        MemoryLoadOp => 37,
        WriteRdReadSetWitness => 38,
        ShuffleRamLazyInitAddressThis => 39,
        ShuffleRamLazyInitAddressNext => 40,
        ShuffleRamAddress(_) => 41,
        ShuffleRamReadTimestamp(_) => 42,
        ShuffleRamReadValue(_) => 43,
        ShuffleRamIsRegisterAccess(_) => 44,
        ShuffleRamWriteValue(_) => 45,
        ExecuteDelegation => 46,
        DelegationType => 47,
        DelegationABIOffset => 48,
        DelegationWriteTimestamp => 49,
        DelegationMemoryReadValue(_) => 50,
        DelegationMemoryReadTimestamp(_) => 51,
        DelegationMemoryWriteValue(_) => 52,
        DelegationRegisterReadValue(_) => 53,
        DelegationRegisterReadTimestamp(_) => 54,
        DelegationRegisterWriteValue(_) => 55,
        DelegationIndirectReadValue { .. } => 56,
        DelegationIndirectReadTimestamp { .. } => 57,
        DelegationIndirectWriteValue { .. } => 58,
        DelegationNondeterminismAccess(_) => 59,
        DelegationNondeterminismAccessNoSplits(_) => 60,
        ExecuteOpcodeFamilyCycle => 61,
        OpcodeFamilyCycleInitialTimestamp => 62,
        OpcodeFamilyCycleFinalTimestamp => 63,
        RS1Index => 64,
        RS2Index => 65,
        MemLoadAddress => 66,
        RDIndex => 67,
        RDIsZero => 68,
        DecodedImm => 69,
        DecodedFunct3 => 70,
        DecodedFunct7 => 71,
        DecodedExecutorFamilyMask => 72,
        LoadStoreRamValue => 73,
        MemStoreAddress => 74,
        DelegationIndirectAccessVariableOffset { .. } => 75,
    };

    let (arg0, arg1) = match placeholder {
        XregInit(idx) | XregFin(idx) => (idx as u64, 0),
        ShuffleRamAddress(access_idx)
        | ShuffleRamReadTimestamp(access_idx)
        | ShuffleRamReadValue(access_idx)
        | ShuffleRamIsRegisterAccess(access_idx)
        | ShuffleRamWriteValue(access_idx)
        | DelegationMemoryReadValue(access_idx)
        | DelegationMemoryReadTimestamp(access_idx)
        | DelegationMemoryWriteValue(access_idx)
        | DelegationNondeterminismAccess(access_idx)
        | DelegationNondeterminismAccessNoSplits(access_idx) => (access_idx as u64, 0),
        DelegationRegisterReadValue(register_index)
        | DelegationRegisterReadTimestamp(register_index)
        | DelegationRegisterWriteValue(register_index) => (register_index as u64, 0),
        DelegationIndirectReadValue {
            register_index,
            word_index,
        }
        | DelegationIndirectReadTimestamp {
            register_index,
            word_index,
        }
        | DelegationIndirectWriteValue {
            register_index,
            word_index,
        } => (register_index as u64, word_index as u64),
        DelegationIndirectAccessVariableOffset { variable_index } => (variable_index as u64, 0),
        _ => (0, 0),
    };

    EncodedOraclePlaceholder { kind, arg0, arg1 }
}

fn placeholder_allows_member_oracle_fallback(placeholder: Placeholder) -> bool {
    use Placeholder::*;

    matches!(
        placeholder,
        ExecuteDelegation
            | DelegationType
            | DelegationABIOffset
            | DelegationWriteTimestamp
            | DelegationMemoryReadValue(_)
            | DelegationMemoryReadTimestamp(_)
            | DelegationMemoryWriteValue(_)
            | DelegationRegisterReadValue(_)
            | DelegationRegisterReadTimestamp(_)
            | DelegationRegisterWriteValue(_)
            | DelegationIndirectReadValue { .. }
            | DelegationIndirectReadTimestamp { .. }
            | DelegationIndirectWriteValue { .. }
            | DelegationNondeterminismAccess(_)
            | DelegationNondeterminismAccessNoSplits(_)
            | DelegationIndirectAccessVariableOffset { .. }
    )
}

/// Trait implemented by SSA witness nodes that can emit LLZK IR inside a struct `@compute`
/// function.
trait EmitLlzkInCompute<'a, 'ctx: 'sco, 'sco, F: FieldInfo> {
    type Output;

    fn emit_compute(
        &self,
        lowering: &mut ComputeLowering<'a, 'ctx, 'sco, F>,
    ) -> Result<Self::Output>;
}

impl<'a, 'ctx: 'sco, 'sco, F, T> EmitLlzkInCompute<'a, 'ctx, 'sco, F> for Vec<T>
where
    F: FieldInfo,
    T: EmitLlzkInCompute<'a, 'ctx, 'sco, F, Output = ()>,
{
    type Output = ();

    fn emit_compute(
        &self,
        lowering: &mut ComputeLowering<'a, 'ctx, 'sco, F>,
    ) -> Result<Self::Output> {
        self.iter().try_for_each(|expr| expr.emit_compute(lowering))
    }
}

/// Bundles the metadata required to lower witness generation into LLZK `@compute`.
///
/// The compiled artifact tells us where every logical variable lives in the witness layout, the
/// SSA blocks preserve the witness placer's evaluation order and conditional write structure, and
/// the placeholder substitution map lets us recognize when oracle-style SSA inputs are
/// actually aliases of explicit LLZK `@compute` arguments.
pub(crate) struct WitnessComputation<F: FieldInfo> {
    compiled: CompiledCircuitArtifact<F>,
    ssa: Vec<Vec<RawExpression<F>>>,
    substitutions: HashMap<(Placeholder, usize), Variable>,
    special_csr_properties: Option<SpecialCsrPropertiesMetadata>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct WitnessVariableUsage {
    pub read_vars: BTreeSet<Variable>,
    pub write_vars: BTreeSet<Variable>,
}

impl<F: FieldInfo> WitnessComputation<F> {
    /// Create a new witness computation plan from the one-row compiler output, witness SSA, and
    /// placeholder substitution map.
    ///
    /// The substitution map is what lets LLZK avoid deriving the same machine-state input from two
    /// different sources. When a placeholder such as `PcInit` already names an explicit
    /// `@compute` argument, witness lowering reads the argument and only falls back to an oracle
    /// hook for placeholders that remain true runtime-only data (like ROM reads).
    pub fn new(
        compiled: CompiledCircuitArtifact<F>,
        ssa: Vec<Vec<RawExpression<F>>>,
        substitutions: HashMap<(Placeholder, usize), Variable>,
        special_csr_properties: Option<SpecialCsrPropertiesMetadata>,
    ) -> Self {
        Self {
            compiled,
            ssa,
            substitutions,
            special_csr_properties,
        }
    }

    /// Collect logical variable reads and writes from the witness SSA.
    pub(crate) fn logical_variable_usage(&self) -> WitnessVariableUsage {
        let mut usage = WitnessVariableUsage::default();
        for expr in self.ssa.iter().flatten() {
            collect_raw_expression_usage(expr, &mut usage);
        }
        usage
    }

    /// Declare runtime hooks if they are needed by the emitted LLZK module.
    pub fn declare_runtime_externs<'ctx>(&self, env: &ModuleEnv<'ctx, F>) -> Result<()> {
        let maybe_declare =
            |name: &str, inputs: &[Type<'ctx>], results: &[Type<'ctx>]| -> Result<()> {
                if env.module_contains_call_to(name)? {
                    env.declare_private_extern_function(name, inputs, results)?;
                }
                Ok(())
            };
        let bool_type = env.bool_type();
        let felt_type = env.felt_type();
        let index_type = env.index_type();

        maybe_declare(READ_FROM_ROM_EXTERN, &[felt_type], &[felt_type, felt_type])?;
        maybe_declare(READ_FROM_MEMORY_SUBTREE_EXTERN, &[index_type], &[felt_type])?;
        maybe_declare(
            WRITE_TO_MEMORY_SUBTREE_EXTERN,
            &[index_type, felt_type],
            &[],
        )?;
        maybe_declare(
            READ_ORACLE_FIELD_EXTERN,
            &[felt_type, felt_type, felt_type, felt_type],
            &[felt_type],
        )?;
        maybe_declare(
            READ_ORACLE_BOOL_EXTERN,
            &[felt_type, felt_type, felt_type],
            &[bool_type],
        )?;
        maybe_declare(
            READ_ORACLE_U8_EXTERN,
            &[felt_type, felt_type, felt_type],
            &[felt_type],
        )?;
        maybe_declare(
            READ_ORACLE_U16_EXTERN,
            &[felt_type, felt_type, felt_type],
            &[felt_type],
        )?;
        maybe_declare(
            READ_ORACLE_U32_EXTERN,
            &[felt_type, felt_type, felt_type],
            &[felt_type, felt_type],
        )?;
        maybe_declare(
            READ_OP_TYPE_BITMASK_EXTERN,
            &[felt_type],
            &[felt_type, felt_type],
        )?;
        Ok(())
    }

    /// Emit LLZK operations that reconstruct witness columns inside a struct `@compute` function.
    pub fn emit_compute<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<()> {
        let has_runtime_memory_reads = self.has_runtime_memory_reads(vars);
        let self_value = builder.get_compute_self_value()?;
        if vars.has_compiled_storage() {
            vars.seed_compute_compiled_inputs(
                builder,
                self_value,
                &self.compiled.variable_mapping,
            )?;
        }
        let mut expr_idx = 0usize;
        // Keep the latest materialized value for each logical variable across SSA blocks.
        //
        // Some witness dumps write the two limbs of one logical register in different blocks.
        // Register-valued LLZK members are rebuilt as whole arrays, so later limb writes must be
        // able to see earlier writes regardless of block boundaries.
        let mut latest_var_values = HashMap::new();
        for block in &self.ssa {
            let mut lowering = ComputeLowering::new(
                builder,
                vars,
                self_value,
                &self.compiled.variable_mapping,
                &self.compiled.witness_layout.width_3_lookups,
                &self.substitutions,
                &self.special_csr_properties,
                has_runtime_memory_reads,
                block,
                &mut latest_var_values,
            );

            for expr in block {
                lowering.set_current_expr_index(expr_idx);
                builder.with_semantic_location(SemanticLocation::compute_ssa(expr_idx), || {
                    expr.emit_compute(&mut lowering)
                })?;
                expr_idx += 1;
            }
        }
        Ok(())
    }

    /// Conservatively detect whether any emitted SSA path will read a compiled memory-subtree
    /// column through the LLZK runtime hook.
    ///
    /// The witness contains writes that seed memory with certain input variables.
    /// If there are no memory reads, however, we know that no seeded memory locations will be
    /// read, so we are free to omit them for the sake of the this particular circuit.
    ///
    /// The scan intentionally over-approximates. If it is unsure, it reports `true` and keeps the
    /// write.
    fn has_runtime_memory_reads(&self, vars: &StructVars<F>) -> bool {
        self.ssa
            .iter()
            .flatten()
            .any(|expr| expr.uses_runtime_memory(&self.compiled.variable_mapping, vars))
    }
}

fn collect_raw_expression_usage<F: FieldInfo>(
    expr: &RawExpression<F>,
    usage: &mut WitnessVariableUsage,
) {
    match expr {
        RawExpression::Bool(expr) => collect_bool_expression_usage(expr, usage),
        RawExpression::Field(expr) => collect_field_expression_usage(expr, usage),
        RawExpression::Integer(expr) => collect_integer_expression_usage(expr, usage),
        RawExpression::PerformLookup { .. }
        | RawExpression::MaybePerformLookup { .. }
        | RawExpression::AccessLookup { .. } => {}
        RawExpression::WriteVariable {
            into_variable,
            source_subexpr,
            ..
        } => {
            usage.write_vars.insert(*into_variable);
            collect_typed_expression_usage(source_subexpr, usage);
        }
    }
}

fn collect_typed_expression_usage<F: FieldInfo>(
    expr: &Expression<F>,
    usage: &mut WitnessVariableUsage,
) {
    match expr {
        Expression::Bool(expr) => collect_bool_expression_usage(expr, usage),
        Expression::Field(expr) => collect_field_expression_usage(expr, usage),
        Expression::U8(expr) | Expression::U16(expr) | Expression::U32(expr) => {
            collect_integer_expression_usage(expr, usage)
        }
    }
}

fn collect_field_expression_usage<F: FieldInfo>(
    expr: &FieldNodeExpression<F>,
    usage: &mut WitnessVariableUsage,
) {
    match expr {
        FieldNodeExpression::Place(variable) => {
            usage.read_vars.insert(*variable);
        }
        FieldNodeExpression::SubExpression(..)
        | FieldNodeExpression::Constant(..)
        | FieldNodeExpression::OracleValue { .. }
        | FieldNodeExpression::LookupOutput { .. }
        | FieldNodeExpression::MaybeLookupOutput { .. } => {}
        FieldNodeExpression::FromInteger(inner) => {
            collect_integer_expression_usage(inner, usage);
        }
        FieldNodeExpression::InverseUnchecked(inner)
        | FieldNodeExpression::InverseOrZero(inner) => {
            collect_field_expression_usage(inner, usage);
        }
        FieldNodeExpression::FromMask(inner) => collect_bool_expression_usage(inner, usage),
        FieldNodeExpression::Add { lhs, rhs }
        | FieldNodeExpression::Sub { lhs, rhs }
        | FieldNodeExpression::Mul { lhs, rhs } => {
            collect_field_expression_usage(lhs, usage);
            collect_field_expression_usage(rhs, usage);
        }
        FieldNodeExpression::AddProduct {
            additive_term,
            mul_0,
            mul_1,
        } => {
            collect_field_expression_usage(additive_term, usage);
            collect_field_expression_usage(mul_0, usage);
            collect_field_expression_usage(mul_1, usage);
        }
        FieldNodeExpression::Select {
            selector,
            if_true,
            if_false,
        } => {
            collect_bool_expression_usage(selector, usage);
            collect_field_expression_usage(if_true, usage);
            collect_field_expression_usage(if_false, usage);
        }
    }
}

fn collect_bool_expression_usage<F: FieldInfo>(
    expr: &BoolNodeExpression<F>,
    usage: &mut WitnessVariableUsage,
) {
    match expr {
        BoolNodeExpression::Place(variable) => {
            usage.read_vars.insert(*variable);
        }
        BoolNodeExpression::SubExpression(..)
        | BoolNodeExpression::Constant(..)
        | BoolNodeExpression::OracleValue { .. } => {}
        BoolNodeExpression::FromGenericInteger(inner) => {
            collect_integer_expression_usage(inner, usage);
        }
        BoolNodeExpression::FromGenericIntegerEquality { lhs, rhs }
        | BoolNodeExpression::FromGenericIntegerCarry { lhs, rhs }
        | BoolNodeExpression::FromGenericIntegerBorrow { lhs, rhs } => {
            collect_integer_expression_usage(lhs, usage);
            collect_integer_expression_usage(rhs, usage);
        }
        BoolNodeExpression::FromField(inner) => collect_field_expression_usage(inner, usage),
        BoolNodeExpression::FromFieldEquality { lhs, rhs } => {
            collect_field_expression_usage(lhs, usage);
            collect_field_expression_usage(rhs, usage);
        }
        BoolNodeExpression::And { lhs, rhs } | BoolNodeExpression::Or { lhs, rhs } => {
            collect_bool_expression_usage(lhs, usage);
            collect_bool_expression_usage(rhs, usage);
        }
        BoolNodeExpression::Select {
            selector,
            if_true,
            if_false,
        } => {
            collect_bool_expression_usage(selector, usage);
            collect_bool_expression_usage(if_true, usage);
            collect_bool_expression_usage(if_false, usage);
        }
        BoolNodeExpression::Negate(inner) => collect_bool_expression_usage(inner, usage),
    }
}

fn collect_integer_expression_usage<F: FieldInfo>(
    expr: &FixedWidthIntegerNodeExpression<F>,
    usage: &mut WitnessVariableUsage,
) {
    match expr {
        FixedWidthIntegerNodeExpression::U8Place(variable)
        | FixedWidthIntegerNodeExpression::U16Place(variable) => {
            usage.read_vars.insert(*variable);
        }
        FixedWidthIntegerNodeExpression::U8SubExpression(..)
        | FixedWidthIntegerNodeExpression::U16SubExpression(..)
        | FixedWidthIntegerNodeExpression::U32SubExpression(..)
        | FixedWidthIntegerNodeExpression::U32OracleValue { .. }
        | FixedWidthIntegerNodeExpression::U16OracleValue { .. }
        | FixedWidthIntegerNodeExpression::U8OracleValue { .. }
        | FixedWidthIntegerNodeExpression::ConstantU8(..)
        | FixedWidthIntegerNodeExpression::ConstantU16(..)
        | FixedWidthIntegerNodeExpression::ConstantU32(..) => {}
        FixedWidthIntegerNodeExpression::U32FromMask(inner) => {
            collect_bool_expression_usage(inner, usage);
        }
        FixedWidthIntegerNodeExpression::U32FromField(inner) => {
            collect_field_expression_usage(inner, usage);
        }
        FixedWidthIntegerNodeExpression::WidenFromU8(inner)
        | FixedWidthIntegerNodeExpression::WidenFromU16(inner)
        | FixedWidthIntegerNodeExpression::TruncateFromU16(inner)
        | FixedWidthIntegerNodeExpression::TruncateFromU32(inner)
        | FixedWidthIntegerNodeExpression::I32FromU32(inner)
        | FixedWidthIntegerNodeExpression::U32FromI32(inner)
        | FixedWidthIntegerNodeExpression::WrappingShl { lhs: inner, .. }
        | FixedWidthIntegerNodeExpression::WrappingShr { lhs: inner, .. }
        | FixedWidthIntegerNodeExpression::BinaryNot(inner) => {
            collect_integer_expression_usage(inner, usage);
        }
        FixedWidthIntegerNodeExpression::WrappingAdd { lhs, rhs }
        | FixedWidthIntegerNodeExpression::WrappingSub { lhs, rhs }
        | FixedWidthIntegerNodeExpression::MulLow { lhs, rhs }
        | FixedWidthIntegerNodeExpression::MulHigh { lhs, rhs }
        | FixedWidthIntegerNodeExpression::DivAssumeNonzero { lhs, rhs }
        | FixedWidthIntegerNodeExpression::RemAssumeNonzero { lhs, rhs }
        | FixedWidthIntegerNodeExpression::SignedDivAssumeNonzeroNoOverflowBits { lhs, rhs }
        | FixedWidthIntegerNodeExpression::SignedRemAssumeNonzeroNoOverflowBits { lhs, rhs }
        | FixedWidthIntegerNodeExpression::SignedMulLowBits { lhs, rhs }
        | FixedWidthIntegerNodeExpression::SignedMulHighBits { lhs, rhs }
        | FixedWidthIntegerNodeExpression::SignedByUnsignedMulLowBits { lhs, rhs }
        | FixedWidthIntegerNodeExpression::SignedByUnsignedMulHighBits { lhs, rhs }
        | FixedWidthIntegerNodeExpression::BinaryAnd { lhs, rhs }
        | FixedWidthIntegerNodeExpression::BinaryOr { lhs, rhs }
        | FixedWidthIntegerNodeExpression::BinaryXor { lhs, rhs } => {
            collect_integer_expression_usage(lhs, usage);
            collect_integer_expression_usage(rhs, usage);
        }
        FixedWidthIntegerNodeExpression::AddProduct {
            additive_term,
            mul_0,
            mul_1,
        } => {
            collect_integer_expression_usage(additive_term, usage);
            collect_integer_expression_usage(mul_0, usage);
            collect_integer_expression_usage(mul_1, usage);
        }
        FixedWidthIntegerNodeExpression::Select {
            selector,
            if_true,
            if_false,
        } => {
            collect_bool_expression_usage(selector, usage);
            collect_integer_expression_usage(if_true, usage);
            collect_integer_expression_usage(if_false, usage);
        }
        FixedWidthIntegerNodeExpression::LowestBits { value, .. } => {
            collect_integer_expression_usage(value, usage);
        }
    }
}

#[derive(Clone, Copy)]
struct U32Parts<'ctx, 'sco> {
    low: Value<'ctx, 'sco>,
    high: Value<'ctx, 'sco>,
}

#[derive(Clone, Copy)]
enum IntegerValue<'ctx, 'sco> {
    U8(Value<'ctx, 'sco>),
    U16(Value<'ctx, 'sco>),
    U32(U32Parts<'ctx, 'sco>),
}

impl<'ctx, 'sco> IntegerValue<'ctx, 'sco> {
    fn bit_width(&self) -> u32 {
        match self {
            Self::U8(_) => 8,
            Self::U16(_) => 16,
            Self::U32(_) => 32,
        }
    }
}

#[derive(Clone, Copy)]
enum ComputedValue<'ctx, 'sco> {
    Field(Value<'ctx, 'sco>),
    Bool(Value<'ctx, 'sco>),
    Integer(IntegerValue<'ctx, 'sco>),
}

/// The translated result of a [`RawExpression`].
enum SsaSlot<'ctx, 'sco> {
    Value(ComputedValue<'ctx, 'sco>),
    Lookup(Vec<Value<'ctx, 'sco>>),
    Unit,
}

/// Returns whether evaluating this SSA node would require reading the compiled
/// [`ColumnAddress::MemorySubtree`] through `read_from_memory_subtree`.
///
/// ROM hooks, oracle hooks, and lookup tuples do not count here. The only
/// consumer of this trait is the seed-write omission check, which only needs to know whether the
/// emitted `@compute` body ever reads back **mutable** memory-subtree state.
trait UsesRuntimeMemory<F: FieldInfo> {
    fn uses_runtime_memory(
        &self,
        variable_mapping: &BTreeMap<Variable, ColumnAddress>,
        vars: &StructVars<F>,
    ) -> bool;
}

impl<F: FieldInfo> UsesRuntimeMemory<F> for Variable {
    fn uses_runtime_memory(
        &self,
        variable_mapping: &BTreeMap<Variable, ColumnAddress>,
        vars: &StructVars<F>,
    ) -> bool {
        matches!(
            variable_mapping.get(self),
            Some(ColumnAddress::MemorySubtree(_))
        ) && !vars.is_compute_exposed(self)
    }
}

impl<F: FieldInfo> UsesRuntimeMemory<F> for Expression<F> {
    fn uses_runtime_memory(
        &self,
        variable_mapping: &BTreeMap<Variable, ColumnAddress>,
        vars: &StructVars<F>,
    ) -> bool {
        match self {
            Expression::Bool(expr) => expr.uses_runtime_memory(variable_mapping, vars),
            Expression::Field(expr) => expr.uses_runtime_memory(variable_mapping, vars),
            Expression::U8(expr) | Expression::U16(expr) | Expression::U32(expr) => {
                expr.uses_runtime_memory(variable_mapping, vars)
            }
        }
    }
}

impl<F: FieldInfo> UsesRuntimeMemory<F> for FieldNodeExpression<F> {
    fn uses_runtime_memory(
        &self,
        variable_mapping: &BTreeMap<Variable, ColumnAddress>,
        vars: &StructVars<F>,
    ) -> bool {
        match self {
            FieldNodeExpression::Place(variable) => {
                variable.uses_runtime_memory(variable_mapping, vars)
            }
            FieldNodeExpression::SubExpression(..)
            | FieldNodeExpression::Constant(..)
            | FieldNodeExpression::OracleValue { .. }
            | FieldNodeExpression::LookupOutput { .. }
            | FieldNodeExpression::MaybeLookupOutput { .. } => {
                // These variants reuse an already-lowered SSA slot, literal, oracle hook, or
                // lookup tuple. None of them performs a fresh memory-subtree read on its own.
                false
            }
            FieldNodeExpression::FromInteger(expr) => {
                expr.uses_runtime_memory(variable_mapping, vars)
            }
            FieldNodeExpression::FromMask(expr) => expr.uses_runtime_memory(variable_mapping, vars),
            FieldNodeExpression::Add { lhs, rhs }
            | FieldNodeExpression::Sub { lhs, rhs }
            | FieldNodeExpression::Mul { lhs, rhs } => {
                lhs.uses_runtime_memory(variable_mapping, vars)
                    || rhs.uses_runtime_memory(variable_mapping, vars)
            }
            FieldNodeExpression::AddProduct {
                additive_term,
                mul_0,
                mul_1,
            } => {
                additive_term.uses_runtime_memory(variable_mapping, vars)
                    || mul_0.uses_runtime_memory(variable_mapping, vars)
                    || mul_1.uses_runtime_memory(variable_mapping, vars)
            }
            FieldNodeExpression::Select {
                selector,
                if_true,
                if_false,
            } => {
                selector.uses_runtime_memory(variable_mapping, vars)
                    || if_true.uses_runtime_memory(variable_mapping, vars)
                    || if_false.uses_runtime_memory(variable_mapping, vars)
            }
            FieldNodeExpression::InverseUnchecked(expr)
            | FieldNodeExpression::InverseOrZero(expr) => {
                expr.uses_runtime_memory(variable_mapping, vars)
            }
        }
    }
}

impl<F: FieldInfo> UsesRuntimeMemory<F> for BoolNodeExpression<F> {
    fn uses_runtime_memory(
        &self,
        variable_mapping: &BTreeMap<Variable, ColumnAddress>,
        vars: &StructVars<F>,
    ) -> bool {
        match self {
            BoolNodeExpression::Place(variable) => {
                variable.uses_runtime_memory(variable_mapping, vars)
            }
            BoolNodeExpression::SubExpression(..)
            | BoolNodeExpression::Constant(..)
            | BoolNodeExpression::OracleValue { .. } => {
                // Boolean subexpressions, literals, and oracle hooks do not read the compiled
                // memory subtree directly.
                false
            }
            BoolNodeExpression::FromGenericInteger(expr) => {
                expr.uses_runtime_memory(variable_mapping, vars)
            }
            BoolNodeExpression::FromGenericIntegerEquality { lhs, rhs }
            | BoolNodeExpression::FromGenericIntegerCarry { lhs, rhs }
            | BoolNodeExpression::FromGenericIntegerBorrow { lhs, rhs } => {
                lhs.uses_runtime_memory(variable_mapping, vars)
                    || rhs.uses_runtime_memory(variable_mapping, vars)
            }
            BoolNodeExpression::FromField(expr) => expr.uses_runtime_memory(variable_mapping, vars),
            BoolNodeExpression::FromFieldEquality { lhs, rhs } => {
                lhs.uses_runtime_memory(variable_mapping, vars)
                    || rhs.uses_runtime_memory(variable_mapping, vars)
            }
            BoolNodeExpression::And { lhs, rhs } | BoolNodeExpression::Or { lhs, rhs } => {
                lhs.uses_runtime_memory(variable_mapping, vars)
                    || rhs.uses_runtime_memory(variable_mapping, vars)
            }
            BoolNodeExpression::Select {
                selector,
                if_true,
                if_false,
            } => {
                selector.uses_runtime_memory(variable_mapping, vars)
                    || if_true.uses_runtime_memory(variable_mapping, vars)
                    || if_false.uses_runtime_memory(variable_mapping, vars)
            }
            BoolNodeExpression::Negate(expr) => expr.uses_runtime_memory(variable_mapping, vars),
        }
    }
}

impl<F: FieldInfo> UsesRuntimeMemory<F> for FixedWidthIntegerNodeExpression<F> {
    fn uses_runtime_memory(
        &self,
        variable_mapping: &BTreeMap<Variable, ColumnAddress>,
        vars: &StructVars<F>,
    ) -> bool {
        match self {
            FixedWidthIntegerNodeExpression::U8Place(variable)
            | FixedWidthIntegerNodeExpression::U16Place(variable) => {
                variable.uses_runtime_memory(variable_mapping, vars)
            }
            FixedWidthIntegerNodeExpression::U8SubExpression(..)
            | FixedWidthIntegerNodeExpression::U16SubExpression(..)
            | FixedWidthIntegerNodeExpression::U32SubExpression(..)
            | FixedWidthIntegerNodeExpression::U32OracleValue { .. }
            | FixedWidthIntegerNodeExpression::U16OracleValue { .. }
            | FixedWidthIntegerNodeExpression::U8OracleValue { .. }
            | FixedWidthIntegerNodeExpression::ConstantU8(..)
            | FixedWidthIntegerNodeExpression::ConstantU16(..)
            | FixedWidthIntegerNodeExpression::ConstantU32(..) => {
                // Integer temporaries, constants, and oracle hooks do not perform a fresh
                // memory-subtree read here.
                false
            }
            FixedWidthIntegerNodeExpression::U32FromMask(expr) => {
                expr.uses_runtime_memory(variable_mapping, vars)
            }
            FixedWidthIntegerNodeExpression::U32FromField(expr) => {
                expr.uses_runtime_memory(variable_mapping, vars)
            }
            FixedWidthIntegerNodeExpression::WidenFromU8(expr)
            | FixedWidthIntegerNodeExpression::WidenFromU16(expr)
            | FixedWidthIntegerNodeExpression::TruncateFromU16(expr)
            | FixedWidthIntegerNodeExpression::TruncateFromU32(expr)
            | FixedWidthIntegerNodeExpression::I32FromU32(expr)
            | FixedWidthIntegerNodeExpression::U32FromI32(expr)
            | FixedWidthIntegerNodeExpression::BinaryNot(expr) => {
                expr.uses_runtime_memory(variable_mapping, vars)
            }
            FixedWidthIntegerNodeExpression::Select {
                selector,
                if_true,
                if_false,
            } => {
                selector.uses_runtime_memory(variable_mapping, vars)
                    || if_true.uses_runtime_memory(variable_mapping, vars)
                    || if_false.uses_runtime_memory(variable_mapping, vars)
            }
            FixedWidthIntegerNodeExpression::WrappingAdd { lhs, rhs }
            | FixedWidthIntegerNodeExpression::WrappingSub { lhs, rhs }
            | FixedWidthIntegerNodeExpression::BinaryAnd { lhs, rhs }
            | FixedWidthIntegerNodeExpression::BinaryOr { lhs, rhs }
            | FixedWidthIntegerNodeExpression::BinaryXor { lhs, rhs }
            | FixedWidthIntegerNodeExpression::MulLow { lhs, rhs }
            | FixedWidthIntegerNodeExpression::MulHigh { lhs, rhs }
            | FixedWidthIntegerNodeExpression::DivAssumeNonzero { lhs, rhs }
            | FixedWidthIntegerNodeExpression::RemAssumeNonzero { lhs, rhs }
            | FixedWidthIntegerNodeExpression::SignedDivAssumeNonzeroNoOverflowBits { lhs, rhs }
            | FixedWidthIntegerNodeExpression::SignedRemAssumeNonzeroNoOverflowBits { lhs, rhs }
            | FixedWidthIntegerNodeExpression::SignedMulLowBits { lhs, rhs }
            | FixedWidthIntegerNodeExpression::SignedMulHighBits { lhs, rhs }
            | FixedWidthIntegerNodeExpression::SignedByUnsignedMulLowBits { lhs, rhs }
            | FixedWidthIntegerNodeExpression::SignedByUnsignedMulHighBits { lhs, rhs } => {
                lhs.uses_runtime_memory(variable_mapping, vars)
                    || rhs.uses_runtime_memory(variable_mapping, vars)
            }
            FixedWidthIntegerNodeExpression::WrappingShl { lhs, .. }
            | FixedWidthIntegerNodeExpression::WrappingShr { lhs, .. } => {
                lhs.uses_runtime_memory(variable_mapping, vars)
            }
            FixedWidthIntegerNodeExpression::LowestBits { value, .. } => {
                value.uses_runtime_memory(variable_mapping, vars)
            }
            FixedWidthIntegerNodeExpression::AddProduct {
                additive_term,
                mul_0,
                mul_1,
            } => {
                additive_term.uses_runtime_memory(variable_mapping, vars)
                    || mul_0.uses_runtime_memory(variable_mapping, vars)
                    || mul_1.uses_runtime_memory(variable_mapping, vars)
            }
        }
    }
}

impl<F: FieldInfo> UsesRuntimeMemory<F> for RawExpression<F> {
    fn uses_runtime_memory(
        &self,
        variable_mapping: &BTreeMap<Variable, ColumnAddress>,
        vars: &StructVars<F>,
    ) -> bool {
        match self {
            RawExpression::Bool(expr) => expr.uses_runtime_memory(variable_mapping, vars),
            RawExpression::Field(expr) => expr.uses_runtime_memory(variable_mapping, vars),
            RawExpression::Integer(expr) => expr.uses_runtime_memory(variable_mapping, vars),
            RawExpression::AccessLookup { .. }
            | RawExpression::PerformLookup { .. }
            | RawExpression::MaybePerformLookup { .. } => {
                // Lookup nodes operate on previously-lowered SSA inputs. If one of those inputs
                // came from the memory subtree, the producer expression for that input already
                // reports it. The lookup node itself may still use ROM or oracle hooks, but it
                // does not issue `read_from_memory_subtree`.
                false
            }
            RawExpression::WriteVariable {
                into_variable,
                source_subexpr,
                condition_subexpr_idx,
            } => {
                source_subexpr.uses_runtime_memory(variable_mapping, vars)
                    || (condition_subexpr_idx.is_some()
                        && matches!(
                            variable_mapping.get(into_variable),
                            Some(ColumnAddress::MemorySubtree(_))
                        )
                        && !vars.has_member(into_variable))
            }
        }
    }
}

/// Lowers one SSA block into LLZK ops while keeping a slot-per-subexpression cache.
///
/// `SubExpression(..)` nodes contain an index to look up the previous SSA slots to
/// reference previously computed values, so we cache that structure of values in this lowering
/// struct.
struct ComputeLowering<'a, 'ctx: 'sco, 'sco, F: FieldInfo> {
    builder: &'a OpsBuilder<'ctx, 'sco, F>,
    vars: &'a StructVars<F>,
    self_value: Value<'ctx, 'sco>,
    variable_mapping: &'a BTreeMap<Variable, ColumnAddress>,
    lookup_sets: &'a [LookupSetDescription<F, COMMON_TABLE_WIDTH>],
    substitutions: &'a HashMap<(Placeholder, usize), Variable>,
    special_csr_properties: &'a Option<SpecialCsrPropertiesMetadata>,
    has_runtime_memory_reads: bool,
    block: &'a [RawExpression<F>],
    current_expr_index: usize,
    slots: Vec<SsaSlot<'ctx, 'sco>>,
    slot_input_origins: Vec<Option<Variable>>,
    slot_u32_input_origins: Vec<Option<[Variable; 2]>>,
    /// The most recently materialized felt value for each logical variable in `@compute`.
    ///
    /// This is not an optimization cache for common subexpressions. It is the backend's local
    /// model of SSA-over-mutable-storage:
    /// - witness SSA can write the same logical variable multiple times,
    /// - LLZK struct members are mutable storage slots, and
    /// - register-valued members are rebuilt as whole two-limb arrays on every write.
    ///
    /// When the low and high limbs of one logical register are written separately, the second
    /// write must see the first limb's latest value so it can rebuild the full register. Reading
    /// the struct member directly is not sufficient, because the write that produced the latest
    /// value may not dominate through the emitted mutable LLZK storage shape or may live in a
    /// different witness SSA block.
    latest_var_values: &'a mut HashMap<Variable, Value<'ctx, 'sco>>,
}

impl<'a, 'ctx: 'sco, 'sco, F: FieldInfo> Deref for ComputeLowering<'a, 'ctx, 'sco, F> {
    type Target = OpsBuilder<'ctx, 'sco, F>;

    fn deref(&self) -> &Self::Target {
        self.builder
    }
}

impl<'a, 'ctx: 'sco, 'sco, F: FieldInfo> ComputeLowering<'a, 'ctx, 'sco, F> {
    /// Create a fresh lowering state for one SSA block.
    #[allow(clippy::too_many_arguments)]
    fn new(
        builder: &'a OpsBuilder<'ctx, 'sco, F>,
        vars: &'a StructVars<F>,
        self_value: Value<'ctx, 'sco>,
        variable_mapping: &'a BTreeMap<Variable, ColumnAddress>,
        lookup_sets: &'a [LookupSetDescription<F, COMMON_TABLE_WIDTH>],
        substitutions: &'a HashMap<(Placeholder, usize), Variable>,
        special_csr_properties: &'a Option<SpecialCsrPropertiesMetadata>,
        has_runtime_memory_reads: bool,
        block: &'a [RawExpression<F>],
        latest_var_values: &'a mut HashMap<Variable, Value<'ctx, 'sco>>,
    ) -> Self {
        Self {
            builder,
            vars,
            self_value,
            variable_mapping,
            lookup_sets,
            substitutions,
            special_csr_properties,
            has_runtime_memory_reads,
            block,
            current_expr_index: 0,
            slots: Vec::new(),
            slot_input_origins: Vec::new(),
            slot_u32_input_origins: Vec::new(),
            latest_var_values,
        }
    }

    /// Record the zero-based flattened SSA expression index currently being lowered.
    fn set_current_expr_index(&mut self, current_expr_index: usize) {
        self.current_expr_index = current_expr_index;
    }

    /// Run a runtime hook under a dedicated `llzk://compute/runtime` location derived from the
    /// current SSA expression.
    fn with_runtime_location<T>(
        &self,
        kind: ComputeRuntimeHookKind,
        f: impl FnOnce() -> Result<T>,
    ) -> Result<T> {
        self.with_semantic_location(
            SemanticLocation::compute_runtime(kind.debug_path(), self.current_expr_index),
            f,
        )
    }

    /// Append one SSA slot to the block-local cache.
    fn push_slot(
        &mut self,
        slot: SsaSlot<'ctx, 'sco>,
        input_origin: Option<Variable>,
        u32_input_origin: Option<[Variable; 2]>,
    ) {
        self.slots.push(slot);
        self.slot_input_origins.push(input_origin);
        self.slot_u32_input_origins.push(u32_input_origin);
    }

    /// Materialize a write-back either into the returned witness struct or into the external
    /// memory runtime.
    ///
    /// The one-row compiler may place some boundary variables in the compiled `MemorySubtree`
    /// even though LLZK also exposes them as public outputs or internal struct members. When that
    /// happens, `@compute` should update the struct member first so the returned LLZK value agrees
    /// with what `@constrain` sees. Only variables that have no struct representation are routed
    /// through the generic memory runtime hook.
    fn lower_write(
        &mut self,
        into_variable: &Variable,
        source_subexpr: &Expression<F>,
        condition_subexpr_idx: Option<usize>,
    ) -> Result<()> {
        let compiled_address = self.variable_mapping.get(into_variable).copied();
        if self.vars.has_compute_input(into_variable) && !self.vars.has_member(into_variable) {
            if self.strict_store_origin_for_expression(source_subexpr) == Some(*into_variable) {
                // Some witness programs redundantly "write" an input-backed boundary variable back
                // to itself. That is a no-op regardless of any guard: if the guard is false we do
                // nothing, and if the guard is true we would still store the exact same boundary
                // value. Skip those cases entirely so `@compute` does not accumulate vacuous
                // `bool.assert %arg == %arg` checks.
                if self.vars.has_compiled_storage() {
                    if let Some(
                        ColumnAddress::WitnessSubtree(_) | ColumnAddress::MemorySubtree(_),
                    ) = compiled_address
                    {
                        let boundary_value = self.vars.get_compute_val(
                            self.builder,
                            self.self_value,
                            into_variable,
                        )?;
                        self.assign_write_targets(into_variable, boundary_value)?;
                    }
                }
                return Ok(());
            }

            if !self.is_legacy_input_backed_write(*into_variable) {
                // Outside of the legacy query-2 shuffle write slot, input-backed writes are just
                // redundant witness-program rematerializations. LLZK models those values as
                // ordinary inputs and does not need a second proof obligation in `@compute`.
                if self.vars.has_compiled_storage() {
                    if let Some(
                        ColumnAddress::WitnessSubtree(_) | ColumnAddress::MemorySubtree(_),
                    ) = compiled_address
                    {
                        let boundary_value = self.vars.get_compute_val(
                            self.builder,
                            self.self_value,
                            into_variable,
                        )?;
                        self.assign_write_targets(into_variable, boundary_value)?;
                    }
                }
                return Ok(());
            }

            // Input-backed boundary values do not need a second storage location inside the
            // returned struct. Instead of silently dropping the write, assert that the value we
            // would have written is the same value already exposed on the LLZK boundary. For a
            // conditional write, the skipped write is valid iff the condition is false or the
            // candidate written value already equals the existing boundary input.
            let location = self.unknown_location();
            let boundary_value =
                self.vars
                    .get_compute_val(self.builder, self.self_value, into_variable)?;
            let written_value = self.expression_to_store_value(source_subexpr)?;

            if let Some(condition_idx) = condition_subexpr_idx {
                let condition = self.slot_as_bool(condition_idx)?;
                let values_eq =
                    self.append_op_with_result(bool::eq(location, written_value, boundary_value)?)?;
                let skipped_write_is_sound = self.append_op_with_result(bool::or(
                    location,
                    self.append_op_with_result(bool::not(location, condition)?)?,
                    values_eq,
                )?)?;
                self.append_bool_assert(
                    location,
                    skipped_write_is_sound,
                    Some("skipped conditional input-backed write must preserve the boundary value"),
                )?;
            } else {
                self.append_assert_equal(
                    location,
                    written_value,
                    boundary_value,
                    Some("skipped input-backed write must match the boundary value"),
                )?;
            }
            return Ok(());
        }

        if self.should_omit_seed_memory_write(
            into_variable,
            source_subexpr,
            condition_subexpr_idx,
        )? {
            return Ok(());
        }

        let mut value = self.expression_to_store_value(source_subexpr)?;
        if let Some(condition_idx) = condition_subexpr_idx {
            let condition = self.slot_as_bool(condition_idx)?;
            let existing = self.current_write_target_value(into_variable)?;
            value = self
                .builder
                .append_select_value(condition, value, existing)?;
        }

        self.assign_write_targets(into_variable, value)
    }

    /// Return `true` when this write is a pure boundary-to-memory seeding copy that can be omitted
    /// without changing the returned LLZK value.
    ///
    /// This only occurs if:
    /// - the target lives in the compiled `MemorySubtree`,
    /// - the write is unconditional,
    /// - the source expression is provably just an explicit `@compute` input value, and
    /// - the whole emitted `@compute` never reads memory-subtree state back.
    fn should_omit_seed_memory_write(
        &self,
        into_variable: &Variable,
        source_subexpr: &Expression<F>,
        condition_subexpr_idx: Option<usize>,
    ) -> Result<bool> {
        if self.has_runtime_memory_reads || condition_subexpr_idx.is_some() {
            Ok(false)
        } else if matches!(
            self.variable_mapping.get(into_variable),
            Some(ColumnAddress::MemorySubtree(_))
        ) {
            Ok(self
                .strict_input_origin_for_expression(source_subexpr)
                .is_some())
        } else {
            Ok(false)
        }
    }

    /// Convert a lowered expression into the felt encoding stored in the LLZK witness struct.
    fn computed_value_to_store(
        &self,
        value: ComputedValue<'ctx, 'sco>,
    ) -> Result<Value<'ctx, 'sco>> {
        match value {
            ComputedValue::Bool(value) => self.append_bool_to_field(value),
            ComputedValue::Field(value) => Ok(value),
            ComputedValue::Integer(value) => self.integer_to_field(value),
        }
    }

    /// Convert a typed SSA reference into the felt-encoded value that the witness struct stores.
    fn expression_to_store_value(&mut self, expr: &Expression<F>) -> Result<Value<'ctx, 'sco>> {
        let value = expr.emit_compute(self)?;
        self.computed_value_to_store(value)
    }

    /// Read the currently materialized value that a conditional write would overwrite.
    ///
    /// This follows the same precedence as write-back:
    /// - logical struct members when present
    /// - compiled witness/memory columns in compiled mode
    /// - runtime memory-subtree storage in logical mode
    ///
    /// We consult `latest_var_values` first because the LLZK storage object may still contain an
    /// older whole-register aggregate. The in-memory cache is the source of truth for the most
    /// recent logical value during one `@compute` lowering pass.
    fn current_write_target_value(&self, variable: &Variable) -> Result<Value<'ctx, 'sco>> {
        if let Some(value) = self.latest_var_values.get(variable).copied() {
            return Ok(value);
        }
        if self.vars.has_member(variable) {
            self.vars
                .get_compute_val(self.builder, self.self_value, variable)
        } else if self.vars.has_compiled_storage() {
            match self.variable_mapping.get(variable).copied() {
                Some(
                    address @ (ColumnAddress::WitnessSubtree(_) | ColumnAddress::MemorySubtree(_)),
                ) => self
                    .vars
                    .get_compute_compiled_column(self.builder, self.self_value, address),
                other => Err(anyhow!(
                    "variable {variable:?} is not exposed to compiled @compute storage (column {other:?})"
                )),
            }
        } else {
            match self.variable_mapping.get(variable).copied() {
                Some(ColumnAddress::MemorySubtree(offset)) => self.read_memory_subtree(offset),
                other => Err(anyhow!(
                    "variable {variable:?} is not exposed to @compute write-back (column {other:?})"
                )),
            }
        }
    }

    /// Write a logical variable everywhere it must live in the emitted `@compute`.
    ///
    /// In compiled mode, logical LLZK members that have compiled witness/memory column mappings
    /// are written through a single path so the logical/public member and its compiled-column
    /// mirror stay synchronized.
    ///
    /// Every successful write also updates `latest_var_values`. That cache is what lets later
    /// writes rebuild register-valued members from the latest logical limbs instead of from a
    /// stale struct aggregate.
    fn assign_write_targets(
        &mut self,
        variable: &Variable,
        value: Value<'ctx, 'sco>,
    ) -> Result<()> {
        if self.vars.has_member(variable) {
            self.vars.assign_compute_member_and_bridge_with_lookup(
                self.builder,
                self.self_value,
                variable,
                value,
                |var| self.latest_var_values.get(var).copied(),
            )?;
            self.latest_var_values.insert(*variable, value);
            return Ok(());
        }

        if self.vars.has_compiled_storage() {
            let result = match self.variable_mapping.get(variable).copied() {
                Some(
                    address @ (ColumnAddress::WitnessSubtree(_) | ColumnAddress::MemorySubtree(_)),
                ) => self.vars.assign_compute_compiled_column(
                    self.builder,
                    self.self_value,
                    address,
                    value,
                ),
                Some(ColumnAddress::OptimizedOut(_)) => Ok(()),
                Some(ColumnAddress::SetupSubtree(..)) => {
                    unreachable!("setup columns are read-only during witness lowering")
                }
                other => Err(anyhow!(
                    "variable {variable:?} is not exposed to compiled @compute storage (column {other:?})"
                )),
            };
            result?;
            self.latest_var_values.insert(*variable, value);
            return Ok(());
        }

        let result = match self.variable_mapping.get(variable).copied() {
            Some(ColumnAddress::MemorySubtree(offset)) => self.write_memory_subtree(offset, value),
            Some(ColumnAddress::SetupSubtree(..)) => {
                unreachable!("setup columns are read-only during witness lowering")
            }
            Some(ColumnAddress::WitnessSubtree(..) | ColumnAddress::OptimizedOut(..)) => self
                .vars
                .assign_compute_member(self.builder, self.self_value, variable, value),
            other => self
                .vars
                .assign_compute_member(self.builder, self.self_value, variable, value)
                .map_err(|_| {
                    anyhow!(
                        "variable {variable:?} is not exposed to @compute write-back (column {other:?})"
                    )
                }),
        };
        result?;
        self.latest_var_values.insert(*variable, value);
        Ok(())
    }

    /// Read `variable` as the felt value currently visible to `@compute`.
    fn read_variable(&self, variable: Variable) -> Result<Value<'ctx, 'sco>> {
        if let Some(value) = self.latest_var_values.get(&variable).copied() {
            return Ok(value);
        }
        if let Some(value) =
            self.vars
                .try_get_compute_val(self.builder, self.self_value, &variable)?
        {
            Ok(value)
        } else if self.vars.has_compiled_storage() {
            match self.variable_mapping.get(&variable) {
                Some(
                    address @ (ColumnAddress::WitnessSubtree(_) | ColumnAddress::MemorySubtree(_)),
                ) => self
                    .vars
                    .get_compute_compiled_column(self.builder, self.self_value, *address),
                other => Err(anyhow!(
                    "variable {variable:?} is not exposed to @compute (column {other:?})"
                )),
            }
        } else {
            match self.variable_mapping.get(&variable) {
                Some(ColumnAddress::MemorySubtree(offset)) => self.read_memory_subtree(*offset),
                other => Err(anyhow!(
                    "variable {variable:?} is not exposed to @compute (column {other:?})"
                )),
            }
        }
    }

    /// Read a compiled memory-subtree column through the LLZK runtime hook.
    fn read_memory_subtree(&self, offset: usize) -> Result<Value<'ctx, 'sco>> {
        if self.vars.has_compiled_storage() {
            return self.vars.get_compute_compiled_column(
                self.builder,
                self.self_value,
                ColumnAddress::MemorySubtree(offset),
            );
        }
        self.with_runtime_location(ComputeRuntimeHookKind::MemoryRead, || {
            let location = self.current_location();
            let index_type = self.index_type();
            let felt_type = self.felt_type();
            let offset = self.get_constant_from_start(index_type, offset as u64)?;
            self.append_call_with_result(
                location,
                READ_FROM_MEMORY_SUBTREE_EXTERN,
                &[offset],
                felt_type,
            )
        })
    }

    /// Write a compiled memory-subtree column through the LLZK runtime hook.
    fn write_memory_subtree(&self, offset: usize, value: Value<'ctx, 'sco>) -> Result<()> {
        if self.vars.has_compiled_storage() {
            return self.vars.assign_compute_compiled_column(
                self.builder,
                self.self_value,
                ColumnAddress::MemorySubtree(offset),
                value,
            );
        }
        self.with_runtime_location(ComputeRuntimeHookKind::MemoryWrite, || {
            let location = self.current_location();
            let index_type = self.index_type();
            let offset = self.get_constant_from_start(index_type, offset as u64)?;
            self.append_call_no_results(location, WRITE_TO_MEMORY_SUBTREE_EXTERN, &[offset, value])
        })
    }

    /// Try to resolve one placeholder limb through the explicit `@compute` boundary arguments.
    ///
    /// Only true LLZK inputs may be read through this path. If a placeholder is aliased to a
    /// struct member/output instead, witness lowering should fail loudly rather than silently
    /// treating that output-backed value as an input again.
    fn try_read_placeholder_input_limb(
        &self,
        placeholder: Placeholder,
        subindex: usize,
    ) -> Result<Option<Value<'ctx, 'sco>>> {
        if let Some(variable) = self.substitutions.get(&(placeholder, subindex)) {
            if self.vars.has_compute_input(variable) {
                self.vars.try_get_compute_input_val(self.builder, variable)
            } else if self.vars.has_member(variable) {
                if placeholder_allows_member_oracle_fallback(placeholder) {
                    Ok(None)
                } else {
                    Err(anyhow!(
                        "placeholder {placeholder:?}[{subindex}] is only exposed as a @compute output/member"
                    ))
                }
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    /// Try to read a boolean placeholder from the existing LLZK inputs before using an oracle
    /// hook.
    fn try_read_bool_placeholder_input(
        &self,
        placeholder: Placeholder,
    ) -> Result<Option<Value<'ctx, 'sco>>> {
        self.try_read_placeholder_input_limb(placeholder, 0)?
            .map(|value| self.append_field_is_nonzero(value))
            .transpose()
    }

    /// Try to read a 32-bit placeholder from the existing LLZK inputs before using an oracle
    /// hook.
    fn try_read_u32_placeholder_input(
        &self,
        placeholder: Placeholder,
    ) -> Result<Option<U32Parts<'ctx, 'sco>>> {
        let Some(low_var) = self.substitutions.get(&(placeholder, 0)) else {
            return Ok(None);
        };
        let Some(high_var) = self.substitutions.get(&(placeholder, 1)) else {
            return Err(anyhow!(
                "placeholder {placeholder:?} is missing its high limb substitution"
            ));
        };

        if (self.vars.has_member(low_var) || self.vars.has_member(high_var))
            && placeholder_allows_member_oracle_fallback(placeholder)
        {
            return Ok(None);
        }

        if self.vars.has_member(low_var)
            || self.vars.has_member(high_var)
            || !self.vars.has_compute_input(low_var)
            || !self.vars.has_compute_input(high_var)
        {
            return Err(anyhow!(
                "placeholder {placeholder:?} is only exposed as a @compute output/member"
            ));
        }

        let low = self.vars.try_get_compute_input_val(self.builder, low_var)?;
        let high = self
            .vars
            .try_get_compute_input_val(self.builder, high_var)?;
        match (low, high) {
            (Some(low), Some(high)) => Ok(Some(U32Parts { low, high })),
            (None, None) => Ok(None),
            (Some(_), None) | (None, Some(_)) => Err(anyhow!(
                "placeholder {placeholder:?} is only partially exposed as a @compute input"
            )),
        }
    }

    /// Return the LLZK type used for oracle hook metadata arguments.
    ///
    /// The backend keeps the placeholder encoding stable at the Rust level, but the emitted ABI
    /// still needs to use LLZK value types. `function.def` cannot use `i64` arguments, so we
    /// materialize the `(kind, arg0, arg1, subindex)` metadata as felt constants instead.
    #[inline]
    fn oracle_abi_type(&self) -> Type<'ctx> {
        self.felt_type()
    }

    /// Materialize one metadata constant for an oracle hook call.
    fn oracle_abi_constant(&self, value: u64) -> Result<Value<'ctx, 'sco>> {
        self.get_constant_from_start(self.oracle_abi_type(), value)
    }

    /// Convert a [`Placeholder`] into the three metadata arguments passed to oracle hooks.
    fn oracle_placeholder_args(&self, placeholder: Placeholder) -> Result<[Value<'ctx, 'sco>; 3]> {
        let encoded = encode_oracle_placeholder(placeholder);
        Ok([
            self.oracle_abi_constant(encoded.kind)?,
            self.oracle_abi_constant(encoded.arg0)?,
            self.oracle_abi_constant(encoded.arg1)?,
        ])
    }

    /// Read a field-valued oracle placeholder through the LLZK runtime hook.
    fn read_field_oracle(
        &self,
        placeholder: Placeholder,
        subindex: usize,
    ) -> Result<Value<'ctx, 'sco>> {
        if let Some(value) = self.try_read_placeholder_input_limb(placeholder, subindex)? {
            return Ok(value);
        }

        self.with_runtime_location(ComputeRuntimeHookKind::OracleField, || {
            let location = self.current_location();
            let felt_type = self.felt_type();
            let [kind, arg0, arg1] = self.oracle_placeholder_args(placeholder)?;
            let subindex = self.oracle_abi_constant(subindex as u64)?;
            self.append_call_with_result(
                location,
                READ_ORACLE_FIELD_EXTERN,
                &[kind, arg0, arg1, subindex],
                felt_type,
            )
        })
    }

    /// Read a boolean oracle placeholder through the LLZK runtime hook.
    fn read_bool_oracle(&self, placeholder: Placeholder) -> Result<Value<'ctx, 'sco>> {
        if let Some(value) = self.try_read_bool_placeholder_input(placeholder)? {
            return Ok(value);
        }

        self.with_runtime_location(ComputeRuntimeHookKind::OracleBool, || {
            let location = self.current_location();
            let bool_type = self.bool_type();
            let [kind, arg0, arg1] = self.oracle_placeholder_args(placeholder)?;
            self.append_call_with_result(
                location,
                READ_ORACLE_BOOL_EXTERN,
                &[kind, arg0, arg1],
                bool_type,
            )
        })
    }

    /// Read an 8-bit oracle placeholder through the LLZK runtime hook.
    fn read_u8_oracle(&self, placeholder: Placeholder) -> Result<Value<'ctx, 'sco>> {
        if let Some(value) = self.try_read_placeholder_input_limb(placeholder, 0)? {
            return Ok(value);
        }

        self.with_runtime_location(ComputeRuntimeHookKind::OracleU8, || {
            let location = self.current_location();
            let felt_type = self.felt_type();
            let [kind, arg0, arg1] = self.oracle_placeholder_args(placeholder)?;
            self.append_call_with_result(
                location,
                READ_ORACLE_U8_EXTERN,
                &[kind, arg0, arg1],
                felt_type,
            )
        })
    }

    /// Read a 16-bit oracle placeholder through the LLZK runtime hook.
    fn read_u16_oracle(&self, placeholder: Placeholder) -> Result<Value<'ctx, 'sco>> {
        if let Some(value) = self.try_read_placeholder_input_limb(placeholder, 0)? {
            return Ok(value);
        }

        self.with_runtime_location(ComputeRuntimeHookKind::OracleU16, || {
            let location = self.current_location();
            let felt_type = self.felt_type();
            let [kind, arg0, arg1] = self.oracle_placeholder_args(placeholder)?;
            self.append_call_with_result(
                location,
                READ_ORACLE_U16_EXTERN,
                &[kind, arg0, arg1],
                felt_type,
            )
        })
    }

    /// Read a 32-bit oracle placeholder through the LLZK runtime hook.
    fn read_u32_oracle(&self, placeholder: Placeholder) -> Result<U32Parts<'ctx, 'sco>> {
        if let Some(value) = self.try_read_u32_placeholder_input(placeholder)? {
            return Ok(value);
        }

        self.with_runtime_location(ComputeRuntimeHookKind::OracleU32, || {
            let location = self.current_location();
            let felt_type = self.felt_type();
            let [low, high] = {
                let [kind, arg0, arg1] = self.oracle_placeholder_args(placeholder)?;
                self.append_call::<2>(
                    location,
                    READ_ORACLE_U32_EXTERN,
                    &[kind, arg0, arg1],
                    &[felt_type, felt_type],
                )?
            };
            Ok(U32Parts { low, high })
        })
    }

    /// Convert a 32-bit limb pair back into felts.
    fn u32_to_field(&self, value: U32Parts<'ctx, 'sco>) -> Result<Value<'ctx, 'sco>> {
        let location = self.unknown_location();
        let u16_modulus = self.get_felt_constant_from_start(U16_MODULUS)?;
        let high_scaled =
            self.append_op_with_result(felt::mul(location, value.high, u16_modulus)?)?;
        self.append_op_with_result(felt::add(location, value.low, high_scaled)?)
    }

    /// Convert an integer witness value into a felt.
    fn integer_to_field(&self, value: IntegerValue<'ctx, 'sco>) -> Result<Value<'ctx, 'sco>> {
        match value {
            IntegerValue::U8(value) | IntegerValue::U16(value) => Ok(value),
            IntegerValue::U32(value) => self.u32_to_field(value),
        }
    }

    /// Decompose a felt value into a 32-bit pair of 16-bit limbs.
    fn field_to_u32(&self, value: Value<'ctx, 'sco>) -> Result<U32Parts<'ctx, 'sco>> {
        let location = self.unknown_location();
        let u16_modulus = self.get_felt_constant_from_start(U16_MODULUS)?;
        let low = self.append_lowest_bits_felt(value, 16)?;
        let high = self.append_op_with_result(felt::uintdiv(location, value, u16_modulus)?)?;
        Ok(U32Parts { low, high })
    }

    /// Build a `u32` constant as two 16-bit limbs.
    fn u32_constant(&self, value: u32) -> Result<U32Parts<'ctx, 'sco>> {
        let low = u64::from(value & 0xffff);
        let high = u64::from(value >> 16);
        Ok(U32Parts {
            low: self.get_felt_constant_from_start(low)?,
            high: self.get_felt_constant_from_start(high)?,
        })
    }

    /// Compute `lhs == rhs` over witness integers.
    fn integer_equal(
        &self,
        lhs: IntegerValue<'ctx, 'sco>,
        rhs: IntegerValue<'ctx, 'sco>,
    ) -> Result<Value<'ctx, 'sco>> {
        let location = self.unknown_location();
        match (lhs, rhs) {
            (IntegerValue::U8(lhs), IntegerValue::U8(rhs))
            | (IntegerValue::U16(lhs), IntegerValue::U16(rhs)) => {
                self.append_op_with_result(bool::eq(location, lhs, rhs)?)
            }
            (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => {
                let low_eq = self.append_op_with_result(bool::eq(location, lhs.low, rhs.low)?)?;
                let high_eq =
                    self.append_op_with_result(bool::eq(location, lhs.high, rhs.high)?)?;
                self.append_op_with_result(bool::and(location, low_eq, high_eq)?)
            }
            _ => bail!("integer equality requires operands of the same width"),
        }
    }

    /// Compute whether an integer witness value is non-zero.
    fn integer_is_nonzero(&self, value: IntegerValue<'ctx, 'sco>) -> Result<Value<'ctx, 'sco>> {
        match value {
            IntegerValue::U8(value) | IntegerValue::U16(value) => {
                self.append_field_is_nonzero(value)
            }
            IntegerValue::U32(value) => {
                let location = self.unknown_location();
                let low_nonzero = self.append_field_is_nonzero(value.low)?;
                let high_nonzero = self.append_field_is_nonzero(value.high)?;
                self.append_op_with_result(bool::or(location, low_nonzero, high_nonzero)?)
            }
        }
    }

    /// Compute a wrapping add together with its carry/overflow bit.
    fn overflowing_add(
        &self,
        lhs: IntegerValue<'ctx, 'sco>,
        rhs: IntegerValue<'ctx, 'sco>,
    ) -> Result<(IntegerValue<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        match (lhs, rhs) {
            (IntegerValue::U8(lhs), IntegerValue::U8(rhs)) => {
                let (sum, carry) = self.add_small(lhs, rhs, 8)?;
                Ok((IntegerValue::U8(sum), carry))
            }
            (IntegerValue::U16(lhs), IntegerValue::U16(rhs)) => {
                let (sum, carry) = self.add_small(lhs, rhs, 16)?;
                Ok((IntegerValue::U16(sum), carry))
            }
            (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => {
                let (sum, carry) = self.add_u32(lhs, rhs)?;
                Ok((IntegerValue::U32(sum), carry))
            }
            _ => bail!("wrapping add requires operands of the same width"),
        }
    }

    /// Compute a wrapping subtraction together with its borrow bit.
    fn overflowing_sub(
        &self,
        lhs: IntegerValue<'ctx, 'sco>,
        rhs: IntegerValue<'ctx, 'sco>,
    ) -> Result<(IntegerValue<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        match (lhs, rhs) {
            (IntegerValue::U8(lhs), IntegerValue::U8(rhs)) => {
                let (diff, borrow) = self.sub_small(lhs, rhs, 8)?;
                Ok((IntegerValue::U8(diff), borrow))
            }
            (IntegerValue::U16(lhs), IntegerValue::U16(rhs)) => {
                let (diff, borrow) = self.sub_small(lhs, rhs, 16)?;
                Ok((IntegerValue::U16(diff), borrow))
            }
            (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => {
                let (diff, borrow) = self.sub_u32(lhs, rhs)?;
                Ok((IntegerValue::U32(diff), borrow))
            }
            _ => bail!("wrapping sub requires operands of the same width"),
        }
    }

    /// Add two `u8`/`u16` values in the field and recover the carry with a bound comparison.
    fn add_small(
        &self,
        lhs: Value<'ctx, 'sco>,
        rhs: Value<'ctx, 'sco>,
        width: u32,
    ) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let modulus = 1u64 << width;
        let modulus = self.get_felt_constant_from_start(modulus)?;
        let sum = self.append_op_with_result(felt::add(location, lhs, rhs)?)?;
        let carry = self.append_op_with_result(bool::ge(location, sum, modulus)?)?;
        let wrapped = self.append_lowest_bits_felt(sum, width)?;
        Ok((wrapped, carry))
    }

    /// Subtract two `u8`/`u16` values while preserving the borrow bit.
    fn sub_small(
        &self,
        lhs: Value<'ctx, 'sco>,
        rhs: Value<'ctx, 'sco>,
        width: u32,
    ) -> Result<(Value<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let borrow = self.append_op_with_result(bool::lt(location, lhs, rhs)?)?;
        let borrow_case = self.append_op_with_result(felt::sub(
            location,
            self.append_op_with_result(felt::add(
                location,
                lhs,
                self.get_felt_constant_from_start(1u64 << width)?,
            )?)?,
            rhs,
        )?)?;
        let direct_case = self.append_op_with_result(felt::sub(location, lhs, rhs)?)?;
        Ok((
            self.append_select_value(borrow, borrow_case, direct_case)?,
            borrow,
        ))
    }

    /// Add two 32-bit limb pairs and recover the carry bit from the high limb.
    fn add_u32(
        &self,
        lhs: U32Parts<'ctx, 'sco>,
        rhs: U32Parts<'ctx, 'sco>,
    ) -> Result<(U32Parts<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let (low, low_carry) = self.add_small(lhs.low, rhs.low, 16)?;
        let carry_felt = self.append_bool_to_field(low_carry)?;
        let high_rhs = self.append_op_with_result(felt::add(location, rhs.high, carry_felt)?)?;
        let (high, high_carry) = self.add_small(lhs.high, high_rhs, 16)?;
        Ok((U32Parts { low, high }, high_carry))
    }

    /// Subtract two 32-bit limb pairs and recover the final borrow bit.
    fn sub_u32(
        &self,
        lhs: U32Parts<'ctx, 'sco>,
        rhs: U32Parts<'ctx, 'sco>,
    ) -> Result<(U32Parts<'ctx, 'sco>, Value<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let (low, low_borrow) = self.sub_small(lhs.low, rhs.low, 16)?;
        let borrow_felt = self.append_bool_to_field(low_borrow)?;
        let high_rhs = self.append_op_with_result(felt::add(location, rhs.high, borrow_felt)?)?;
        let (high, high_borrow) = self.sub_small(lhs.high, high_rhs, 16)?;
        Ok((U32Parts { low, high }, high_borrow))
    }

    /// Return the all-zero 32-bit value.
    fn zero_u32(&self) -> Result<U32Parts<'ctx, 'sco>> {
        self.u32_constant(0)
    }

    /// Split a 32-bit value into little-endian bytes.
    fn u32_to_bytes(&self, value: U32Parts<'ctx, 'sco>) -> Result<[Value<'ctx, 'sco>; 4]> {
        Ok([
            self.append_lowest_bits_felt(value.low, 8)?,
            self.append_shifted_low_bits(value.low, 8, 8)?,
            self.append_lowest_bits_felt(value.high, 8)?,
            self.append_shifted_low_bits(value.high, 8, 8)?,
        ])
    }

    /// Reassemble a 32-bit value from little-endian bytes.
    fn bytes_to_u32(&self, bytes: [Value<'ctx, 'sco>; 4]) -> Result<U32Parts<'ctx, 'sco>> {
        let location = self.unknown_location();
        let byte_scale = self.get_felt_constant_from_start(1 << 8)?;
        let low = self.append_op_with_result(felt::add(
            location,
            bytes[0],
            self.append_op_with_result(felt::mul(location, bytes[1], byte_scale)?)?,
        )?)?;
        let high = self.append_op_with_result(felt::add(
            location,
            bytes[2],
            self.append_op_with_result(felt::mul(location, bytes[3], byte_scale)?)?,
        )?)?;
        Ok(U32Parts { low, high })
    }

    /// Multiply two 32-bit values using byte-wise convolution.
    ///
    /// Each intermediate stays below the field modulus because the computation only multiplies
    /// 8-bit values and propagates carries base 256.
    fn multiply_u32_unsigned(
        &self,
        lhs: U32Parts<'ctx, 'sco>,
        rhs: U32Parts<'ctx, 'sco>,
    ) -> Result<(U32Parts<'ctx, 'sco>, U32Parts<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let lhs_bytes = self.u32_to_bytes(lhs)?;
        let rhs_bytes = self.u32_to_bytes(rhs)?;
        let zero = self.get_felt_constant_from_start(0)?;
        let byte_modulus = self.get_felt_constant_from_start(1 << 8)?;

        let mut sums = [zero; 8];
        for (i, lhs_byte) in lhs_bytes.into_iter().enumerate() {
            for (j, rhs_byte) in rhs_bytes.into_iter().enumerate() {
                let product =
                    self.append_op_with_result(felt::mul(location, lhs_byte, rhs_byte)?)?;
                sums[i + j] =
                    self.append_op_with_result(felt::add(location, sums[i + j], product)?)?;
            }
        }

        let mut carry = zero;
        let mut bytes = [zero; 8];
        for idx in 0..7 {
            let total = self.append_op_with_result(felt::add(location, sums[idx], carry)?)?;
            bytes[idx] = self.append_lowest_bits_felt(total, 8)?;
            carry = self.append_op_with_result(felt::uintdiv(location, total, byte_modulus)?)?;
        }
        bytes[7] = self.append_op_with_result(felt::add(location, sums[7], carry)?)?;

        Ok((
            self.bytes_to_u32([bytes[0], bytes[1], bytes[2], bytes[3]])?,
            self.bytes_to_u32([bytes[4], bytes[5], bytes[6], bytes[7]])?,
        ))
    }

    /// Read the sign bit of a 32-bit two's-complement value.
    fn u32_sign_bit(&self, value: U32Parts<'ctx, 'sco>) -> Result<Value<'ctx, 'sco>> {
        self.append_field_is_nonzero(self.append_shifted_low_bits(value.high, 15, 1)?)
    }

    /// Select between two 32-bit values.
    fn select_u32(
        &self,
        condition: Value<'ctx, 'sco>,
        if_true: U32Parts<'ctx, 'sco>,
        if_false: U32Parts<'ctx, 'sco>,
    ) -> Result<U32Parts<'ctx, 'sco>> {
        Ok(U32Parts {
            low: self.append_select_value(condition, if_true.low, if_false.low)?,
            high: self.append_select_value(condition, if_true.high, if_false.high)?,
        })
    }

    /// Multiply two signed 32-bit values and return their low and high 32-bit words.
    fn multiply_i32(
        &self,
        lhs: U32Parts<'ctx, 'sco>,
        rhs: U32Parts<'ctx, 'sco>,
    ) -> Result<(U32Parts<'ctx, 'sco>, U32Parts<'ctx, 'sco>)> {
        let (low, unsigned_high) = self.multiply_u32_unsigned(lhs, rhs)?;
        let zero = self.zero_u32()?;
        let lhs_negative = self.u32_sign_bit(lhs)?;
        let rhs_negative = self.u32_sign_bit(rhs)?;
        let lhs_correction = self.select_u32(lhs_negative, rhs, zero)?;
        let rhs_correction = self.select_u32(rhs_negative, lhs, zero)?;
        let (corrected, _) = self.sub_u32(unsigned_high, lhs_correction)?;
        let (high, _) = self.sub_u32(corrected, rhs_correction)?;
        Ok((low, high))
    }

    /// Multiply a signed and an unsigned 32-bit value and return their low and high 32-bit words.
    fn multiply_i32_u32(
        &self,
        lhs: U32Parts<'ctx, 'sco>,
        rhs: U32Parts<'ctx, 'sco>,
    ) -> Result<(U32Parts<'ctx, 'sco>, U32Parts<'ctx, 'sco>)> {
        let (low, unsigned_high) = self.multiply_u32_unsigned(lhs, rhs)?;
        let zero = self.zero_u32()?;
        let lhs_negative = self.u32_sign_bit(lhs)?;
        let lhs_correction = self.select_u32(lhs_negative, rhs, zero)?;
        let (high, _) = self.sub_u32(unsigned_high, lhs_correction)?;
        Ok((low, high))
    }

    /// Read one bit from a 32-bit limb pair as a felt `0`/`1`.
    fn u32_bit_as_felt(
        &self,
        value: U32Parts<'ctx, 'sco>,
        bit_idx: u32,
    ) -> Result<Value<'ctx, 'sco>> {
        if bit_idx < 16 {
            self.append_shifted_low_bits(value.low, u64::from(bit_idx), 1)
        } else {
            self.append_shifted_low_bits(value.high, u64::from(bit_idx - 16), 1)
        }
    }

    /// Conditionally set one quotient bit in a 32-bit value.
    fn set_u32_bit_if(
        &self,
        value: U32Parts<'ctx, 'sco>,
        bit_idx: u32,
        condition: Value<'ctx, 'sco>,
    ) -> Result<U32Parts<'ctx, 'sco>> {
        let zero = self.zero_u32()?;
        let increment = self.select_u32(condition, self.u32_constant(1u32 << bit_idx)?, zero)?;
        Ok(self.add_u32(value, increment)?.0)
    }

    /// Compute unsigned 32-bit division and remainder for a non-zero divisor.
    ///
    /// This is a standard restoring long-division loop over the two-limb `u32`
    /// representation. We cannot use `felt.uintdiv` / `felt.umod` directly here,
    /// because those integer semantics apply to a single field element, while our
    /// words are full 32-bit values encoded as two 16-bit felts over Mersenne31.
    fn div_rem_u32_nonzero(
        &self,
        dividend: U32Parts<'ctx, 'sco>,
        divisor: U32Parts<'ctx, 'sco>,
    ) -> Result<(U32Parts<'ctx, 'sco>, U32Parts<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let mut quotient = self.zero_u32()?;
        let mut remainder = self.zero_u32()?;

        for bit_idx in (0..32).rev() {
            let shifted_remainder = self.shift_left_u32(remainder, 1)?;
            let next_bit = self.u32_bit_as_felt(dividend, bit_idx)?;
            let trial_remainder = U32Parts {
                low: self.append_op_with_result(felt::add(
                    location,
                    shifted_remainder.low,
                    next_bit,
                )?)?,
                high: shifted_remainder.high,
            };
            let (subtracted, borrow) = self.sub_u32(trial_remainder, divisor)?;
            let take_bit = self.append_op_with_result(bool::not(location, borrow)?)?;

            remainder = self.select_u32(take_bit, subtracted, trial_remainder)?;
            quotient = self.set_u32_bit_if(quotient, bit_idx, take_bit)?;
        }

        Ok((quotient, remainder))
    }

    /// Compute the two's-complement absolute value of a signed 32-bit word.
    ///
    /// The signed div/rem SSA nodes that call this helper already exclude the
    /// `INT_MIN / -1` overflow case, so wrapping negation is sufficient here.
    fn abs_i32_no_overflow(&self, value: U32Parts<'ctx, 'sco>) -> Result<U32Parts<'ctx, 'sco>> {
        let zero = self.zero_u32()?;
        let negative = self.u32_sign_bit(value)?;
        let (negated, _) = self.sub_u32(zero, value)?;
        self.select_u32(negative, negated, value)
    }

    /// Compute signed 32-bit division and remainder for a non-zero divisor in
    /// the "no overflow bits" case used by the source witness SSA.
    fn div_rem_i32_nonzero_no_overflow(
        &self,
        dividend: U32Parts<'ctx, 'sco>,
        divisor: U32Parts<'ctx, 'sco>,
    ) -> Result<(U32Parts<'ctx, 'sco>, U32Parts<'ctx, 'sco>)> {
        let location = self.unknown_location();
        let dividend_negative = self.u32_sign_bit(dividend)?;
        let divisor_negative = self.u32_sign_bit(divisor)?;
        let dividend_abs = self.abs_i32_no_overflow(dividend)?;
        let divisor_abs = self.abs_i32_no_overflow(divisor)?;
        let (quotient_abs, remainder_abs) = self.div_rem_u32_nonzero(dividend_abs, divisor_abs)?;

        let zero = self.zero_u32()?;
        let quotient_negative =
            self.append_op_with_result(bool::xor(location, dividend_negative, divisor_negative)?)?;
        let (negated_quotient, _) = self.sub_u32(zero, quotient_abs)?;
        let (negated_remainder, _) = self.sub_u32(zero, remainder_abs)?;

        Ok((
            self.select_u32(quotient_negative, negated_quotient, quotient_abs)?,
            self.select_u32(dividend_negative, negated_remainder, remainder_abs)?,
        ))
    }

    /// Apply a logical right shift to an integer witness value.
    fn shift_right(
        &self,
        value: IntegerValue<'ctx, 'sco>,
        magnitude: u32,
    ) -> Result<IntegerValue<'ctx, 'sco>> {
        let location = self.unknown_location();
        let magnitude_value = self.get_felt_constant_from_start(u64::from(magnitude))?;
        match value {
            IntegerValue::U8(value) => Ok(IntegerValue::U8(
                self.append_op_with_result(felt::shr(location, value, magnitude_value)?)?,
            )),
            IntegerValue::U16(value) => Ok(IntegerValue::U16(
                self.append_op_with_result(felt::shr(location, value, magnitude_value)?)?,
            )),
            IntegerValue::U32(value) => {
                Ok(IntegerValue::U32(self.shift_right_u32(value, magnitude)?))
            }
        }
    }

    /// Apply a logical left shift to an integer witness value.
    fn shift_left(
        &self,
        value: IntegerValue<'ctx, 'sco>,
        magnitude: u32,
    ) -> Result<IntegerValue<'ctx, 'sco>> {
        let location = self.unknown_location();
        let magnitude_value = self.get_felt_constant_from_start(u64::from(magnitude))?;
        match value {
            IntegerValue::U8(value) => {
                let shifted =
                    self.append_op_with_result(felt::shl(location, value, magnitude_value)?)?;
                Ok(IntegerValue::U8(self.append_lowest_bits_felt(shifted, 8)?))
            }
            IntegerValue::U16(value) => {
                let shifted =
                    self.append_op_with_result(felt::shl(location, value, magnitude_value)?)?;
                Ok(IntegerValue::U16(
                    self.append_lowest_bits_felt(shifted, 16)?,
                ))
            }
            IntegerValue::U32(value) => {
                Ok(IntegerValue::U32(self.shift_left_u32(value, magnitude)?))
            }
        }
    }

    /// Keep only the lowest `num_bits` of an integer witness value.
    fn lowest_bits(
        &self,
        value: IntegerValue<'ctx, 'sco>,
        num_bits: u32,
    ) -> Result<IntegerValue<'ctx, 'sco>> {
        match value {
            IntegerValue::U8(value) => Ok(IntegerValue::U8(
                self.append_lowest_bits_felt(value, num_bits.min(8))?,
            )),
            IntegerValue::U16(value) => Ok(IntegerValue::U16(
                self.append_lowest_bits_felt(value, num_bits.min(16))?,
            )),
            IntegerValue::U32(value) => {
                if num_bits >= 32 {
                    Ok(IntegerValue::U32(value))
                } else if num_bits <= 16 {
                    let zero = self.get_felt_constant_from_start(0)?;
                    Ok(IntegerValue::U32(U32Parts {
                        low: self.append_lowest_bits_felt(value.low, num_bits)?,
                        high: zero,
                    }))
                } else {
                    Ok(IntegerValue::U32(U32Parts {
                        low: value.low,
                        high: self.append_lowest_bits_felt(value.high, num_bits - 16)?,
                    }))
                }
            }
        }
    }

    /// Select between two integer values of the same width.
    fn select_integer(
        &self,
        condition: Value<'ctx, 'sco>,
        if_true: IntegerValue<'ctx, 'sco>,
        if_false: IntegerValue<'ctx, 'sco>,
    ) -> Result<IntegerValue<'ctx, 'sco>> {
        match (if_true, if_false) {
            (IntegerValue::U8(lhs), IntegerValue::U8(rhs)) => Ok(IntegerValue::U8(
                self.append_select_value(condition, lhs, rhs)?,
            )),
            (IntegerValue::U16(lhs), IntegerValue::U16(rhs)) => Ok(IntegerValue::U16(
                self.append_select_value(condition, lhs, rhs)?,
            )),
            (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => Ok(IntegerValue::U32(U32Parts {
                low: self.append_select_value(condition, lhs.low, rhs.low)?,
                high: self.append_select_value(condition, lhs.high, rhs.high)?,
            })),
            _ => bail!("integer select requires both branches to have the same width"),
        }
    }

    /// Apply bitwise `not` while respecting the integer width.
    fn bitwise_not(&self, value: IntegerValue<'ctx, 'sco>) -> Result<IntegerValue<'ctx, 'sco>> {
        let location = self.unknown_location();
        match value {
            IntegerValue::U8(value) => {
                let mask = self.get_felt_constant_from_start(U8_MODULUS - 1)?;
                Ok(IntegerValue::U8(self.append_op_with_result(
                    felt::bit_xor(location, value, mask)?,
                )?))
            }
            IntegerValue::U16(value) => {
                let mask = self.get_felt_constant_from_start(U16_MODULUS - 1)?;
                Ok(IntegerValue::U16(self.append_op_with_result(
                    felt::bit_xor(location, value, mask)?,
                )?))
            }
            IntegerValue::U32(value) => Ok(IntegerValue::U32(U32Parts {
                low: match self.bitwise_not(IntegerValue::U16(value.low))? {
                    IntegerValue::U16(value) => value,
                    _ => unreachable!(),
                },
                high: match self.bitwise_not(IntegerValue::U16(value.high))? {
                    IntegerValue::U16(value) => value,
                    _ => unreachable!(),
                },
            })),
        }
    }

    /// Apply a width-preserving bitwise binary operation.
    fn bitwise_binop<FN>(
        &self,
        op: FN,
        lhs: IntegerValue<'ctx, 'sco>,
        rhs: IntegerValue<'ctx, 'sco>,
    ) -> Result<IntegerValue<'ctx, 'sco>>
    where
        FN: Copy
            + Fn(
                Location<'ctx>,
                Value<'ctx, 'sco>,
                Value<'ctx, 'sco>,
            ) -> Result<Operation<'ctx>, llzk::error::Error>,
    {
        let location = self.unknown_location();
        let apply = |lhs, rhs| -> Result<Value<'ctx, 'sco>> {
            self.append_op_with_result(op(location, lhs, rhs)?)
        };

        match (lhs, rhs) {
            (IntegerValue::U8(lhs), IntegerValue::U8(rhs)) => {
                Ok(IntegerValue::U8(apply(lhs, rhs)?))
            }
            (IntegerValue::U16(lhs), IntegerValue::U16(rhs)) => {
                Ok(IntegerValue::U16(apply(lhs, rhs)?))
            }
            (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => Ok(IntegerValue::U32(U32Parts {
                low: apply(lhs.low, rhs.low)?,
                high: apply(lhs.high, rhs.high)?,
            })),
            _ => bail!("bitwise operation requires operands of the same width"),
        }
    }

    /// Shift a 32-bit value right by manipulating its two 16-bit limbs directly.
    fn shift_right_u32(
        &self,
        value: U32Parts<'ctx, 'sco>,
        magnitude: u32,
    ) -> Result<U32Parts<'ctx, 'sco>> {
        let location = self.unknown_location();
        let zero = self.get_felt_constant_from_start(0)?;
        if magnitude == 0 {
            return Ok(value);
        }
        if magnitude >= 32 {
            return Ok(U32Parts {
                low: zero,
                high: zero,
            });
        }
        if magnitude >= 16 {
            let shift = magnitude - 16;
            let shift_value = self.get_felt_constant_from_start(u64::from(shift))?;
            return Ok(U32Parts {
                low: self.append_op_with_result(felt::shr(location, value.high, shift_value)?)?,
                high: zero,
            });
        }
        let magnitude_value = self.get_felt_constant_from_start(u64::from(magnitude))?;
        let carry_mask = self.get_felt_constant_from_start((1u64 << magnitude) - 1)?;
        let carry_shift = self.get_felt_constant_from_start(u64::from(16 - magnitude))?;

        let low_base =
            self.append_op_with_result(felt::shr(location, value.low, magnitude_value)?)?;
        let high_base =
            self.append_op_with_result(felt::shr(location, value.high, magnitude_value)?)?;
        let carry_bits =
            self.append_op_with_result(felt::bit_and(location, value.high, carry_mask)?)?;
        let carry = self.append_op_with_result(felt::shl(location, carry_bits, carry_shift)?)?;
        Ok(U32Parts {
            low: self.append_op_with_result(felt::bit_or(location, low_base, carry)?)?,
            high: high_base,
        })
    }

    /// Shift a 32-bit value left by manipulating its two 16-bit limbs directly.
    fn shift_left_u32(
        &self,
        value: U32Parts<'ctx, 'sco>,
        magnitude: u32,
    ) -> Result<U32Parts<'ctx, 'sco>> {
        let location = self.unknown_location();
        let zero = self.get_felt_constant_from_start(0)?;
        if magnitude == 0 {
            return Ok(value);
        }
        if magnitude >= 32 {
            return Ok(U32Parts {
                low: zero,
                high: zero,
            });
        }
        if magnitude >= 16 {
            let shift = magnitude - 16;
            let shift_value = self.get_felt_constant_from_start(u64::from(shift))?;
            let shifted_high =
                self.append_op_with_result(felt::shl(location, value.low, shift_value)?)?;
            return Ok(U32Parts {
                low: zero,
                high: self.append_lowest_bits_felt(shifted_high, 16)?,
            });
        }

        let magnitude_value = self.get_felt_constant_from_start(u64::from(magnitude))?;
        let carry_shift = self.get_felt_constant_from_start(u64::from(16 - magnitude))?;

        let low_shifted =
            self.append_op_with_result(felt::shl(location, value.low, magnitude_value)?)?;
        let high_shifted =
            self.append_op_with_result(felt::shl(location, value.high, magnitude_value)?)?;
        let carry = self.append_op_with_result(felt::shr(location, value.low, carry_shift)?)?;
        Ok(U32Parts {
            low: self.append_lowest_bits_felt(low_shifted, 16)?,
            high: self.append_op_with_result(felt::bit_or(
                location,
                self.append_lowest_bits_felt(high_shifted, 16)?,
                carry,
            )?)?,
        })
    }

    /// Read the inputs for one SSA lookup invocation.
    fn lookup_inputs_as_fields(
        &self,
        input_subexpr_idxes: &[usize],
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        input_subexpr_idxes
            .iter()
            .map(|idx| self.slot_as_field(*idx))
            .collect()
    }

    /// Lower either `perform_lookup` or `maybe_perform_lookup` directly from the raw SSA node.
    fn lower_lookup_invocation(
        &self,
        input_subexpr_idxes: &[usize],
        table_id_subexpr_idx: usize,
        lookup_mapping_idx: Option<usize>,
        mask_id_subexpr_idx: Option<usize>,
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        let inputs = self.lookup_inputs_as_fields(input_subexpr_idxes)?;
        let outputs = if let Some(table) =
            self.resolve_lookup_table(table_id_subexpr_idx, lookup_mapping_idx)?
        {
            self.compute_lookup_for_table(table, &inputs, num_outputs)?
        } else {
            self.compute_dynamic_lookup(
                self.slot_as_field(table_id_subexpr_idx)?,
                &inputs,
                num_outputs,
            )?
        };

        if let Some(mask_id_subexpr_idx) = mask_id_subexpr_idx {
            let mask = self.slot_as_bool(mask_id_subexpr_idx)?;
            self.mask_lookup_outputs(mask, outputs)
        } else {
            Ok(outputs)
        }
    }

    /// Resolve the table id referenced by a lookup SSA node when it is statically identifiable.
    ///
    /// The witness placer currently materializes table ids as constant subexpressions. We inspect
    /// the original block first, then fall back to the compiled lookup metadata when the SSA node
    /// carries a `lookup_mapping_idx`. If neither source is constant we return `None`, and the
    /// caller can emit a runtime dispatch across the supported deterministic table families.
    fn resolve_lookup_table(
        &self,
        table_id_subexpr_idx: usize,
        lookup_mapping_idx: Option<usize>,
    ) -> Result<Option<TableType>> {
        let table_expr = self
            .block
            .get(table_id_subexpr_idx)
            .ok_or_else(|| anyhow!("SSA slot {table_id_subexpr_idx} is out of bounds"))?;
        let table = match table_expr {
            RawExpression::Integer(FixedWidthIntegerNodeExpression::ConstantU8(value)) => {
                Some(TableType::get_table_from_id(u32::from(*value)))
            }
            RawExpression::Integer(FixedWidthIntegerNodeExpression::ConstantU16(value)) => {
                Some(TableType::get_table_from_id(u32::from(*value)))
            }
            RawExpression::Integer(FixedWidthIntegerNodeExpression::ConstantU32(value)) => {
                Some(TableType::get_table_from_id(*value))
            }
            RawExpression::Field(FieldNodeExpression::Constant(value)) => {
                let table_id: u64 = value.as_u64_reduced();
                Some(TableType::get_table_from_id(u32::try_from(table_id)?))
            }
            _ => None,
        };

        if let Some(lookup_mapping_idx) = lookup_mapping_idx {
            if let Some(expected) = self.lookup_sets.get(lookup_mapping_idx) {
                match expected.table_index {
                    TableIndex::Constant(expected_table) => {
                        if let Some(table) = table {
                            if expected_table != table {
                                bail!(
                                    "SSA lookup mapping {lookup_mapping_idx} expects table {:?}, found {:?}",
                                    expected_table,
                                    table
                                );
                            }
                        }
                        return Ok(Some(expected_table));
                    }
                    TableIndex::Variable(column) => {
                        // TODO(LLZK compute): specialize dynamic lookup columns once a circuit
                        // needs table families that cannot be handled by
                        // the runtime dispatch below.
                        let _ = column;
                    }
                }
            }
        }

        Ok(table)
    }

    /// Lower the lookup into `table` into LLZK.
    fn compute_lookup_for_table(
        &self,
        table: TableType,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        match table {
            TableType::RangeCheckSmall => {
                self.compute_range_check_small_lookup(inputs, num_outputs)
            }
            TableType::RangeCheck9x9 => {
                self.compute_range_check_two_tuple_lookup(inputs, num_outputs, "RangeCheck9x9")
            }
            TableType::RangeCheck10x10 => {
                self.compute_range_check_two_tuple_lookup(inputs, num_outputs, "RangeCheck10x10")
            }
            TableType::RangeCheck11 => {
                self.compute_range_check_single_entry_lookup(inputs, num_outputs, "RangeCheck11")
            }
            TableType::RangeCheck12 => {
                self.compute_range_check_single_entry_lookup(inputs, num_outputs, "RangeCheck12")
            }
            TableType::RangeCheck13 => {
                self.compute_range_check_single_entry_lookup(inputs, num_outputs, "RangeCheck13")
            }
            TableType::U16GetSignAndHighByte => {
                self.compute_u16_get_sign_and_high_byte_lookup(inputs, num_outputs)
            }
            TableType::U16SplitAsBytes => {
                self.compute_u16_split_as_bytes_lookup(inputs, num_outputs)
            }
            TableType::ConditionalJmpBranchSlt => {
                self.compute_conditional_jmp_branch_slt_lookup(inputs, num_outputs)
            }
            TableType::JumpCleanupOffset => {
                self.compute_jump_cleanup_offset_lookup(inputs, num_outputs)
            }
            TableType::MemoryGetOffsetAndMaskWithTrap => {
                self.compute_memory_get_offset_and_mask_with_trap_lookup(inputs, num_outputs)
            }
            TableType::RomAddressSpaceSeparator => {
                self.compute_rom_address_space_separator_lookup(inputs, num_outputs)
            }
            TableType::RomRead => self.compute_rom_read_lookup(inputs, num_outputs),
            TableType::SpecialCSRProperties => {
                self.compute_special_csr_properties_lookup(inputs, num_outputs)
            }
            TableType::MemoryOffsetGetBits => {
                self.compute_memory_offset_get_bits_lookup(inputs, num_outputs)
            }
            TableType::MemoryLoadHalfwordOrByte => {
                self.compute_memory_load_halfword_or_byte_lookup(inputs, num_outputs)
            }
            TableType::ExtendLoadedValue => {
                self.compute_extend_loaded_value_lookup(inputs, num_outputs)
            }
            TableType::StoreByteSourceContribution => {
                self.compute_store_byte_source_contribution_lookup(inputs, num_outputs)
            }
            TableType::StoreByteExistingContribution => {
                self.compute_store_byte_existing_contribution_lookup(inputs, num_outputs)
            }
            TableType::MemStoreClearOriginalRamValueLimb => {
                self.compute_mem_store_clear_original_ram_value_limb_lookup(inputs, num_outputs)
            }
            TableType::MemStoreClearWrittenValueLimb => {
                self.compute_mem_store_clear_written_value_limb_lookup(inputs, num_outputs)
            }
            TableType::AlignedRomRead => self.compute_aligned_rom_read_lookup(inputs, num_outputs),
            TableType::TruncateShiftAmount => {
                self.compute_truncate_shift_amount_lookup(inputs, num_outputs)
            }
            TableType::Xor => {
                self.compute_bitwise_lookup(inputs, num_outputs, "Xor", felt::bit_xor)
            }
            TableType::Xor3 => {
                self.compute_bitwise_lookup(inputs, num_outputs, "Xor3", felt::bit_xor)
            }
            TableType::Xor4 => {
                self.compute_bitwise_lookup(inputs, num_outputs, "Xor4", felt::bit_xor)
            }
            TableType::Xor7 => {
                self.compute_bitwise_lookup(inputs, num_outputs, "Xor7", felt::bit_xor)
            }
            TableType::Xor9 => {
                self.compute_bitwise_lookup(inputs, num_outputs, "Xor9", felt::bit_xor)
            }
            TableType::Xor12 => {
                self.compute_bitwise_lookup(inputs, num_outputs, "Xor12", felt::bit_xor)
            }
            TableType::Or => self.compute_bitwise_lookup(inputs, num_outputs, "Or", felt::bit_or),
            TableType::And => {
                self.compute_bitwise_lookup(inputs, num_outputs, "And", felt::bit_and)
            }
            TableType::RangeCheck16WithZeroPads => {
                self.compute_range_check_16_with_zero_pads_lookup(inputs, num_outputs)
            }
            TableType::QuickDecodeDecompositionCheck4x4x4 => {
                self.compute_quick_decode_decomposition_lookup(inputs, num_outputs, [4, 4, 4])
            }
            TableType::QuickDecodeDecompositionCheck7x3x6 => {
                self.compute_quick_decode_decomposition_lookup(inputs, num_outputs, [7, 3, 6])
            }
            TableType::OpTypeBitmask => self.compute_op_type_bitmask_lookup(inputs, num_outputs),
            TableType::ShiftImplementation => {
                self.compute_shift_implementation_lookup(inputs, num_outputs)
            }
            TableType::SRASignFiller => self.compute_sra_sign_filler_lookup(inputs, num_outputs),
            TableType::ConditionalOpAllConditionsResolver => {
                self.compute_conditional_op_all_conditions_lookup(inputs, num_outputs)
            }
            TableType::SllWith16BitInputLow => {
                self.compute_logical_shift_16_bit_lookup::<false, false>(inputs, num_outputs)
            }
            TableType::SllWith16BitInputHigh => {
                self.compute_logical_shift_16_bit_lookup::<true, false>(inputs, num_outputs)
            }
            TableType::SrlWith16BitInputLow => {
                self.compute_logical_shift_16_bit_lookup::<false, true>(inputs, num_outputs)
            }
            TableType::SrlWith16BitInputHigh => {
                self.compute_logical_shift_16_bit_lookup::<true, true>(inputs, num_outputs)
            }
            TableType::Sra16BitInputSignFill => {
                self.compute_sra_16_bit_input_sign_fill_lookup(inputs, num_outputs)
            }
            TableType::KeccakPermutationIndices12
            | TableType::KeccakPermutationIndices34
            | TableType::KeccakPermutationIndices56 => {
                self.compute_keccak_permutation_indices_lookup(table, inputs, num_outputs)
            }
            _ => {
                // TODO: add deterministic lowering for the remaining lookup tables
                // used by the supported circuits.
                panic!("unsupported lookup table in @compute: {:?}", table)
            }
        }
    }

    /// Runtime-dispatch a lookup whose table id is chosen by witness expressions.
    ///
    /// `load_store_subword_only` builds several table ids by selecting among constant table
    /// numbers inside SSA blocks. For those cases, we compute the supported candidate tables up
    /// front and select the matching output tuple by comparing the runtime table id.
    fn compute_dynamic_lookup(
        &self,
        table_id: Value<'ctx, 'sco>,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        let supported_tables: &[TableType] = match inputs.len() {
            1 => &[
                TableType::JumpCleanupOffset,
                TableType::MemoryGetOffsetAndMaskWithTrap,
                TableType::RomAddressSpaceSeparator,
                TableType::MemoryLoadHalfwordOrByte,
                TableType::MemStoreClearOriginalRamValueLimb,
                TableType::MemStoreClearWrittenValueLimb,
            ],
            2 => &[TableType::Xor, TableType::Or, TableType::And],
            3 => &[
                TableType::MemoryLoadHalfwordOrByte,
                TableType::MemStoreClearOriginalRamValueLimb,
                TableType::MemStoreClearWrittenValueLimb,
            ],
            n => panic!("dynamic lookup with {} inputs is not supported", n),
        };

        let mut tables = supported_tables.iter().copied();
        let Some(first_table) = tables.next() else {
            unreachable!("dynamic lookup dispatch requires at least one supported table");
        };

        let first_inputs = self.repack_dynamic_lookup_inputs(first_table, inputs)?;
        let mut outputs = self.compute_lookup_for_table(first_table, &first_inputs, num_outputs)?;
        for table in tables {
            let candidate_inputs = self.repack_dynamic_lookup_inputs(table, inputs)?;
            let candidate_outputs =
                self.compute_lookup_for_table(table, &candidate_inputs, num_outputs)?;
            let is_selected =
                self.append_field_eq_constant(table_id, u64::from(table.to_table_id()))?;
            outputs = candidate_outputs
                .into_iter()
                .zip(outputs.into_iter())
                .map(|(candidate, fallback)| {
                    self.append_select_value(is_selected, candidate, fallback)
                })
                .collect::<Result<Vec<_>>>()?;
        }

        Ok(outputs)
    }

    /// Compute the two output limbs for the keccak permutation index helper tables.
    fn compute_keccak_permutation_indices_lookup(
        &self,
        table: TableType,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        let control_with_exe = match inputs {
            [control_with_exe] => {
                if num_outputs != 2 {
                    bail!("{table:?} expects exactly two outputs in output-producing mode");
                }
                *control_with_exe
            }
            [_control_with_exe, _, _] => {
                if num_outputs != 0 {
                    bail!("{table:?} expects zero outputs in row-validation mode");
                }
                return Ok(vec![]);
            }
            _ => {
                bail!(
                    "{table:?} expects either one key input or a width-3 row, found {} inputs",
                    inputs.len()
                );
            }
        };

        let (first_0, second_0) = keccak_permutation_indices_outputs(table, 0);
        let mut selected_first = self.get_felt_constant_from_start(first_0)?;
        let mut selected_second = self.get_felt_constant_from_start(second_0)?;

        for control in 1..(1u64 << 12) {
            let (candidate_first, candidate_second) =
                keccak_permutation_indices_outputs(table, control);
            let is_selected = self.append_field_eq_constant(control_with_exe, control)?;
            selected_first = self.append_select_value(
                is_selected,
                self.get_felt_constant_from_start(candidate_first)?,
                selected_first,
            )?;
            selected_second = self.append_select_value(
                is_selected,
                self.get_felt_constant_from_start(candidate_second)?,
                selected_second,
            )?;
        }

        Ok(vec![selected_first, selected_second])
    }

    /// The quick decoder decomposition tables only certify input bit widths.
    fn compute_quick_decode_decomposition_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
        _expected_widths: [u32; 3],
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 3 {
            bail!(
                "quick decoder decomposition lookup expects 3 inputs, found {}",
                inputs.len()
            );
        }
        if num_outputs != 0 {
            bail!(
                "quick decoder decomposition lookup expects 0 outputs, found {}",
                num_outputs
            );
        }
        Ok(vec![])
    }

    /// Evaluate the decoder bitmask helper table exactly when witness SSA requests outputs.
    fn compute_op_type_bitmask_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        match inputs {
            [packed_opcode] => {
                if num_outputs != 2 {
                    bail!(
                        "OpTypeBitmask expects 2 outputs in value-producing mode, found {}",
                        num_outputs
                    );
                }

                self.with_runtime_location(ComputeRuntimeHookKind::DecoderBitmask, || {
                    let location = self.current_location();
                    let felt_type = self.felt_type();
                    let [first, second] = self.append_call::<2>(
                        location,
                        READ_OP_TYPE_BITMASK_EXTERN,
                        &[*packed_opcode],
                        &[felt_type, felt_type],
                    )?;
                    Ok(vec![first, second])
                })
            }
            [_packed_opcode, _first_chunk, _second_chunk] => {
                if num_outputs != 0 {
                    bail!(
                        "OpTypeBitmask expects 0 outputs in row-validation mode, found {}",
                        num_outputs
                    );
                }
                Ok(vec![])
            }
            _ => bail!(
                "OpTypeBitmask expects either one packed key or a width-3 row, found {} inputs",
                inputs.len()
            ),
        }
    }

    /// Repack unpacked dynamic-lookup inputs into the single felt key expected by the
    /// deterministic table lowerings that mirror the existing subword load/store helper tables.
    fn repack_dynamic_lookup_inputs(
        &self,
        table: TableType,
        inputs: &[Value<'ctx, 'sco>],
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        match (table, inputs) {
            (
                TableType::MemoryLoadHalfwordOrByte
                | TableType::MemStoreClearOriginalRamValueLimb
                | TableType::MemStoreClearWrittenValueLimb,
                [limb, offset, funct3],
            ) => {
                let location = self.unknown_location();
                let offset_scale = self.get_felt_constant_from_start(1u64 << 16)?;
                let funct3_scale = self.get_felt_constant_from_start(1u64 << 18)?;
                let packed = self.append_op_with_result(felt::add(
                    location,
                    *limb,
                    self.append_op_with_result(felt::add(
                        location,
                        self.append_op_with_result(felt::mul(location, *offset, offset_scale)?)?,
                        self.append_op_with_result(felt::mul(location, *funct3, funct3_scale)?)?,
                    )?)?,
                )?)?;
                Ok(vec![packed])
            }
            _ => Ok(inputs.to_vec()),
        }
    }

    /// Materialize the all-zero lookup row used by `maybe_lookup` and by padded table outputs.
    fn zero_lookup_outputs(&self, num_outputs: usize) -> Result<Vec<Value<'ctx, 'sco>>> {
        let zero = self.get_felt_constant_from_start(0)?;
        Ok((0..num_outputs).map(|_| zero).collect())
    }

    /// Apply the `maybe_lookup` mask to already-lowered lookup outputs.
    fn mask_lookup_outputs(
        &self,
        mask: Value<'ctx, 'sco>,
        outputs: Vec<Value<'ctx, 'sco>>,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        let zero = self.get_felt_constant_from_start(0)?;
        outputs
            .into_iter()
            // Inactive lookups return an all-zero tuple.
            .map(|value| self.append_select_value(mask, value, zero))
            .collect()
    }

    /// Resize a concrete lookup result tuple to the size requested by the SSA node.
    ///
    /// Some tables conceptually produce fewer than the full width-3 row, with trailing zeros
    /// reserved for unused columns. The SSA only asks for the outputs it later reads, so this
    /// helper trims or zero-pads accordingly.
    fn finalize_lookup_outputs(
        &self,
        mut outputs: Vec<Value<'ctx, 'sco>>,
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if outputs.len() > num_outputs {
            outputs.truncate(num_outputs);
            return Ok(outputs);
        }

        if outputs.len() < num_outputs {
            outputs.extend(self.zero_lookup_outputs(num_outputs - outputs.len())?);
        }

        Ok(outputs)
    }

    /// Lower the width-3 two-tuple 8-bit range check table.
    ///
    /// This lookup does not produce witness outputs; it only constrains `(a, b, 0)` rows on the
    /// constrain side.
    fn compute_range_check_small_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 3 {
            bail!("RangeCheckSmall expects 3 inputs, found {}", inputs.len());
        }

        self.finalize_lookup_outputs(vec![], num_outputs)
    }

    /// Lower the width-3 two-tuple range-check tables.
    ///
    /// These tables only constrain `(a, b, 0)` rows on the constrain side, so witness lowering
    /// just pads the output tuple when the query requests materialized outputs.
    fn compute_range_check_two_tuple_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
        table_name: &str,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 3 {
            bail!("{table_name} expects 3 inputs, found {}", inputs.len());
        }

        self.finalize_lookup_outputs(vec![], num_outputs)
    }

    /// Lower the width-3 single-entry range-check tables.
    ///
    /// Like the other formal width-3 range checks, these tables do not produce witness outputs.
    fn compute_range_check_single_entry_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
        table_name: &str,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 3 {
            bail!("{table_name} expects 3 inputs, found {}", inputs.len());
        }

        self.finalize_lookup_outputs(vec![], num_outputs)
    }

    /// Lower the `U16GetSignAndHighByte` table directly from the input limb.
    fn compute_u16_get_sign_and_high_byte_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!(
                "U16GetSignAndHighByte expects 1 input, found {}",
                inputs.len()
            );
        }

        let input = inputs[0];
        let sign = self.append_bool_to_field(
            self.append_field_is_nonzero(self.append_shifted_low_bits(input, 15, 1)?)?,
        )?;
        let high_byte = self.append_shifted_low_bits(input, 8, 8)?;

        self.finalize_lookup_outputs(vec![sign, high_byte], num_outputs)
    }

    /// Lower `U16SplitAsBytes` directly from the 16-bit input limb.
    fn compute_u16_split_as_bytes_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!("U16SplitAsBytes expects 1 input, found {}", inputs.len());
        }

        let input = inputs[0];
        let low_byte = self.append_lowest_bits_felt(input, 8)?;
        let high_byte = self.append_shifted_low_bits(input, 8, 8)?;
        self.finalize_lookup_outputs(vec![low_byte, high_byte], num_outputs)
    }

    /// Lower the ROM word lookup keyed by aligned byte address.
    ///
    /// Unlike `AlignedRomRead`, this table is keyed by the byte address itself, so we first shift
    /// off the alignment bits to recover the ROM word index expected by the external hook.
    fn compute_rom_read_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!("RomRead expects 1 input, found {}", inputs.len());
        }

        self.with_runtime_location(ComputeRuntimeHookKind::RomRead, || {
            let location = self.current_location();
            let word_index = self.append_op_with_result(felt::shr(
                location,
                inputs[0],
                self.get_felt_constant_from_start(2)?,
            )?)?;
            let felt_type = self.felt_type();
            let [low, high] = self.append_call::<2>(
                location,
                READ_FROM_ROM_EXTERN,
                &[word_index],
                &[felt_type, felt_type],
            )?;
            self.finalize_lookup_outputs(vec![low, high], num_outputs)
        })
    }

    /// Lower the CSR support/delegation table using metadata recovered from the source circuit.
    fn compute_special_csr_properties_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!(
                "SpecialCSRProperties expects 1 input, found {}",
                inputs.len()
            );
        }

        let metadata = self.special_csr_properties.as_ref().ok_or_else(|| {
            anyhow!("missing SpecialCSRProperties metadata for LLZK witness lowering")
        })?;
        let csr_index = inputs[0];
        let (is_supported, is_for_delegation) =
            self.append_special_csr_properties_outputs(csr_index, metadata)?;

        self.finalize_lookup_outputs(vec![is_supported, is_for_delegation], num_outputs)
    }

    /// Lower the `TruncateShiftAmount` table by masking the lower five bits.
    fn compute_truncate_shift_amount_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!(
                "TruncateShiftAmount expects 1 input, found {}",
                inputs.len()
            );
        }

        let truncated = self.append_lowest_bits_felt(inputs[0], 5)?;
        self.finalize_lookup_outputs(vec![truncated], num_outputs)
    }

    /// Lower the width-3 `(value, 0, 0)` 16-bit range check table.
    fn compute_range_check_16_with_zero_pads_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 3 {
            bail!(
                "RangeCheck16WithZeroPads expects 3 inputs, found {}",
                inputs.len()
            );
        }

        self.finalize_lookup_outputs(vec![], num_outputs)
    }

    /// Lower the generic byte-wise XOR/OR/AND tables.
    fn compute_bitwise_lookup<FN>(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
        table_name: &str,
        op: FN,
    ) -> Result<Vec<Value<'ctx, 'sco>>>
    where
        FN: Copy
            + Fn(
                Location<'ctx>,
                Value<'ctx, 'sco>,
                Value<'ctx, 'sco>,
            ) -> Result<Operation<'ctx>, llzk::error::Error>,
    {
        if inputs.len() != 2 {
            bail!("{table_name} expects 2 inputs, found {}", inputs.len());
        }

        let location = self.unknown_location();
        let output = self.append_op_with_result(op(location, inputs[0], inputs[1])?)?;
        self.finalize_lookup_outputs(vec![output], num_outputs)
    }

    /// Lower `MemoryOffsetGetBits` by reading the lowest two address bits directly.
    fn compute_memory_offset_get_bits_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!(
                "MemoryOffsetGetBits expects 1 input, found {}",
                inputs.len()
            );
        }

        let input = inputs[0];
        let bit_0 = self.append_lowest_bits_felt(input, 1)?;
        let bit_1 = self.append_shifted_low_bits(input, 1, 1)?;
        self.finalize_lookup_outputs(vec![bit_0, bit_1], num_outputs)
    }

    /// Lower the generic shift implementation table used by reduced-machine shifts.
    fn compute_shift_implementation_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!(
                "ShiftImplementation expects 1 input, found {}",
                inputs.len()
            );
        }

        let (in_place, overflow) = self.append_shift_implementation_outputs(inputs[0])?;

        self.finalize_lookup_outputs(vec![in_place, overflow], num_outputs)
    }

    /// Lower the generic SRA sign-filler table.
    fn compute_sra_sign_filler_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!("SRASignFiller expects 1 input, found {}", inputs.len());
        }

        let (low, high) = self.append_sra_sign_filler_outputs(inputs[0])?;
        self.finalize_lookup_outputs(vec![low, high], num_outputs)
    }

    /// Lower the generic branch/SLT condition resolver used by reduced-machine conditional ops.
    fn compute_conditional_op_all_conditions_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!(
                "ConditionalOpAllConditionsResolver expects 1 input, found {}",
                inputs.len()
            );
        }

        let (should_branch, should_store) =
            self.append_conditional_op_all_conditions_outputs(inputs[0])?;
        self.finalize_lookup_outputs(vec![should_branch, should_store], num_outputs)
    }

    /// Lower the generic 16-bit logical shift helper tables.
    fn compute_logical_shift_16_bit_lookup<
        const INPUT_IS_HIGH: bool,
        const IS_RIGHT_SHIFT: bool,
    >(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!(
                "logical 16-bit shift table expects 1 input, found {}",
                inputs.len()
            );
        }

        let (low, high) =
            self.append_logical_shift_16_bit_outputs::<INPUT_IS_HIGH, IS_RIGHT_SHIFT>(inputs[0])?;
        self.finalize_lookup_outputs(vec![low, high], num_outputs)
    }

    /// Lower the special SRA filler mask table keyed by a 16-bit input word and shift amount.
    fn compute_sra_16_bit_input_sign_fill_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!(
                "Sra16BitInputSignFill expects 1 input, found {}",
                inputs.len()
            );
        }

        let (low, high) = self.append_sra_16_bit_input_sign_fill_outputs(inputs[0])?;
        self.finalize_lookup_outputs(vec![low, high], num_outputs)
    }

    /// Lower the generic load-extension table used by reduced-machine loads.
    fn compute_extend_loaded_value_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!("ExtendLoadedValue expects 1 input, found {}", inputs.len());
        }

        let (out_low, out_high) = self.append_extend_loaded_value_outputs(inputs[0])?;

        self.finalize_lookup_outputs(vec![out_low, out_high], num_outputs)
    }

    /// Lower the byte-source contribution table used by reduced-machine stores.
    fn compute_store_byte_source_contribution_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 2 {
            bail!(
                "StoreByteSourceContribution expects 2 inputs, found {}",
                inputs.len()
            );
        }

        self.finalize_lookup_outputs(
            vec![self.append_store_byte_source_contribution_output(inputs[0], inputs[1])?],
            num_outputs,
        )
    }

    /// Lower the existing-byte contribution table used by reduced-machine stores.
    fn compute_store_byte_existing_contribution_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 2 {
            bail!(
                "StoreByteExistingContribution expects 2 inputs, found {}",
                inputs.len()
            );
        }

        self.finalize_lookup_outputs(
            vec![self.append_store_byte_existing_contribution_output(inputs[0], inputs[1])?],
            num_outputs,
        )
    }

    /// Lower the branch/jump condition lookup used by `jump_branch_slt`.
    ///
    /// This matches `create_conditional_jmp_branch_slt_family_resolution_table` directly instead
    /// of routing through a materialized table: unpack the four comparison bits, derive the signed
    /// and unsigned comparison predicates, and then select the requested condition by `funct3`.
    fn compute_conditional_jmp_branch_slt_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 2 {
            bail!(
                "ConditionalJmpBranchSlt expects 2 inputs, found {}",
                inputs.len()
            );
        }

        let location = self.unknown_location();
        let shift = |value, amount| {
            let amount = self.get_felt_constant_from_start(amount)?;
            self.append_op_with_result(felt::shr(location, value, amount)?)
        };

        let a = inputs[0];
        let funct3 = inputs[1];

        let uf = self.append_lowest_bits_felt(a, 1)?;
        let out_is_zero = self.append_lowest_bits_felt(shift(a, 1)?, 1)?;
        let sign1_felt = self.append_lowest_bits_felt(shift(a, 2)?, 1)?;
        let sign2_felt = self.append_lowest_bits_felt(shift(a, 3)?, 1)?;

        let eq = self.append_field_is_nonzero(out_is_zero)?;
        let unsigned_lt = self.append_field_is_nonzero(uf)?;
        let sign1 = self.append_field_is_nonzero(sign1_felt)?;
        let sign2 = self.append_field_is_nonzero(sign2_felt)?;
        let not_sign1 = self.append_op_with_result(bool::not(location, sign1)?)?;
        let not_sign2 = self.append_op_with_result(bool::not(location, sign2)?)?;
        let sign1_xor_sign2 = self.append_op_with_result(bool::or(
            location,
            self.append_op_with_result(bool::and(location, sign1, not_sign2)?)?,
            self.append_op_with_result(bool::and(location, not_sign1, sign2)?)?,
        )?)?;
        let signed_lt = self.append_select_value(sign1_xor_sign2, sign1, unsigned_lt)?;
        let not_eq = self.append_op_with_result(bool::not(location, eq)?)?;
        let not_signed_lt = self.append_op_with_result(bool::not(location, signed_lt)?)?;
        let not_unsigned_lt = self.append_op_with_result(bool::not(location, unsigned_lt)?)?;

        let match_funct3 = |value| {
            let value = self.get_felt_constant_from_start(value)?;
            self.append_op_with_result(bool::eq(location, funct3, value)?)
        };

        let flag = self.append_select_value(
            match_funct3(0)?,
            eq,
            self.append_select_value(
                match_funct3(1)?,
                not_eq,
                self.append_select_value(
                    match_funct3(2)?,
                    signed_lt,
                    self.append_select_value(
                        match_funct3(3)?,
                        unsigned_lt,
                        self.append_select_value(
                            match_funct3(4)?,
                            signed_lt,
                            self.append_select_value(
                                match_funct3(5)?,
                                not_signed_lt,
                                self.append_select_value(
                                    match_funct3(6)?,
                                    unsigned_lt,
                                    not_unsigned_lt,
                                )?,
                            )?,
                        )?,
                    )?,
                )?,
            )?,
        )?;

        self.finalize_lookup_outputs(vec![self.append_bool_to_field(flag)?], num_outputs)
    }

    /// Lower the low-PC cleanup lookup used by jumps and taken branches.
    ///
    /// The table returns `(bit_1, cleaned_low)` where `cleaned_low` is the 4-byte-aligned version
    /// of the low PC limb. We compute that in `@compute` rather than embedding the
    /// full generated table.
    fn compute_jump_cleanup_offset_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!("JumpCleanupOffset expects 1 input, found {}", inputs.len());
        }

        let input = inputs[0];
        let location = self.unknown_location();
        let one = self.get_felt_constant_from_start(1)?;
        let check_bit = self.append_lowest_bits_felt(
            self.append_op_with_result(felt::shr(location, input, one)?)?,
            1,
        )?;
        let low_bits = self.append_lowest_bits_felt(input, 2)?;
        let cleaned = self.append_op_with_result(felt::sub(location, input, low_bits)?)?;

        self.finalize_lookup_outputs(vec![check_bit, cleaned], num_outputs)
    }

    /// Lower the packed offset/mask lookup used by subword memory ops.
    ///
    /// This mirrors `create_memory_offset_mask_with_trap_table`: unpack the low address bits and
    /// control flags from the composite key, derive the alignment trap condition, and then rebuild
    /// the compact bitmask consumed by the later witness SSA writes.
    fn compute_memory_get_offset_and_mask_with_trap_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!(
                "MemoryGetOffsetAndMaskWithTrap expects 1 input, found {}",
                inputs.len()
            );
        }

        let input = inputs[0];
        let location = self.unknown_location();
        let offset = self.append_lowest_bits_felt(input, 2)?;
        let funct3 = self.append_shifted_low_bits(input, 16, 3)?;
        let is_store = self.append_field_is_nonzero(self.append_shifted_low_bits(input, 17, 1)?)?;
        let rd_is_x0 = self.append_field_is_nonzero(self.append_shifted_low_bits(input, 18, 1)?)?;

        let offset_is_nonzero = self.append_field_is_nonzero(offset)?;
        let offset_is_odd =
            self.append_field_is_nonzero(self.append_lowest_bits_felt(offset, 1)?)?;
        let false_bool = self.get_bool_constant_from_start(false)?;
        let two = self.get_felt_constant_from_start(2)?;
        let four = self.get_felt_constant_from_start(4)?;
        let match_funct3 = |value| self.append_field_eq_constant(funct3, value);

        let is_word = match_funct3(0b010)?;
        let is_halfword = self.append_op_with_result(bool::or(
            location,
            match_funct3(0b001)?,
            match_funct3(0b101)?,
        )?)?;
        let is_byte = self.append_op_with_result(bool::or(
            location,
            match_funct3(0b000)?,
            match_funct3(0b100)?,
        )?)?;

        let less_than_word =
            self.append_op_with_result(bool::or(location, is_halfword, is_byte)?)?;
        let base_trap = self.append_select_value(
            is_word,
            offset_is_nonzero,
            self.append_select_value(
                is_halfword,
                offset_is_odd,
                self.append_op_with_result(bool::not(location, is_byte)?)?,
            )?,
        )?;

        let valid_funct3_for_load =
            self.append_op_with_result(bool::or(location, is_word, less_than_word)?)?;
        let is_load = self.append_op_with_result(bool::not(location, is_store)?)?;
        let allow_x0_unaligned_load = self.append_op_with_result(bool::and(
            location,
            valid_funct3_for_load,
            self.append_op_with_result(bool::and(location, is_load, rd_is_x0)?)?,
        )?)?;
        let is_trap = self.append_select_value(allow_x0_unaligned_load, false_bool, base_trap)?;

        let use_high_limb = self.append_op_with_result(bool::ge(location, offset, two)?)?;
        let bitmask = self.append_op_with_result(felt::add(
            location,
            self.append_bool_to_field(less_than_word)?,
            self.append_op_with_result(felt::add(
                location,
                self.append_op_with_result(felt::mul(
                    location,
                    self.append_bool_to_field(use_high_limb)?,
                    two,
                )?)?,
                self.append_op_with_result(felt::mul(
                    location,
                    self.append_bool_to_field(is_trap)?,
                    four,
                )?)?,
            )?)?,
        )?)?;

        self.finalize_lookup_outputs(vec![offset, bitmask], num_outputs)
    }

    /// Lower the ROM/RAM separator lookup used by subword loads.
    ///
    /// The generated table depends only on the fixed ROM boundary for the machine configuration,
    /// so `@compute` can reconstruct the same `(is_ram_range, rom_chunk)` tuple directly from the
    /// address high limb without consulting the materialized lookup table.
    fn compute_rom_address_space_separator_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!(
                "RomAddressSpaceSeparator expects 1 input, found {}",
                inputs.len()
            );
        }

        let input = inputs[0];
        let location = self.unknown_location();
        let rom_bound =
            self.get_felt_constant_from_start(1u64 << common_constants::ROM_SECOND_WORD_BITS)?;
        let is_ram_range = self.append_op_with_result(bool::ge(location, input, rom_bound)?)?;
        let rom_chunk =
            self.append_lowest_bits_felt(input, common_constants::ROM_SECOND_WORD_BITS as u32)?;

        self.finalize_lookup_outputs(
            vec![self.append_bool_to_field(is_ram_range)?, rom_chunk],
            num_outputs,
        )
    }

    /// Lower the byte/halfword load extension table used by subword loads.
    ///
    /// This follows `create_memory_load_halfword_or_byte_table`: decode the selected 16-bit limb,
    /// the byte offset inside that limb, and the `funct3` mode, then rebuild the two 16-bit output
    /// limbs that represent the loaded 32-bit value.
    fn compute_memory_load_halfword_or_byte_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!(
                "MemoryLoadHalfwordOrByte expects 1 input, found {}",
                inputs.len()
            );
        }

        let input = inputs[0];
        let location = self.unknown_location();
        let limb_value = self.append_lowest_bits_felt(input, 16)?;
        let offset = self.append_shifted_low_bits(input, 16, 2)?;
        let funct3 = self.append_shifted_low_bits(input, 18, 3)?;
        let offset_is_odd =
            self.append_field_is_nonzero(self.append_lowest_bits_felt(offset, 1)?)?;
        let use_low_byte = self.append_op_with_result(bool::not(location, offset_is_odd)?)?;
        let low_byte = self.append_lowest_bits_felt(limb_value, 8)?;
        let high_byte = self.append_shifted_low_bits(limb_value, 8, 8)?;
        let selected_byte = self.append_select_value(use_low_byte, low_byte, high_byte)?;
        let byte_sign =
            self.append_field_is_nonzero(self.append_shifted_low_bits(selected_byte, 7, 1)?)?;
        let limb_sign =
            self.append_field_is_nonzero(self.append_shifted_low_bits(limb_value, 15, 1)?)?;
        let zero = self.get_felt_constant_from_start(0)?;
        let byte_sign_extend = self.get_felt_constant_from_start(0xff00)?;
        let full_sign_extend = self.get_felt_constant_from_start(0xffff)?;
        let byte_signed_low = self.append_select_value(
            byte_sign,
            self.append_op_with_result(felt::add(location, selected_byte, byte_sign_extend)?)?,
            selected_byte,
        )?;
        let byte_signed_high = self.append_select_value(byte_sign, full_sign_extend, zero)?;
        let halfword_signed_high = self.append_select_value(limb_sign, full_sign_extend, zero)?;
        let halfword_low = self.append_select_value(offset_is_odd, zero, limb_value)?;
        let halfword_signed_high =
            self.append_select_value(offset_is_odd, zero, halfword_signed_high)?;

        let match_funct3 = |value| self.append_field_eq_constant(funct3, value);
        let low = self.append_select_value(
            match_funct3(0b010)?,
            zero,
            self.append_select_value(
                match_funct3(0b001)?,
                halfword_low,
                self.append_select_value(
                    match_funct3(0b101)?,
                    halfword_low,
                    self.append_select_value(
                        match_funct3(0b000)?,
                        byte_signed_low,
                        self.append_select_value(match_funct3(0b100)?, selected_byte, zero)?,
                    )?,
                )?,
            )?,
        )?;
        let high = self.append_select_value(
            match_funct3(0b010)?,
            zero,
            self.append_select_value(
                match_funct3(0b001)?,
                halfword_signed_high,
                self.append_select_value(
                    match_funct3(0b101)?,
                    zero,
                    self.append_select_value(match_funct3(0b000)?, byte_signed_high, zero)?,
                )?,
            )?,
        )?;

        self.finalize_lookup_outputs(vec![low, high], num_outputs)
    }

    /// Lower the table that clears bytes from the original RAM limb on stores.
    ///
    /// This mirrors `create_memory_store_halfword_or_byte_clear_source_limb_table`, which keeps
    /// only the untouched bytes of the original RAM limb before the cleaned write contribution is
    /// added back in.
    fn compute_mem_store_clear_original_ram_value_limb_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!(
                "MemStoreClearOriginalRamValueLimb expects 1 input, found {}",
                inputs.len()
            );
        }

        let input = inputs[0];
        let location = self.unknown_location();
        let limb_value = self.append_lowest_bits_felt(input, 16)?;
        let offset = self.append_shifted_low_bits(input, 16, 2)?;
        let funct3 = self.append_shifted_low_bits(input, 18, 3)?;
        let offset_is_odd =
            self.append_field_is_nonzero(self.append_lowest_bits_felt(offset, 1)?)?;
        let byte_clear_mask = self.get_felt_constant_from_start(0xff00)?;
        let zero = self.get_felt_constant_from_start(0)?;
        let cleaned_byte = self.append_select_value(
            offset_is_odd,
            self.append_lowest_bits_felt(limb_value, 8)?,
            self.append_op_with_result(felt::bit_and(location, limb_value, byte_clear_mask)?)?,
        )?;
        let cleaned = self.append_select_value(
            self.append_field_eq_constant(funct3, 0b000)?,
            cleaned_byte,
            zero,
        )?;

        self.finalize_lookup_outputs(vec![cleaned], num_outputs)
    }

    /// Lower the table that positions the written byte/halfword contribution.
    ///
    /// This matches `create_memory_store_halfword_or_byte_clear_written_limb_table`: depending on
    /// the store width and byte offset, keep either the full halfword or the selected byte shifted
    /// into its destination position.
    fn compute_mem_store_clear_written_value_limb_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!(
                "MemStoreClearWrittenValueLimb expects 1 input, found {}",
                inputs.len()
            );
        }

        let input = inputs[0];
        let location = self.unknown_location();
        let limb_value = self.append_lowest_bits_felt(input, 16)?;
        let offset = self.append_shifted_low_bits(input, 16, 2)?;
        let funct3 = self.append_shifted_low_bits(input, 18, 3)?;
        let offset_is_odd =
            self.append_field_is_nonzero(self.append_lowest_bits_felt(offset, 1)?)?;
        let value_to_store = self.append_lowest_bits_felt(limb_value, 8)?;
        let shift_amount = self.get_felt_constant_from_start(8)?;
        let zero = self.get_felt_constant_from_start(0)?;
        let shifted_byte = self.append_select_value(
            offset_is_odd,
            self.append_op_with_result(felt::shl(location, value_to_store, shift_amount)?)?,
            value_to_store,
        )?;
        let cleaned = self.append_select_value(
            self.append_field_eq_constant(funct3, 0b001)?,
            limb_value,
            self.append_select_value(
                self.append_field_eq_constant(funct3, 0b000)?,
                shifted_byte,
                zero,
            )?,
        )?;

        self.finalize_lookup_outputs(vec![cleaned], num_outputs)
    }

    /// Lower the ROM word lookup used by subword ROM loads through the external ROM hook.
    ///
    /// The aligned ROM table is keyed by word index and returns the 32-bit opcode split into two
    /// 16-bit limbs. We intentionally defer this lookup to the downstream LLZK executor instead of
    /// baking a placeholder bytecode image into the emitted IR.
    fn compute_aligned_rom_read_lookup(
        &self,
        inputs: &[Value<'ctx, 'sco>],
        num_outputs: usize,
    ) -> Result<Vec<Value<'ctx, 'sco>>> {
        if inputs.len() != 1 {
            bail!("AlignedRomRead expects 1 input, found {}", inputs.len());
        }

        self.with_runtime_location(ComputeRuntimeHookKind::RomRead, || {
            let location = self.current_location();
            let felt_type = self.felt_type();
            let [low, high] = self.append_call::<2>(
                location,
                READ_FROM_ROM_EXTERN,
                inputs,
                &[felt_type, felt_type],
            )?;
            self.finalize_lookup_outputs(vec![low, high], num_outputs)
        })
    }

    /// Read a field-valued SSA slot by index.
    fn slot_as_field(&self, idx: usize) -> Result<Value<'ctx, 'sco>> {
        match self
            .slots
            .get(idx)
            .ok_or_else(|| anyhow!("SSA slot {idx} is out of bounds"))?
        {
            SsaSlot::Value(ComputedValue::Field(value)) => Ok(*value),
            SsaSlot::Value(ComputedValue::Integer(value)) => self.integer_to_field(*value),
            SsaSlot::Value(ComputedValue::Bool(value)) => self.append_bool_to_field(*value),
            SsaSlot::Lookup(_) => bail!("SSA slot {idx} is a lookup tuple, not a scalar value"),
            SsaSlot::Unit => bail!("SSA slot {idx} has no scalar value"),
        }
    }

    /// Read a boolean `i1` SSA slot by index.
    fn slot_as_bool(&self, idx: usize) -> Result<Value<'ctx, 'sco>> {
        match self
            .slots
            .get(idx)
            .ok_or_else(|| anyhow!("SSA slot {idx} is out of bounds"))?
        {
            SsaSlot::Value(ComputedValue::Bool(value)) => Ok(*value),
            _ => bail!("SSA slot {idx} does not contain a boolean value"),
        }
    }

    /// Read an integer SSA slot by index.
    fn slot_as_integer(&self, idx: usize) -> Result<IntegerValue<'ctx, 'sco>> {
        match self
            .slots
            .get(idx)
            .ok_or_else(|| anyhow!("SSA slot {idx} is out of bounds"))?
        {
            SsaSlot::Value(ComputedValue::Integer(value)) => Ok(*value),
            _ => bail!("SSA slot {idx} does not contain an integer value"),
        }
    }

    /// Read a lookup tuple SSA slot by index.
    fn slot_as_lookup(&self, idx: usize) -> Result<&[Value<'ctx, 'sco>]> {
        match self
            .slots
            .get(idx)
            .ok_or_else(|| anyhow!("SSA slot {idx} is out of bounds"))?
        {
            SsaSlot::Lookup(values) => Ok(values),
            _ => bail!("SSA slot {idx} does not contain lookup outputs"),
        }
    }

    fn strict_input_origin_for_expression(&self, expr: &Expression<F>) -> Option<Variable> {
        match expr {
            Expression::Bool(expr) => self.strict_input_origin_for_bool_expr(expr),
            Expression::Field(expr) => self.strict_input_origin_for_field_expr(expr),
            Expression::U8(expr) | Expression::U16(expr) | Expression::U32(expr) => {
                self.strict_input_origin_for_integer_expr(expr)
            }
        }
    }

    fn strict_store_origin_for_expression(&self, expr: &Expression<F>) -> Option<Variable> {
        match expr {
            Expression::Bool(expr) => self.strict_input_origin_for_bool_expr(expr),
            Expression::Field(expr) => self.strict_store_origin_for_field_expr(expr),
            Expression::U8(expr) | Expression::U16(expr) | Expression::U32(expr) => {
                self.strict_store_origin_for_integer_expr(expr)
            }
        }
    }

    fn strict_input_origin_for_field_expr(
        &self,
        expr: &FieldNodeExpression<F>,
    ) -> Option<Variable> {
        match expr {
            FieldNodeExpression::Place(var) => self.vars.has_compute_input(var).then_some(*var),
            FieldNodeExpression::SubExpression(idx) => {
                self.slot_input_origins.get(*idx).copied().flatten()
            }
            FieldNodeExpression::FromInteger(inner) => {
                self.strict_input_origin_for_integer_expr(inner)
            }
            FieldNodeExpression::FromMask(inner) => self.strict_input_origin_for_bool_expr(inner),
            FieldNodeExpression::OracleValue { placeholder, .. } => {
                self.strict_placeholder_input_origin(*placeholder)
            }
            _ => None,
        }
    }

    fn strict_store_origin_for_field_expr(
        &self,
        expr: &FieldNodeExpression<F>,
    ) -> Option<Variable> {
        match expr {
            FieldNodeExpression::Place(var) => self.vars.has_compute_input(var).then_some(*var),
            FieldNodeExpression::SubExpression(idx) => {
                self.slot_input_origins.get(*idx).copied().flatten()
            }
            FieldNodeExpression::FromInteger(inner) => {
                self.strict_store_origin_for_integer_expr(inner)
            }
            FieldNodeExpression::FromMask(inner) => self.strict_input_origin_for_bool_expr(inner),
            FieldNodeExpression::OracleValue { placeholder, .. } => {
                self.strict_placeholder_input_limb_origin(*placeholder, 0)
            }
            _ => None,
        }
    }

    fn strict_input_origin_for_bool_expr(&self, expr: &BoolNodeExpression<F>) -> Option<Variable> {
        match expr {
            BoolNodeExpression::Place(var) => self.vars.has_compute_input(var).then_some(*var),
            BoolNodeExpression::SubExpression(idx) => {
                self.slot_input_origins.get(*idx).copied().flatten()
            }
            BoolNodeExpression::OracleValue { placeholder } => {
                self.strict_placeholder_input_origin(*placeholder)
            }
            _ => None,
        }
    }

    fn strict_placeholder_input_origin(&self, placeholder: Placeholder) -> Option<Variable> {
        self.strict_placeholder_input_limb_origin(placeholder, 0)
    }

    fn strict_placeholder_input_limb_origin(
        &self,
        placeholder: Placeholder,
        subindex: usize,
    ) -> Option<Variable> {
        self.substitutions
            .get(&(placeholder, subindex))
            .copied()
            .filter(|var| self.vars.has_compute_input(var))
    }

    fn strict_placeholder_u32_input_origin(
        &self,
        placeholder: Placeholder,
    ) -> Option<[Variable; 2]> {
        Some([
            self.strict_placeholder_input_limb_origin(placeholder, 0)?,
            self.strict_placeholder_input_limb_origin(placeholder, 1)?,
        ])
    }

    fn is_legacy_input_backed_write(&self, variable: Variable) -> bool {
        [
            (Placeholder::WriteRegMemWriteValue, 0),
            (Placeholder::WriteRegMemWriteValue, 1),
            (Placeholder::ShuffleRamWriteValue(2), 0),
            (Placeholder::ShuffleRamWriteValue(2), 1),
        ]
        .into_iter()
        .any(|key| {
            self.substitutions
                .get(&key)
                .is_some_and(|mapped| *mapped == variable)
        })
    }

    fn strict_input_origin_for_integer_expr(
        &self,
        expr: &FixedWidthIntegerNodeExpression<F>,
    ) -> Option<Variable> {
        match expr {
            FixedWidthIntegerNodeExpression::U8Place(var)
            | FixedWidthIntegerNodeExpression::U16Place(var) => {
                self.vars.has_compute_input(var).then_some(*var)
            }
            FixedWidthIntegerNodeExpression::U8SubExpression(idx)
            | FixedWidthIntegerNodeExpression::U16SubExpression(idx)
            | FixedWidthIntegerNodeExpression::U32SubExpression(idx) => {
                self.slot_input_origins.get(*idx).copied().flatten()
            }
            FixedWidthIntegerNodeExpression::U32OracleValue { placeholder }
            | FixedWidthIntegerNodeExpression::U16OracleValue { placeholder }
            | FixedWidthIntegerNodeExpression::U8OracleValue { placeholder } => {
                self.strict_placeholder_input_origin(*placeholder)
            }
            FixedWidthIntegerNodeExpression::WidenFromU8(inner)
            | FixedWidthIntegerNodeExpression::WidenFromU16(inner)
            | FixedWidthIntegerNodeExpression::TruncateFromU16(inner)
            | FixedWidthIntegerNodeExpression::TruncateFromU32(inner)
            | FixedWidthIntegerNodeExpression::I32FromU32(inner)
            | FixedWidthIntegerNodeExpression::U32FromI32(inner) => {
                self.strict_input_origin_for_integer_expr(inner)
            }
            FixedWidthIntegerNodeExpression::WrappingShr { lhs, magnitude }
                if *magnitude == 0 || *magnitude == 16 =>
            {
                self.strict_input_origin_for_integer_expr(lhs)
            }
            _ => None,
        }
    }

    fn strict_store_origin_for_integer_expr(
        &self,
        expr: &FixedWidthIntegerNodeExpression<F>,
    ) -> Option<Variable> {
        match expr {
            FixedWidthIntegerNodeExpression::U8Place(var)
            | FixedWidthIntegerNodeExpression::U16Place(var) => {
                self.vars.has_compute_input(var).then_some(*var)
            }
            FixedWidthIntegerNodeExpression::U8SubExpression(idx)
            | FixedWidthIntegerNodeExpression::U16SubExpression(idx) => {
                self.slot_input_origins.get(*idx).copied().flatten()
            }
            FixedWidthIntegerNodeExpression::U8OracleValue { placeholder }
            | FixedWidthIntegerNodeExpression::U16OracleValue { placeholder } => {
                self.strict_placeholder_input_limb_origin(*placeholder, 0)
            }
            FixedWidthIntegerNodeExpression::WidenFromU8(inner)
            | FixedWidthIntegerNodeExpression::WidenFromU16(inner)
            | FixedWidthIntegerNodeExpression::TruncateFromU16(inner) => {
                self.strict_store_origin_for_integer_expr(inner)
            }
            FixedWidthIntegerNodeExpression::TruncateFromU32(inner) => {
                self.strict_u32_low_limb_origin(inner)
            }
            FixedWidthIntegerNodeExpression::WrappingShr { lhs, magnitude } if *magnitude == 0 => {
                self.strict_store_origin_for_integer_expr(lhs)
            }
            FixedWidthIntegerNodeExpression::WrappingShr { lhs, magnitude } if *magnitude == 16 => {
                self.strict_u32_high_limb_origin(lhs)
            }
            _ => None,
        }
    }

    fn strict_u32_input_origin_for_integer_expr(
        &self,
        expr: &FixedWidthIntegerNodeExpression<F>,
    ) -> Option<[Variable; 2]> {
        match expr {
            FixedWidthIntegerNodeExpression::U32SubExpression(idx) => {
                self.slot_u32_input_origins.get(*idx).copied().flatten()
            }
            FixedWidthIntegerNodeExpression::U32OracleValue { placeholder } => {
                self.strict_placeholder_u32_input_origin(*placeholder)
            }
            FixedWidthIntegerNodeExpression::I32FromU32(inner)
            | FixedWidthIntegerNodeExpression::U32FromI32(inner) => {
                self.strict_u32_input_origin_for_integer_expr(inner)
            }
            FixedWidthIntegerNodeExpression::WrappingShr { lhs, magnitude } if *magnitude == 0 => {
                self.strict_u32_input_origin_for_integer_expr(lhs)
            }
            _ => None,
        }
    }

    fn strict_u32_low_limb_origin(
        &self,
        expr: &FixedWidthIntegerNodeExpression<F>,
    ) -> Option<Variable> {
        self.strict_u32_input_origin_for_integer_expr(expr)
            .map(|[low, _]| low)
    }

    fn strict_u32_high_limb_origin(
        &self,
        expr: &FixedWidthIntegerNodeExpression<F>,
    ) -> Option<Variable> {
        self.strict_u32_input_origin_for_integer_expr(expr)
            .map(|[_, high]| high)
    }
}

impl<'a, 'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInCompute<'a, 'ctx, 'sco, F> for RawExpression<F> {
    type Output = ();

    fn emit_compute(
        &self,
        lowering: &mut ComputeLowering<'a, 'ctx, 'sco, F>,
    ) -> Result<Self::Output> {
        let (slot, input_origin, u32_input_origin) = match self {
            RawExpression::Bool(expr) => (
                SsaSlot::Value(ComputedValue::Bool(expr.emit_compute(lowering)?)),
                lowering.strict_input_origin_for_bool_expr(expr),
                None,
            ),
            RawExpression::Field(expr) => (
                SsaSlot::Value(ComputedValue::Field(expr.emit_compute(lowering)?)),
                lowering.strict_input_origin_for_field_expr(expr),
                None,
            ),
            RawExpression::Integer(expr) => {
                let input_origin = lowering
                    .strict_store_origin_for_integer_expr(expr)
                    .or_else(|| lowering.strict_input_origin_for_integer_expr(expr));
                let u32_input_origin = lowering.strict_u32_input_origin_for_integer_expr(expr);
                (
                    SsaSlot::Value(ComputedValue::Integer(expr.emit_compute(lowering)?)),
                    input_origin,
                    u32_input_origin,
                )
            }
            RawExpression::AccessLookup {
                subindex,
                output_index,
            } => {
                let lookup_value = *lowering
                    .slot_as_lookup(*subindex)?
                    .get(*output_index)
                    .ok_or_else(|| anyhow!("lookup output {output_index} is out of bounds"))?;
                (
                    SsaSlot::Value(ComputedValue::Field(lookup_value)),
                    None,
                    None,
                )
            }
            RawExpression::PerformLookup {
                input_subexpr_idxes,
                table_id_subexpr_idx,
                num_outputs,
                lookup_mapping_idx,
            } => (
                SsaSlot::Lookup(lowering.lower_lookup_invocation(
                    input_subexpr_idxes,
                    *table_id_subexpr_idx,
                    Some(*lookup_mapping_idx),
                    None,
                    *num_outputs,
                )?),
                None,
                None,
            ),
            RawExpression::MaybePerformLookup {
                input_subexpr_idxes,
                table_id_subexpr_idx,
                mask_id_subexpr_idx,
                num_outputs,
            } => (
                SsaSlot::Lookup(lowering.lower_lookup_invocation(
                    input_subexpr_idxes,
                    *table_id_subexpr_idx,
                    None,
                    Some(*mask_id_subexpr_idx),
                    *num_outputs,
                )?),
                None,
                None,
            ),
            RawExpression::WriteVariable {
                into_variable,
                source_subexpr,
                condition_subexpr_idx,
            } => {
                lowering.lower_write(into_variable, source_subexpr, *condition_subexpr_idx)?;
                (SsaSlot::Unit, None, None)
            }
        };

        lowering.push_slot(slot, input_origin, u32_input_origin);
        Ok(())
    }
}

impl<'a, 'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInCompute<'a, 'ctx, 'sco, F> for Expression<F> {
    type Output = ComputedValue<'ctx, 'sco>;

    fn emit_compute(
        &self,
        lowering: &mut ComputeLowering<'a, 'ctx, 'sco, F>,
    ) -> Result<Self::Output> {
        match self {
            Expression::Bool(expr) => Ok(ComputedValue::Bool(expr.emit_compute(lowering)?)),
            Expression::Field(expr) => Ok(ComputedValue::Field(expr.emit_compute(lowering)?)),
            Expression::U8(expr) | Expression::U16(expr) | Expression::U32(expr) => {
                Ok(ComputedValue::Integer(expr.emit_compute(lowering)?))
            }
        }
    }
}

impl<'a, 'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInCompute<'a, 'ctx, 'sco, F>
    for FieldNodeExpression<F>
{
    type Output = Value<'ctx, 'sco>;

    fn emit_compute(
        &self,
        lowering: &mut ComputeLowering<'a, 'ctx, 'sco, F>,
    ) -> Result<Self::Output> {
        match self {
            FieldNodeExpression::Place(variable) => lowering.read_variable(*variable),
            FieldNodeExpression::SubExpression(idx) => lowering.slot_as_field(*idx),
            FieldNodeExpression::Constant(constant) => {
                lowering.get_felt_constant_from_start(constant.as_u64_reduced())
            }
            FieldNodeExpression::FromInteger(expr) => {
                let value = expr.emit_compute(lowering)?;
                lowering.integer_to_field(value)
            }
            FieldNodeExpression::FromMask(expr) => {
                let value = expr.emit_compute(lowering)?;
                lowering.append_bool_to_field(value)
            }
            FieldNodeExpression::OracleValue {
                placeholder,
                subindex,
            } => lowering.read_field_oracle(*placeholder, *subindex),
            FieldNodeExpression::Add { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.append_op_with_result(felt::add(lowering.unknown_location(), lhs, rhs)?)
            }
            FieldNodeExpression::Sub { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.append_op_with_result(felt::sub(lowering.unknown_location(), lhs, rhs)?)
            }
            FieldNodeExpression::Mul { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.append_op_with_result(felt::mul(lowering.unknown_location(), lhs, rhs)?)
            }
            FieldNodeExpression::AddProduct {
                additive_term,
                mul_0,
                mul_1,
            } => {
                let mul_0 = mul_0.emit_compute(lowering)?;
                let mul_1 = mul_1.emit_compute(lowering)?;
                let product = lowering.append_op_with_result(felt::mul(
                    lowering.unknown_location(),
                    mul_0,
                    mul_1,
                )?)?;
                let additive_term = additive_term.emit_compute(lowering)?;
                lowering.append_op_with_result(felt::add(
                    lowering.unknown_location(),
                    additive_term,
                    product,
                )?)
            }
            FieldNodeExpression::Select {
                selector,
                if_true,
                if_false,
            } => {
                let selector = selector.emit_compute(lowering)?;
                let if_true = if_true.emit_compute(lowering)?;
                let if_false = if_false.emit_compute(lowering)?;
                lowering
                    .builder
                    .append_select_value(selector, if_true, if_false)
            }
            FieldNodeExpression::InverseUnchecked(expr) => {
                let value = expr.emit_compute(lowering)?;
                lowering
                    .builder
                    .append_op_with_result(felt::inv(lowering.unknown_location(), value)?)
            }
            // TODO(LLZK compute): lower inverse-or-zero deterministically instead of using a
            // witness hole.
            FieldNodeExpression::InverseOrZero(_expr) => lowering.new_nondet_felt(),
            FieldNodeExpression::LookupOutput { .. }
            | FieldNodeExpression::MaybeLookupOutput { .. } => {
                bail!("lookup outputs must be rewritten into SSA access nodes before lowering")
            }
        }
    }
}

impl<'a, 'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInCompute<'a, 'ctx, 'sco, F>
    for BoolNodeExpression<F>
{
    type Output = Value<'ctx, 'sco>;

    fn emit_compute(
        &self,
        lowering: &mut ComputeLowering<'a, 'ctx, 'sco, F>,
    ) -> Result<Self::Output> {
        match self {
            BoolNodeExpression::Place(variable) => {
                lowering.append_field_is_nonzero(lowering.read_variable(*variable)?)
            }
            BoolNodeExpression::SubExpression(idx) => lowering.slot_as_bool(*idx),
            BoolNodeExpression::Constant(constant) => {
                lowering.get_constant_from_start(lowering.bool_type(), *constant as u64)
            }
            BoolNodeExpression::OracleValue { placeholder } => {
                lowering.read_bool_oracle(*placeholder)
            }
            BoolNodeExpression::FromGenericInteger(expr) => {
                let value = expr.emit_compute(lowering)?;
                lowering.integer_is_nonzero(value)
            }
            BoolNodeExpression::FromGenericIntegerEquality { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.integer_equal(lhs, rhs)
            }
            BoolNodeExpression::FromGenericIntegerCarry { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.overflowing_add(lhs, rhs).map(|(_, carry)| carry)
            }
            BoolNodeExpression::FromGenericIntegerBorrow { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.overflowing_sub(lhs, rhs).map(|(_, borrow)| borrow)
            }
            BoolNodeExpression::FromField(expr) => {
                let value = expr.emit_compute(lowering)?;
                lowering.append_field_is_nonzero(value)
            }
            BoolNodeExpression::FromFieldEquality { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.append_op_with_result(bool::eq(lowering.unknown_location(), lhs, rhs)?)
            }
            BoolNodeExpression::And { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.append_op_with_result(bool::and(lowering.unknown_location(), lhs, rhs)?)
            }
            BoolNodeExpression::Or { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.append_op_with_result(bool::or(lowering.unknown_location(), lhs, rhs)?)
            }
            BoolNodeExpression::Select {
                selector,
                if_true,
                if_false,
            } => {
                let selector = selector.emit_compute(lowering)?;
                let if_true = if_true.emit_compute(lowering)?;
                let if_false = if_false.emit_compute(lowering)?;
                lowering
                    .builder
                    .append_select_value(selector, if_true, if_false)
            }
            BoolNodeExpression::Negate(expr) => {
                let value = expr.emit_compute(lowering)?;
                lowering
                    .builder
                    .append_op_with_result(bool::not(lowering.unknown_location(), value)?)
            }
        }
    }
}

impl<'a, 'ctx: 'sco, 'sco, F: FieldInfo> EmitLlzkInCompute<'a, 'ctx, 'sco, F>
    for FixedWidthIntegerNodeExpression<F>
{
    type Output = IntegerValue<'ctx, 'sco>;

    fn emit_compute(
        &self,
        lowering: &mut ComputeLowering<'a, 'ctx, 'sco, F>,
    ) -> Result<Self::Output> {
        match self {
            FixedWidthIntegerNodeExpression::U8Place(variable) => {
                Ok(IntegerValue::U8(lowering.read_variable(*variable)?))
            }
            FixedWidthIntegerNodeExpression::U16Place(variable) => {
                Ok(IntegerValue::U16(lowering.read_variable(*variable)?))
            }
            FixedWidthIntegerNodeExpression::U8SubExpression(idx)
            | FixedWidthIntegerNodeExpression::U16SubExpression(idx)
            | FixedWidthIntegerNodeExpression::U32SubExpression(idx) => {
                lowering.slot_as_integer(*idx)
            }
            FixedWidthIntegerNodeExpression::U32OracleValue { placeholder } => {
                Ok(IntegerValue::U32(lowering.read_u32_oracle(*placeholder)?))
            }
            FixedWidthIntegerNodeExpression::U16OracleValue { placeholder } => {
                Ok(IntegerValue::U16(lowering.read_u16_oracle(*placeholder)?))
            }
            FixedWidthIntegerNodeExpression::U8OracleValue { placeholder } => {
                Ok(IntegerValue::U8(lowering.read_u8_oracle(*placeholder)?))
            }
            FixedWidthIntegerNodeExpression::ConstantU8(constant) => Ok(IntegerValue::U8(
                lowering.get_felt_constant_from_start(u64::from(*constant))?,
            )),
            FixedWidthIntegerNodeExpression::ConstantU16(constant) => Ok(IntegerValue::U16(
                lowering.get_felt_constant_from_start(u64::from(*constant))?,
            )),
            FixedWidthIntegerNodeExpression::ConstantU32(constant) => {
                Ok(IntegerValue::U32(lowering.u32_constant(*constant)?))
            }
            FixedWidthIntegerNodeExpression::U32FromMask(expr) => {
                let value = expr.emit_compute(lowering)?;
                let low = lowering.append_bool_to_field(value)?;
                Ok(IntegerValue::U32(U32Parts {
                    low,
                    high: lowering.get_felt_constant_from_start(0)?,
                }))
            }
            FixedWidthIntegerNodeExpression::U32FromField(expr) => {
                let value = expr.emit_compute(lowering)?;
                Ok(IntegerValue::U32(lowering.field_to_u32(value)?))
            }
            FixedWidthIntegerNodeExpression::WidenFromU8(expr) => {
                match expr.emit_compute(lowering)? {
                    IntegerValue::U8(value) => Ok(IntegerValue::U16(value)),
                    other => bail!(
                        "expected u8 input when widening to u16, found {}-bit value",
                        other.bit_width()
                    ),
                }
            }
            FixedWidthIntegerNodeExpression::WidenFromU16(expr) => {
                match expr.emit_compute(lowering)? {
                    IntegerValue::U16(value) => Ok(IntegerValue::U32(U32Parts {
                        low: value,
                        high: lowering.get_felt_constant_from_start(0)?,
                    })),
                    other => bail!(
                        "expected u16 input when widening to u32, found {}-bit value",
                        other.bit_width()
                    ),
                }
            }
            FixedWidthIntegerNodeExpression::TruncateFromU16(expr) => {
                match expr.emit_compute(lowering)? {
                    IntegerValue::U16(value) => Ok(IntegerValue::U8(
                        lowering.append_lowest_bits_felt(value, 8)?,
                    )),
                    other => bail!(
                        "expected u16 input when truncating to u8, found {}-bit value",
                        other.bit_width()
                    ),
                }
            }
            FixedWidthIntegerNodeExpression::TruncateFromU32(expr) => {
                match expr.emit_compute(lowering)? {
                    IntegerValue::U32(value) => Ok(IntegerValue::U16(value.low)),
                    other => bail!(
                        "expected u32 input when truncating to u16, found {}-bit value",
                        other.bit_width()
                    ),
                }
            }
            FixedWidthIntegerNodeExpression::I32FromU32(expr)
            | FixedWidthIntegerNodeExpression::U32FromI32(expr) => expr.emit_compute(lowering),
            FixedWidthIntegerNodeExpression::Select {
                selector,
                if_true,
                if_false,
            } => {
                let selector = selector.emit_compute(lowering)?;
                let if_true = if_true.emit_compute(lowering)?;
                let if_false = if_false.emit_compute(lowering)?;
                lowering.select_integer(selector, if_true, if_false)
            }
            FixedWidthIntegerNodeExpression::WrappingAdd { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.overflowing_add(lhs, rhs).map(|(value, _)| value)
            }
            FixedWidthIntegerNodeExpression::WrappingSub { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.overflowing_sub(lhs, rhs).map(|(value, _)| value)
            }
            FixedWidthIntegerNodeExpression::WrappingShl { lhs, magnitude } => {
                let lhs = lhs.emit_compute(lowering)?;
                lowering.shift_left(lhs, *magnitude)
            }
            FixedWidthIntegerNodeExpression::WrappingShr { lhs, magnitude } => {
                let lhs = lhs.emit_compute(lowering)?;
                lowering.shift_right(lhs, *magnitude)
            }
            FixedWidthIntegerNodeExpression::LowestBits { value, num_bits } => {
                let value = value.emit_compute(lowering)?;
                lowering.lowest_bits(value, *num_bits)
            }
            FixedWidthIntegerNodeExpression::BinaryNot(expr) => {
                let value = expr.emit_compute(lowering)?;
                lowering.bitwise_not(value)
            }
            FixedWidthIntegerNodeExpression::BinaryAnd { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.bitwise_binop(felt::bit_and, lhs, rhs)
            }
            FixedWidthIntegerNodeExpression::BinaryOr { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.bitwise_binop(felt::bit_or, lhs, rhs)
            }
            FixedWidthIntegerNodeExpression::BinaryXor { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                lowering.bitwise_binop(felt::bit_xor, lhs, rhs)
            }
            FixedWidthIntegerNodeExpression::MulLow { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                match (lhs, rhs) {
                    (IntegerValue::U8(lhs), IntegerValue::U8(rhs)) => {
                        Ok(IntegerValue::U8(lowering.append_lowest_bits_felt(
                            lowering.append_op_with_result(felt::mul(
                                lowering.unknown_location(),
                                lhs,
                                rhs,
                            )?)?,
                            8,
                        )?))
                    }
                    (IntegerValue::U16(lhs), IntegerValue::U16(rhs)) => {
                        Ok(IntegerValue::U16(lowering.append_lowest_bits_felt(
                            lowering.append_op_with_result(felt::mul(
                                lowering.unknown_location(),
                                lhs,
                                rhs,
                            )?)?,
                            16,
                        )?))
                    }
                    (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => Ok(IntegerValue::U32(
                        lowering.multiply_u32_unsigned(lhs, rhs)?.0,
                    )),
                    _ => bail!("MulLow requires operands of the same width"),
                }
            }
            FixedWidthIntegerNodeExpression::MulHigh { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                match (lhs, rhs) {
                    (IntegerValue::U8(lhs), IntegerValue::U8(rhs)) => {
                        Ok(IntegerValue::U8(lowering.append_shifted_low_bits(
                            lowering.append_op_with_result(felt::mul(
                                lowering.unknown_location(),
                                lhs,
                                rhs,
                            )?)?,
                            8,
                            8,
                        )?))
                    }
                    (IntegerValue::U16(lhs), IntegerValue::U16(rhs)) => {
                        Ok(IntegerValue::U16(lowering.append_shifted_low_bits(
                            lowering.append_op_with_result(felt::mul(
                                lowering.unknown_location(),
                                lhs,
                                rhs,
                            )?)?,
                            16,
                            16,
                        )?))
                    }
                    (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => Ok(IntegerValue::U32(
                        lowering.multiply_u32_unsigned(lhs, rhs)?.1,
                    )),
                    _ => bail!("MulHigh requires operands of the same width"),
                }
            }
            FixedWidthIntegerNodeExpression::DivAssumeNonzero { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                match (lhs, rhs) {
                    (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => {
                        Ok(IntegerValue::U32(lowering.div_rem_u32_nonzero(lhs, rhs)?.0))
                    }
                    _ => bail!("DivAssumeNonzero requires 32-bit operands"),
                }
            }
            FixedWidthIntegerNodeExpression::RemAssumeNonzero { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                match (lhs, rhs) {
                    (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => {
                        Ok(IntegerValue::U32(lowering.div_rem_u32_nonzero(lhs, rhs)?.1))
                    }
                    _ => bail!("RemAssumeNonzero requires 32-bit operands"),
                }
            }
            FixedWidthIntegerNodeExpression::SignedDivAssumeNonzeroNoOverflowBits { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                match (lhs, rhs) {
                    (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => Ok(IntegerValue::U32(
                        lowering.div_rem_i32_nonzero_no_overflow(lhs, rhs)?.0,
                    )),
                    _ => bail!("SignedDivAssumeNonzeroNoOverflowBits requires 32-bit operands"),
                }
            }
            FixedWidthIntegerNodeExpression::SignedRemAssumeNonzeroNoOverflowBits { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                match (lhs, rhs) {
                    (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => Ok(IntegerValue::U32(
                        lowering.div_rem_i32_nonzero_no_overflow(lhs, rhs)?.1,
                    )),
                    _ => bail!("SignedRemAssumeNonzeroNoOverflowBits requires 32-bit operands"),
                }
            }
            FixedWidthIntegerNodeExpression::SignedMulLowBits { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                match (lhs, rhs) {
                    (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => {
                        Ok(IntegerValue::U32(lowering.multiply_i32(lhs, rhs)?.0))
                    }
                    _ => bail!("SignedMulLowBits requires 32-bit operands"),
                }
            }
            FixedWidthIntegerNodeExpression::SignedMulHighBits { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                match (lhs, rhs) {
                    (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => {
                        Ok(IntegerValue::U32(lowering.multiply_i32(lhs, rhs)?.1))
                    }
                    _ => bail!("SignedMulHighBits requires 32-bit operands"),
                }
            }
            FixedWidthIntegerNodeExpression::SignedByUnsignedMulLowBits { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                match (lhs, rhs) {
                    (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => {
                        Ok(IntegerValue::U32(lowering.multiply_i32_u32(lhs, rhs)?.0))
                    }
                    _ => bail!("SignedByUnsignedMulLowBits requires 32-bit operands"),
                }
            }
            FixedWidthIntegerNodeExpression::SignedByUnsignedMulHighBits { lhs, rhs } => {
                let lhs = lhs.emit_compute(lowering)?;
                let rhs = rhs.emit_compute(lowering)?;
                match (lhs, rhs) {
                    (IntegerValue::U32(lhs), IntegerValue::U32(rhs)) => {
                        Ok(IntegerValue::U32(lowering.multiply_i32_u32(lhs, rhs)?.1))
                    }
                    _ => bail!("SignedByUnsignedMulHighBits requires 32-bit operands"),
                }
            }
            FixedWidthIntegerNodeExpression::AddProduct { .. } => {
                panic!("unsupported integer operation in @compute: {:?}", self)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use prover::cs::tables::TableDriver;
    use prover::field::Mersenne31Field;
    use prover::field::PrimeField;

    fn field(value: u64) -> Mersenne31Field {
        Mersenne31Field::from_u64_unchecked(value)
    }

    fn lookup_values<const N: usize>(
        table_driver: &TableDriver<Mersenne31Field>,
        table: TableType,
        inputs: &[u64],
    ) -> [u64; N] {
        let keys: Vec<_> = inputs.iter().copied().map(field).collect();
        table_driver
            .lookup_values::<N>(&keys, table.to_table_id())
            .map(|value| value.as_u64_reduced())
    }

    fn jump_branch_lookup_outputs(input_bits: u64, funct3: u64) -> [u64; 1] {
        let uf = input_bits & 1;
        let out_is_zero = (input_bits >> 1) & 1;
        let sign1 = (input_bits >> 2) & 1;
        let sign2 = (input_bits >> 3) & 1;

        let eq = out_is_zero != 0;
        let unsigned_lt = uf != 0;
        let signed_lt = if sign1 ^ sign2 == 1 {
            sign1 != 0
        } else {
            unsigned_lt
        };

        let flag = match funct3 {
            0b000 => eq,
            0b001 => !eq,
            0b010 | 0b100 => signed_lt,
            0b011 | 0b110 => unsigned_lt,
            0b101 => !signed_lt,
            0b111 => !unsigned_lt,
            _ => unreachable!(),
        };

        [flag as u64]
    }

    fn jump_cleanup_offset_outputs(input: u64) -> [u64; 2] {
        [(input >> 1) & 1, input & !0x3]
    }

    fn memory_get_offset_and_mask_with_trap_outputs(input: u64) -> [u64; 2] {
        let mem_address_low = input & 0xffff;
        let funct3 = (input >> 16) & 0b111;
        let is_store = ((input >> 17) & 1) != 0;
        let rd_is_x0 = ((input >> 18) & 1) != 0;

        let offset = mem_address_low & 0b11;
        let mut less_than_word = false;
        let mut is_trap = match (funct3, offset) {
            (0b010, offset) => offset != 0,
            (0b001, offset) | (0b101, offset) => {
                less_than_word = true;
                offset & 1 != 0
            }
            (0b000, _) | (0b100, _) => {
                less_than_word = true;
                false
            }
            _ => true,
        };
        let valid_funct3_for_load = matches!(funct3, 0b000 | 0b001 | 0b010 | 0b100 | 0b101);

        if valid_funct3_for_load && !is_store && rd_is_x0 {
            is_trap = false;
        }

        let use_high_limb = offset > 1;
        let mut bitmask = less_than_word as u64;
        bitmask |= (use_high_limb as u64) << 1;
        bitmask |= (is_trap as u64) << 2;

        [offset, bitmask]
    }

    fn rom_address_space_separator_outputs(input: u64) -> [u64; 2] {
        let bound = 1u64 << common_constants::ROM_SECOND_WORD_BITS;
        [(input >= bound) as u64, input % bound]
    }

    fn memory_load_halfword_or_byte_outputs(input: u64) -> [u64; 2] {
        let limb_value = input & 0xffff;
        let offset = (input >> 16) & 0b11;
        let funct3 = (input >> 18) & 0b111;
        let use_low_byte = offset & 1 == 0;

        match (funct3, offset) {
            (0b010, _) => [0, 0],
            (0b001, offset) => {
                if offset & 1 != 0 {
                    [0, 0]
                } else if (limb_value >> 15) != 0 {
                    [limb_value, 0xffff]
                } else {
                    [limb_value, 0]
                }
            }
            (0b101, offset) => {
                if offset & 1 != 0 {
                    [0, 0]
                } else {
                    [limb_value, 0]
                }
            }
            (0b000, _) => {
                let source = if use_low_byte {
                    limb_value & 0xff
                } else {
                    limb_value >> 8
                };
                if (source >> 7) != 0 {
                    [source | 0xff00, 0xffff]
                } else {
                    [source, 0]
                }
            }
            (0b100, _) => {
                let source = if use_low_byte {
                    limb_value & 0xff
                } else {
                    limb_value >> 8
                };
                [source, 0]
            }
            _ => [0, 0],
        }
    }

    fn mem_store_clear_original_ram_value_limb_outputs(input: u64) -> [u64; 2] {
        let limb_value = input & 0xffff;
        let offset = (input >> 16) & 0b11;
        let funct3 = (input >> 18) & 0b111;

        let cleaned_value = match (funct3, offset) {
            (0b010, _) | (0b001, _) => 0,
            (0b000, offset) => {
                let mask = if offset & 1 != 0 { 0x00ff } else { 0xff00 };
                limb_value & mask
            }
            _ => 0,
        };

        [cleaned_value, 0]
    }

    fn mem_store_clear_written_value_limb_outputs(input: u64) -> [u64; 2] {
        let limb_value = input & 0xffff;
        let offset = (input >> 16) & 0b11;
        let funct3 = (input >> 18) & 0b111;

        let cleaned_value = match (funct3, offset) {
            (0b010, _) => 0,
            (0b001, _) => limb_value,
            (0b000, offset) => {
                let value_to_store = limb_value & 0xff;
                if offset & 1 != 0 {
                    value_to_store << 8
                } else {
                    value_to_store
                }
            }
            _ => 0,
        };

        [cleaned_value, 0]
    }

    #[test]
    fn jump_branch_lookup_semantics_match_table_driver() {
        let bytecode_words = (1 << (16 + jump_branch_slt::ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
        let table_driver = jump_branch_slt::get_table_driver(&vec![0u32; bytecode_words]);

        for input_bits in 0..(1 << 4) {
            for funct3 in 0..(1 << 3) {
                assert_eq!(
                    lookup_values::<1>(
                        &table_driver,
                        TableType::ConditionalJmpBranchSlt,
                        &[input_bits, funct3],
                    ),
                    jump_branch_lookup_outputs(input_bits, funct3),
                );
            }
        }

        for input in 0..(1 << 16) {
            assert_eq!(
                lookup_values::<2>(&table_driver, TableType::JumpCleanupOffset, &[input]),
                jump_cleanup_offset_outputs(input),
            );
        }
    }

    #[test]
    fn subword_lookup_semantics_match_table_driver() {
        let bytecode_words =
            (1 << (16 + load_store_subword_only::ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
        let table_driver = load_store_subword_only::get_table_driver(&vec![0u32; bytecode_words]);

        for address_low in [0u64, 1, 2, 3, 0x1234, 0xffff] {
            for funct3 in 0..8u64 {
                for is_store in 0..=1u64 {
                    for rd_is_x0 in 0..=1u64 {
                        let input =
                            address_low | (funct3 << 16) | (is_store << 17) | (rd_is_x0 << 18);
                        assert_eq!(
                            lookup_values::<2>(
                                &table_driver,
                                TableType::MemoryGetOffsetAndMaskWithTrap,
                                &[input],
                            ),
                            memory_get_offset_and_mask_with_trap_outputs(input),
                        );
                    }
                }
            }
        }

        let rom_bound = 1u64 << common_constants::ROM_SECOND_WORD_BITS;
        for input in [
            0u64,
            1,
            rom_bound.saturating_sub(1),
            rom_bound,
            rom_bound + 1,
            0xffff,
        ] {
            assert_eq!(
                lookup_values::<2>(&table_driver, TableType::RomAddressSpaceSeparator, &[input]),
                rom_address_space_separator_outputs(input),
            );
        }

        let limb_values = [0u64, 1, 0x7f, 0x80, 0xff, 0x100, 0x7fff, 0x8000, 0xffff];
        for limb_value in limb_values {
            for offset in 0..4u64 {
                for funct3 in 0..8u64 {
                    let input = limb_value | (offset << 16) | (funct3 << 18);
                    assert_eq!(
                        lookup_values::<2>(
                            &table_driver,
                            TableType::MemoryLoadHalfwordOrByte,
                            &[input],
                        ),
                        memory_load_halfword_or_byte_outputs(input),
                    );
                    assert_eq!(
                        lookup_values::<2>(
                            &table_driver,
                            TableType::MemStoreClearOriginalRamValueLimb,
                            &[input],
                        ),
                        mem_store_clear_original_ram_value_limb_outputs(input),
                    );
                    assert_eq!(
                        lookup_values::<2>(
                            &table_driver,
                            TableType::MemStoreClearWrittenValueLimb,
                            &[input],
                        ),
                        mem_store_clear_written_value_limb_outputs(input),
                    );
                }
            }
        }
    }

    #[test]
    fn oracle_placeholder_encoding_is_stable_for_parameterized_variants() {
        assert_eq!(
            encode_oracle_placeholder(Placeholder::PcInit),
            EncodedOraclePlaceholder {
                kind: 6,
                arg0: 0,
                arg1: 0,
            }
        );
        assert_eq!(
            encode_oracle_placeholder(Placeholder::ShuffleRamReadValue(2)),
            EncodedOraclePlaceholder {
                kind: 43,
                arg0: 2,
                arg1: 0,
            }
        );
        assert_eq!(
            encode_oracle_placeholder(Placeholder::DelegationIndirectReadValue {
                register_index: 5,
                word_index: 1,
            }),
            EncodedOraclePlaceholder {
                kind: 56,
                arg0: 5,
                arg1: 1,
            }
        );
    }
}
