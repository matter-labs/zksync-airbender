//! LLZK circuit emission coordination and variable extraction helpers.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::ops::Deref;

use anyhow::anyhow;
use anyhow::bail;
use anyhow::Result;
use llzk::dialect::felt;
use llzk::prelude::*;
use prover::cs::constraint::Term;
use prover::cs::cs::circuit::CircuitOutput;
use prover::cs::cs::circuit::DisjunctiveLookup;
use prover::cs::cs::circuit::IndirectAccessType;
use prover::cs::cs::circuit::LinkedVariablesPair;
use prover::cs::cs::circuit::LookupQuery;
use prover::cs::cs::circuit::LookupQueryTableType;
use prover::cs::cs::circuit::PicusExpr;
use prover::cs::cs::circuit::PicusStructuredConstraint;
use prover::cs::cs::circuit::RangeCheckQuery;
use prover::cs::cs::circuit::RegisterAccessType;
use prover::cs::cs::circuit::RegisterAndIndirectAccesses;
use prover::cs::cs::circuit::ShuffleRamMemQuery;
use prover::cs::cs::circuit::ShuffleRamQueryType;
use prover::cs::definitions::AlignedColumnSet;
use prover::cs::definitions::BatchedRamTimestampComparisonAuxVars;
use prover::cs::definitions::ColumnAddress;
use prover::cs::definitions::CompiledDegree1Constraint;
use prover::cs::definitions::CompiledDegree2Constraint;
use prover::cs::definitions::LookupAndMemoryArgumentLayout;
use prover::cs::definitions::LookupInput;
use prover::cs::definitions::MemorySubtree;
use prover::cs::definitions::OpcodeFamilyCircuitState;
use prover::cs::definitions::RegisterAndIndirectAccessTimestampComparisonAuxVars;
use prover::cs::definitions::SetupLayout;
use prover::cs::definitions::Variable;
use prover::cs::definitions::WitnessSubtree;
use prover::cs::definitions::TIMESTAMP_COLUMNS_NUM_BITS;
use prover::cs::definitions::TIMESTAMP_STEP;
use prover::cs::one_row_compiler::CompiledCircuitArtifact;
use prover::cs::tables::LookupWrapper;
use prover::cs::tables::TableType;
use prover::cs::types::Boolean;
use prover::cs::types::Num;
use prover::field::PrimeField;

use crate::builder::*;
use crate::config::ConstraintLoweringMode;
use crate::config::LlzkStructLayout;
use crate::config::UnusedVariablePolicy;
use crate::constraints::AddConstraints;
use crate::constraints::EmitLlzkInConstrain;
use crate::field::FieldInfo;
use crate::witness::WitnessComputation;
use crate::witness::WitnessVariableUsage;

/// Trait implemented by types that can emit LLZK IR within the module scope.
pub(crate) trait EmitLlzkInModule<'ctx, F: FieldInfo> {
    type Output;

    fn emit_llzk(&self, env: &ModuleEnv<'ctx, F>) -> Result<Self::Output>;
}

/// Extension trait for [`StructDefOpLike`] that adds a method for filling the `@compute`
/// function.
pub trait AddCompute<'ctx: 'op, 'op, F: FieldInfo>: StructDefOpLike<'ctx, 'op> {
    /// Invokes the callback scoped in `@compute`. The `struct.new` and `function.return %self`
    /// operations are added automatically and do not need to be inserted by the provided callback.
    fn add_compute(
        &'op self,
        env: &'ctx ModuleEnv<'ctx, F>,
        f: impl FnOnce(&mut OpsBuilder<'ctx, 'op, F>) -> anyhow::Result<()>,
    ) -> anyhow::Result<()> {
        let compute_fn = self.get_compute_func().ok_or_else(|| {
            anyhow!(
                "struct {} is missing its @compute function",
                StructDefOpLike::name(self)
            )
        })?;
        let mut ops_builder = OpsBuilder::new(env, compute_fn);
        f(&mut ops_builder)
    }
}

impl<'ctx: 'op, 'op, F: FieldInfo, T: StructDefOpMutLike<'ctx, 'op>> AddCompute<'ctx, 'op, F>
    for T
{
}

/// Minimal compiled artifact used when LLZK only needs logical lowering and witness SSA.
///
/// Standalone logical recipes do not currently have a compatible one-row compiler entrypoint.
/// The backend still constructs a [`WitnessComputation`] for them, but logical lowering only
/// needs the variable mapping surface, so an empty artifact is sufficient.
pub(crate) fn empty_compiled_artifact<F: PrimeField>(
    variable_mapping: BTreeMap<Variable, ColumnAddress>,
) -> CompiledCircuitArtifact<F> {
    CompiledCircuitArtifact {
        witness_layout: WitnessSubtree {
            multiplicities_columns_for_range_check_16: Default::default(),
            multiplicities_columns_for_timestamp_range_check: Default::default(),
            multiplicities_columns_for_decoder_in_executor_families: Default::default(),
            multiplicities_columns_for_generic_lookup: Default::default(),
            range_check_8_columns: Default::default(),
            range_check_16_columns: Default::default(),
            width_3_lookups: Vec::new(),
            range_check_16_lookup_expressions: Vec::new(),
            timestamp_range_check_lookup_expressions: Vec::new(),
            offset_for_special_shuffle_ram_timestamps_range_check_expressions: 0,
            boolean_vars_columns_range: Default::default(),
            scratch_space_columns_range: Default::default(),
            total_width: 0,
        },
        memory_layout: MemorySubtree {
            shuffle_ram_inits_and_teardowns: Vec::new(),
            shuffle_ram_access_sets: Vec::new(),
            delegation_request_layout: None,
            delegation_processor_layout: None,
            machine_state_layout: None,
            intermediate_state_layout: None,
            batched_ram_accesses: Vec::new(),
            register_and_indirect_accesses: Vec::new(),
            total_width: 0,
        },
        setup_layout: SetupLayout {
            timestamp_setup_columns: Default::default(),
            range_check_16_setup_column: Default::default(),
            timestamp_range_check_setup_column: Default::default(),
            generic_lookup_setup_columns: Default::default(),
            preprocessed_decoder_setup_columns: Default::default(),
            total_width: 0,
        },
        stage_2_layout: LookupAndMemoryArgumentLayout {
            intermediate_polys_for_range_check_16:
                prover::cs::definitions::OptimizedOraclesForLookupWidth1::empty(),
            remainder_for_range_check_16: None,
            lazy_init_address_range_check_16: None,
            intermediate_polys_for_timestamp_range_checks:
                prover::cs::definitions::OptimizedOraclesForLookupWidth1::empty(),
            intermediate_polys_for_generic_lookup: AlignedColumnSet::empty(),
            intermediate_poly_for_decoder_accesses: AlignedColumnSet::empty(),
            intermediate_poly_for_range_check_16_multiplicity: AlignedColumnSet::empty(),
            intermediate_poly_for_timestamp_range_check_multiplicity: AlignedColumnSet::empty(),
            intermediate_polys_for_generic_multiplicities: AlignedColumnSet::empty(),
            intermediate_polys_for_decoder_multiplicities: AlignedColumnSet::empty(),
            delegation_processing_aux_poly: None,
            intermediate_polys_for_memory_init_teardown: AlignedColumnSet::empty(),
            intermediate_polys_for_memory_argument: AlignedColumnSet::empty(),
            intermediate_polys_for_state_permutation: AlignedColumnSet::empty(),
            intermediate_polys_for_permutation_masking: AlignedColumnSet::empty(),
            intermediate_poly_for_grand_product: AlignedColumnSet::empty(),
            ext4_polys_offset: 0,
            total_width: 0,
        },
        degree_2_constraints: Vec::new(),
        degree_1_constraints: Vec::new(),
        state_linkage_constraints: Vec::new(),
        public_inputs: Vec::new(),
        variable_mapping,
        scratch_space_size_for_witness_gen: 0,
        lazy_init_address_aux_vars: Vec::new(),
        memory_queries_timestamp_comparison_aux_vars: Vec::new(),
        batched_memory_access_timestamp_comparison_aux_vars: BatchedRamTimestampComparisonAuxVars {
            predicate: ColumnAddress::placeholder(),
            write_timestamp_columns: Default::default(),
            write_timestamp: [ColumnAddress::placeholder(); 2],
            aux_borrow_vars: Vec::new(),
        },
        register_and_indirect_access_timestamp_comparison_aux_vars:
            RegisterAndIndirectAccessTimestampComparisonAuxVars {
                predicate: ColumnAddress::placeholder(),
                write_timestamp_columns: Default::default(),
                write_timestamp: [ColumnAddress::placeholder(); 2],
                aux_borrow_sets: Vec::new(),
            },
        executor_family_circuit_next_timestamp_aux_var: None,
        executor_family_decoder_table_size: 0,
        trace_len: 1,
        table_offsets: Vec::new(),
        total_tables_size: 0,
    }
}

/// This enum holds information about extracted variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExtractedVariable {
    /// A register value represented by a low and high limb.
    Register { low: Variable, high: Variable },
    /// A scalar field element.
    Scalar(Variable),
}

impl ExtractedVariable {
    /// Create a new register.
    pub fn register(reg: [Variable; 2]) -> Self {
        Self::Register {
            low: reg[0],
            high: reg[1],
        }
    }

    /// Create a new felt.
    pub fn scalar(v: Variable) -> Self {
        Self::Scalar(v)
    }

    /// Checks if the given `variable` is contained in the extraction.
    pub fn contains(&self, v: &Variable) -> bool {
        match self {
            ExtractedVariable::Register { low, high } => v == low || v == high,
            ExtractedVariable::Scalar(variable) => v == variable,
        }
    }

    /// Number of contained vars.
    pub fn num_vars(&self) -> usize {
        match self {
            ExtractedVariable::Register { .. } => 2,
            ExtractedVariable::Scalar(_) => 1,
        }
    }

    /// Stable variable-oriented label for layout debug locations.
    pub fn debug_label(&self) -> String {
        match self {
            ExtractedVariable::Register { low, high } => format!("Register({low:?},{high:?})"),
            ExtractedVariable::Scalar(variable) => format!("{variable:?}"),
        }
    }
}

/// Explicit LLZK boundary description for circuits that do not expose an
/// `executor_machine_state`.
///
/// Standalone op harnesses and delegations build their own logical interface directly from the
/// underlying circuit variables. The backend uses this spec in place of the executor-state-based
/// extraction path used by unrolled opcode families.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LlzkBoundarySpec {
    pub inputs: Vec<ExtractedVariable>,
    pub outputs: Vec<ExtractedVariable>,
    pub include_shuffle_ram_io: bool,
    pub use_legacy_query2_input: bool,
    pub proof_system_signal_vars: BTreeSet<Variable>,
}

impl LlzkBoundarySpec {
    pub fn new(inputs: Vec<ExtractedVariable>, outputs: Vec<ExtractedVariable>) -> Self {
        Self {
            inputs,
            outputs,
            include_shuffle_ram_io: false,
            use_legacy_query2_input: false,
            proof_system_signal_vars: BTreeSet::new(),
        }
    }

    pub fn with_shuffle_ram_io(mut self) -> Self {
        self.include_shuffle_ram_io = true;
        self
    }

    pub fn with_signal_vars(mut self, signal_vars: impl IntoIterator<Item = Variable>) -> Self {
        self.proof_system_signal_vars.extend(signal_vars);
        self
    }
}

/// Trait for extracting inputs, outputs, and intermediate variables from the implementing circuit
/// representation.
pub trait VariableExtractor {
    /// Extract all variables that need to be passed as inputs.
    fn get_inputs(&self) -> Result<Vec<ExtractedVariable>>;
    /// Extract all variables that need to be produced as outputs.
    fn get_outputs(&self) -> Result<Vec<ExtractedVariable>>;
    /// Extract all variables that are only internal.
    fn get_intermediates(&self) -> Result<Vec<ExtractedVariable>>;
    /// Return whether an extracted output should be marked as a proof-system signal.
    fn is_signal_output(&self, _output: &ExtractedVariable) -> bool {
        true
    }
    /// Return whether an extracted intermediate should be marked as a proof-system signal.
    fn is_signal_intermediate(&self, _intermediate: &ExtractedVariable) -> bool {
        false
    }
}

impl<F: PrimeField> VariableExtractor for OpcodeFamilyCircuitState<F> {
    fn get_inputs(&self) -> Result<Vec<ExtractedVariable>> {
        // The source circuit also tracks many of these executor machine inputs through placeholder
        // substitutions for the witness/oracle path, so `@compute` lowers those placeholder
        // reads back to these inputs so the same logical value is not derived from two
        // unrelated sources downstream.
        let mut inputs = vec![
            ExtractedVariable::scalar(self.execute),
            ExtractedVariable::register(self.cycle_start_state.pc),
            ExtractedVariable::register(self.cycle_start_state.timestamp),
            ExtractedVariable::scalar(self.decoder_data.rs1_index),
            ExtractedVariable::scalar(self.decoder_data.rs2_index),
            ExtractedVariable::scalar(self.decoder_data.rd_index),
            ExtractedVariable::scalar(self.decoder_data.rd_is_zero),
            ExtractedVariable::register(self.decoder_data.imm),
            ExtractedVariable::scalar(self.decoder_data.funct3),
            ExtractedVariable::scalar(self.decoder_data.circuit_family_extra_mask),
        ];
        if let Some(v) = self.decoder_data.funct7 {
            inputs.push(ExtractedVariable::scalar(v));
        }
        inputs.sort();
        Ok(inputs)
    }

    fn get_outputs(&self) -> Result<Vec<ExtractedVariable>> {
        let mut outputs = vec![
            ExtractedVariable::register(self.cycle_end_state.pc),
            ExtractedVariable::register(self.cycle_end_state.timestamp),
        ];
        outputs.sort();
        Ok(outputs)
    }

    fn get_intermediates(&self) -> Result<Vec<ExtractedVariable>> {
        Ok(vec![])
    }
}

/// `unified_reduced_machine` still consumes shuffle query 2's write value as a pre-existing
/// witness input in its generated witness program. Other currently supported circuits can expose
/// that same logical value as a normal LLZK output member instead.
fn uses_legacy_query2_write_input(circuit_name: &str) -> bool {
    circuit_name == "unified_reduced_machine"
}

/// High-level categories the backend uses to decide whether a logical variable is live.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum VariableUsageSite {
    ExtractedInput,
    ExtractedOutput,
    Constraint,
    ParallelConstraint,
    Lookup,
    DisjunctiveLookup,
    BooleanInvariant,
    RangeCheck,
    LinkedVariable,
    ShuffleRamQuery,
    RegisterIndirectAccess,
    Substitution,
    WitnessRead,
    WitnessWrite,
}

/// Aggregated LLZK-facing usage facts for one logical variable.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct VariableUsageRecord {
    usage_sites: BTreeSet<VariableUsageSite>,
    compiled_mapping: Option<ColumnAddress>,
}

/// Result of classifying logical variables into live vs suspicious-unused buckets.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct VariableUsageAnalysis {
    live_variables: BTreeSet<Variable>,
    suspicious_unused_variables: BTreeSet<Variable>,
    records: BTreeMap<Variable, VariableUsageRecord>,
}

/// Backend-local report for a variable that ended up unused after LLZK-facing liveness analysis.
#[derive(Clone, Debug, PartialEq, Eq)]
struct UnusedVariableFinding {
    variable: Variable,
    emitted: bool,
    compiled_mapping: Option<ColumnAddress>,
    would_have_been_blanket_extracted: bool,
}

/// Complete extraction plan derived from logical variable liveness and CLI emission policy.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct VariableExtractionPlan {
    inputs: Vec<ExtractedVariable>,
    outputs: Vec<ExtractedVariable>,
    live_intermediates: Vec<ExtractedVariable>,
    emitted_intermediates: Vec<ExtractedVariable>,
    /// Logical variables that correspond to real proof-system storage in the compiled artifact.
    ///
    /// LLZK members/arguments backed by these variables should carry the `signal` attribute. Live
    /// logical values outside this set are true intermediates and remain non-signal even if they
    /// are emitted for debugging or compatibility.
    proof_system_signal_vars: BTreeSet<Variable>,
    bridge_eligible_member_vars: BTreeSet<Variable>,
    usage_analysis: VariableUsageAnalysis,
    unused_findings: Vec<UnusedVariableFinding>,
}

impl VariableExtractionPlan {
    fn classify<F: FieldInfo>(
        circuit_name: &str,
        circuit_output: &CircuitOutput<F>,
        compiled_artifact: &CompiledCircuitArtifact<F>,
        witness: &WitnessComputation<F>,
        boundary_spec: Option<&LlzkBoundarySpec>,
        unused_variable_policy: UnusedVariablePolicy,
        emit_suspicious_unused: bool,
    ) -> Result<Self> {
        let inputs = extracted_inputs(circuit_output, boundary_spec, circuit_name)?;
        let outputs = extracted_outputs(circuit_output, boundary_spec, circuit_name)?;
        let usage_analysis = analyze_variable_usage(
            circuit_output,
            compiled_artifact,
            witness,
            &inputs,
            &outputs,
        )?;
        let mut proof_system_signal_vars = usage_analysis
            .records
            .iter()
            .filter_map(|(variable, record)| {
                compiled_mapping_is_proof_system_signal(record.compiled_mapping)
                    .then_some(*variable)
            })
            .collect::<BTreeSet<_>>();
        if let Some(boundary_spec) = boundary_spec {
            proof_system_signal_vars.extend(boundary_spec.proof_system_signal_vars.iter().copied());
        }
        let input_vars = extracted_variable_set(&inputs);
        let output_vars = extracted_variable_set(&outputs);
        if boundary_spec.is_some() {
            proof_system_signal_vars.extend(input_vars.iter().copied());
            proof_system_signal_vars.extend(output_vars.iter().copied());
        }
        let mut live_intermediate_vars = usage_analysis
            .live_variables
            .iter()
            .copied()
            .filter(|variable| !input_vars.contains(variable) && !output_vars.contains(variable))
            .collect::<Vec<_>>();
        live_intermediate_vars.sort();

        let mut emitted_unused_vars = Vec::new();
        for variable in usage_analysis.suspicious_unused_variables.iter().copied() {
            if emit_suspicious_unused {
                emitted_unused_vars.push(variable);
            }
        }
        emitted_unused_vars.sort();
        emitted_unused_vars.dedup();

        let live_intermediates = live_intermediate_vars
            .iter()
            .copied()
            .map(ExtractedVariable::scalar)
            .collect::<Vec<_>>();
        let mut emitted_intermediates = live_intermediates.clone();
        emitted_intermediates.extend(
            emitted_unused_vars
                .iter()
                .copied()
                .map(ExtractedVariable::scalar),
        );
        emitted_intermediates.sort();

        let mut bridge_eligible_member_vars = output_vars.clone();
        bridge_eligible_member_vars.extend(live_intermediate_vars.iter().copied());

        let mut unused_findings = Vec::new();
        for variable in 0u64..u64::try_from(circuit_output.num_of_variables)? {
            let variable = Variable(variable);
            let Some(record) = usage_analysis.records.get(&variable) else {
                bail!("missing usage classification for {variable:?}");
            };
            if !usage_analysis
                .suspicious_unused_variables
                .contains(&variable)
            {
                continue;
            }
            unused_findings.push(UnusedVariableFinding {
                variable,
                emitted: emitted_unused_vars.binary_search(&variable).is_ok(),
                compiled_mapping: record.compiled_mapping,
                would_have_been_blanket_extracted: would_blanket_extract_intermediate(
                    circuit_output,
                    &input_vars,
                    &output_vars,
                    variable,
                ),
            });
        }

        handle_unused_variable_policy(circuit_name, unused_variable_policy, &unused_findings)?;

        Ok(Self {
            inputs,
            outputs,
            live_intermediates,
            emitted_intermediates,
            proof_system_signal_vars,
            bridge_eligible_member_vars,
            usage_analysis,
            unused_findings,
        })
    }

    fn print_unused_variable_report(
        &self,
        circuit_name: &str,
        unused_variable_policy: UnusedVariablePolicy,
    ) {
        if matches!(unused_variable_policy, UnusedVariablePolicy::Ignore)
            || self.unused_findings.is_empty()
        {
            return;
        }

        eprintln!(
            "unused variable summary for {}: {} suspicious",
            circuit_name,
            self.unused_findings.len()
        );
        for finding in &self.unused_findings {
            eprintln!(
                "  - suspicious {:?}: emitted={}, compiled_mapping={:?}, blanket_intermediate={}",
                finding.variable,
                finding.emitted,
                finding.compiled_mapping,
                finding.would_have_been_blanket_extracted,
            );
        }
    }
}

fn handle_unused_variable_policy(
    circuit_name: &str,
    unused_variable_policy: UnusedVariablePolicy,
    unused_findings: &[UnusedVariableFinding],
) -> Result<()> {
    if !matches!(unused_variable_policy, UnusedVariablePolicy::Error) {
        return Ok(());
    }

    let suspicious = unused_findings.iter().collect::<Vec<_>>();
    if suspicious.is_empty() {
        return Ok(());
    }

    bail!(
        "found {} suspicious unused logical variable(s) while generating {}: {}",
        suspicious.len(),
        circuit_name,
        suspicious
            .iter()
            .map(|finding| format!("{:?}", finding.variable))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn extracted_variable_set(vars: &[ExtractedVariable]) -> BTreeSet<Variable> {
    let mut set = BTreeSet::new();
    for var in vars {
        match var {
            ExtractedVariable::Register { low, high } => {
                set.insert(*low);
                set.insert(*high);
            }
            ExtractedVariable::Scalar(variable) => {
                set.insert(*variable);
            }
        }
    }
    set
}

/// Return whether a compiled variable mapping corresponds to a real proof-system signal.
///
/// LLZK `signal` members are values backed by witness or memory columns that actually participate
/// in the proof system. Setup-only columns and optimized-out scratch slots are still useful for
/// backend diagnostics, but they are not witness-stored signals and should remain plain
/// intermediates when emitted as logical members.
fn compiled_mapping_is_proof_system_signal(mapping: Option<ColumnAddress>) -> bool {
    matches!(
        mapping,
        Some(ColumnAddress::WitnessSubtree(_) | ColumnAddress::MemorySubtree(_))
    )
}

/// Return whether every limb of an extracted value maps to compiled witness/memory storage.
///
/// This is the backend's definition of a proof-system signal. Extracted values that are live only
/// in logical LLZK lowering remain non-signal intermediates even if they are emitted as members.
fn extracted_variable_is_signal(
    variable: &ExtractedVariable,
    proof_system_signal_vars: &BTreeSet<Variable>,
) -> bool {
    match variable {
        ExtractedVariable::Register { low, high } => {
            proof_system_signal_vars.contains(low) && proof_system_signal_vars.contains(high)
        }
        ExtractedVariable::Scalar(variable) => proof_system_signal_vars.contains(variable),
    }
}

fn would_blanket_extract_intermediate<F: PrimeField>(
    co: &CircuitOutput<F>,
    input_vars: &BTreeSet<Variable>,
    output_vars: &BTreeSet<Variable>,
    variable: Variable,
) -> bool {
    let in_ram_reads = co
        .shuffle_ram_queries
        .iter()
        .any(|q| q.read_value[0] == variable || q.read_value[1] == variable);
    !input_vars.contains(&variable) && !output_vars.contains(&variable) && !in_ram_reads
}

/// Classify logical variables by whether they participate in any LLZK-visible semantics.
///
/// This intentionally combines both `@compute`-side and `@constrain`-side usage so the backend
/// can distinguish semantically live values from variables that merely occupy the logical id
/// space but are never referenced by any emitted LLZK artifact.
fn analyze_variable_usage<F: FieldInfo>(
    circuit_output: &CircuitOutput<F>,
    compiled_artifact: &CompiledCircuitArtifact<F>,
    witness: &WitnessComputation<F>,
    inputs: &[ExtractedVariable],
    outputs: &[ExtractedVariable],
) -> Result<VariableUsageAnalysis> {
    let mut records = (0u64..u64::try_from(circuit_output.num_of_variables)?)
        .map(|raw| (Variable(raw), VariableUsageRecord::default()))
        .collect::<BTreeMap<_, _>>();

    for (&variable, &address) in &compiled_artifact.variable_mapping {
        if let Some(record) = records.get_mut(&variable) {
            record.compiled_mapping = Some(address);
        }
    }

    for input in inputs {
        mark_extracted_variable_usage(&mut records, input, VariableUsageSite::ExtractedInput)?;
    }
    for output in outputs {
        mark_extracted_variable_usage(&mut records, output, VariableUsageSite::ExtractedOutput)?;
    }

    for (constraint, _) in &circuit_output.constraints {
        for term in &constraint.terms {
            mark_term_usage(&mut records, term, VariableUsageSite::Constraint)?;
        }
    }
    if circuit_output
        .picus_extraction_metadata
        .parallel_constraints_enabled
    {
        for constraint in &circuit_output
            .picus_extraction_metadata
            .parallel_constraints
        {
            mark_parallel_constraint_usage(
                &mut records,
                constraint,
                VariableUsageSite::ParallelConstraint,
            )?;
        }
    }
    for lookup in &circuit_output.lookups {
        mark_lookup_query_usage(&mut records, lookup, VariableUsageSite::Lookup)?;
    }
    for relation in &circuit_output.picus_extraction_metadata.disjunctive_lookups {
        mark_disjunctive_lookup_usage(
            &mut records,
            relation,
            VariableUsageSite::DisjunctiveLookup,
        )?;
    }
    for variable in &circuit_output.boolean_vars {
        mark_usage(&mut records, *variable, VariableUsageSite::BooleanInvariant)?;
    }
    for range_check in &circuit_output.range_check_expressions {
        mark_range_check_usage(&mut records, range_check, VariableUsageSite::RangeCheck)?;
    }
    for linked in &circuit_output.linked_variables {
        mark_linked_variable_usage(&mut records, linked, VariableUsageSite::LinkedVariable)?;
    }
    for query in &circuit_output.shuffle_ram_queries {
        mark_shuffle_query_usage(&mut records, query, VariableUsageSite::ShuffleRamQuery)?;
    }
    for access in &circuit_output.register_and_indirect_memory_accesses {
        mark_register_and_indirect_usage(
            &mut records,
            access,
            VariableUsageSite::RegisterIndirectAccess,
        )?;
    }
    for variable in circuit_output.substitutions.values().copied() {
        mark_usage(&mut records, variable, VariableUsageSite::Substitution)?;
    }
    let witness_usage = witness.logical_variable_usage();
    mark_witness_usage(&mut records, &witness_usage)?;

    let live_variables = records
        .iter()
        .filter_map(|(variable, record)| (!record.usage_sites.is_empty()).then_some(*variable))
        .collect::<BTreeSet<_>>();
    let mut suspicious_unused_variables = BTreeSet::new();
    for (variable, record) in &records {
        if !record.usage_sites.is_empty() {
            continue;
        }
        suspicious_unused_variables.insert(*variable);
    }

    Ok(VariableUsageAnalysis {
        live_variables,
        suspicious_unused_variables,
        records,
    })
}

fn mark_usage(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    variable: Variable,
    site: VariableUsageSite,
) -> Result<()> {
    let Some(record) = records.get_mut(&variable) else {
        bail!("usage collection referenced out-of-range logical variable {variable:?}");
    };
    record.usage_sites.insert(site);
    Ok(())
}

fn mark_extracted_variable_usage(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    variable: &ExtractedVariable,
    site: VariableUsageSite,
) -> Result<()> {
    match variable {
        ExtractedVariable::Register { low, high } => {
            mark_usage(records, *low, site)?;
            mark_usage(records, *high, site)?;
        }
        ExtractedVariable::Scalar(variable) => mark_usage(records, *variable, site)?,
    }
    Ok(())
}

fn mark_boolean_usage(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    boolean: Boolean,
    site: VariableUsageSite,
) -> Result<()> {
    match boolean {
        Boolean::Is(variable) | Boolean::Not(variable) => mark_usage(records, variable, site)?,
        Boolean::Constant(_) => {}
    }
    Ok(())
}

fn mark_num_usage<F: PrimeField>(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    num: Num<F>,
    site: VariableUsageSite,
) -> Result<()> {
    if let Num::Var(variable) = num {
        mark_usage(records, variable, site)?;
    }
    Ok(())
}

fn mark_lookup_input_usage<F: PrimeField>(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    input: &LookupInput<F>,
    site: VariableUsageSite,
) -> Result<()> {
    match input {
        LookupInput::Variable(variable) => mark_usage(records, *variable, site)?,
        LookupInput::Expression { linear_terms, .. } => {
            for (_, variable) in linear_terms {
                mark_usage(records, *variable, site)?;
            }
        }
    }
    Ok(())
}

fn mark_term_usage<F: PrimeField>(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    term: &Term<F>,
    site: VariableUsageSite,
) -> Result<()> {
    if let Term::Expression { inner, degree, .. } = term {
        for variable in inner.iter().take(*degree) {
            mark_usage(records, *variable, site)?;
        }
    }
    Ok(())
}

fn mark_lookup_query_usage<F: PrimeField>(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    lookup: &LookupQuery<F>,
    site: VariableUsageSite,
) -> Result<()> {
    for input in &lookup.row {
        mark_lookup_input_usage(records, input, site)?;
    }
    if let LookupQueryTableType::Variable(variable) = lookup.table {
        mark_usage(records, variable, site)?;
    }
    Ok(())
}

fn mark_disjunctive_lookup_usage<F: PrimeField>(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    lookup: &DisjunctiveLookup<F>,
    site: VariableUsageSite,
) -> Result<()> {
    for case in &lookup.cases {
        mark_boolean_usage(records, case.flag, site)?;
        for input in &case.row {
            mark_lookup_input_usage(records, input, site)?;
        }
        mark_num_usage(records, case.table, site)?;
    }
    Ok(())
}

fn mark_range_check_usage<F: PrimeField>(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    query: &RangeCheckQuery<F>,
    site: VariableUsageSite,
) -> Result<()> {
    mark_lookup_input_usage(records, &query.input, site)
}

fn mark_linked_variable_usage(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    linked: &LinkedVariablesPair,
    site: VariableUsageSite,
) -> Result<()> {
    mark_usage(records, linked.initial_var, site)?;
    mark_usage(records, linked.final_var, site)
}

fn mark_shuffle_query_usage(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    query: &ShuffleRamMemQuery,
    site: VariableUsageSite,
) -> Result<()> {
    match query.query_type {
        ShuffleRamQueryType::RegisterOnly { register_index } => {
            mark_usage(records, register_index, site)?;
        }
        ShuffleRamQueryType::RegisterOrRam {
            is_register,
            address,
        } => {
            mark_boolean_usage(records, is_register, site)?;
            mark_usage(records, address[0], site)?;
            mark_usage(records, address[1], site)?;
        }
    }
    for variable in query.read_value {
        mark_usage(records, variable, site)?;
    }
    for variable in query.write_value {
        mark_usage(records, variable, site)?;
    }
    Ok(())
}

fn mark_register_and_indirect_usage(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    access: &RegisterAndIndirectAccesses,
    site: VariableUsageSite,
) -> Result<()> {
    match access.register_access {
        RegisterAccessType::Read { read_value } => {
            mark_usage(records, read_value[0], site)?;
            mark_usage(records, read_value[1], site)?;
        }
        RegisterAccessType::Write {
            read_value,
            write_value,
        } => {
            for variable in read_value.into_iter().chain(write_value) {
                mark_usage(records, variable, site)?;
            }
        }
    }
    for indirect in &access.indirect_accesses {
        match indirect {
            IndirectAccessType::Read {
                read_value,
                variable_dependent,
                ..
            } => {
                mark_usage(records, read_value[0], site)?;
                mark_usage(records, read_value[1], site)?;
                if let Some((_, variable, _)) = variable_dependent {
                    mark_usage(records, *variable, site)?;
                }
            }
            IndirectAccessType::Write {
                read_value,
                write_value,
                variable_dependent,
                ..
            } => {
                for variable in read_value.into_iter().chain(write_value) {
                    mark_usage(records, *variable, site)?;
                }
                if let Some((_, variable, _)) = variable_dependent {
                    mark_usage(records, *variable, site)?;
                }
            }
        }
    }
    Ok(())
}

fn mark_witness_usage(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    usage: &WitnessVariableUsage,
) -> Result<()> {
    for variable in &usage.read_vars {
        mark_usage(records, *variable, VariableUsageSite::WitnessRead)?;
    }
    for variable in &usage.write_vars {
        mark_usage(records, *variable, VariableUsageSite::WitnessWrite)?;
    }
    Ok(())
}

fn mark_parallel_constraint_usage<F: PrimeField>(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    constraint: &PicusStructuredConstraint<F>,
    site: VariableUsageSite,
) -> Result<()> {
    match constraint {
        PicusStructuredConstraint::Eq { lhs, rhs } => {
            mark_parallel_expr_usage(records, lhs, site)?;
            mark_parallel_expr_usage(records, rhs, site)?;
        }
    }
    Ok(())
}

fn mark_parallel_expr_usage<F: PrimeField>(
    records: &mut BTreeMap<Variable, VariableUsageRecord>,
    expr: &PicusExpr<F>,
    site: VariableUsageSite,
) -> Result<()> {
    match expr {
        PicusExpr::Variable(variable) => mark_usage(records, *variable, site)?,
        PicusExpr::Constant(_) => {}
        PicusExpr::Add(lhs, rhs) | PicusExpr::Sub(lhs, rhs) | PicusExpr::Mul(lhs, rhs) => {
            mark_parallel_expr_usage(records, lhs, site)?;
            mark_parallel_expr_usage(records, rhs, site)?;
        }
    }
    Ok(())
}

const COMPILED_WITNESS_COLUMNS_MEMBER: &str = "compiled_witness_columns";
const COMPILED_MEMORY_COLUMNS_MEMBER: &str = "compiled_memory_columns";

#[derive(Clone, Debug, PartialEq, Eq)]
struct MemberBinding {
    name: String,
    index: Option<u64>,
    is_public: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct InputBinding {
    arg_num: usize,
    index: Option<u64>,
}

/// One compiled-mode bridge from a logical member limb to a compiled witness/memory column.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CompiledMemberBridge {
    variable: Variable,
    member_name: String,
    member_index: Option<u64>,
    address: ColumnAddress,
    is_public: bool,
}

impl CompiledMemberBridge {
    fn debug_name(&self) -> String {
        match self.member_index {
            Some(index) => format!("{}[{index}]", self.member_name),
            None => self.member_name.clone(),
        }
    }
}

/// Summary of which logical members were bridged into compiled-mode constraints.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct CompiledMemberBridgeSummary {
    pub bridged_public_outputs: usize,
    pub bridged_internal_members: usize,
    pub unbridged_private_members: usize,
}

/// Summary of the dense compiled-column storage that LLZK materialized.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct CompiledStorageLayoutSummary {
    pub original_witness_width: usize,
    pub dense_witness_width: usize,
    pub original_memory_width: usize,
    pub dense_memory_width: usize,
}

impl CompiledStorageLayoutSummary {
    pub fn dropped_witness_slots(self) -> usize {
        self.original_witness_width
            .saturating_sub(self.dense_witness_width)
    }

    pub fn dropped_memory_slots(self) -> usize {
        self.original_memory_width
            .saturating_sub(self.dense_memory_width)
    }
}

/// Dense storage layout for compiled witness/memory columns in compiled LLZK mode.
///
/// The one-row compiler uses sparse witness/memory subtree offsets. LLZK stores those columns in
/// private arrays on the struct, so compiled mode remaps the used offsets to dense array indices
/// and leaves dead slots out of the emitted IR entirely.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct CompiledStorageLayout {
    original_witness_width: usize,
    original_memory_width: usize,
    witness_indices: BTreeMap<usize, usize>,
    memory_indices: BTreeMap<usize, usize>,
}

impl CompiledStorageLayout {
    /// Build the sparse compiled-column layout from the set of addresses LLZK can actually touch.
    fn from_compiled_artifact<F: FieldInfo>(
        compiled_artifact: &CompiledCircuitArtifact<F>,
        mapped_inputs: impl IntoIterator<Item = Variable>,
        mapped_members: impl IntoIterator<Item = Variable>,
        extra_addresses: impl IntoIterator<Item = ColumnAddress>,
    ) -> Result<Self> {
        let mut used_witness_offsets = BTreeSet::new();
        let mut used_memory_offsets = BTreeSet::new();
        let witness_width = compiled_artifact.witness_layout.total_width;
        let memory_width = compiled_artifact.memory_layout.total_width;

        let mut record = |address: ColumnAddress| -> Result<()> {
            match address {
                ColumnAddress::WitnessSubtree(offset) => {
                    if offset >= witness_width {
                        anyhow::bail!(
                            "compiled witness offset {offset} exceeds declared width {witness_width}"
                        );
                    }
                    used_witness_offsets.insert(offset);
                }
                ColumnAddress::MemorySubtree(offset) => {
                    if offset >= memory_width {
                        anyhow::bail!(
                            "compiled memory offset {offset} exceeds declared width {memory_width}"
                        );
                    }
                    used_memory_offsets.insert(offset);
                }
                _ => {}
            }
            Ok(())
        };

        for constraint in &compiled_artifact.degree_1_constraints {
            for (_, address) in constraint.linear_terms.iter() {
                record(*address)?;
            }
        }
        for constraint in &compiled_artifact.degree_2_constraints {
            for (_, address) in constraint.linear_terms.iter() {
                record(*address)?;
            }
            for (_, lhs, rhs) in constraint.quadratic_terms.iter() {
                record(*lhs)?;
                record(*rhs)?;
            }
        }
        for variable in mapped_inputs.into_iter().chain(mapped_members) {
            if let Some(address) = compiled_artifact.variable_mapping.get(&variable).copied() {
                record(address)?;
            }
        }
        for address in extra_addresses {
            record(address)?;
        }

        Ok(Self::from_used_offsets(
            witness_width,
            memory_width,
            &used_witness_offsets.into_iter().collect::<Vec<_>>(),
            &used_memory_offsets.into_iter().collect::<Vec<_>>(),
        )?)
    }

    fn from_used_offsets(
        original_witness_width: usize,
        original_memory_width: usize,
        witness_offsets: &[usize],
        memory_offsets: &[usize],
    ) -> Result<Self> {
        let mut witness_indices = BTreeMap::new();
        let mut memory_indices = BTreeMap::new();

        for (dense_idx, offset) in witness_offsets.iter().copied().enumerate() {
            if offset >= original_witness_width {
                anyhow::bail!(
                    "compiled witness offset {offset} exceeds declared width {original_witness_width}"
                );
            }
            witness_indices.insert(offset, dense_idx);
        }
        for (dense_idx, offset) in memory_offsets.iter().copied().enumerate() {
            if offset >= original_memory_width {
                anyhow::bail!(
                    "compiled memory offset {offset} exceeds declared width {original_memory_width}"
                );
            }
            memory_indices.insert(offset, dense_idx);
        }

        Ok(Self {
            original_witness_width,
            original_memory_width,
            witness_indices,
            memory_indices,
        })
    }

    fn remap(&self, address: ColumnAddress) -> Result<ColumnAddress> {
        match address {
            ColumnAddress::WitnessSubtree(offset) => self
                .witness_indices
                .get(&offset)
                .copied()
                .map(ColumnAddress::WitnessSubtree)
                .ok_or_else(|| {
                    anyhow!(
                        "compiled witness offset {offset} is not materialized in the sparse LLZK storage layout"
                    )
                }),
            ColumnAddress::MemorySubtree(offset) => self
                .memory_indices
                .get(&offset)
                .copied()
                .map(ColumnAddress::MemorySubtree)
                .ok_or_else(|| {
                    anyhow!(
                        "compiled memory offset {offset} is not materialized in the sparse LLZK storage layout"
                    )
                }),
            other => Err(anyhow!(
                "compiled sparse storage only supports witness/memory subtree addresses, got {other:?}"
            )),
        }
    }

    fn dense_witness_width(&self) -> usize {
        self.witness_indices.len()
    }

    fn dense_memory_width(&self) -> usize {
        self.memory_indices.len()
    }

    fn summary(&self) -> CompiledStorageLayoutSummary {
        CompiledStorageLayoutSummary {
            original_witness_width: self.original_witness_width,
            dense_witness_width: self.dense_witness_width(),
            original_memory_width: self.original_memory_width,
            dense_memory_width: self.dense_memory_width(),
        }
    }

    #[cfg(test)]
    fn identity(witness_width: usize, memory_width: usize) -> Self {
        Self::from_used_offsets(
            witness_width,
            memory_width,
            &(0..witness_width).collect::<Vec<_>>(),
            &(0..memory_width).collect::<Vec<_>>(),
        )
        .expect("identity compiled storage layout should always be valid")
    }
}

/// One compiled-mode bridge from an explicit `@constrain` argument to a compiled column.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CompiledInputBridge {
    variable: Variable,
    arg_num: usize,
    arg_index: Option<u64>,
    address: ColumnAddress,
}

/// Build the compiled-mode bridge list for logical members that still need a struct-level mirror.
fn build_compiled_member_bridges(
    member_map: &HashMap<Variable, MemberBinding>,
    bridge_eligible_member_vars: &BTreeSet<Variable>,
    variable_mapping: &BTreeMap<Variable, ColumnAddress>,
) -> Result<(Vec<CompiledMemberBridge>, CompiledMemberBridgeSummary)> {
    let mut members = member_map.iter().collect::<Vec<_>>();
    members.sort_by_key(|(variable, _)| variable.0);

    let mut bridges = Vec::new();
    let mut summary = CompiledMemberBridgeSummary::default();

    for (variable, binding) in members {
        if !bridge_eligible_member_vars.contains(variable) {
            continue;
        }
        match variable_mapping.get(variable).copied() {
            Some(
                address @ (ColumnAddress::WitnessSubtree(_) | ColumnAddress::MemorySubtree(_)),
            ) => {
                bridges.push(CompiledMemberBridge {
                    variable: *variable,
                    member_name: binding.name.clone(),
                    member_index: binding.index,
                    address,
                    is_public: binding.is_public,
                });
                if binding.is_public {
                    summary.bridged_public_outputs += 1;
                } else {
                    summary.bridged_internal_members += 1;
                }
            }
            Some(other) if binding.is_public => {
                anyhow::bail!(
                    "compiled mode requires public output member {} ({variable:?}) to map to a witness/memory column, found {other:?}",
                    match binding.index {
                        Some(index) => format!("{}[{index}]", binding.name),
                        None => binding.name.clone(),
                    }
                );
            }
            None if binding.is_public => {
                anyhow::bail!(
                    "compiled mode requires public output member {} ({variable:?}) to map to a compiled witness/memory column",
                    match binding.index {
                        Some(index) => format!("{}[{index}]", binding.name),
                        None => binding.name.clone(),
                    }
                );
            }
            _ => {
                summary.unbridged_private_members += 1;
            }
        }
    }

    Ok((bridges, summary))
}

/// Build the compiled-mode bridge list that ties explicit `@constrain` args to compiled columns.
fn build_compiled_input_bridges(
    input_map: &HashMap<Variable, InputBinding>,
    variable_mapping: &BTreeMap<Variable, ColumnAddress>,
) -> Vec<CompiledInputBridge> {
    let mut inputs = input_map.iter().collect::<Vec<_>>();
    inputs.sort_by_key(|(variable, binding)| (binding.arg_num, binding.index, variable.0));

    inputs
        .into_iter()
        .filter_map(
            |(variable, binding)| match variable_mapping.get(variable).copied() {
                Some(
                    address @ (ColumnAddress::WitnessSubtree(_) | ColumnAddress::MemorySubtree(_)),
                ) => Some(CompiledInputBridge {
                    variable: *variable,
                    arg_num: binding.arg_num,
                    arg_index: binding.index,
                    address,
                }),
                _ => None,
            },
        )
        .collect()
}

fn shuffle_write_value_is_input(query_index: usize, use_legacy_query2_input: bool) -> bool {
    use_legacy_query2_input && query_index == 2
}

fn extend_extracted_inputs_with_shuffle_queries<F: PrimeField>(
    inputs: &mut Vec<ExtractedVariable>,
    co: &CircuitOutput<F>,
    use_legacy_query2_input: bool,
) {
    for (query_index, query) in co.shuffle_ram_queries.iter().enumerate() {
        inputs.push(ExtractedVariable::register(query.read_value));
        if !query.is_readonly()
            && shuffle_write_value_is_input(query_index, use_legacy_query2_input)
        {
            inputs.push(ExtractedVariable::register(query.write_value));
        }
        if let ShuffleRamQueryType::RegisterOrRam {
            is_register,
            address,
        } = query.query_type
        {
            inputs.push(ExtractedVariable::register(address));
            if let Some(is_register) = is_register.get_variable() {
                inputs.push(ExtractedVariable::scalar(is_register));
            }
        }
    }
}

fn extend_extracted_outputs_with_shuffle_queries<F: PrimeField>(
    outputs: &mut Vec<ExtractedVariable>,
    co: &CircuitOutput<F>,
    use_legacy_query2_input: bool,
) {
    for (query_index, query) in co.shuffle_ram_queries.iter().enumerate() {
        if !query.is_readonly()
            && !shuffle_write_value_is_input(query_index, use_legacy_query2_input)
        {
            outputs.push(ExtractedVariable::register(query.write_value));
        }
    }
}

fn extracted_inputs<F: PrimeField>(
    co: &CircuitOutput<F>,
    boundary_spec: Option<&LlzkBoundarySpec>,
    circuit_name: &str,
) -> Result<Vec<ExtractedVariable>> {
    let mut inputs = if let Some(boundary_spec) = boundary_spec {
        boundary_spec.inputs.clone()
    } else {
        let exec_state = &co
            .executor_machine_state
            .ok_or_else(|| anyhow!("executor_machine_state not initialized"))?;
        exec_state.get_inputs()?
    };

    let use_legacy_query2_input = boundary_spec
        .map(|spec| spec.use_legacy_query2_input)
        .unwrap_or_else(|| uses_legacy_query2_write_input(circuit_name));
    if boundary_spec
        .map(|spec| spec.include_shuffle_ram_io)
        .unwrap_or(true)
    {
        extend_extracted_inputs_with_shuffle_queries(&mut inputs, co, use_legacy_query2_input);
    }
    inputs.sort();
    inputs.dedup();
    Ok(inputs)
}

fn extracted_outputs<F: PrimeField>(
    co: &CircuitOutput<F>,
    boundary_spec: Option<&LlzkBoundarySpec>,
    circuit_name: &str,
) -> Result<Vec<ExtractedVariable>> {
    let mut outputs = if let Some(boundary_spec) = boundary_spec {
        boundary_spec.outputs.clone()
    } else {
        let exec_state = &co
            .executor_machine_state
            .ok_or_else(|| anyhow!("executor_machine_state not initialized"))?;
        exec_state.get_outputs()?
    };
    let use_legacy_query2_input = boundary_spec
        .map(|spec| spec.use_legacy_query2_input)
        .unwrap_or_else(|| uses_legacy_query2_write_input(circuit_name));
    if boundary_spec
        .map(|spec| spec.include_shuffle_ram_io)
        .unwrap_or(true)
    {
        extend_extracted_outputs_with_shuffle_queries(&mut outputs, co, use_legacy_query2_input);
    }
    outputs.sort();
    outputs.dedup();
    Ok(outputs)
}

fn extracted_intermediates<F: PrimeField>(
    co: &CircuitOutput<F>,
    boundary_spec: Option<&LlzkBoundarySpec>,
    circuit_name: &str,
) -> Result<Vec<ExtractedVariable>> {
    let io = [
        extracted_inputs(co, boundary_spec, circuit_name)?,
        extracted_outputs(co, boundary_spec, circuit_name)?,
    ]
    .concat();
    let mut intermediates = (0u64..u64::try_from(co.num_of_variables)?)
        .map(Variable)
        .filter(|v| {
            let in_ram_reads = co
                .shuffle_ram_queries
                .iter()
                .any(|&q| q.read_value[0] == *v || q.read_value[1] == *v);
            let in_io = io.iter().any(|x| x.contains(v));
            !in_io && !in_ram_reads
        })
        .map(ExtractedVariable::Scalar)
        .collect::<Vec<_>>();

    intermediates.sort();
    Ok(intermediates)
}

impl<F: PrimeField> VariableExtractor for CircuitOutput<F> {
    fn get_inputs(&self) -> Result<Vec<ExtractedVariable>> {
        extracted_inputs(self, None, "")
    }

    fn get_outputs(&self) -> Result<Vec<ExtractedVariable>> {
        extracted_outputs(self, None, "")
    }

    fn get_intermediates(&self) -> Result<Vec<ExtractedVariable>> {
        extracted_intermediates(self, None, "")
    }
}

impl<F: FieldInfo> VariableExtractor for CircuitBundle<F> {
    fn get_inputs(&self) -> Result<Vec<ExtractedVariable>> {
        Ok(self.extraction_plan.inputs.clone())
    }

    fn get_outputs(&self) -> Result<Vec<ExtractedVariable>> {
        Ok(self.extraction_plan.outputs.clone())
    }

    fn get_intermediates(&self) -> Result<Vec<ExtractedVariable>> {
        Ok(self.extraction_plan.emitted_intermediates.clone())
    }

    fn is_signal_output(&self, output: &ExtractedVariable) -> bool {
        if self.boundary_spec.is_some() {
            extracted_variable_is_signal(output, &self.extraction_plan.proof_system_signal_vars)
        } else {
            true
        }
    }

    fn is_signal_intermediate(&self, intermediate: &ExtractedVariable) -> bool {
        extracted_variable_is_signal(intermediate, &self.extraction_plan.proof_system_signal_vars)
    }
}

fn num_vars(vars: impl IntoIterator<Item = ExtractedVariable>) -> usize {
    vars.into_iter().map(|v| v.num_vars()).sum()
}

fn emit_compiled_degree1_constraint<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    constraint: &CompiledDegree1Constraint<F>,
) -> Result<()> {
    let mut sum =
        builder.get_felt_constant_from_start(constraint.constant_term.as_u64_reduced())?;
    for (term_idx, (coeff, address)) in constraint.linear_terms.iter().enumerate() {
        builder.with_column_offset(term_idx, || {
            let col = vars.get_constrain_compiled_column(builder, *address)?;
            let scaled = builder.append_const_scaling_here(coeff.as_u64_reduced(), col)?;
            sum = builder.append_sum_here(&[sum, scaled])?;
            Ok(())
        })?;
    }
    builder.append_constrain_eq_here(sum, builder.get_felt_constant_from_start(0)?)
}

fn emit_compiled_degree2_constraint<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    constraint: &CompiledDegree2Constraint<F>,
) -> Result<()> {
    let mut terms =
        Vec::with_capacity(constraint.linear_terms.len() + constraint.quadratic_terms.len() + 1);
    terms.push(builder.get_felt_constant_from_start(constraint.constant_term.as_u64_reduced())?);
    for (term_idx, (coeff, address)) in constraint.linear_terms.iter().enumerate() {
        let scaled = builder.with_column_offset(term_idx, || {
            let col = vars.get_constrain_compiled_column(builder, *address)?;
            builder.append_const_scaling_here(coeff.as_u64_reduced(), col)
        })?;
        terms.push(scaled);
    }
    let quad_base = constraint.linear_terms.len();
    for (term_idx, (coeff, lhs, rhs)) in constraint.quadratic_terms.iter().enumerate() {
        let scaled = builder.with_column_offset(quad_base + term_idx, || {
            let lhs = vars.get_constrain_compiled_column(builder, *lhs)?;
            let rhs = vars.get_constrain_compiled_column(builder, *rhs)?;
            let product = builder.append_product_here(&[lhs, rhs])?;
            builder.append_const_scaling_here(coeff.as_u64_reduced(), product)
        })?;
        terms.push(scaled);
    }
    let sum = builder.append_sum_here(&terms)?;
    builder.append_constrain_eq_here(sum, builder.get_felt_constant_from_start(0)?)
}

fn emit_compiled_member_bridge<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    bridge: &CompiledMemberBridge,
) -> Result<()> {
    let logical = vars
        .get_constrain_member_val(builder, &bridge.variable)?
        .ok_or_else(|| {
            anyhow!(
                "compiled member bridge references unavailable member {} ({:?})",
                bridge.debug_name(),
                bridge.variable
            )
        })?;
    let compiled = vars.get_constrain_compiled_column(builder, bridge.address)?;
    builder.append_constrain_eq_here(logical, compiled)
}

fn emit_compiled_input_bridge<'ctx, 'sco, F: FieldInfo>(
    builder: &OpsBuilder<'ctx, 'sco, F>,
    vars: &StructVars<F>,
    bridge: &CompiledInputBridge,
) -> Result<()> {
    let logical = vars
        .get_constrain_input_val(builder, &bridge.variable)?
        .ok_or_else(|| {
            anyhow!(
                "compiled input bridge references unavailable input {:?}",
                bridge.variable
            )
        })?;
    let compiled = vars.get_constrain_compiled_column(builder, bridge.address)?;
    builder.append_constrain_eq_here(logical, compiled)
}

/// Metadata related to the circuit's `SpecialCSRProperties` lookup table, extracted
/// from the [`CircuitOutput`] for lowering convenience.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct SpecialCsrPropertiesMetadata {
    pub supported_only_indices: Vec<u16>,
    pub delegation_indices: Vec<u16>,
}

impl SpecialCsrPropertiesMetadata {
    /// Recover the `SpecialCSRProperties` table semantics from the finalized circuit output.
    pub(crate) fn new<F: FieldInfo>(circuit_output: &CircuitOutput<F>) -> Option<Self> {
        let LookupWrapper::Dimensional3(table) = circuit_output
            .table_driver
            .get_table(TableType::SpecialCSRProperties)
        else {
            return None;
        };

        let mut metadata = Self::default();
        for row in table.data.iter() {
            let csr_index = row[0].as_u64_reduced() as u16;
            let is_supported = !row[1].is_zero();
            let is_delegation = !row[2].is_zero();

            if is_delegation {
                metadata.delegation_indices.push(csr_index);
            } else if is_supported {
                metadata.supported_only_indices.push(csr_index);
            }
        }

        if metadata.is_empty() {
            None
        } else {
            Some(metadata)
        }
    }

    fn is_empty(&self) -> bool {
        self.supported_only_indices.is_empty() && self.delegation_indices.is_empty()
    }
}

/// Holds the circuit artifacts required to emit one LLZK circuit struct.
pub struct CircuitBundle<F: FieldInfo> {
    /// Name to give the emitted LLZK struct.
    name: String,
    /// The option for how to generate the `@compute`/`@constraint` or `@product`
    /// methods of the emitted LLZK struct.
    layout: LlzkStructLayout,
    /// Whether `@constrain` is lowered from logical constraints or compiled columns.
    constraint_lowering_mode: ConstraintLoweringMode,
    /// Policy for reporting suspicious unused variables.
    unused_variable_policy: UnusedVariablePolicy,
    /// The output of the airbender circuit, used for constraint and witness generation
    circuit_output: CircuitOutput<F>,
    /// One-row compiler output shared by witness lowering and compiled constraint lowering.
    compiled_artifact: CompiledCircuitArtifact<F>,
    /// Optional explicit LLZK boundary for circuits that do not expose an executor machine state.
    boundary_spec: Option<LlzkBoundarySpec>,
    /// The output of the witness SSA generation, used for generating witness computation in LLZK,
    /// and for logical variable liveness classification.
    witness: WitnessComputation<F>,
    /// Usage-based extraction/classification plan for this circuit.
    extraction_plan: VariableExtractionPlan,
}

impl<F: FieldInfo> CircuitBundle<F> {
    /// Create a new emission bundle for a single circuit.
    ///
    /// The witness program is always constructed because the backend uses it both for `@compute`
    /// lowering and for usage-based logical-variable classification, even in constrain-only modes.
    pub fn new(
        name: &str,
        layout: LlzkStructLayout,
        constraint_lowering_mode: ConstraintLoweringMode,
        unused_variable_policy: UnusedVariablePolicy,
        emit_suspicious_unused: bool,
        circuit_output: CircuitOutput<F>,
        compiled_artifact: CompiledCircuitArtifact<F>,
        boundary_spec: Option<LlzkBoundarySpec>,
        witness: WitnessComputation<F>,
    ) -> Result<Self> {
        let extraction_plan = VariableExtractionPlan::classify(
            name,
            &circuit_output,
            &compiled_artifact,
            &witness,
            boundary_spec.as_ref(),
            unused_variable_policy,
            emit_suspicious_unused,
        )?;
        Ok(Self {
            name: name.to_string(),
            layout,
            constraint_lowering_mode,
            unused_variable_policy,
            circuit_output,
            compiled_artifact,
            boundary_spec,
            witness,
            extraction_plan,
        })
    }

    /// Return a reference to the circuit's emitted struct name.
    pub fn name(&self) -> &str {
        &self.name
    }

    fn bridge_eligible_member_vars(&self) -> &BTreeSet<Variable> {
        &self.extraction_plan.bridge_eligible_member_vars
    }

    /// Additional compiled addresses that are materialized only by backend-specific helpers.
    ///
    /// The current compiled-mode lowering does not have any direct compiled-only accesses outside
    /// the one-row compiler's constraints and variable mapping, but keeping this hook explicit
    /// avoids silently forgetting future helper-introduced columns.
    fn extra_compiled_addresses(&self) -> Vec<ColumnAddress> {
        Vec::new()
    }

    /// Emit the compiler-defined executor timestamp transition into `@compute`.
    ///
    /// The one-row compiler always enforces
    /// `cycle_end_state.timestamp = cycle_start_state.timestamp + TIMESTAMP_STEP`
    /// for executor circuits. We must materialize that value in `@compute` in both lowering
    /// modes:
    /// - logical mode needs the explicit timestamp output member
    /// - compiled mode additionally needs the compiled witness/memory column that backs the same
    ///   logical member
    ///
    /// `@constrain` only needs the explicit timestamp patch in logical mode; compiled mode gets
    /// the constrain-side relation from compiled degree-1/degree-2 constraints.
    fn emit_executor_timestamp_compute<'ctx, 'sco>(
        &self,
        builder: &mut OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<()> {
        let Some(exec_state) = self.executor_machine_state.as_ref() else {
            return Ok(());
        };
        let [end_low_var, end_high_var] = exec_state.cycle_end_state.timestamp;
        if !vars.has_member(&end_low_var) || !vars.has_member(&end_high_var) {
            return Ok(());
        }

        builder.with_semantic_location(SemanticLocation::compute_executor_timestamp(), || {
            let self_value = builder.get_compute_self_value()?;
            let [start_low_var, start_high_var] = exec_state.cycle_start_state.timestamp;
            let start_low = vars.get_compute_val(builder, self_value, &start_low_var)?;
            let start_high = vars.get_compute_val(builder, self_value, &start_high_var)?;
            let step = builder.get_felt_constant_from_start(TIMESTAMP_STEP as u64)?;
            let modulus =
                builder.get_felt_constant_from_start(1u64 << TIMESTAMP_COLUMNS_NUM_BITS)?;
            let low_sum = builder.append_op_with_result(felt::add(
                builder.current_location(),
                start_low,
                step,
            )?)?;
            let end_low = builder.append_op_with_result(felt::umod(
                builder.current_location(),
                low_sum,
                modulus,
            )?)?;
            let carry = builder.append_op_with_result(felt::uintdiv(
                builder.current_location(),
                low_sum,
                modulus,
            )?)?;
            let end_high = builder.append_op_with_result(felt::add(
                builder.current_location(),
                start_high,
                carry,
            )?)?;
            let mut latest_timestamp_values = HashMap::new();
            vars.assign_compute_member_and_bridge_with_lookup(
                builder,
                self_value,
                &end_low_var,
                end_low,
                |var| latest_timestamp_values.get(var).copied(),
            )?;
            latest_timestamp_values.insert(end_low_var, end_low);
            vars.assign_compute_member_and_bridge_with_lookup(
                builder,
                self_value,
                &end_high_var,
                end_high,
                |var| latest_timestamp_values.get(var).copied(),
            )
        })
    }

    /// Emit the compiler-defined executor timestamp transition into `@constrain`.
    fn emit_executor_timestamp_constraints<'ctx, 'sco>(
        &self,
        builder: &mut OpsBuilder<'ctx, 'sco, F>,
        vars: &StructVars<F>,
    ) -> Result<()> {
        let Some(exec_state) = self.executor_machine_state.as_ref() else {
            return Ok(());
        };

        builder.with_semantic_location(SemanticLocation::constrain_executor_timestamp(), || {
            let [start_low_var, start_high_var] = exec_state.cycle_start_state.timestamp;
            let [end_low_var, end_high_var] = exec_state.cycle_end_state.timestamp;
            let start_low = vars.get_constrain_val(builder, &start_low_var)?;
            let start_high = vars.get_constrain_val(builder, &start_high_var)?;
            let end_low = vars.get_constrain_val(builder, &end_low_var)?;
            let end_high = vars.get_constrain_val(builder, &end_high_var)?;
            let step = builder.get_felt_constant_from_start(TIMESTAMP_STEP as u64)?;
            let modulus =
                builder.get_felt_constant_from_start(1u64 << TIMESTAMP_COLUMNS_NUM_BITS)?;
            let low_sum = builder.append_op_with_result(felt::add(
                builder.current_location(),
                start_low,
                step,
            )?)?;
            let expected_low = builder.append_op_with_result(felt::umod(
                builder.current_location(),
                low_sum,
                modulus,
            )?)?;
            let carry = builder.append_op_with_result(felt::uintdiv(
                builder.current_location(),
                low_sum,
                modulus,
            )?)?;
            let expected_high = builder.append_op_with_result(felt::add(
                builder.current_location(),
                start_high,
                carry,
            )?)?;
            builder.append_constrain_eq_here(end_low, expected_low)?;
            builder.append_constrain_eq_here(end_high, expected_high)?;
            builder.append_range_constraint(end_low, TIMESTAMP_COLUMNS_NUM_BITS as usize)?;
            builder.append_range_constraint(end_high, TIMESTAMP_COLUMNS_NUM_BITS as usize)
        })
    }
}

impl<F: FieldInfo> Deref for CircuitBundle<F> {
    type Target = CircuitOutput<F>;

    fn deref(&self) -> &Self::Target {
        &self.circuit_output
    }
}

impl<'ctx, F: FieldInfo> EmitLlzkInModule<'ctx, F> for CircuitBundle<F> {
    type Output = ();

    fn emit_llzk(&self, env: &ModuleEnv<'ctx, F>) -> Result<Self::Output> {
        if !F::is_built_in() {
            // To support this, we would need to add a FieldSpecAttr on the root module.
            todo!("non-built-in fields are not yet supported")
        }

        if matches!(self.layout, LlzkStructLayout::Product) {
            // To do this, we would continue to emit `@compute` and `@constrain` as we
            // currently do, but would then run the product program pass afterwards.
            todo!("@product program generation is currently unsupported");
        }

        let mut struct_builder = StructBuilder::new(env, self.name());
        struct_builder
            .with_location(env.semantic_location(SemanticLocation::layout_struct(self.name())))
            .with_compute_location(
                env.semantic_location(SemanticLocation::layout_function(self.name(), "compute")),
            )
            .with_constrain_location(
                env.semantic_location(SemanticLocation::layout_function(self.name(), "constrain")),
            );

        // Sanity check: usage classification should partition the full logical variable space.
        let num_input_vars = num_vars(self.get_inputs()?);
        let num_output_vars = num_vars(self.get_outputs()?);
        let num_live_intermediate_vars = num_vars(self.extraction_plan.live_intermediates.clone());
        let live_count = num_input_vars + num_output_vars + num_live_intermediate_vars;
        assert_eq!(
            self.extraction_plan.usage_analysis.live_variables.len(),
            live_count
        );
        let classified = self.extraction_plan.usage_analysis.live_variables.len()
            + self
                .extraction_plan
                .usage_analysis
                .suspicious_unused_variables
                .len();
        assert_eq!(self.num_of_variables, classified);

        let vars = StructVars::new(
            &self.circuit_output,
            &self.compiled_artifact,
            self.constraint_lowering_mode,
            &self.extra_compiled_addresses(),
            self.bridge_eligible_member_vars(),
            self,
            &mut struct_builder,
        )?;
        self.extraction_plan
            .print_unused_variable_report(self.name(), self.unused_variable_policy);
        if let Some(summary) = vars.compiled_bridge_summary() {
            eprintln!(
                "compiled member bridge summary for {}: {} bridged public outputs, {} bridged internal members, {} unbridged private members",
                self.name(),
                summary.bridged_public_outputs,
                summary.bridged_internal_members,
                summary.unbridged_private_members,
            );
        }
        if let Some(summary) = vars.compiled_storage_summary() {
            eprintln!(
                "compiled storage summary for {}: witness {} -> {} (dropped {}), memory {} -> {} (dropped {})",
                self.name(),
                summary.original_witness_width,
                summary.dense_witness_width,
                summary.dropped_witness_slots(),
                summary.original_memory_width,
                summary.dense_memory_width,
                summary.dropped_memory_slots(),
            );
        }
        let struct_op = struct_builder.build_in_module()?;

        if !matches!(&self.layout, LlzkStructLayout::ComputeOnly) {
            struct_op.add_constraints(
                env,
                |builder: &mut OpsBuilder<'_, '_, F>| -> Result<()> {
                    builder.with_semantic_location(
                        SemanticLocation::layout_function(self.name(), "constrain"),
                        || {
                            // Add some constants to reuse at the beginning here.
                            builder.insert_constant_at_start(builder.index_type(), 1)?;
                            builder.insert_constant_at_start(builder.index_type(), 0)?;
                            builder.insert_constant_at_start(builder.felt_type(), 1)?;
                            builder.insert_constant_at_start(builder.felt_type(), 0)?;
                            match self.constraint_lowering_mode {
                                ConstraintLoweringMode::Logical => {
                                    for (idx, bool_var) in self.boolean_vars.iter().enumerate() {
                                        builder.with_semantic_location(
                                            SemanticLocation::constrain_boolean(idx),
                                            || {
                                                let val =
                                                    vars.get_constrain_val(builder, bool_var)?;
                                                builder.append_boolean_constraint(val)
                                            },
                                        )?;
                                    }
                                    for (idx, range_check) in
                                        self.range_check_expressions.iter().enumerate()
                                    {
                                        builder.with_semantic_location(
                                            SemanticLocation::constrain_range_check(idx),
                                            || range_check.emit_constrain(builder, &vars),
                                        )?;
                                    }
                                    for (idx, lookup) in self.lookups.iter().enumerate() {
                                        builder.with_semantic_location(
                                            SemanticLocation::constrain_lookup(idx),
                                            || lookup.emit_constrain(builder, &vars),
                                        )?;
                                    }
                                    if self.picus_extraction_metadata.parallel_constraints_enabled {
                                        for (idx, constraint) in self
                                            .picus_extraction_metadata
                                            .parallel_constraints
                                            .iter()
                                            .enumerate()
                                        {
                                            builder.with_semantic_location(
                                                SemanticLocation::constrain_parallel_constraint(
                                                    idx,
                                                ),
                                                || constraint.emit_constrain(builder, &vars),
                                            )?;
                                        }
                                    } else {
                                        for (idx, constraint) in self.constraints.iter().enumerate()
                                        {
                                            builder.with_semantic_location(
                                                SemanticLocation::constrain_constraint(idx),
                                                || constraint.emit_constrain(builder, &vars),
                                            )?;
                                        }
                                    }
                                    for (idx, linked_pair) in
                                        self.linked_variables.iter().enumerate()
                                    {
                                        builder.with_semantic_location(
                                            SemanticLocation::constrain_linked_variable(idx),
                                            || {
                                                let initial = vars.get_constrain_val(
                                                    builder,
                                                    &linked_pair.initial_var,
                                                )?;
                                                let final_ = vars.get_constrain_val(
                                                    builder,
                                                    &linked_pair.final_var,
                                                )?;
                                                builder.append_constrain_eq_here(initial, final_)
                                            },
                                        )?;
                                    }
                                }
                                ConstraintLoweringMode::Compiled => {
                                    for (idx, constraint) in self
                                        .compiled_artifact
                                        .degree_1_constraints
                                        .iter()
                                        .enumerate()
                                    {
                                        builder.with_semantic_location(
                                            SemanticLocation::constrain_compiled_degree1(idx),
                                            || {
                                                emit_compiled_degree1_constraint(
                                                    builder, &vars, constraint,
                                                )
                                            },
                                        )?;
                                    }
                                    for (idx, constraint) in self
                                        .compiled_artifact
                                        .degree_2_constraints
                                        .iter()
                                        .enumerate()
                                    {
                                        builder.with_semantic_location(
                                            SemanticLocation::constrain_compiled_degree2(idx),
                                            || {
                                                emit_compiled_degree2_constraint(
                                                    builder, &vars, constraint,
                                                )
                                            },
                                        )?;
                                    }
                                    for (idx, bridge) in
                                        vars.compiled_input_bridges().iter().enumerate()
                                    {
                                        builder.with_semantic_location(
                                            SemanticLocation::constrain_compiled_input_bridge(idx),
                                            || emit_compiled_input_bridge(builder, &vars, bridge),
                                        )?;
                                    }
                                    for (idx, bridge) in
                                        vars.compiled_member_bridges().iter().enumerate()
                                    {
                                        builder.with_semantic_location(
                                            SemanticLocation::constrain_compiled_member_bridge(idx),
                                            || emit_compiled_member_bridge(builder, &vars, bridge),
                                        )?;
                                    }
                                }
                            }
                            Ok(())
                        },
                    )?;
                    if matches!(
                        self.constraint_lowering_mode,
                        ConstraintLoweringMode::Logical
                    ) {
                        self.emit_executor_timestamp_constraints(builder, &vars)
                    } else {
                        Ok(())
                    }
                },
            )?;
        }

        if !matches!(&self.layout, LlzkStructLayout::ConstrainOnly) {
            struct_op.add_compute(env, |builder: &mut OpsBuilder<'_, '_, F>| {
                builder.with_semantic_location(
                    SemanticLocation::layout_function(self.name(), "compute"),
                    || self.witness.emit_compute(builder, &vars),
                )?;
                self.emit_executor_timestamp_compute(builder, &vars)
            })?;

            self.witness.declare_runtime_externs(env)?;
        }
        Ok(())
    }
}

/// Holds the information about the variables and their representation in the LLZK struct.
pub struct StructVars<F: FieldInfo> {
    /// Ties [`StructVars`] to a specific field. This is prefered to having every member
    /// take the [`FieldInfo`] struct as a parameter, because mixed-field operations are
    /// currently not supported.
    _field: PhantomData<F>,
    /// Maps internal and output Variables to a tuple `(member name, optional index if the member
    /// is an array type)`. All members are assumed to be either felts or "registers", which are
    /// flat, two-element felt arrays.
    member_map: HashMap<Variable, MemberBinding>,
    /// Maps input variables to a tuple `(input arg number, optional limb index)`.
    ///
    /// The stored arg number is zero-based with respect to the logical circuit inputs. Constraint
    /// lowering adds one when reading from `@constrain` because argument 0 is the struct `self`
    /// value, while witness lowering uses the arg number directly in `@compute`.
    arg_map: HashMap<Variable, (usize, Option<u64>)>,
    /// Private array member holding compiled witness-subtree columns when compiled lowering is
    /// enabled.
    compiled_witness_member: Option<String>,
    compiled_storage_layout: Option<CompiledStorageLayout>,
    /// Private array member holding compiled memory-subtree columns when compiled lowering is
    /// enabled.
    compiled_memory_member: Option<String>,
    /// Explicit LLZK inputs mirrored into compiled witness/memory columns in compiled mode.
    compiled_input_bridges: Vec<CompiledInputBridge>,
    /// Logical members mirrored into compiled witness/memory columns in compiled mode.
    compiled_member_bridges: Vec<CompiledMemberBridge>,
    /// Fast bridge lookup for `@compute` writes.
    compiled_member_bridge_map: HashMap<Variable, ColumnAddress>,
    /// Validation summary for the compiled-mode bridge, populated only in compiled mode.
    compiled_bridge_summary: Option<CompiledMemberBridgeSummary>,
    /// Validation summary for sparse compiled storage, populated only in compiled mode.
    compiled_storage_summary: Option<CompiledStorageLayoutSummary>,
    /// Exact support/delegation policy for `SpecialCSRProperties`, if this circuit uses that
    /// table.
    special_csr_properties: Option<SpecialCsrPropertiesMetadata>,
}

impl<F: FieldInfo> StructVars<F> {
    fn member_variable_by_slot(&self, member_name: &str, index: Option<u64>) -> Option<Variable> {
        self.member_map.iter().find_map(|(variable, binding)| {
            (binding.name == member_name && binding.index == index).then_some(*variable)
        })
    }

    /// Creates a new [`StructVars`] instance by:
    /// - Extracting struct inputs/outputs/intermediate variables (into [`ExtractedVariable`]s) from
    ///   the provided [`CircuitOutput`] instance,
    /// - Adding new struct arguments and members based on the [`ExtractedVariable`]s
    fn new<'ctx, E: VariableExtractor>(
        co: &CircuitOutput<F>,
        compiled_artifact: &CompiledCircuitArtifact<F>,
        constraint_lowering_mode: ConstraintLoweringMode,
        extra_compiled_addresses: &[ColumnAddress],
        bridge_eligible_member_vars: &BTreeSet<Variable>,
        extractor: &E,
        struct_builder: &mut StructBuilder<'ctx, '_, F>,
    ) -> Result<Self> {
        let special_csr_properties = SpecialCsrPropertiesMetadata::new(co);
        let felt_type = struct_builder.felt_type();
        let register_type = struct_builder.register_type();
        let mut compiled_witness_member = None;
        let mut compiled_memory_member = None;
        // Add inputs to struct.
        let mut arg_map: HashMap<Variable, (usize, Option<u64>)> = HashMap::new();
        let mut input_map: HashMap<Variable, InputBinding> = HashMap::new();
        for (input_num, input) in extractor.get_inputs()?.iter().enumerate() {
            let debug_label = input.debug_label();
            let location = struct_builder.semantic_labeled_location(
                &debug_label,
                SemanticLocation::layout_argument(),
                SemanticLocation::layout_argument_label(&debug_label),
            );
            match input {
                ExtractedVariable::Register { low, high } => {
                    arg_map.insert(*low, (input_num, Some(0)));
                    arg_map.insert(*high, (input_num, Some(1)));
                    input_map.insert(
                        *low,
                        InputBinding {
                            arg_num: input_num,
                            index: Some(0),
                        },
                    );
                    input_map.insert(
                        *high,
                        InputBinding {
                            arg_num: input_num,
                            index: Some(1),
                        },
                    );
                    struct_builder.with_input_location(register_type, location);
                }
                ExtractedVariable::Scalar(variable) => {
                    arg_map.insert(*variable, (input_num, None));
                    input_map.insert(
                        *variable,
                        InputBinding {
                            arg_num: input_num,
                            index: None,
                        },
                    );
                    struct_builder.with_input_location(felt_type, location);
                }
            };
        }
        let compiled_storage_layout =
            if matches!(constraint_lowering_mode, ConstraintLoweringMode::Compiled) {
                Some(CompiledStorageLayout::from_compiled_artifact(
                    compiled_artifact,
                    input_map.keys().copied(),
                    bridge_eligible_member_vars.iter().copied(),
                    extra_compiled_addresses.iter().copied(),
                )?)
            } else {
                None
            };

        // Add outputs to struct.
        let mut member_map: HashMap<Variable, MemberBinding> = HashMap::new();
        for output in extractor.get_outputs()?.iter() {
            let debug_label = output.debug_label();
            let location = struct_builder.semantic_labeled_location(
                &debug_label,
                SemanticLocation::layout_member(),
                SemanticLocation::layout_member_label(&debug_label),
            );
            // TODO: better naming scheme
            match output {
                ExtractedVariable::Register { low, high } => {
                    let name = format!("out_reg_{}_{}", low.0, high.0);
                    member_map.insert(
                        *low,
                        MemberBinding {
                            name: name.clone(),
                            index: Some(0),
                            is_public: true,
                        },
                    );
                    member_map.insert(
                        *high,
                        MemberBinding {
                            name: name.clone(),
                            index: Some(1),
                            is_public: true,
                        },
                    );
                    if extractor.is_signal_output(output) {
                        struct_builder.with_signal_member_location(
                            name,
                            register_type,
                            true,
                            location,
                        );
                    } else {
                        struct_builder.with_member_location(name, register_type, true, location);
                    }
                }
                ExtractedVariable::Scalar(variable) => {
                    let name = format!("out_var_{}", variable.0);
                    member_map.insert(
                        *variable,
                        MemberBinding {
                            name: name.clone(),
                            index: None,
                            is_public: true,
                        },
                    );
                    if extractor.is_signal_output(output) {
                        struct_builder.with_signal_member_location(name, felt_type, true, location);
                    } else {
                        struct_builder.with_member_location(name, felt_type, true, location);
                    }
                }
            }
        }

        // Add intermediates to struct.
        for output in extractor.get_intermediates()?.iter() {
            let debug_label = output.debug_label();
            let location = struct_builder.semantic_labeled_location(
                &debug_label,
                SemanticLocation::layout_member(),
                SemanticLocation::layout_member_label(&debug_label),
            );
            match output {
                ExtractedVariable::Register { low, high } => {
                    let name = format!("internal_reg_{}_{}", low.0, high.0);
                    member_map.insert(
                        *low,
                        MemberBinding {
                            name: name.clone(),
                            index: Some(0),
                            is_public: false,
                        },
                    );
                    member_map.insert(
                        *high,
                        MemberBinding {
                            name: name.clone(),
                            index: Some(1),
                            is_public: false,
                        },
                    );
                    if extractor.is_signal_intermediate(output) {
                        struct_builder.with_signal_member_location(
                            name,
                            register_type,
                            false,
                            location,
                        );
                    } else {
                        struct_builder.with_member_location(name, register_type, false, location);
                    }
                }
                ExtractedVariable::Scalar(variable) => {
                    let name = format!("internal_var_{}", variable.0);
                    member_map.insert(
                        *variable,
                        MemberBinding {
                            name: name.clone(),
                            index: None,
                            is_public: false,
                        },
                    );
                    if extractor.is_signal_intermediate(output) {
                        struct_builder
                            .with_signal_member_location(name, felt_type, false, location);
                    } else {
                        struct_builder.with_member_location(name, felt_type, false, location);
                    }
                }
            }
        }

        let (compiled_member_bridges, compiled_bridge_summary) =
            if matches!(constraint_lowering_mode, ConstraintLoweringMode::Compiled) {
                let (bridges, summary) = build_compiled_member_bridges(
                    &member_map,
                    bridge_eligible_member_vars,
                    &compiled_artifact.variable_mapping,
                )?;
                (bridges, Some(summary))
            } else {
                (Vec::new(), None)
            };
        let compiled_input_bridges =
            if matches!(constraint_lowering_mode, ConstraintLoweringMode::Compiled) {
                build_compiled_input_bridges(&input_map, &compiled_artifact.variable_mapping)
            } else {
                Vec::new()
            };
        let compiled_member_bridge_map = compiled_member_bridges
            .iter()
            .map(|bridge| (bridge.variable, bridge.address))
            .collect();
        let compiled_storage_summary = compiled_storage_layout
            .as_ref()
            .map(CompiledStorageLayout::summary);

        if matches!(constraint_lowering_mode, ConstraintLoweringMode::Compiled) {
            let compiled_storage_layout = compiled_storage_layout
                .as_ref()
                .ok_or_else(|| anyhow!("compiled constraint lowering requires a storage layout"))?;
            if compiled_storage_layout.dense_witness_width() > 0 {
                struct_builder.with_signal_member(
                    COMPILED_WITNESS_COLUMNS_MEMBER.to_string(),
                    struct_builder
                        .felt_array_type(compiled_storage_layout.dense_witness_width())?,
                    false,
                );
                compiled_witness_member = Some(COMPILED_WITNESS_COLUMNS_MEMBER.to_string());
            }
            if compiled_storage_layout.dense_memory_width() > 0 {
                struct_builder.with_signal_member(
                    COMPILED_MEMORY_COLUMNS_MEMBER.to_string(),
                    struct_builder.felt_array_type(compiled_storage_layout.dense_memory_width())?,
                    false,
                );
                compiled_memory_member = Some(COMPILED_MEMORY_COLUMNS_MEMBER.to_string());
            }
        }

        Ok(Self {
            _field: PhantomData,
            member_map,
            arg_map,
            compiled_witness_member,
            compiled_storage_layout,
            compiled_memory_member,
            compiled_input_bridges,
            compiled_member_bridges,
            compiled_member_bridge_map,
            compiled_bridge_summary,
            compiled_storage_summary,
            special_csr_properties,
        })
    }

    /// Try to read a variable from the `@constrain` view of the struct.
    ///
    /// `@constrain` receives the struct instance as argument 0, so public inputs begin at
    /// argument 1.
    pub fn try_get_constrain_val<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        var: &Variable,
    ) -> Result<Option<Value<'ctx, 'sco>>> {
        if let Some(val) = self.get_constrain_input_val(builder, var)? {
            Ok(Some(val))
        } else {
            self.get_constrain_member_val(builder, var)
        }
    }

    /// Try to read a variable from the explicit `@constrain` input argument list, excluding
    /// struct-member fallback through `%arg0`.
    pub fn get_constrain_input_val<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        var: &Variable,
    ) -> Result<Option<Value<'ctx, 'sco>>> {
        self.get_input_val_at_offset::<1>(builder, var)
    }

    /// Read a variable from the `@constrain` view of the struct and error if it is unavailable.
    pub fn get_constrain_val<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        var: &Variable,
    ) -> Result<Value<'ctx, 'sco>> {
        self.try_get_constrain_val(builder, var)?
            .ok_or_else(|| anyhow!("Could not find {var:?} in constrain inputs or members"))
    }

    /// Try to read a variable from the explicit `@compute` argument list.
    pub fn try_get_compute_input_val<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        var: &Variable,
    ) -> Result<Option<Value<'ctx, 'sco>>> {
        // `@compute` does not receive a `self` argument. Its public inputs begin at argument 0 and
        // the partially constructed witness struct is the result of the leading `struct.new`.
        self.get_compute_arg_val(builder, var)
    }

    /// Try to read a variable from the full `@compute` view of the struct.
    ///
    /// This checks the explicit function arguments first and then falls back to struct member
    /// reads.
    pub fn try_get_compute_val<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        self_value: Value<'ctx, 'sco>,
        var: &Variable,
    ) -> Result<Option<Value<'ctx, 'sco>>> {
        if let Some(val) = self.try_get_compute_input_val(builder, var)? {
            Ok(Some(val))
        } else {
            self.get_member_val_from(builder, self_value, var)
        }
    }

    /// Read a variable from the `@compute` view of the struct and error if it is unavailable.
    pub fn get_compute_val<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        self_value: Value<'ctx, 'sco>,
        var: &Variable,
    ) -> Result<Value<'ctx, 'sco>> {
        self.try_get_compute_val(builder, self_value, var)?
            .ok_or_else(|| anyhow!("Could not find {var:?} in compute inputs or members"))
    }

    /// Return `true` when `var` is one of the explicit `@compute` arguments.
    pub fn has_compute_input(&self, var: &Variable) -> bool {
        self.arg_map.contains_key(var)
    }

    /// Return `true` when `var` is represented by a struct member.
    pub fn has_member(&self, var: &Variable) -> bool {
        self.member_map.contains_key(var)
    }

    /// Return `true` when compiled witness/memory column storage is present on the struct.
    pub fn has_compiled_storage(&self) -> bool {
        self.compiled_witness_member.is_some() || self.compiled_memory_member.is_some()
    }

    /// Return the logical-member bridges used only by compiled constraint lowering.
    pub fn compiled_member_bridges(&self) -> &[CompiledMemberBridge] {
        &self.compiled_member_bridges
    }

    /// Return the explicit-input bridges used only by compiled constraint lowering.
    pub fn compiled_input_bridges(&self) -> &[CompiledInputBridge] {
        &self.compiled_input_bridges
    }

    /// Return the compiled-mode member-bridge validation summary, if any.
    pub fn compiled_bridge_summary(&self) -> Option<CompiledMemberBridgeSummary> {
        self.compiled_bridge_summary
    }

    /// Return the compiled-mode sparse-storage validation summary, if any.
    pub fn compiled_storage_summary(&self) -> Option<CompiledStorageLayoutSummary> {
        self.compiled_storage_summary
    }

    /// Return the compiled witness/memory column mirrored by the logical struct member `var`.
    pub fn compiled_member_bridge_address(&self, var: &Variable) -> Option<ColumnAddress> {
        self.compiled_member_bridge_map.get(var).copied()
    }

    /// Return `true` when `var` is visible through either the `@compute` inputs or the returned
    /// struct.
    pub fn is_compute_exposed(&self, var: &Variable) -> bool {
        self.has_compute_input(var) || self.has_member(var)
    }

    /// Return metadata for the circuit's `SpecialCSRProperties` table when present.
    pub fn special_csr_properties(&self) -> Option<&SpecialCsrPropertiesMetadata> {
        self.special_csr_properties.as_ref()
    }

    /// Update `var` with `value` by creating a `struct.writem` operation in `@compute` targeting
    /// the struct member that corresponds to `var`.
    ///
    /// The function handles both scalar members and register-valued members, where a single
    /// logical variable corresponds to one limb of a two-element array.
    pub fn assign_compute_member<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        self_value: Value<'ctx, 'sco>,
        var: &Variable,
        value: Value<'ctx, 'sco>,
    ) -> Result<()> {
        self.assign_compute_member_with_lookup(builder, self_value, var, value, |_| None)
    }

    /// Update a struct member in `@compute`, rebuilding register-valued members from a fresh
    /// array so the write does not spuriously depend on the previous member value.
    ///
    /// `latest_value` is required for register members because LLZK stores them as one aggregate
    /// array member while witness SSA writes the two limbs independently. The helper uses the
    /// latest sibling limb value to assemble the full `[low, high]` register on every write.
    /// Without that logical cache, the fallback would be to re-read the struct member or insert a
    /// zero placeholder, both of which can produce semantically wrong `@compute` output.
    pub fn assign_compute_member_with_lookup<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        self_value: Value<'ctx, 'sco>,
        var: &Variable,
        value: Value<'ctx, 'sco>,
        mut latest_value: impl FnMut(&Variable) -> Option<Value<'ctx, 'sco>>,
    ) -> Result<()> {
        let binding = self
            .member_map
            .get(var)
            .ok_or_else(|| anyhow!("Variable {var:?} is not stored as a struct member"))?;
        let location = builder.current_location();
        match binding.index {
            None => builder.append_member_write(location, self_value, &binding.name, value),
            Some(index) => {
                let mut limbs = [None, None];
                for limb_idx in 0..2u64 {
                    let limb_var = self
                        .member_variable_by_slot(&binding.name, Some(limb_idx))
                        .ok_or_else(|| {
                            anyhow!(
                                "register member {} is missing limb {limb_idx} in member map",
                                binding.name
                            )
                        })?;
                    let limb_value = if limb_idx == index {
                        value
                    } else if let Some(existing) = latest_value(&limb_var) {
                        existing
                    } else {
                        builder.get_constant_from_start(builder.felt_type(), 0)?
                    };
                    limbs[limb_idx as usize] = Some(limb_value);
                }
                let register = builder.append_new_felt_array_from_values(
                    location,
                    &[
                        limbs[0].expect("register limb 0 must be initialized"),
                        limbs[1].expect("register limb 1 must be initialized"),
                    ],
                )?;
                builder.append_member_write(location, self_value, &binding.name, register)
            }
        }
    }

    /// Update a logical struct member and its compiled-column mirror, if one exists, using
    /// already-materialized compute values to rebuild register-valued members without reading
    /// their previous struct value.
    pub fn assign_compute_member_and_bridge_with_lookup<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        self_value: Value<'ctx, 'sco>,
        var: &Variable,
        value: Value<'ctx, 'sco>,
        latest_value: impl FnMut(&Variable) -> Option<Value<'ctx, 'sco>>,
    ) -> Result<()> {
        if let Some(address) = self.compiled_member_bridge_address(var) {
            self.assign_compute_compiled_column(builder, self_value, address, value)?;
        }
        self.assign_compute_member_with_lookup(builder, self_value, var, value, latest_value)
    }

    fn compiled_member_name(&self, address: ColumnAddress) -> Result<(&str, usize)> {
        match self.remap_compiled_address(address)? {
            ColumnAddress::WitnessSubtree(offset) => self
                .compiled_witness_member
                .as_deref()
                .map(|name| (name, offset))
                .ok_or_else(|| anyhow!("compiled witness column storage is unavailable")),
            ColumnAddress::MemorySubtree(offset) => self
                .compiled_memory_member
                .as_deref()
                .map(|name| (name, offset))
                .ok_or_else(|| anyhow!("compiled memory column storage is unavailable")),
            other => Err(anyhow!(
                "compiled column storage only supports witness/memory subtree addresses, got {other:?}"
            )),
        }
    }

    fn dense_compiled_width(&self, address: ColumnAddress) -> Result<usize> {
        let layout = self
            .compiled_storage_layout
            .as_ref()
            .ok_or_else(|| anyhow!("compiled storage layout is unavailable"))?;
        match address {
            ColumnAddress::WitnessSubtree(_) => Ok(layout.dense_witness_width()),
            ColumnAddress::MemorySubtree(_) => Ok(layout.dense_memory_width()),
            other => Err(anyhow!(
                "compiled sparse storage only supports witness/memory subtree addresses, got {other:?}"
            )),
        }
    }

    fn remap_compiled_address(&self, address: ColumnAddress) -> Result<ColumnAddress> {
        self.compiled_storage_layout
            .as_ref()
            .ok_or_else(|| anyhow!("compiled storage layout is unavailable"))?
            .remap(address)
    }

    /// Seed an uninitialized compiled-column array member in `@compute`.
    fn initialize_compute_compiled_storage<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        self_value: Value<'ctx, 'sco>,
        member_name: &str,
        len: usize,
    ) -> Result<()> {
        let location = builder.current_location();
        let new_array = builder.append_new_felt_array(location, len)?;
        builder.append_member_write(location, self_value, member_name, new_array)
    }

    /// Write a compiled witness/memory column through the private struct array in `@compute`.
    pub fn assign_compute_compiled_column<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        self_value: Value<'ctx, 'sco>,
        address: ColumnAddress,
        value: Value<'ctx, 'sco>,
    ) -> Result<()> {
        let (member_name, offset) = self.compiled_member_name(address)?;
        let location = builder.current_location();
        let array_ty = builder.felt_array_type(self.dense_compiled_width(address)?)?;
        let array = builder.append_member_read_here(self_value, array_ty, member_name)?;
        let index = builder.get_constant_from_start(builder.index_type(), offset as u64)?;
        builder.append_array_write(location, array, &[index], value)?;
        builder.append_member_write(location, self_value, member_name, array)
    }

    /// Read a compiled witness/memory column from the private struct array in `@compute`.
    pub fn get_compute_compiled_column<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        self_value: Value<'ctx, 'sco>,
        address: ColumnAddress,
    ) -> Result<Value<'ctx, 'sco>> {
        let (member_name, offset) = self.compiled_member_name(address)?;
        let member_ty = builder.felt_array_type(self.dense_compiled_width(address)?)?;
        let array = builder.append_member_read_here(self_value, member_ty, member_name)?;
        let index = builder.get_constant_from_start(builder.index_type(), offset as u64)?;
        builder.append_array_read_here(array, &[index])
    }

    /// Read a compiled witness/memory column from the private struct array in `@constrain`.
    pub fn get_constrain_compiled_column<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        address: ColumnAddress,
    ) -> Result<Value<'ctx, 'sco>> {
        let self_value = builder.get_arg_value(0)?;
        self.get_compute_compiled_column(builder, self_value, address)
    }

    /// Seed compiled-column storage from the explicit `@compute` arguments before SSA replay.
    pub fn seed_compute_compiled_inputs<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        self_value: Value<'ctx, 'sco>,
        variable_mapping: &std::collections::BTreeMap<Variable, ColumnAddress>,
    ) -> Result<()> {
        if let Some(member_name) = self.compiled_witness_member.as_deref() {
            self.initialize_compute_compiled_storage(
                builder,
                self_value,
                member_name,
                self.compiled_storage_layout
                    .as_ref()
                    .expect(
                        "compiled storage layout must exist when compiled witness storage exists",
                    )
                    .dense_witness_width(),
            )?;
        }
        if let Some(member_name) = self.compiled_memory_member.as_deref() {
            self.initialize_compute_compiled_storage(
                builder,
                self_value,
                member_name,
                self.compiled_storage_layout
                    .as_ref()
                    .expect(
                        "compiled storage layout must exist when compiled memory storage exists",
                    )
                    .dense_memory_width(),
            )?;
        }
        for (variable, _) in self.arg_map.iter() {
            if let Some(address) = variable_mapping.get(variable).copied() {
                if matches!(
                    address,
                    ColumnAddress::WitnessSubtree(_) | ColumnAddress::MemorySubtree(_)
                ) {
                    let value = self.get_compute_val(builder, self_value, variable)?;
                    self.assign_compute_compiled_column(builder, self_value, address, value)?;
                }
            }
        }
        Ok(())
    }

    fn get_input_val_at_offset<'ctx, 'sco, const ARG_OFFSET: usize>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        var: &Variable,
    ) -> Result<Option<Value<'ctx, 'sco>>> {
        match self.arg_map.get(var) {
            None => Ok(None),
            Some((arg_no, index)) => {
                let arg_val = builder.get_arg_value(*arg_no + ARG_OFFSET)?;
                let val = match index {
                    None => arg_val,
                    Some(index) => {
                        let indices =
                            &[builder.get_constant_from_start(builder.index_type(), *index)?];
                        builder.append_array_read_here(arg_val, indices)?
                    }
                };
                Ok(Some(val))
            }
        }
    }

    fn get_input_from_map<'ctx, 'sco, const ARG_OFFSET: usize>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        var: &Variable,
        arg_map: &HashMap<Variable, (usize, Option<u64>)>,
    ) -> Result<Option<Value<'ctx, 'sco>>> {
        match arg_map.get(var) {
            None => Ok(None),
            Some((arg_no, index)) => {
                let arg_val = builder.get_arg_value(*arg_no + ARG_OFFSET)?;
                let val = match index {
                    None => arg_val,
                    Some(index) => {
                        let indices =
                            &[builder.get_constant_from_start(builder.index_type(), *index)?];
                        builder.append_array_read_here(arg_val, indices)?
                    }
                };
                Ok(Some(val))
            }
        }
    }

    fn get_compute_arg_val<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        var: &Variable,
    ) -> Result<Option<Value<'ctx, 'sco>>> {
        self.get_input_from_map::<0>(builder, var, &self.arg_map)
    }

    fn get_constrain_member_val<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        var: &Variable,
    ) -> Result<Option<Value<'ctx, 'sco>>> {
        let self_val = builder.get_arg_value(0)?;
        self.get_member_val_from(builder, self_val, var)
    }

    /// Get the value from the struct member corresponding to `var` from the struct instance
    /// represented by `self_val`.
    fn get_member_val_from<'ctx, 'sco>(
        &self,
        builder: &OpsBuilder<'ctx, 'sco, F>,
        self_val: Value<'ctx, 'sco>,
        var: &Variable,
    ) -> Result<Option<Value<'ctx, 'sco>>> {
        match self.member_map.get(var) {
            None => Ok(None),
            Some(binding) => match binding.index {
                None => {
                    let member_ty = builder.felt_type();
                    let member_val =
                        builder.append_member_read_here(self_val, member_ty, &binding.name)?;
                    Ok(Some(member_val))
                }
                Some(index) => {
                    let member_ty = builder.register_type();
                    let member_val =
                        builder.append_member_read_here(self_val, member_ty, &binding.name)?;
                    let indices = &[builder.get_constant_from_start(builder.index_type(), index)?];
                    let read_val = builder.append_array_read_here(member_val, indices)?;
                    Ok(Some(read_val))
                }
            },
        }
    }

    /// A test-only function that allows direct construction of [`StructVars`] with synthetic
    /// struct members, arguments, and optional `SpecialCSRProperties` metadata.
    #[cfg(test)]
    pub(crate) fn from_test_maps_with_special_csr_properties(
        member_map: HashMap<Variable, (String, Option<u64>)>,
        arg_map: HashMap<Variable, (usize, Option<u64>)>,
        special_csr_properties: Option<SpecialCsrPropertiesMetadata>,
    ) -> Self {
        Self {
            member_map: member_map
                .into_iter()
                .map(|(variable, (name, index))| {
                    (
                        variable,
                        MemberBinding {
                            name,
                            index,
                            is_public: false,
                        },
                    )
                })
                .collect(),
            arg_map,
            compiled_witness_member: None,
            compiled_storage_layout: None,
            compiled_memory_member: None,
            compiled_input_bridges: Vec::new(),
            compiled_member_bridges: Vec::new(),
            compiled_member_bridge_map: HashMap::new(),
            compiled_bridge_summary: None,
            compiled_storage_summary: None,
            _field: PhantomData,
            special_csr_properties,
        }
    }

    #[cfg(test)]
    pub(crate) fn from_test_maps_with_compiled_storage(
        member_map: HashMap<Variable, (String, Option<u64>)>,
        arg_map: HashMap<Variable, (usize, Option<u64>)>,
        compiled_witness_width: usize,
        compiled_memory_width: usize,
        special_csr_properties: Option<SpecialCsrPropertiesMetadata>,
    ) -> Self {
        let compiled_storage_layout =
            CompiledStorageLayout::identity(compiled_witness_width, compiled_memory_width);
        Self {
            member_map: member_map
                .into_iter()
                .map(|(variable, (name, index))| {
                    (
                        variable,
                        MemberBinding {
                            name,
                            index,
                            is_public: false,
                        },
                    )
                })
                .collect(),
            arg_map,
            compiled_witness_member: (compiled_witness_width > 0)
                .then(|| COMPILED_WITNESS_COLUMNS_MEMBER.to_string()),
            compiled_storage_layout: Some(compiled_storage_layout.clone()),
            compiled_memory_member: (compiled_memory_width > 0)
                .then(|| COMPILED_MEMORY_COLUMNS_MEMBER.to_string()),
            compiled_input_bridges: Vec::new(),
            compiled_member_bridges: Vec::new(),
            compiled_member_bridge_map: HashMap::new(),
            compiled_bridge_summary: None,
            compiled_storage_summary: Some(compiled_storage_layout.summary()),
            _field: PhantomData,
            special_csr_properties,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::collections::HashMap;
    use std::marker::PhantomData;

    use anyhow::Result;
    use melior::ir::operation::OperationPrintingFlags;
    use prover::cs::constraint::Constraint;
    use prover::cs::constraint::Term;
    use prover::cs::cs::circuit::CircuitOutput;
    use prover::cs::cs::circuit::PicusExpr;
    use prover::cs::cs::circuit::PicusExtractionMetadata;
    use prover::cs::cs::circuit::PicusStructuredConstraint;
    use prover::cs::cs::witness_placer::graph_description::Expression;
    use prover::cs::cs::witness_placer::graph_description::FieldNodeExpression;
    use prover::cs::cs::witness_placer::graph_description::RawExpression;
    use prover::cs::definitions::AlignedColumnSet;
    use prover::cs::definitions::BatchedRamTimestampComparisonAuxVars;
    use prover::cs::definitions::ColumnAddress;
    use prover::cs::definitions::ColumnSet;
    use prover::cs::definitions::LookupAndMemoryArgumentLayout;
    use prover::cs::definitions::MemorySubtree;
    use prover::cs::definitions::RegisterAndIndirectAccessTimestampComparisonAuxVars;
    use prover::cs::definitions::SetupLayout;
    use prover::cs::definitions::WitnessSubtree;
    use prover::cs::one_row_compiler::CompiledCircuitArtifact;
    use prover::cs::tables::TableDriver;
    use prover::field::Field;
    use prover::field::Mersenne31Field;

    use super::*;
    use crate::config::ConstraintLoweringMode;
    use crate::config::DebugLocationStyle;
    use crate::config::LlzkStructLayout;
    use crate::config::UnusedVariablePolicy;

    fn empty_circuit_output(num_of_variables: usize) -> CircuitOutput<Mersenne31Field> {
        CircuitOutput {
            state_input: Vec::new(),
            state_output: Vec::new(),
            table_driver: TableDriver::new(),
            num_of_variables,
            constraints: Vec::new(),
            lookups: Vec::new(),
            shuffle_ram_queries: Vec::new(),
            delegated_computation_requests: Vec::new(),
            degegated_request_to_process: None,
            register_and_indirect_memory_accesses: Vec::new(),
            decoder_machine_state: None,
            executor_machine_state: None,
            linked_variables: Vec::new(),
            range_check_expressions: Vec::new(),
            boolean_vars: Vec::new(),
            substitutions: HashMap::new(),
            picus_extraction_metadata: PicusExtractionMetadata::default(),
        }
    }

    fn empty_compiled_artifact(
        variable_mapping: BTreeMap<Variable, ColumnAddress>,
    ) -> CompiledCircuitArtifact<Mersenne31Field> {
        CompiledCircuitArtifact {
            witness_layout: WitnessSubtree {
                multiplicities_columns_for_range_check_16: ColumnSet::empty(),
                multiplicities_columns_for_timestamp_range_check: ColumnSet::empty(),
                multiplicities_columns_for_decoder_in_executor_families: ColumnSet::empty(),
                multiplicities_columns_for_generic_lookup: ColumnSet::empty(),
                range_check_8_columns: ColumnSet::empty(),
                range_check_16_columns: ColumnSet::empty(),
                width_3_lookups: Vec::new(),
                range_check_16_lookup_expressions: Vec::new(),
                timestamp_range_check_lookup_expressions: Vec::new(),
                offset_for_special_shuffle_ram_timestamps_range_check_expressions: 0,
                boolean_vars_columns_range: ColumnSet::empty(),
                scratch_space_columns_range: ColumnSet::empty(),
                total_width: 0,
            },
            memory_layout: MemorySubtree {
                shuffle_ram_inits_and_teardowns: Vec::new(),
                shuffle_ram_access_sets: Vec::new(),
                delegation_request_layout: None,
                delegation_processor_layout: None,
                machine_state_layout: None,
                intermediate_state_layout: None,
                batched_ram_accesses: Vec::new(),
                register_and_indirect_accesses: Vec::new(),
                total_width: 0,
            },
            setup_layout: SetupLayout {
                timestamp_setup_columns: ColumnSet::empty(),
                range_check_16_setup_column: ColumnSet::empty(),
                timestamp_range_check_setup_column: ColumnSet::empty(),
                generic_lookup_setup_columns: ColumnSet::empty(),
                preprocessed_decoder_setup_columns: ColumnSet::empty(),
                total_width: 0,
            },
            stage_2_layout: LookupAndMemoryArgumentLayout {
                intermediate_polys_for_range_check_16:
                    prover::cs::definitions::OptimizedOraclesForLookupWidth1::empty(),
                remainder_for_range_check_16: None,
                lazy_init_address_range_check_16: None,
                intermediate_polys_for_timestamp_range_checks:
                    prover::cs::definitions::OptimizedOraclesForLookupWidth1::empty(),
                intermediate_polys_for_generic_lookup: AlignedColumnSet::empty(),
                intermediate_poly_for_decoder_accesses: AlignedColumnSet::empty(),
                intermediate_poly_for_range_check_16_multiplicity: AlignedColumnSet::empty(),
                intermediate_poly_for_timestamp_range_check_multiplicity: AlignedColumnSet::empty(),
                intermediate_polys_for_generic_multiplicities: AlignedColumnSet::empty(),
                intermediate_polys_for_decoder_multiplicities: AlignedColumnSet::empty(),
                delegation_processing_aux_poly: None,
                intermediate_polys_for_memory_init_teardown: AlignedColumnSet::empty(),
                intermediate_polys_for_memory_argument: AlignedColumnSet::empty(),
                intermediate_polys_for_state_permutation: AlignedColumnSet::empty(),
                intermediate_polys_for_permutation_masking: AlignedColumnSet::empty(),
                intermediate_poly_for_grand_product: AlignedColumnSet::empty(),
                ext4_polys_offset: 0,
                total_width: 0,
            },
            degree_2_constraints: Vec::new(),
            degree_1_constraints: Vec::new(),
            state_linkage_constraints: Vec::new(),
            public_inputs: Vec::new(),
            variable_mapping,
            scratch_space_size_for_witness_gen: 0,
            lazy_init_address_aux_vars: Vec::new(),
            memory_queries_timestamp_comparison_aux_vars: Vec::new(),
            batched_memory_access_timestamp_comparison_aux_vars:
                BatchedRamTimestampComparisonAuxVars {
                    predicate: ColumnAddress::placeholder(),
                    write_timestamp_columns: ColumnSet::empty(),
                    write_timestamp: [ColumnAddress::placeholder(); 2],
                    aux_borrow_vars: Vec::new(),
                },
            register_and_indirect_access_timestamp_comparison_aux_vars:
                RegisterAndIndirectAccessTimestampComparisonAuxVars {
                    predicate: ColumnAddress::placeholder(),
                    write_timestamp_columns: ColumnSet::empty(),
                    write_timestamp: [ColumnAddress::placeholder(); 2],
                    aux_borrow_sets: Vec::new(),
                },
            executor_family_circuit_next_timestamp_aux_var: None,
            executor_family_decoder_table_size: 0,
            trace_len: 1,
            table_offsets: Vec::new(),
            total_tables_size: 0,
        }
    }

    fn witness_with_ssa(
        ssa: Vec<Vec<RawExpression<Mersenne31Field>>>,
    ) -> WitnessComputation<Mersenne31Field> {
        WitnessComputation::new(
            empty_compiled_artifact(BTreeMap::new()),
            ssa,
            HashMap::new(),
            None,
        )
    }

    fn empty_witness() -> WitnessComputation<Mersenne31Field> {
        witness_with_ssa(vec![])
    }

    fn emit_bundle_ir(
        name: &str,
        circuit_output: CircuitOutput<Mersenne31Field>,
        boundary_spec: Option<LlzkBoundarySpec>,
        constraint_lowering_mode: ConstraintLoweringMode,
    ) -> String {
        let ctx = LlzkContext::new();
        let module = llzk_module(Location::unknown(&ctx));
        let env = ModuleEnv::<Mersenne31Field>::new(&ctx, &module, DebugLocationStyle::Named);
        let bundle = CircuitBundle::new(
            name,
            LlzkStructLayout::ConstrainOnly,
            constraint_lowering_mode,
            UnusedVariablePolicy::Ignore,
            false,
            circuit_output,
            empty_compiled_artifact(BTreeMap::new()),
            boundary_spec,
            empty_witness(),
        )
        .unwrap();
        bundle.emit_llzk(&env).unwrap();
        verify_operation_with_diags(&module.as_operation()).unwrap();
        module
            .as_operation()
            .to_string_with_flags(OperationPrintingFlags::new().enable_debug_info(true, false))
            .unwrap()
    }

    fn emit_compiled_constraint_ir(
        compiled_storage_layout: CompiledStorageLayout,
        emit: impl FnOnce(
            &OpsBuilder<'_, '_, Mersenne31Field>,
            &StructVars<Mersenne31Field>,
        ) -> Result<()>,
    ) -> String {
        let ctx = LlzkContext::new();
        let module = llzk_module(Location::unknown(&ctx));
        let env = ModuleEnv::<Mersenne31Field>::new(&ctx, &module, DebugLocationStyle::Named);
        let mut struct_builder = StructBuilder::new(&env, "compiled_constraint_test");
        struct_builder.with_member(
            COMPILED_WITNESS_COLUMNS_MEMBER.to_string(),
            env.felt_array_type(compiled_storage_layout.dense_witness_width())
                .expect("test witness width should fit in an LLZK array type"),
            false,
        );
        struct_builder.with_member(
            COMPILED_MEMORY_COLUMNS_MEMBER.to_string(),
            env.felt_array_type(compiled_storage_layout.dense_memory_width())
                .expect("test memory width should fit in an LLZK array type"),
            false,
        );

        let mut vars = StructVars::from_test_maps_with_compiled_storage(
            HashMap::new(),
            HashMap::new(),
            compiled_storage_layout.dense_witness_width(),
            compiled_storage_layout.dense_memory_width(),
            None,
        );
        vars.compiled_storage_layout = Some(compiled_storage_layout.clone());
        vars.compiled_storage_summary = Some(compiled_storage_layout.summary());

        let struct_op = struct_builder.build_in_module().unwrap();
        struct_op
            .add_constraints(&env, |ops| emit(ops, &vars))
            .unwrap();
        verify_operation_with_diags(&module.as_operation()).unwrap();
        module
            .as_operation()
            .to_string_with_flags(OperationPrintingFlags::new().enable_debug_info(true, false))
            .unwrap()
    }

    fn compiled_test_vars(
        member_map: HashMap<Variable, MemberBinding>,
        arg_map: HashMap<Variable, (usize, Option<u64>)>,
        input_bridges: Vec<CompiledInputBridge>,
        bridges: Vec<CompiledMemberBridge>,
        summary: CompiledMemberBridgeSummary,
        compiled_storage_layout: CompiledStorageLayout,
    ) -> StructVars<Mersenne31Field> {
        let compiled_member_bridge_map = bridges
            .iter()
            .map(|bridge| (bridge.variable, bridge.address))
            .collect();
        StructVars {
            _field: PhantomData,
            member_map,
            arg_map,
            compiled_witness_member: Some(COMPILED_WITNESS_COLUMNS_MEMBER.to_string()),
            compiled_storage_layout: Some(compiled_storage_layout.clone()),
            compiled_memory_member: Some(COMPILED_MEMORY_COLUMNS_MEMBER.to_string()),
            compiled_input_bridges: input_bridges,
            compiled_member_bridges: bridges,
            compiled_member_bridge_map,
            compiled_bridge_summary: Some(summary),
            compiled_storage_summary: Some(compiled_storage_layout.summary()),
            special_csr_properties: None,
        }
    }

    #[test]
    fn compiled_degree1_constraint_reads_compiled_columns() {
        let ir =
            emit_compiled_constraint_ir(CompiledStorageLayout::identity(4, 2), |builder, vars| {
                let constraint = CompiledDegree1Constraint {
                    linear_terms: Box::from([
                        (Mersenne31Field::ONE, ColumnAddress::WitnessSubtree(1)),
                        (Mersenne31Field::MINUS_ONE, ColumnAddress::MemorySubtree(0)),
                    ]),
                    constant_term: Mersenne31Field::ZERO,
                };
                builder
                    .with_semantic_location(SemanticLocation::constrain_compiled_degree1(0), || {
                        emit_compiled_degree1_constraint(builder, vars, &constraint)
                    })
            });

        assert!(ir.contains("@compiled_witness_columns"));
        assert!(ir.contains("@compiled_memory_columns"));
        assert!(ir.contains("llzk://constrain/compiled/degree1"));
    }

    #[test]
    fn compiled_degree2_constraint_emits_product_of_compiled_columns() {
        let ir =
            emit_compiled_constraint_ir(CompiledStorageLayout::identity(4, 2), |builder, vars| {
                let constraint = CompiledDegree2Constraint {
                    quadratic_terms: Box::from([(
                        Mersenne31Field::ONE,
                        ColumnAddress::WitnessSubtree(0),
                        ColumnAddress::MemorySubtree(1),
                    )]),
                    linear_terms: Box::from([(
                        Mersenne31Field::ONE,
                        ColumnAddress::WitnessSubtree(2),
                    )]),
                    constant_term: Mersenne31Field::ZERO,
                };
                builder
                    .with_semantic_location(SemanticLocation::constrain_compiled_degree2(0), || {
                        emit_compiled_degree2_constraint(builder, vars, &constraint)
                    })
            });

        assert!(ir.contains("felt.mul"));
        assert!(ir.contains("llzk://constrain/compiled/degree2"));
    }

    #[test]
    fn build_compiled_member_bridges_maps_public_scalar_members() {
        let member_map = HashMap::from([(
            Variable(7),
            MemberBinding {
                name: "out_var_7".to_string(),
                index: None,
                is_public: true,
            },
        )]);
        let variable_mapping = BTreeMap::from([(Variable(7), ColumnAddress::WitnessSubtree(3))]);

        let (bridges, summary) = build_compiled_member_bridges(
            &member_map,
            &BTreeSet::from([Variable(7)]),
            &variable_mapping,
        )
        .unwrap();

        assert_eq!(bridges.len(), 1);
        assert_eq!(bridges[0].variable, Variable(7));
        assert_eq!(bridges[0].member_name, "out_var_7");
        assert_eq!(bridges[0].member_index, None);
        assert_eq!(bridges[0].address, ColumnAddress::WitnessSubtree(3));
        assert_eq!(summary.bridged_public_outputs, 1);
        assert_eq!(summary.bridged_internal_members, 0);
        assert_eq!(summary.unbridged_private_members, 0);
    }

    #[test]
    fn compiled_storage_layout_remaps_sparse_offsets_to_dense_indices() {
        let layout = CompiledStorageLayout::from_used_offsets(10, 8, &[1, 4, 9], &[2, 7]).unwrap();

        assert_eq!(
            layout.remap(ColumnAddress::WitnessSubtree(1)).unwrap(),
            ColumnAddress::WitnessSubtree(0)
        );
        assert_eq!(
            layout.remap(ColumnAddress::WitnessSubtree(4)).unwrap(),
            ColumnAddress::WitnessSubtree(1)
        );
        assert_eq!(
            layout.remap(ColumnAddress::WitnessSubtree(9)).unwrap(),
            ColumnAddress::WitnessSubtree(2)
        );
        assert_eq!(
            layout.remap(ColumnAddress::MemorySubtree(2)).unwrap(),
            ColumnAddress::MemorySubtree(0)
        );
        assert_eq!(
            layout.remap(ColumnAddress::MemorySubtree(7)).unwrap(),
            ColumnAddress::MemorySubtree(1)
        );
        assert_eq!(layout.summary().dense_witness_width, 3);
        assert_eq!(layout.summary().dense_memory_width, 2);
    }

    #[test]
    fn compiled_storage_layout_errors_on_unmapped_offset() {
        let layout = CompiledStorageLayout::from_used_offsets(6, 5, &[1, 4], &[0, 2]).unwrap();
        let err = layout.remap(ColumnAddress::WitnessSubtree(3)).unwrap_err();
        assert!(err
            .to_string()
            .contains("compiled witness offset 3 is not materialized"));
    }

    #[test]
    fn build_compiled_member_bridges_maps_register_limbs_independently() {
        let member_map = HashMap::from([
            (
                Variable(10),
                MemberBinding {
                    name: "out_reg_10_11".to_string(),
                    index: Some(0),
                    is_public: true,
                },
            ),
            (
                Variable(11),
                MemberBinding {
                    name: "out_reg_10_11".to_string(),
                    index: Some(1),
                    is_public: true,
                },
            ),
        ]);
        let variable_mapping = BTreeMap::from([
            (Variable(10), ColumnAddress::WitnessSubtree(0)),
            (Variable(11), ColumnAddress::MemorySubtree(1)),
        ]);

        let (bridges, summary) = build_compiled_member_bridges(
            &member_map,
            &BTreeSet::from([Variable(10), Variable(11)]),
            &variable_mapping,
        )
        .unwrap();

        assert_eq!(bridges.len(), 2);
        assert_eq!(bridges[0].member_index, Some(0));
        assert_eq!(bridges[0].address, ColumnAddress::WitnessSubtree(0));
        assert_eq!(bridges[1].member_index, Some(1));
        assert_eq!(bridges[1].address, ColumnAddress::MemorySubtree(1));
        assert_eq!(summary.bridged_public_outputs, 2);
    }

    #[test]
    fn build_compiled_member_bridges_errors_on_unmapped_public_output() {
        let member_map = HashMap::from([(
            Variable(9),
            MemberBinding {
                name: "out_var_9".to_string(),
                index: None,
                is_public: true,
            },
        )]);

        let err = build_compiled_member_bridges(
            &member_map,
            &BTreeSet::from([Variable(9)]),
            &BTreeMap::new(),
        )
        .unwrap_err();
        assert!(err
            .to_string()
            .contains("compiled mode requires public output member out_var_9"));
    }

    #[test]
    fn build_compiled_member_bridges_allows_unmapped_private_member() {
        let member_map = HashMap::from([(
            Variable(9),
            MemberBinding {
                name: "internal_var_9".to_string(),
                index: None,
                is_public: false,
            },
        )]);

        let (bridges, summary) = build_compiled_member_bridges(
            &member_map,
            &BTreeSet::from([Variable(9)]),
            &BTreeMap::new(),
        )
        .unwrap();
        assert!(bridges.is_empty());
        assert_eq!(summary.unbridged_private_members, 1);
    }

    #[test]
    fn build_compiled_member_bridges_skips_members_that_are_not_bridge_eligible() {
        let member_map = HashMap::from([(
            Variable(9),
            MemberBinding {
                name: "internal_var_9".to_string(),
                index: None,
                is_public: false,
            },
        )]);
        let (bridges, summary) = build_compiled_member_bridges(
            &member_map,
            &BTreeSet::new(),
            &BTreeMap::from([(Variable(9), ColumnAddress::WitnessSubtree(0))]),
        )
        .unwrap();

        assert!(bridges.is_empty());
        assert_eq!(summary.unbridged_private_members, 0);
    }

    #[test]
    fn variable_used_only_in_logical_constraint_is_live() {
        let mut circuit_output = empty_circuit_output(3);
        circuit_output.constraints.push((
            Constraint {
                terms: vec![Term::Expression {
                    coeff: Mersenne31Field::ONE,
                    inner: [
                        Variable(1),
                        Variable::placeholder_variable(),
                        Variable::placeholder_variable(),
                        Variable::placeholder_variable(),
                    ],
                    degree: 1,
                }],
            },
            false,
        ));

        let usage = analyze_variable_usage(
            &circuit_output,
            &empty_compiled_artifact(BTreeMap::new()),
            &empty_witness(),
            &[],
            &[],
        )
        .unwrap();

        assert!(usage.live_variables.contains(&Variable(1)));
        assert!(usage.suspicious_unused_variables.contains(&Variable(0)));
        assert!(usage.suspicious_unused_variables.contains(&Variable(2)));
    }

    #[test]
    fn variable_used_only_in_witness_ssa_is_live() {
        let circuit_output = empty_circuit_output(3);
        let witness = witness_with_ssa(vec![vec![RawExpression::WriteVariable {
            into_variable: Variable(1),
            source_subexpr: Expression::Field(FieldNodeExpression::Place(Variable(2))),
            condition_subexpr_idx: None,
        }]]);

        let usage = analyze_variable_usage(
            &circuit_output,
            &empty_compiled_artifact(BTreeMap::new()),
            &witness,
            &[],
            &[],
        )
        .unwrap();

        assert!(usage.live_variables.contains(&Variable(1)));
        assert!(usage.live_variables.contains(&Variable(2)));
        assert!(usage
            .records
            .get(&Variable(1))
            .unwrap()
            .usage_sites
            .contains(&VariableUsageSite::WitnessWrite));
        assert!(usage
            .records
            .get(&Variable(2))
            .unwrap()
            .usage_sites
            .contains(&VariableUsageSite::WitnessRead));
    }

    #[test]
    fn unannotated_unused_variables_are_suspicious() {
        let usage = analyze_variable_usage(
            &empty_circuit_output(2),
            &empty_compiled_artifact(BTreeMap::new()),
            &empty_witness(),
            &[],
            &[],
        )
        .unwrap();

        assert!(usage.suspicious_unused_variables.contains(&Variable(0)));
        assert!(usage.suspicious_unused_variables.contains(&Variable(1)));
    }

    #[test]
    fn unused_variable_policy_error_fails_on_suspicious_findings() {
        let err = handle_unused_variable_policy(
            "synthetic",
            UnusedVariablePolicy::Error,
            &[UnusedVariableFinding {
                variable: Variable(5),
                emitted: false,
                compiled_mapping: None,
                would_have_been_blanket_extracted: true,
            }],
        )
        .unwrap_err();

        assert!(err
            .to_string()
            .contains("found 1 suspicious unused logical variable"));
    }

    #[test]
    fn compiled_mapping_signal_classification_only_accepts_witness_and_memory() {
        assert!(compiled_mapping_is_proof_system_signal(Some(
            ColumnAddress::WitnessSubtree(0)
        )));
        assert!(compiled_mapping_is_proof_system_signal(Some(
            ColumnAddress::MemorySubtree(0)
        )));
        assert!(!compiled_mapping_is_proof_system_signal(Some(
            ColumnAddress::SetupSubtree(0)
        )));
        assert!(!compiled_mapping_is_proof_system_signal(Some(
            ColumnAddress::OptimizedOut(0)
        )));
        assert!(!compiled_mapping_is_proof_system_signal(None));
    }

    #[test]
    fn load_store_subword_only_problematic_vars_are_not_proof_system_signals() {
        use load_store_subword_only::get_circuit;
        use load_store_subword_only::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;

        let bytecode_size = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
        let bytecode = vec![0u32; bytecode_size];
        let compiled = get_circuit(&bytecode);

        for variable in [Variable(28), Variable(29)] {
            let mapping = compiled.variable_mapping.get(&variable).copied();
            assert!(
                matches!(
                    mapping,
                    Some(ColumnAddress::SetupSubtree(_) | ColumnAddress::OptimizedOut(_))
                ),
                "{variable:?} unexpectedly mapped to {mapping:?}"
            );
            assert!(!compiled_mapping_is_proof_system_signal(mapping));
        }
    }

    #[test]
    fn mul_div_problematic_vars_are_not_proof_system_signals() {
        use mul_div::get_circuit;
        use mul_div::ROM_ADDRESS_SPACE_SECOND_WORD_BITS;

        let bytecode_size = (1 << (16 + ROM_ADDRESS_SPACE_SECOND_WORD_BITS)) / 4;
        let bytecode = vec![0u32; bytecode_size];
        let compiled = get_circuit(&bytecode);

        for variable in [Variable(40), Variable(41), Variable(48)] {
            let mapping = compiled.variable_mapping.get(&variable).copied();
            assert!(
                matches!(
                    mapping,
                    Some(ColumnAddress::SetupSubtree(_) | ColumnAddress::OptimizedOut(_))
                ),
                "{variable:?} unexpectedly mapped to {mapping:?}"
            );
            assert!(!compiled_mapping_is_proof_system_signal(mapping));
        }
    }

    #[test]
    fn build_compiled_input_bridges_maps_scalar_and_register_inputs() {
        let input_map = HashMap::from([
            (
                Variable(4),
                InputBinding {
                    arg_num: 0,
                    index: None,
                },
            ),
            (
                Variable(7),
                InputBinding {
                    arg_num: 1,
                    index: Some(0),
                },
            ),
            (
                Variable(8),
                InputBinding {
                    arg_num: 1,
                    index: Some(1),
                },
            ),
        ]);
        let variable_mapping = BTreeMap::from([
            (Variable(4), ColumnAddress::WitnessSubtree(2)),
            (Variable(7), ColumnAddress::MemorySubtree(0)),
            (Variable(8), ColumnAddress::MemorySubtree(1)),
        ]);

        let bridges = build_compiled_input_bridges(&input_map, &variable_mapping);

        assert_eq!(bridges.len(), 3);
        assert_eq!(bridges[0].variable, Variable(4));
        assert_eq!(bridges[0].arg_num, 0);
        assert_eq!(bridges[0].arg_index, None);
        assert_eq!(bridges[0].address, ColumnAddress::WitnessSubtree(2));
        assert_eq!(bridges[1].variable, Variable(7));
        assert_eq!(bridges[1].arg_num, 1);
        assert_eq!(bridges[1].arg_index, Some(0));
        assert_eq!(bridges[1].address, ColumnAddress::MemorySubtree(0));
        assert_eq!(bridges[2].variable, Variable(8));
        assert_eq!(bridges[2].arg_num, 1);
        assert_eq!(bridges[2].arg_index, Some(1));
        assert_eq!(bridges[2].address, ColumnAddress::MemorySubtree(1));
    }

    #[test]
    fn compiled_member_bridge_constrains_public_scalar_member() {
        let ctx = LlzkContext::new();
        let module = llzk_module(Location::unknown(&ctx));
        let env = ModuleEnv::<Mersenne31Field>::new(&ctx, &module, DebugLocationStyle::Named);
        let mut struct_builder = StructBuilder::new(&env, "compiled_member_bridge_test");
        struct_builder.with_member("out_var_7".to_string(), env.felt_type(), true);
        struct_builder.with_member(
            COMPILED_WITNESS_COLUMNS_MEMBER.to_string(),
            env.felt_array_type(4)
                .expect("test witness width should fit in an LLZK array type"),
            false,
        );
        struct_builder.with_member(
            COMPILED_MEMORY_COLUMNS_MEMBER.to_string(),
            env.felt_array_type(2)
                .expect("test memory width should fit in an LLZK array type"),
            false,
        );

        let member_map = HashMap::from([(
            Variable(7),
            MemberBinding {
                name: "out_var_7".to_string(),
                index: None,
                is_public: true,
            },
        )]);
        let (bridges, summary) = build_compiled_member_bridges(
            &member_map,
            &BTreeSet::from([Variable(7)]),
            &BTreeMap::from([(Variable(7), ColumnAddress::WitnessSubtree(1))]),
        )
        .unwrap();
        let vars = compiled_test_vars(
            member_map,
            HashMap::new(),
            Vec::new(),
            bridges.clone(),
            summary,
            CompiledStorageLayout::identity(4, 2),
        );

        let struct_op = struct_builder.build_in_module().unwrap();
        struct_op
            .add_constraints(&env, |ops| {
                ops.with_semantic_location(
                    SemanticLocation::constrain_compiled_member_bridge(0),
                    || emit_compiled_member_bridge(ops, &vars, &bridges[0]),
                )
            })
            .unwrap();
        verify_operation_with_diags(&module.as_operation()).unwrap();
        let ir = module
            .as_operation()
            .to_string_with_flags(OperationPrintingFlags::new().enable_debug_info(true, false))
            .unwrap();

        assert!(ir.contains("llzk://constrain/compiled/member_bridge"));
        assert!(ir.contains("@out_var_7"));
        assert!(ir.contains("@compiled_witness_columns"));
        assert!(ir.contains("constrain.eq"));
    }

    #[test]
    fn compiled_member_bridge_constrains_register_limb_members() {
        let ctx = LlzkContext::new();
        let module = llzk_module(Location::unknown(&ctx));
        let env = ModuleEnv::<Mersenne31Field>::new(&ctx, &module, DebugLocationStyle::Named);
        let mut struct_builder = StructBuilder::new(&env, "compiled_register_bridge_test");
        struct_builder.with_member("out_reg_10_11".to_string(), env.register_type(), true);
        struct_builder.with_member(
            COMPILED_WITNESS_COLUMNS_MEMBER.to_string(),
            env.felt_array_type(4)
                .expect("test witness width should fit in an LLZK array type"),
            false,
        );
        struct_builder.with_member(
            COMPILED_MEMORY_COLUMNS_MEMBER.to_string(),
            env.felt_array_type(2)
                .expect("test memory width should fit in an LLZK array type"),
            false,
        );

        let member_map = HashMap::from([
            (
                Variable(10),
                MemberBinding {
                    name: "out_reg_10_11".to_string(),
                    index: Some(0),
                    is_public: true,
                },
            ),
            (
                Variable(11),
                MemberBinding {
                    name: "out_reg_10_11".to_string(),
                    index: Some(1),
                    is_public: true,
                },
            ),
        ]);
        let (bridges, summary) = build_compiled_member_bridges(
            &member_map,
            &BTreeSet::from([Variable(10), Variable(11)]),
            &BTreeMap::from([
                (Variable(10), ColumnAddress::WitnessSubtree(0)),
                (Variable(11), ColumnAddress::WitnessSubtree(1)),
            ]),
        )
        .unwrap();
        let vars = compiled_test_vars(
            member_map,
            HashMap::new(),
            Vec::new(),
            bridges.clone(),
            summary,
            CompiledStorageLayout::identity(4, 2),
        );

        let struct_op = struct_builder.build_in_module().unwrap();
        struct_op
            .add_constraints(&env, |ops| {
                for (idx, bridge) in bridges.iter().enumerate() {
                    ops.with_semantic_location(
                        SemanticLocation::constrain_compiled_member_bridge(idx),
                        || emit_compiled_member_bridge(ops, &vars, bridge),
                    )?;
                }
                Ok(())
            })
            .unwrap();
        verify_operation_with_diags(&module.as_operation()).unwrap();
        let ir = module
            .as_operation()
            .to_string_with_flags(OperationPrintingFlags::new().enable_debug_info(true, false))
            .unwrap();

        assert!(ir.contains("@out_reg_10_11"));
        assert!(ir.contains("llzk://constrain/compiled/member_bridge"));
        assert!(ir.matches("constrain.eq").count() >= 2);
    }

    #[test]
    fn compiled_input_bridge_constrains_explicit_input_arg() {
        let ctx = LlzkContext::new();
        let module = llzk_module(Location::unknown(&ctx));
        let env = ModuleEnv::<Mersenne31Field>::new(&ctx, &module, DebugLocationStyle::Named);
        let mut struct_builder = StructBuilder::new(&env, "compiled_input_bridge_test");
        struct_builder.with_input(env.felt_type());
        struct_builder.with_member(
            COMPILED_WITNESS_COLUMNS_MEMBER.to_string(),
            env.felt_array_type(4)
                .expect("test witness width should fit in an LLZK array type"),
            false,
        );
        struct_builder.with_member(
            COMPILED_MEMORY_COLUMNS_MEMBER.to_string(),
            env.felt_array_type(2)
                .expect("test memory width should fit in an LLZK array type"),
            false,
        );

        let input_bridges = build_compiled_input_bridges(
            &HashMap::from([(
                Variable(7),
                InputBinding {
                    arg_num: 0,
                    index: None,
                },
            )]),
            &BTreeMap::from([(Variable(7), ColumnAddress::WitnessSubtree(1))]),
        );
        let vars = compiled_test_vars(
            HashMap::new(),
            HashMap::from([(Variable(7), (0, None))]),
            input_bridges.clone(),
            Vec::new(),
            CompiledMemberBridgeSummary::default(),
            CompiledStorageLayout::identity(4, 2),
        );

        let struct_op = struct_builder.build_in_module().unwrap();
        struct_op
            .add_constraints(&env, |ops| {
                ops.with_semantic_location(
                    SemanticLocation::constrain_compiled_input_bridge(0),
                    || emit_compiled_input_bridge(ops, &vars, &input_bridges[0]),
                )
            })
            .unwrap();
        verify_operation_with_diags(&module.as_operation()).unwrap();
        let ir = module
            .as_operation()
            .to_string_with_flags(OperationPrintingFlags::new().enable_debug_info(true, false))
            .unwrap();

        assert!(ir.contains("llzk://constrain/compiled/input_bridge"));
        assert!(ir.contains("%arg1"));
        assert!(ir.contains("@compiled_witness_columns"));
        assert!(ir.contains("constrain.eq"));
    }

    #[test]
    fn compiled_member_bridge_uses_dense_remapped_index() {
        let ctx = LlzkContext::new();
        let module = llzk_module(Location::unknown(&ctx));
        let env = ModuleEnv::<Mersenne31Field>::new(&ctx, &module, DebugLocationStyle::Named);
        let mut struct_builder = StructBuilder::new(&env, "compiled_sparse_member_bridge_test");
        struct_builder.with_member("out_var_7".to_string(), env.felt_type(), true);
        struct_builder.with_member(
            COMPILED_WITNESS_COLUMNS_MEMBER.to_string(),
            env.felt_array_type(1)
                .expect("test witness width should fit in an LLZK array type"),
            false,
        );
        let member_map = HashMap::from([(
            Variable(7),
            MemberBinding {
                name: "out_var_7".to_string(),
                index: None,
                is_public: true,
            },
        )]);
        let (bridges, summary) = build_compiled_member_bridges(
            &member_map,
            &BTreeSet::from([Variable(7)]),
            &BTreeMap::from([(Variable(7), ColumnAddress::WitnessSubtree(3))]),
        )
        .unwrap();
        let vars = compiled_test_vars(
            member_map,
            HashMap::new(),
            Vec::new(),
            bridges.clone(),
            summary,
            CompiledStorageLayout::from_used_offsets(8, 0, &[3], &[]).unwrap(),
        );

        let struct_op = struct_builder.build_in_module().unwrap();
        struct_op
            .add_constraints(&env, |ops| {
                ops.with_semantic_location(
                    SemanticLocation::constrain_compiled_member_bridge(0),
                    || emit_compiled_member_bridge(ops, &vars, &bridges[0]),
                )
            })
            .unwrap();
        verify_operation_with_diags(&module.as_operation()).unwrap();
        let ir = module
            .as_operation()
            .to_string_with_flags(OperationPrintingFlags::new().enable_debug_info(true, false))
            .unwrap();

        assert!(ir.contains("[%c0]"));
        assert!(!ir.contains("[%c3]"));
        assert!(ir.contains("!array.type<1 x !felt.type<\"mersenne31\">>"));
    }

    #[test]
    fn compiled_input_bridge_uses_dense_remapped_index() {
        let ctx = LlzkContext::new();
        let module = llzk_module(Location::unknown(&ctx));
        let env = ModuleEnv::<Mersenne31Field>::new(&ctx, &module, DebugLocationStyle::Named);
        let mut struct_builder = StructBuilder::new(&env, "compiled_sparse_input_bridge_test");
        struct_builder.with_input(env.felt_type());
        struct_builder.with_member(
            COMPILED_WITNESS_COLUMNS_MEMBER.to_string(),
            env.felt_array_type(1)
                .expect("test witness width should fit in an LLZK array type"),
            false,
        );

        let input_bridges = build_compiled_input_bridges(
            &HashMap::from([(
                Variable(7),
                InputBinding {
                    arg_num: 0,
                    index: None,
                },
            )]),
            &BTreeMap::from([(Variable(7), ColumnAddress::WitnessSubtree(3))]),
        );
        let vars = compiled_test_vars(
            HashMap::new(),
            HashMap::from([(Variable(7), (0, None))]),
            input_bridges.clone(),
            Vec::new(),
            CompiledMemberBridgeSummary::default(),
            CompiledStorageLayout::from_used_offsets(8, 0, &[3], &[]).unwrap(),
        );

        let struct_op = struct_builder.build_in_module().unwrap();
        struct_op
            .add_constraints(&env, |ops| {
                ops.with_semantic_location(
                    SemanticLocation::constrain_compiled_input_bridge(0),
                    || emit_compiled_input_bridge(ops, &vars, &input_bridges[0]),
                )
            })
            .unwrap();
        verify_operation_with_diags(&module.as_operation()).unwrap();
        let ir = module
            .as_operation()
            .to_string_with_flags(OperationPrintingFlags::new().enable_debug_info(true, false))
            .unwrap();

        assert!(ir.contains("[%c0]"));
        assert!(!ir.contains("[%c3]"));
        assert!(ir.contains("!array.type<1 x !felt.type<\"mersenne31\">>"));
    }

    #[test]
    fn logical_lowering_uses_parallel_constraints_when_enabled() {
        let ordinary_var = Variable(0);
        let parallel_var = Variable(1);
        let mut circuit_output = empty_circuit_output(2);
        circuit_output.constraints.push((
            Constraint {
                terms: vec![Term::from(ordinary_var)],
            },
            false,
        ));
        circuit_output.picus_extraction_metadata = PicusExtractionMetadata {
            parallel_constraints_enabled: true,
            parallel_constraints: vec![PicusStructuredConstraint::Eq {
                lhs: PicusExpr::Variable(parallel_var),
                rhs: PicusExpr::Constant(Mersenne31Field::ONE),
            }],
            ..PicusExtractionMetadata::default()
        };
        let boundary_spec = Some(
            LlzkBoundarySpec::new(
                vec![
                    ExtractedVariable::scalar(ordinary_var),
                    ExtractedVariable::scalar(parallel_var),
                ],
                Vec::new(),
            )
            .with_signal_vars(BTreeSet::from([ordinary_var, parallel_var])),
        );

        let ir = emit_bundle_ir(
            "parallel_constraints_test",
            circuit_output,
            boundary_spec,
            ConstraintLoweringMode::Logical,
        );

        assert!(ir.contains("llzk://constrain/parallel_constraints"));
        assert!(!ir.contains("llzk://constrain/constraints"));
    }

    #[test]
    fn logical_lowering_uses_ordinary_constraints_when_parallel_disabled() {
        let ordinary_var = Variable(0);
        let parallel_var = Variable(1);
        let mut circuit_output = empty_circuit_output(2);
        circuit_output.constraints.push((
            Constraint {
                terms: vec![Term::from(ordinary_var)],
            },
            false,
        ));
        circuit_output.picus_extraction_metadata = PicusExtractionMetadata {
            parallel_constraints_enabled: false,
            parallel_constraints: vec![PicusStructuredConstraint::Eq {
                lhs: PicusExpr::Variable(parallel_var),
                rhs: PicusExpr::Constant(Mersenne31Field::ONE),
            }],
            ..PicusExtractionMetadata::default()
        };
        let boundary_spec = Some(
            LlzkBoundarySpec::new(
                vec![
                    ExtractedVariable::scalar(ordinary_var),
                    ExtractedVariable::scalar(parallel_var),
                ],
                Vec::new(),
            )
            .with_signal_vars(BTreeSet::from([ordinary_var, parallel_var])),
        );

        let ir = emit_bundle_ir(
            "ordinary_constraints_test",
            circuit_output,
            boundary_spec,
            ConstraintLoweringMode::Logical,
        );

        assert!(!ir.contains("llzk://constrain/parallel_constraints"));
        assert!(ir.contains("llzk://constrain/constraints"));
    }
}
