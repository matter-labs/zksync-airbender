use anyhow::Result;
use llzk::prelude::*;
use melior::ir::operation::OperationPrintingFlags;
use mlir_sys::mlirBytecodeWriterConfigCreate;
use mlir_sys::mlirBytecodeWriterConfigDestroy;
use mlir_sys::mlirOperationWriteBytecodeWithConfig;
use mlir_sys::MlirStringRef;
use prover::cs::cs::circuit::CircuitOutput;
use prover::cs::cs::circuit::ShuffleRamMemQuery;
use prover::cs::cs::circuit::ShuffleRamQueryType;
use prover::cs::cs::placeholder::Placeholder;
use prover::cs::definitions::Variable;
use prover::cs::one_row_compiler::OneRowCompiler;
use prover::field::Mersenne31Field;
use std::collections::HashMap;
use std::ffi::c_void;
use std::fs::File;
use std::fs::{self};
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;
use std::slice;

use crate::builder::ModuleEnv;
use crate::codegen::empty_compiled_artifact;
use crate::codegen::CircuitBundle;
use crate::codegen::EmitLlzkInModule as _;
use crate::codegen::SpecialCsrPropertiesMetadata;
use crate::config::ConstraintLoweringMode;
use crate::config::DebugLocationStyle;
use crate::config::LlzkStructLayout;
use crate::config::OptLevel;
use crate::config::UnusedVariablePolicy;
use crate::output_format::OutputFormat;
use crate::recipes::CircuitBuildKind;
pub use crate::recipes::CircuitRecipe;
use crate::witness::WitnessComputation;

use llzk::targets::pcl::translate_module;

mod builder;
mod codegen;
pub mod config;
mod constraints;
mod field;
mod keccak_tables;
mod lookups;
pub mod output_format;
pub mod recipes;
#[cfg(test)]
mod test_helpers;
mod witness;

fn boundary_spec_variables(
    boundary_spec: Option<&crate::codegen::LlzkBoundarySpec>,
) -> (Vec<Variable>, Vec<Variable>) {
    let Some(boundary_spec) = boundary_spec else {
        return (Vec::new(), Vec::new());
    };

    let flatten = |values: &[crate::codegen::ExtractedVariable]| {
        values
            .iter()
            .flat_map(|value| match value {
                crate::codegen::ExtractedVariable::Register { low, high } => {
                    [Some(*low), Some(*high)]
                }
                crate::codegen::ExtractedVariable::Scalar(variable) => [Some(*variable), None],
            })
            .flatten()
            .collect::<Vec<_>>()
    };

    (
        flatten(&boundary_spec.inputs),
        flatten(&boundary_spec.outputs),
    )
}

/// Shared generation options for emitting one or more circuit families.
#[derive(Clone, Debug)]
pub struct CircuitGenerationConfig {
    pub output: String,
    pub format: OutputFormat,
    pub emit_bytecode: bool,
    pub dump_circuit_artifact: bool,
    pub dump_circuit_output: bool,
    pub opt_level: OptLevel,
    pub layout: LlzkStructLayout,
    pub debug_location_style: DebugLocationStyle,
    pub constraint_lowering_mode: ConstraintLoweringMode,
    pub unused_variable_policy: UnusedVariablePolicy,
    pub emit_suspicious_unused: bool,
}

impl CircuitGenerationConfig {
    /// Build, lower, and serialize one circuit family from the given recipe.
    pub fn generate_recipe(&self, recipe: CircuitRecipe) -> Result<()> {
        if self.emit_bytecode && !self.format.supports_bytecode() {
            anyhow::bail!(
                "bytecode emission is only supported for '{}' and '{}', not '{}'",
                OutputFormat::Llzk,
                OutputFormat::PclMlir,
                self.format
            );
        }
        let built = (recipe.build)()?;
        let (boundary_input_vars, boundary_output_vars) =
            boundary_spec_variables(built.boundary_spec.as_ref());
        let circuit_output = built.circuit_output;
        if self.dump_circuit_output {
            write_circuit_output(&circuit_output, &self.output, recipe.name)?;
        }
        let substitutions = merge_llzk_placeholder_aliases(&circuit_output);
        let special_csr_properties = SpecialCsrPropertiesMetadata::new(&circuit_output);

        let compiler = OneRowCompiler::<Mersenne31Field>::default();
        let compiled_artifact = match recipe.build_kind {
            CircuitBuildKind::ExecutorPreprocessedBytecode {
                bytecode_size,
                trace_len_log2,
            } => compiler.compile_executor_circuit_assuming_preprocessed_bytecode(
                circuit_output.clone(),
                bytecode_size,
                trace_len_log2,
            ),
            CircuitBuildKind::PlainCircuit { trace_len_log2 } => {
                match self.constraint_lowering_mode {
                    ConstraintLoweringMode::Logical => {
                        let _ = trace_len_log2;
                        empty_compiled_artifact(Default::default())
                    }
                    ConstraintLoweringMode::Compiled => {
                        if circuit_output.shuffle_ram_queries.is_empty()
                            && circuit_output
                                .register_and_indirect_memory_accesses
                                .is_empty()
                            && circuit_output.degegated_request_to_process.is_none()
                        {
                            compiler.compile_stateless_circuit(
                                circuit_output.clone(),
                                &boundary_input_vars,
                                &boundary_output_vars,
                                trace_len_log2,
                            )
                        } else {
                            compiler.compile_output_for_chunked_memory_argument(
                                circuit_output.clone(),
                                trace_len_log2,
                            )
                        }
                    }
                }
            }
            CircuitBuildKind::Delegation { trace_len_log2 } => {
                compiler.compile_to_evaluate_delegations(circuit_output.clone(), trace_len_log2)
            }
        };
        let witness = WitnessComputation::new(
            compiled_artifact.clone(),
            built.witness_ssa,
            substitutions,
            special_csr_properties,
        );
        if self.dump_circuit_artifact {
            write_circuit_artifact(&compiled_artifact, &self.output, recipe.name)?;
        }

        let ctx = LlzkContext::new();
        let module_location = format!("llzk://layout/module/{}", recipe.name);
        let mut module = llzk_module(Location::new(&ctx, &module_location, 0, 0));
        let env: ModuleEnv<'_, Mersenne31Field> =
            ModuleEnv::new(&ctx, &module, self.debug_location_style);

        let circuit_bundle = CircuitBundle::new(
            recipe.name,
            self.layout,
            self.constraint_lowering_mode,
            self.unused_variable_policy,
            self.emit_suspicious_unused,
            circuit_output,
            compiled_artifact,
            built.boundary_spec,
            witness,
        )?;
        circuit_bundle.emit_llzk(&env)?;

        verify_operation_with_diags(&module.as_operation())?;
        run_optimizer_pipeline(&ctx, &mut module, self.format, self.opt_level)?;
        verify_operation_with_diags(&module.as_operation())?;

        let res = GenCircuitResult::new(self.format, self.emit_bytecode, &module)?;
        write_result(
            &res,
            self.format,
            self.emit_bytecode,
            &self.output,
            recipe.name,
        )?;

        Ok(())
    }

    /// Generate several circuits using the same generation configuration.
    pub fn generate_recipes(&self, recipes: impl IntoIterator<Item = CircuitRecipe>) -> Result<()> {
        for recipe in recipes {
            self.generate_recipe(recipe)?;
        }
        Ok(())
    }
}

/// A wrapper for the two circuit outputs, that being MLIR formats (LLZK and PCL IR)
/// and PCL code.
enum GenCircuitResult<'ctx> {
    Mlir {
        module: &'ctx Module<'ctx>,
        emit_bytecode: bool,
    },
    Pcl(String),
}

impl<'ctx> GenCircuitResult<'ctx> {
    /// Construct a new result from the given MLIR module based on the expected
    /// output format.
    pub fn new(
        format: OutputFormat,
        emit_bytecode: bool,
        module: &'ctx Module<'ctx>,
    ) -> Result<Self> {
        Ok(match format {
            OutputFormat::Llzk | OutputFormat::PclMlir => Self::Mlir {
                module,
                emit_bytecode,
            },
            OutputFormat::Pcl => Self::Pcl(translate_module(module)?),
        })
    }

    /// Write the result to the given file.
    pub fn dump<F: Write>(&self, file: &mut F) -> Result<()> {
        match self {
            GenCircuitResult::Mlir {
                module,
                emit_bytecode,
            } => {
                if *emit_bytecode {
                    write_mlir_bytecode(module, file)?;
                } else {
                    // pretty_form is not parsable by llzk-opt
                    let flags = OperationPrintingFlags::new().enable_debug_info(true, false);
                    write!(
                        file,
                        "{}",
                        module.as_operation().to_string_with_flags(flags)?
                    )?;
                }
            }
            GenCircuitResult::Pcl(picus_program) => write!(file, "{}", picus_program)?,
        }
        Ok(())
    }
}

fn write_mlir_bytecode<'ctx, F: Write>(module: &Module<'ctx>, file: &mut F) -> Result<()> {
    let mut buffer = Vec::<u8>::new();
    let mut callback_data = (&mut buffer, Result::<()>::Ok(()));
    let config = unsafe { mlirBytecodeWriterConfigCreate() };
    let result = unsafe {
        mlirOperationWriteBytecodeWithConfig(
            module.as_operation().to_raw(),
            config,
            Some(write_bytecode_callback),
            &mut callback_data as *mut _ as *mut c_void,
        )
    };
    unsafe { mlirBytecodeWriterConfigDestroy(config) };
    callback_data.1?;
    if result.value != 1 {
        anyhow::bail!("failed to write MLIR bytecode with the default writer configuration");
    }
    file.write_all(&buffer)?;
    Ok(())
}

unsafe extern "C" fn write_bytecode_callback(
    raw_string: mlir_sys::MlirStringRef,
    data: *mut c_void,
) {
    let (buffer, result) = &mut *(data as *mut (&mut Vec<u8>, Result<()>));
    if result.is_err() {
        return;
    }
    let MlirStringRef { data, length } = raw_string;
    let bytes = slice::from_raw_parts(data as *const u8, length);
    buffer.extend_from_slice(bytes);
}

/// Merge the core circuit substitutions with the extra placeholder aliases that LLZK can derive
/// from the extracted shuffle-RAM queries.
///
/// The shared circuit library already records substitutions for executor-state placeholders (e.g.,
/// mapping [`Placeholder::PcInit`] to a [`Variable`]), but some witness placeholders are only
/// visible indirectly through [`ShuffleRamMemQuery`] values. LLZK treats those query values as
/// struct inputs/outputs, so we need these aliases for witness generation so the `@compute` and
/// `@constrain` logic target the same set of LLZK args/members.
fn merge_llzk_placeholder_aliases<F: prover::field::PrimeField>(
    circuit_output: &CircuitOutput<F>,
) -> HashMap<(Placeholder, usize), Variable> {
    let mut substitutions = circuit_output.substitutions.clone();
    for (key, variable) in
        derive_shuffle_ram_placeholder_aliases(&circuit_output.shuffle_ram_queries)
    {
        substitutions.entry(key).or_insert(variable);
    }
    substitutions
}

/// Derive aliases for shuffle-RAM placeholders that are already exposed to the [`CircuitOutput`].
///
/// The source circuit code uses the same register variables for multiple placeholders, and they
/// differ between the [`CircuitOutput`] and [`WitnessComputation`], so adding these aliases
/// allows `@compute` and `@constrain` to reference the same final LLZK members/arguments for
/// computation and constraints.
///
/// Sources:
/// - In `get_rs1_as_shuffle_ram` and `get_rs2_as_shuffle_ram` (`cs/src/machine/utils.rs`), the
///   registers allocated from `FirstRegMem` and `SecondRegMem` are passed directly into
///   `form_mem_op_for_register_only`, so the placeholder value and
///   [`ShuffleRamMemQuery::read_value`] are literally the same two variables.
/// - In the legacy destination-write helpers `set_rd_with_mask_as_shuffle_ram` and
///   `set_rd_without_mask_as_shuffle_ram`, the register allocated from `WriteRdReadSetWitness`
///   becomes the returned query's `read_value`, again without creating a second variable.
/// - In the newer decode/reduced-machine paths (`decode_and_read_operands.rs` /
///   `reduced_machine_ops.rs`), the placeholders `ShuffleRamReadValue(0)`,
///   `ShuffleRamReadValue(1)`, and `ShuffleRamReadValue(2)` are each allocated first and then
///   written directly into `ShuffleRamMemQuery.read_value`.
/// - Those same paths also allocate `ShuffleRamAddress(1)` and `ShuffleRamAddress(2)` first and
///   then store the resulting registers directly in `ShuffleRamQueryType::RegisterOrRam.address`.
///   LLZK now exposes those query addresses as ordinary inputs, so witness lowering can read the
///   existing boundary value instead of issuing a second oracle call.
/// - `ShuffleRamQueryType::RegisterOrRam` also stores a separate `is_register` discriminator. When
///   that flag is a real circuit variable, it is exposed as an LLZK input and can safely alias
///   `ShuffleRamIsRegisterAccess(i)`. We intentionally do not synthesize aliases for constant
///   discriminators because there is no boundary variable to map them to.
/// - In the unrolled load/store families, `WriteRegMemReadWitness` is assigned into the same
///   `rd_or_store_ram_access_query_read_value` limbs that are later added as shuffle-RAM query 2,
///   so aliasing it to query 2's `read_value` preserves the existing witness flow.
/// - Those same families also route `WriteRegMemWriteValue` and `ShuffleRamWriteValue(2)` into
///   query 2's `write_value`. `unified_reduced_machine` still consumes that slot as a pre-existing
///   witness input, so LLZK keeps it input-backed for that circuit only. The alias is recorded here
///   so witness lowering can canonicalize those legacy placeholders onto the same boundary value
///   when that mixed policy is active.
fn derive_shuffle_ram_placeholder_aliases(
    queries: &[ShuffleRamMemQuery],
) -> HashMap<(Placeholder, usize), Variable> {
    let mut aliases = HashMap::new();

    // `ShuffleRamReadValue(i)` is only defined for `i in {0, 1, 2}`.
    for (query_index, query) in queries.iter().take(3).enumerate() {
        insert_register_alias(
            &mut aliases,
            Placeholder::ShuffleRamReadValue(query_index),
            query.read_value,
        );
    }
    // query 0 is the RS1 read slot (`FirstRegMem` / `ShuffleRamReadValue(0)`):

    if let Some(query) = queries.first() {
        insert_register_alias(&mut aliases, Placeholder::FirstRegMem, query.read_value);
    }
    // query 1 is the RS2 read slot (`SecondRegMem` / `ShuffleRamReadValue(1)`)
    if let Some(query) = queries.get(1) {
        insert_register_alias(&mut aliases, Placeholder::SecondRegMem, query.read_value);
        insert_query_address_alias(&mut aliases, Placeholder::ShuffleRamAddress(1), query);
        insert_query_is_register_alias(
            &mut aliases,
            Placeholder::ShuffleRamIsRegisterAccess(1),
            query,
        );
    }
    // query 2 is the destination prior-value slot (`WriteRdReadSetWitness`,
    //   `WriteRegMemReadWitness`, `ShuffleRamReadValue(2)`, `ShuffleRamAddress(2)`, and
    //   `ShuffleRamIsRegisterAccess(2)`)
    if let Some(query) = queries.get(2) {
        insert_register_alias(
            &mut aliases,
            Placeholder::WriteRdReadSetWitness,
            query.read_value,
        );
        insert_register_alias(
            &mut aliases,
            Placeholder::WriteRegMemReadWitness,
            query.read_value,
        );
        insert_register_alias(
            &mut aliases,
            Placeholder::WriteRegMemWriteValue,
            query.write_value,
        );
        insert_register_alias(
            &mut aliases,
            Placeholder::ShuffleRamWriteValue(2),
            query.write_value,
        );
        insert_query_address_alias(&mut aliases, Placeholder::ShuffleRamAddress(2), query);
        insert_query_is_register_alias(
            &mut aliases,
            Placeholder::ShuffleRamIsRegisterAccess(2),
            query,
        );
    }

    aliases
}

/// Insert both limbs of a `RegisterOrRam` query address if the query carries one.
fn insert_query_address_alias(
    aliases: &mut HashMap<(Placeholder, usize), Variable>,
    placeholder: Placeholder,
    query: &ShuffleRamMemQuery,
) {
    if let ShuffleRamQueryType::RegisterOrRam { address, .. } = query.query_type {
        insert_register_alias(aliases, placeholder, address);
    }
}

/// Insert the discriminator variable for a `RegisterOrRam` query when the source circuit stores
/// it as a real boolean variable rather than a constant.
fn insert_query_is_register_alias(
    aliases: &mut HashMap<(Placeholder, usize), Variable>,
    placeholder: Placeholder,
    query: &ShuffleRamMemQuery,
) {
    if let ShuffleRamQueryType::RegisterOrRam { is_register, .. } = query.query_type {
        if let Some(variable) = is_register.get_variable() {
            insert_scalar_alias(aliases, placeholder, variable);
        }
    }
}

/// Insert both limbs of a register-valued placeholder alias.
fn insert_register_alias(
    aliases: &mut HashMap<(Placeholder, usize), Variable>,
    placeholder: Placeholder,
    register: [Variable; 2],
) {
    for (subindex, variable) in register.into_iter().enumerate() {
        aliases.entry((placeholder, subindex)).or_insert(variable);
    }
}

/// Insert the single variable backing a scalar-valued placeholder alias.
fn insert_scalar_alias(
    aliases: &mut HashMap<(Placeholder, usize), Variable>,
    placeholder: Placeholder,
    variable: Variable,
) {
    aliases.entry((placeholder, 0)).or_insert(variable);
}

/// Write `res` to the specified `output` destination.
fn write_result<'ctx>(
    res: &GenCircuitResult<'ctx>,
    format: OutputFormat,
    emit_bytecode: bool,
    output: &str,
    name: &str,
) -> Result<()> {
    match output {
        // Stdout.
        "-" => {
            let mut file = std::io::stdout();
            res.dump(&mut file)?;
            eprintln!("Written successfully!");
        }
        // A file.
        output
            if [".llzk", ".llzk.bc", ".mlir", ".mlir.bc", ".pcl"]
                .into_iter()
                .any(|suffix| output.ends_with(suffix)) =>
        {
            let outpath = Path::new(output);
            let mut file = File::create(outpath).map_err(anyhow::Error::from)?;
            res.dump(&mut file)?;
            println!("Written successfully: {}", outpath.display());
        }
        // A directory.
        output => {
            // Write to file
            let file_name = format!("{}.{}", name, format.extension(emit_bytecode));
            let outpath = Path::new(output).join(file_name);
            // Ensure parent directories exist
            if let Some(parent) = outpath.parent() {
                fs::create_dir_all(parent).map_err(anyhow::Error::from)?;
            }
            let mut file = File::create(&outpath).map_err(anyhow::Error::from)?;
            res.dump(&mut file)?;
            println!("Written successfully: {}", outpath.display());
        }
    }
    Ok(())
}

fn write_circuit_artifact(
    artifact: &prover::cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field>,
    output: &str,
    name: &str,
) -> Result<()> {
    if output == "-" {
        anyhow::bail!("cannot use --dump-circuit-artifact when writing circuit output to stdout");
    }

    let outpath = artifact_output_path(output, name);
    if let Some(parent) = outpath.parent() {
        fs::create_dir_all(parent).map_err(anyhow::Error::from)?;
    }
    let file = File::create(&outpath).map_err(anyhow::Error::from)?;
    serde_json::to_writer_pretty(file, artifact)?;
    println!("Written successfully: {}", outpath.display());
    Ok(())
}

fn write_circuit_output(
    circuit_output: &CircuitOutput<Mersenne31Field>,
    output: &str,
    name: &str,
) -> Result<()> {
    if output == "-" {
        anyhow::bail!("cannot use --dump-circuit-output when writing circuit output to stdout");
    }

    let outpath = sibling_output_path(output, name, "circuit_output.txt");
    if let Some(parent) = outpath.parent() {
        fs::create_dir_all(parent).map_err(anyhow::Error::from)?;
    }
    let mut file = File::create(&outpath).map_err(anyhow::Error::from)?;
    write!(file, "{:#?}", circuit_output)?;
    println!("Written successfully: {}", outpath.display());
    Ok(())
}

fn artifact_output_path(output: &str, name: &str) -> PathBuf {
    sibling_output_path(output, name, "compiled_circuit_artifact.json")
}

fn sibling_output_path(output: &str, name: &str, suffix: &str) -> PathBuf {
    let file_name = format!("{name}.{suffix}");
    match output {
        output
            if [".llzk", ".llzk.bc", ".mlir", ".mlir.bc", ".pcl"]
                .into_iter()
                .any(|suffix| output.ends_with(suffix)) =>
        {
            let outpath = Path::new(output);
            let parent = outpath.parent().unwrap_or_else(|| Path::new("."));
            parent.join(file_name)
        }
        output => Path::new(output).join(file_name),
    }
}

fn run_optimizer_pipeline(
    ctx: &Context,
    module: &mut Module,
    format: OutputFormat,
    opt_level: OptLevel,
) -> Result<()> {
    let pm = PassManager::new(ctx);
    // First cleanup the IR
    match opt_level {
        OptLevel::O0 => {} // No opt.
        OptLevel::O1 => {
            pm.add_pass(melior_passes::create_cse());
            pm.add_pass(melior_passes::create_canonicalizer());
        }
        OptLevel::O2 => {
            pm.add_pass(melior_passes::create_canonicalizer());
            pm.add_pass(llzk::passes::create_redundant_read_and_write_elimination_pass());
            pm.add_pass(melior_passes::create_cse());
            pm.add_pass(melior_passes::create_canonicalizer());
        }
    }
    // Then convert to the output format
    match format {
        OutputFormat::Llzk => {} // LLZK is the default
        OutputFormat::PclMlir | OutputFormat::Pcl => {
            // Convert to PCL IR
            pm.add_pass(llzk::passes::create_array_to_scalar_pass());
            pm.add_pass(llzk::passes::create_pcl_lowering_pass());
        }
    }

    pm.run(module)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use prover::cs::cs::circuit::ShuffleRamQueryType;

    fn register_query(local_timestamp_in_cycle: usize, read_value: [u64; 2]) -> ShuffleRamMemQuery {
        ShuffleRamMemQuery {
            query_type: ShuffleRamQueryType::RegisterOnly {
                register_index: Variable(100 + local_timestamp_in_cycle as u64),
            },
            local_timestamp_in_cycle,
            read_value: [Variable(read_value[0]), Variable(read_value[1])],
            write_value: [Variable(read_value[0]), Variable(read_value[1])],
        }
    }

    fn register_or_ram_query(
        local_timestamp_in_cycle: usize,
        read_value: [u64; 2],
        write_value: [u64; 2],
        address: [u64; 2],
        is_register: prover::cs::types::Boolean,
    ) -> ShuffleRamMemQuery {
        ShuffleRamMemQuery {
            query_type: ShuffleRamQueryType::RegisterOrRam {
                is_register,
                address: [Variable(address[0]), Variable(address[1])],
            },
            local_timestamp_in_cycle,
            read_value: [Variable(read_value[0]), Variable(read_value[1])],
            write_value: [Variable(write_value[0]), Variable(write_value[1])],
        }
    }

    #[test]
    fn artifact_output_path_uses_directory_output() {
        let path = artifact_output_path("llzk_backend/output", "optimized_decoder");
        assert_eq!(
            path,
            Path::new("llzk_backend/output")
                .join("optimized_decoder.compiled_circuit_artifact.json")
        );
    }

    #[test]
    fn artifact_output_path_uses_parent_of_explicit_output_file() {
        let path = artifact_output_path("llzk_backend/output/add_op.llzk", "add_op");
        assert_eq!(
            path,
            Path::new("llzk_backend/output").join("add_op.compiled_circuit_artifact.json")
        );
    }

    #[test]
    fn sibling_output_path_uses_directory_output() {
        let path = sibling_output_path(
            "llzk_backend/output",
            "jump_branch_slt",
            "circuit_output.txt",
        );
        assert_eq!(
            path,
            Path::new("llzk_backend/output").join("jump_branch_slt.circuit_output.txt")
        );
    }

    #[test]
    fn shuffle_placeholder_aliases_cover_legacy_register_reads() {
        let aliases = derive_shuffle_ram_placeholder_aliases(&[
            register_query(0, [10, 11]),
            register_query(1, [20, 21]),
            register_query(2, [30, 31]),
        ]);

        assert_eq!(aliases[&(Placeholder::FirstRegMem, 0)], Variable(10));
        assert_eq!(aliases[&(Placeholder::FirstRegMem, 1)], Variable(11));
        assert_eq!(aliases[&(Placeholder::SecondRegMem, 0)], Variable(20));
        assert_eq!(aliases[&(Placeholder::SecondRegMem, 1)], Variable(21));
        assert_eq!(
            aliases[&(Placeholder::WriteRdReadSetWitness, 0)],
            Variable(30)
        );
        assert_eq!(
            aliases[&(Placeholder::WriteRegMemReadWitness, 1)],
            Variable(31)
        );
    }

    #[test]
    fn shuffle_placeholder_aliases_cover_supported_shuffle_reads() {
        let aliases = derive_shuffle_ram_placeholder_aliases(&[
            register_query(0, [10, 11]),
            register_query(1, [20, 21]),
            register_query(2, [30, 31]),
            register_query(3, [40, 41]),
        ]);

        assert_eq!(
            aliases[&(Placeholder::ShuffleRamReadValue(0), 0)],
            Variable(10)
        );
        assert_eq!(
            aliases[&(Placeholder::ShuffleRamReadValue(1), 1)],
            Variable(21)
        );
        assert_eq!(
            aliases[&(Placeholder::ShuffleRamReadValue(2), 0)],
            Variable(30)
        );
        assert!(!aliases.contains_key(&(Placeholder::ShuffleRamReadValue(3), 0)));
        assert!(!aliases.contains_key(&(Placeholder::ShuffleRamReadValue(3), 1)));
    }

    #[test]
    fn shuffle_placeholder_aliases_cover_supported_shuffle_writes() {
        let aliases = derive_shuffle_ram_placeholder_aliases(&[
            register_query(0, [10, 11]),
            register_query(1, [20, 21]),
            ShuffleRamMemQuery {
                query_type: ShuffleRamQueryType::RegisterOnly {
                    register_index: Variable(102),
                },
                local_timestamp_in_cycle: 2,
                read_value: [Variable(30), Variable(31)],
                write_value: [Variable(40), Variable(41)],
            },
        ]);

        assert_eq!(
            aliases[&(Placeholder::ShuffleRamWriteValue(2), 0)],
            Variable(40)
        );
        assert_eq!(
            aliases[&(Placeholder::WriteRegMemWriteValue, 1)],
            Variable(41)
        );
    }

    #[test]
    fn shuffle_placeholder_aliases_cover_supported_shuffle_addresses() {
        let aliases = derive_shuffle_ram_placeholder_aliases(&[
            register_query(0, [10, 11]),
            register_or_ram_query(
                1,
                [20, 21],
                [20, 21],
                [50, 51],
                prover::cs::types::Boolean::Constant(true),
            ),
            register_or_ram_query(
                2,
                [30, 31],
                [40, 41],
                [60, 61],
                prover::cs::types::Boolean::Constant(true),
            ),
        ]);

        assert_eq!(
            aliases[&(Placeholder::ShuffleRamAddress(1), 0)],
            Variable(50)
        );
        assert_eq!(
            aliases[&(Placeholder::ShuffleRamAddress(1), 1)],
            Variable(51)
        );
        assert_eq!(
            aliases[&(Placeholder::ShuffleRamAddress(2), 0)],
            Variable(60)
        );
        assert_eq!(
            aliases[&(Placeholder::ShuffleRamAddress(2), 1)],
            Variable(61)
        );
    }

    #[test]
    fn shuffle_placeholder_aliases_cover_variable_is_register_discriminators() {
        let aliases = derive_shuffle_ram_placeholder_aliases(&[
            register_query(0, [10, 11]),
            register_or_ram_query(
                1,
                [20, 21],
                [20, 21],
                [50, 51],
                prover::cs::types::Boolean::Is(Variable(70)),
            ),
            register_or_ram_query(
                2,
                [30, 31],
                [40, 41],
                [60, 61],
                prover::cs::types::Boolean::Is(Variable(71)),
            ),
        ]);

        assert_eq!(
            aliases[&(Placeholder::ShuffleRamIsRegisterAccess(1), 0)],
            Variable(70)
        );
        assert_eq!(
            aliases[&(Placeholder::ShuffleRamIsRegisterAccess(2), 0)],
            Variable(71)
        );
    }

    #[test]
    fn shuffle_placeholder_aliases_skip_constant_is_register_discriminators() {
        let aliases = derive_shuffle_ram_placeholder_aliases(&[
            register_query(0, [10, 11]),
            register_or_ram_query(
                1,
                [20, 21],
                [20, 21],
                [50, 51],
                prover::cs::types::Boolean::Constant(true),
            ),
            register_or_ram_query(
                2,
                [30, 31],
                [40, 41],
                [60, 61],
                prover::cs::types::Boolean::Constant(false),
            ),
        ]);

        assert!(!aliases.contains_key(&(Placeholder::ShuffleRamIsRegisterAccess(1), 0)));
        assert!(!aliases.contains_key(&(Placeholder::ShuffleRamIsRegisterAccess(2), 0)));
    }
}
