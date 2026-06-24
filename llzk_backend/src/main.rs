use anyhow::Result;
use clap::Args;
use clap::Parser;
use clap::Subcommand;
use clap::ValueEnum;
use llzk_backend::config::ConstraintLoweringMode;
use llzk_backend::config::DebugLocationStyle;
use llzk_backend::config::LlzkStructLayout;
use llzk_backend::config::OptLevel;
use llzk_backend::config::UnusedVariablePolicy;
use llzk_backend::output_format::OutputFormat;
use llzk_backend::recipes;
use llzk_backend::CircuitGenerationConfig;
use llzk_backend::CircuitRecipe;

#[derive(ValueEnum, Clone, Copy, PartialEq, Eq)]
enum Circuits {
    AddSubLuiAuipcMop,
    JumpBranchSlt,
    LoadStoreSubwordOnly,
    LoadStoreWordOnly,
    MulDiv,
    ShiftBinaryCsr,
    UnifiedReducedMachine,
    AddOp,
    SubOp,
    LuiOp,
    AuipcOp,
    XorOp,
    OrOp,
    AndOp,
    SllOp,
    SrlOp,
    SraOp,
    AddmodOp,
    SubmodOp,
    MulmodOp,
    ConditionalOp,
    JumpOpTrusted,
    JumpOpUntrusted,
    MulOpSigned,
    MulOpUnsignedOnly,
    DivremOpSigned,
    DivremOpUnsignedOnly,
    CsrrwOp,
    LoadOp,
    StoreOp,
    OptimizedDecoder,
    BigintWithControlDelegation,
    Blake2WithExtendedControlDelegation,
    KeccakSpecial5Delegation,
}

impl Circuits {
    fn recipe(self) -> CircuitRecipe {
        match self {
            Self::AddSubLuiAuipcMop => recipes::add_sub_lui_auipc_mop_recipe(),
            Self::JumpBranchSlt => recipes::jump_branch_slt_recipe(),
            Self::LoadStoreSubwordOnly => recipes::load_store_subword_only_recipe(),
            Self::LoadStoreWordOnly => recipes::load_store_word_only_recipe(),
            Self::MulDiv => recipes::mul_div_recipe(),
            Self::ShiftBinaryCsr => recipes::shift_binary_csr_recipe(),
            Self::UnifiedReducedMachine => recipes::unified_reduced_machine_recipe(),
            Self::AddOp => recipes::add_op_recipe(),
            Self::SubOp => recipes::sub_op_recipe(),
            Self::LuiOp => recipes::lui_op_recipe(),
            Self::AuipcOp => recipes::auipc_op_recipe(),
            Self::XorOp => recipes::xor_op_recipe(),
            Self::OrOp => recipes::or_op_recipe(),
            Self::AndOp => recipes::and_op_recipe(),
            Self::SllOp => recipes::sll_op_recipe(),
            Self::SrlOp => recipes::srl_op_recipe(),
            Self::SraOp => recipes::sra_op_recipe(),
            Self::AddmodOp => recipes::addmod_op_recipe(),
            Self::SubmodOp => recipes::submod_op_recipe(),
            Self::MulmodOp => recipes::mulmod_op_recipe(),
            Self::ConditionalOp => recipes::conditional_op_recipe(),
            Self::JumpOpTrusted => recipes::jump_op_trusted_recipe(),
            Self::JumpOpUntrusted => recipes::jump_op_untrusted_recipe(),
            Self::MulOpSigned => recipes::mul_op_signed_recipe(),
            Self::MulOpUnsignedOnly => recipes::mul_op_unsigned_only_recipe(),
            Self::DivremOpSigned => recipes::divrem_op_signed_recipe(),
            Self::DivremOpUnsignedOnly => recipes::divrem_op_unsigned_only_recipe(),
            Self::CsrrwOp => recipes::csrrw_op_recipe(),
            Self::LoadOp => recipes::load_op_recipe(),
            Self::StoreOp => recipes::store_op_recipe(),
            Self::OptimizedDecoder => recipes::optimized_decoder_recipe(),
            Self::BigintWithControlDelegation => recipes::bigint_with_control_delegation_recipe(),
            Self::Blake2WithExtendedControlDelegation => {
                recipes::blake2_with_extended_control_delegation_recipe()
            }
            Self::KeccakSpecial5Delegation => recipes::keccak_special5_delegation_recipe(),
        }
    }
}

#[derive(ValueEnum, Clone, Copy, PartialEq, Eq)]
enum MlirSerialization {
    Bytecode,
    Plaintext,
}

#[derive(Args, Clone)]
struct GenerateArgs {
    /// Output directory or output file name
    #[arg(short, long)]
    output: String,
    /// Output serialization format to write.
    #[arg(short, long, default_value_t = OutputFormat::Llzk)]
    format: OutputFormat,
    /// Optimization level for the post-lowering MLIR pipeline.
    #[arg(short = 'O', default_value_t = OptLevel::O1)]
    opt_level: OptLevel,
    /// Struct/program organization used for the generated LLZK module.
    #[arg(long, default_value_t = LlzkStructLayout::ComputeConstrain)]
    layout: LlzkStructLayout,
    /// Style used for emitted debug locations in generated IR.
    #[arg(long, default_value_t = DebugLocationStyle::FileLineCol)]
    debug_location_style: DebugLocationStyle,
    /// Whether to lower constraints from logical Circuit output or compiled artifacts.
    #[arg(long, default_value_t = ConstraintLoweringMode::Logical)]
    constraint_lowering_mode: ConstraintLoweringMode,
    /// How to handle logical variables that end up unused in emitted LLZK.
    #[arg(long, default_value_t = UnusedVariablePolicy::Warn)]
    unused_variable_policy: UnusedVariablePolicy,
    /// Whether to emit suspicious unused logical variables as intermediate members.
    #[arg(long, default_value_t = false)]
    emit_suspicious_unused: bool,
    /// MLIR serialization to use when the selected output format supports both forms.
    ///
    /// Defaults to `bytecode`, as MLIR bytecode preserves LLZK version information that
    /// the plaintext IR cannot preserve.
    ///
    /// This allows downstream LLZK tooling to recognize
    /// older IR versions and perform automatic upgrades when possible.
    #[arg(long, value_enum, default_value_t = MlirSerialization::Bytecode)]
    emit: MlirSerialization,
    /// Write the compiled circuit artifact JSON alongside the generated output.
    #[arg(long, default_value_t = false)]
    dump_circuit_artifact: bool,
    /// Write the raw circuit output JSON alongside the generated output.
    #[arg(long, default_value_t = false)]
    dump_circuit_output: bool,
}

impl GenerateArgs {
    fn generation_config(&self) -> CircuitGenerationConfig {
        CircuitGenerationConfig {
            output: self.output.clone(),
            format: self.format,
            opt_level: self.opt_level,
            layout: self.layout,
            debug_location_style: self.debug_location_style,
            constraint_lowering_mode: self.constraint_lowering_mode,
            unused_variable_policy: self.unused_variable_policy,
            emit_suspicious_unused: self.emit_suspicious_unused,
            emit_bytecode: matches!(self.emit, MlirSerialization::Bytecode),
            dump_circuit_artifact: self.dump_circuit_artifact,
            dump_circuit_output: self.dump_circuit_output,
        }
    }
}

#[derive(Parser)]
#[command(version, about, long_about=None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Generate the specified output for the specified circuit
    GenCircuit {
        /// Circuit family or standalone operation to generate.
        #[arg(long)]
        circuit: Circuits,
        #[command(flatten)]
        args: GenerateArgs,
    },
    /// Generate outputs for all supported circuits
    GenAllCircuits {
        #[command(flatten)]
        args: GenerateArgs,
    },
}

pub fn setup_logging() {
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info"))
        .format_timestamp_millis()
        .format_module_path(false)
        .format_target(false)
        .init();
}

fn main() -> Result<()> {
    setup_logging();
    let cli = Cli::parse();
    match &cli.command {
        Commands::GenCircuit { circuit, args } => {
            let config = args.generation_config();
            config.generate_recipe(circuit.recipe())?;
        }
        Commands::GenAllCircuits { args } => {
            let config = args.generation_config();
            config.generate_recipes(
                Circuits::value_variants()
                    .iter()
                    .copied()
                    .map(Circuits::recipe),
            )?;
        }
    }
    Ok(())
}
