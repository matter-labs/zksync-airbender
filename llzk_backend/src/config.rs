//! Configurations for the backend.
use std::fmt;

use clap::ValueEnum;

#[repr(u8)]
#[derive(Debug, Clone, Copy, ValueEnum)]
/// Options for optimization level to be applied to the generated LLZK IR.
pub enum OptLevel {
    /// No optimizations
    #[value(name = "0")]
    O0,
    /// Basic MLIR optimizations
    #[value(name = "1")]
    O1,
    /// MLIR and LLZK optimizations
    #[value(name = "2")]
    O2,
}

impl fmt::Display for OptLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(
            self.to_possible_value()
                .expect("ValueEnum variant should always have a PossibleValue")
                .get_name(),
        )
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, ValueEnum)]
/// Options for how LLZK structs will be generated.
pub enum LlzkStructLayout {
    /// Generate separate `@compute` and `@constrain` functions populated with
    /// witness generation logic and constraint emission, respectively.
    ComputeConstrain,
    /// Generate separate `@compute` and `@constrain` functions, but only the
    /// `@compute` functions will be populated.
    ComputeOnly,
    /// Generate separate `@compute` and `@constrain` functions, but only the
    /// `@constrain` functions will be populated.
    ConstrainOnly,
    /// Generate the unified `@product` function that contains both witness generation
    /// and constrain emission logic.
    Product,
}

impl fmt::Display for LlzkStructLayout {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(
            self.to_possible_value()
                .expect("ValueEnum variant should always have a PossibleValue")
                .get_name(),
        )
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, ValueEnum)]
/// Options for how semantic debug locations are rendered in emitted LLZK IR.
pub enum DebugLocationStyle {
    /// Emit plain file/line/column locations only.
    FileLineCol,
    /// Emit descriptive MLIR `NameLoc`s for layout values such as arguments and members.
    Named,
}

impl fmt::Display for DebugLocationStyle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(
            self.to_possible_value()
                .expect("ValueEnum variant should always have a PossibleValue")
                .get_name(),
        )
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, ValueEnum, PartialEq, Eq)]
/// Options for how `@constrain` is lowered into LLZK.
pub enum ConstraintLoweringMode {
    /// Lower constraints directly from the logical `CircuitOutput`.
    Logical,
    /// Lower constraints from the one-row compiler's `CompiledCircuitArtifact`.
    Compiled,
}

impl fmt::Display for ConstraintLoweringMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(
            self.to_possible_value()
                .expect("ValueEnum variant should always have a PossibleValue")
                .get_name(),
        )
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, ValueEnum, PartialEq, Eq)]
/// Options for how suspicious unused logical variables are handled during LLZK generation.
pub enum UnusedVariablePolicy {
    /// Report suspicious unused variables and continue generation.
    Warn,
    /// Fail generation if any suspicious unused variables are found.
    Error,
    /// Suppress diagnostics, but still classify variables for extraction.
    Ignore,
}

impl fmt::Display for UnusedVariablePolicy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(
            self.to_possible_value()
                .expect("ValueEnum variant should always have a PossibleValue")
                .get_name(),
        )
    }
}
