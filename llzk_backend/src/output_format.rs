//! Utilities for specifying the output of the code generation process.

#[derive(clap::ValueEnum, Clone, Copy, PartialEq, Eq, Debug)]
pub enum OutputFormat {
    /// LLZK IR
    Llzk,
    /// Picus Constraint Language MLIR Dialect (mid-level IR between LLZK and PCL)
    PclMlir,
    /// Picus Constraint Language
    Pcl,
}

impl OutputFormat {
    /// Standard file extension for the given output format.
    pub fn extension(&self, bytecode: bool) -> &'static str {
        match self {
            OutputFormat::Llzk if bytecode => "llzk.bc",
            OutputFormat::Llzk => "llzk",
            OutputFormat::PclMlir if bytecode => "mlir.bc",
            OutputFormat::PclMlir => "mlir",
            OutputFormat::Pcl => "pcl",
        }
    }

    /// Whether this format supports MLIR bytecode emission.
    pub fn supports_bytecode(&self) -> bool {
        matches!(self, OutputFormat::Llzk | OutputFormat::PclMlir)
    }
}

impl std::fmt::Display for OutputFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OutputFormat::Llzk => write!(f, "llzk"),
            OutputFormat::PclMlir => write!(f, "pcl-mlir"),
            OutputFormat::Pcl => write!(f, "pcl"),
        }
    }
}
