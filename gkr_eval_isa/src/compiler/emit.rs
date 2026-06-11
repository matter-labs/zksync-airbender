//! Instruction emitter: lowers ProgramView nodes to ISA instructions (Task 5).

use super::{CompileParams, CompiledLayer};
use cs::gkr_compiler::codegen_ir::CodegenLayer;
use gkr_design_space::graph::AnalysisGraph;

pub(crate) fn emit_layer(
    _layer: &CodegenLayer,
    _g: &AnalysisGraph,
    _params: CompileParams,
) -> CompiledLayer {
    todo!("Task 5")
}
