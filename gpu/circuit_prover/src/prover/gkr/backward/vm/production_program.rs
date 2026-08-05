//! Per-circuit construction of the two typed backward program families.

use gpu_gkr_compiler::{
    compile_continuations, compile_r0, ContinuationProgramBundle, GpuResourceProfile,
    R0ProgramBundle,
};

use gkr_eval_ir::DagCircuit;

pub(crate) struct CompiledBackwardPrograms {
    pub(crate) r0: R0ProgramBundle,
    pub(crate) continuations: ContinuationProgramBundle,
}

/// Lower the raw circuit once, then compile R0 and continuation programs through
/// their separate compiler entry points.
pub(crate) fn compile_all(
    dag: &DagCircuit,
) -> Result<CompiledBackwardPrograms, String> {
    let profile = GpuResourceProfile::production();
    let r0 = compile_r0(dag, &profile).map_err(|error| format!("R0 compiler: {error}"))?;
    let continuations = compile_continuations(dag, &profile)
        .map_err(|error| format!("continuation compiler: {error}"))?;
    Ok(CompiledBackwardPrograms { r0, continuations })
}
