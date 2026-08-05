//! CPU-only offline search and symbolic compiler for GPU GKR evaluation.

pub mod analysis;
pub mod backward;
pub mod forward;
mod interval_pack;
#[doc(hidden)]
pub mod manual;
mod profile;
mod schedule;
mod search;
mod source_bind;

pub use backward::{
    ContinuationCompileError, ContinuationLayerProgram, ContinuationProgramBundle, R0CompileError,
    R0LayerProgram, R0ProgramBundle, compile_continuations, compile_r0,
};
pub use forward::artifact::{
    ForwardArtifactError, ForwardLayerArtifact, ForwardSearchArtifact, RelationUnit, SiteConsumer,
    SiteKey, parse_forward_artifact, validate_forward_artifact,
};
pub use forward::compile::CompiledCircuit as ForwardProgramBundle;
pub use forward::context::CompiledLayer as ForwardLayerProgram;
pub use forward::error::CompileError as ForwardCompileError;
pub use profile::{
    ContinuationResourceProfile, ForwardResourceProfile, GpuResourceProfile, R0ResourceProfile,
    ResourceProfileError, validate_continuation_profile, validate_r0_profile,
};
pub use search::{
    CrossoverKind, ForwardSearchError, ForwardSearchRequest, SearchConfig, search_forward,
};

pub(crate) use backward::common::BwdRegime;

pub fn compile_forward(
    dag: &gkr_eval_ir::DagCircuit,
    artifact: &ForwardSearchArtifact,
) -> Result<ForwardProgramBundle, ForwardCompileError> {
    validate_forward_artifact(dag, artifact)
        .map_err(|error| ForwardCompileError::InvalidSchedule(error.to_string()))?;
    let program = forward::compile::compile_circuit(dag, artifact)?;
    for (layer_index, (compiled, retained)) in
        program.layers.iter().zip(&artifact.layers).enumerate()
    {
        if compiled.stats.dram_traffic != retained.predicted_traffic {
            return Err(ForwardCompileError::InvalidSchedule(format!(
                "layer {layer_index}: retained predicted_traffic {} != realized {}",
                retained.predicted_traffic, compiled.stats.dram_traffic
            )));
        }
    }
    Ok(program)
}
