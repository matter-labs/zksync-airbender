//! CPU-only offline search and symbolic compiler for GPU GKR evaluation.

mod analysis;
mod backward;
mod forward;
mod interval_pack;
#[cfg(feature = "search")]
mod search;
mod source_bind;

pub use backward::*;
pub use forward::artifact::{
    parse_forward_artifact, ForwardArtifactError, ForwardLayerArtifact, ForwardSearchArtifact,
    RelationUnit, SiteConsumer, SiteKey,
};
pub use forward::compile::CompiledCircuit as ForwardProgramBundle;
pub use forward::context::CompiledLayer;
pub use forward::encode::encode as encode_forward_program;
pub use forward::encode::encode_with_source_layout as encode_forward_program_with_source_layout;
pub use forward::error::CompileError as ForwardCompileError;
pub use forward::error::EncodeError as ForwardEncodeError;
pub use forward::isa::{
    DstLine as ForwardDstLine, Instr as ForwardInstr, LdcSub as ForwardLdcSub,
    MovDir as ForwardMovDir, OperandField as ForwardOperandField,
    OperandLine as ForwardOperandLine, Program as ForwardProgram, Sign as ForwardSign,
    SourceLayout as ForwardSourceLayout, MAX_COLS as FORWARD_MAX_COLS,
    SOURCE_WINDOW_COLUMNS as FORWARD_SOURCE_WINDOW_COLUMNS,
};
pub use forward::source::{
    virtual_setup_kind_code, SpecialStrategy as ForwardSpecialStrategy, KIND_ORDER,
};
#[cfg(feature = "search")]
pub use search::{search_forward, ForwardSearchError, ForwardSearchRequest, SearchConfig};

pub(crate) use backward::common::BwdRegime;

pub fn compile_forward(
    dag: &gkr_eval_ir::DagCircuit,
    artifact: &ForwardSearchArtifact,
) -> Result<ForwardProgramBundle, ForwardCompileError> {
    forward::artifact::validate_forward_artifact(dag, artifact)
        .map_err(|error| ForwardCompileError::InvalidSchedule(error.to_string()))?;
    let layers = forward::compile::compile_circuit(dag, artifact)?;
    for compiled in &layers {
        forward::validate::validate_compiled(compiled)?;
    }
    for (layer_index, (compiled, retained)) in layers.iter().zip(&artifact.layers).enumerate() {
        if compiled.stats.dram_traffic != retained.predicted_traffic {
            return Err(ForwardCompileError::InvalidSchedule(format!(
                "layer {layer_index}: retained predicted_traffic {} != realized {}",
                retained.predicted_traffic, compiled.stats.dram_traffic
            )));
        }
    }
    Ok(forward::compile::CompiledCircuit {
        layers: layers
            .into_iter()
            .map(forward::context::CompiledLayerBuild::into_runtime)
            .collect(),
    })
}
