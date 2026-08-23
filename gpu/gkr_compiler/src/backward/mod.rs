pub(crate) mod common;
pub(crate) mod continuation;
pub(crate) mod r0;
pub mod window;
pub mod window_dr;
pub mod window_manifest;

pub use common::group::{
    analyze_coeff_grouping, materialize_coeff_grouping_for_semantics, CoeffGroupingAnalysis,
    CoeffGroupingCandidate, CoeffGroupingMemberAnalysis,
};
pub use common::interp::{
    interpret_coeff_layer as interpret_coefficient_layer, CoeffResolver, LeanInterpError,
};
pub use common::lean::{
    LeanAtom, LeanCodecError, LeanProgram, LeanTerm, LEAN_CLASS_SHIFT, LEAN_COEFFICIENT_SHIFT,
    LEAN_CONT_OPCODES, LEAN_GROUP_FLAG_C0, LEAN_GROUP_FLAG_C2, LEAN_R0_OPCODES,
    LEAN_WORDS_PER_TERM, SOURCE_NONE,
};
pub use common::lean_bind::{
    LeanBindError, LeanBoundColumn, LeanBoundWindow, LeanSourceBinding, LeanSourceSlot,
};
pub use common::limits::{
    category_arity, TermCategory, DESCRIPTOR_ALIGNMENT_BYTES, HEADER_COEFFICIENT_BITS,
    HEADER_OPCODE_BITS, KERNEL_ARGUMENT_CEILING_BYTES, LEAN_CONT_GROUP_HEADER_CLASS,
    LEAN_DESCRIPTOR_PROGRAM_BYTES, LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_IMMEDIATES,
    MAX_COEFFICIENT_ENCODINGS, MAX_SOURCE_WINDOWS, PUBLISH_TARGET_DEPTH, SOURCE_WINDOW_COLUMNS,
};
pub use common::model::{
    CoeffChallenge, CoeffError, CoeffGroup, CoeffGroupMember, CoeffLayer, CoeffProduct,
    CoeffSource, CoeffTerm, CoefficientRecipeId, ImmediateId, NormalizedCoefficientRecipe,
    Projection, ProjectionId, SourceId, TermId,
};
pub use common::order::split_round_robin;
pub use common::source_layout::WindowFamily;

pub fn decode_r0_program(program: &LeanProgram) -> Result<Vec<LeanAtom>, LeanCodecError> {
    common::lean::decode_atoms(program, crate::BwdRegime::R0)
}

pub fn decode_continuation_program(program: &LeanProgram) -> Result<Vec<LeanAtom>, LeanCodecError> {
    common::lean::decode_atoms(program, crate::BwdRegime::Ext)
}
pub use continuation::{
    compile_continuations, interpret_continuation_program, ContinuationCompileError,
    ContinuationLayerProgram, ContinuationProgramBundle,
};
pub use r0::{compile_r0, interpret_r0_program, R0CompileError, R0LayerProgram, R0ProgramBundle};
pub use window::{
    build_window_grouped_program, derive_window_shape, lower_window_program, lower_window_sections,
    validate_window_coefficient_ids, validate_window_source_lanes, walk_window_source_lanes,
    window_operand_words, window_operands, window_source_slots, SemanticSourceKey,
    SourceProjection, StoredSource, WindowCapacities, WindowCoefficientPlan, WindowGroupedAtom,
    WindowGroupedMember, WindowGroupedProgram, WindowLoweringError, WindowLoweringInputs,
    WindowOperandWords, WindowPhase, WindowProgram, WindowShape, WindowSourceLane,
    WINDOW_COEFFICIENT_BANK_BIAS, WINDOW_MAX_COEFFICIENT_PLANS, WINDOW_SECTION_WORDS,
    WINDOW_SHAPE_DEFINED_BITS,
};
pub use window_dr::{
    lower_dr_window_program, project_dr_window_inputs, DrWindowInputOccurrence,
    DrWindowInputOutput, DrWindowInputProjection, DrWindowLoweringError, DrWindowProgram,
    DrWindowSlotPlan, DrWindowSourceLane,
};
pub use window_manifest::{
    render_windowed_r0_manifest, render_windowed_r0_registry, render_windowed_r0_translation_unit,
    resolve_windowed_r0_dispatch, validate_windowed_r0_dispatch, windowed_r0_bank,
    windowed_r0_generated_artifacts, windowed_r0_kernel_symbol, windowed_r0_translation_unit_name,
    WINDOWED_R0_BLOCK_THREADS, WINDOWED_R0_DISPATCH, WINDOWED_R0_FALLBACK_MASK,
    WINDOWED_R0_GENERATED_NATIVE_DIR, WINDOWED_R0_GENERATED_REGISTRY, WINDOWED_R0_KERNEL_COUNT,
};

pub const MAX_BACKWARD_COEFFICIENT_RECIPES: usize = common::limits::LEAN_MAX_COEFFICIENT_RECIPES;
pub const MAX_BACKWARD_SOURCES: usize = common::limits::LEAN_MAX_SOURCES;

#[cfg(test)]
mod corpus_tests;
