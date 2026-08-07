pub(crate) mod common;
pub(crate) mod continuation;
pub(crate) mod r0;

pub use common::lean::{
    LeanAtom, LeanCodecError, LeanProgram, LeanTerm, LEAN_CLASS_SHIFT, LEAN_COEFFICIENT_SHIFT,
    LEAN_CONT_OPCODES, LEAN_GROUP_FLAG_C0, LEAN_GROUP_FLAG_C2, LEAN_R0_OPCODES,
    LEAN_WORDS_PER_TERM, SOURCE_NONE,
};
pub use common::lean_bind::{LeanBindError, LeanBoundColumn, LeanBoundWindow, LeanSourceBinding};
pub use common::limits::{
    category_arity, TermCategory, DESCRIPTOR_ALIGNMENT_BYTES, HEADER_COEFFICIENT_BITS,
    HEADER_OPCODE_BITS, KERNEL_ARGUMENT_CEILING_BYTES, LEAN_CONT_GROUP_HEADER_CLASS,
    LEAN_DESCRIPTOR_PROGRAM_BYTES, LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_IMMEDIATES,
    MAX_COEFFICIENT_ENCODINGS, MAX_SOURCE_WINDOWS, PUBLISH_TARGET_DEPTH, SOURCE_WINDOW_COLUMNS,
};
pub use common::model::{
    CoeffChallenge, CoeffError, CoeffProduct, CoefficientRecipeId, ImmediateId,
    NormalizedCoefficientRecipe, SourceId,
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
    compile_continuations, ContinuationCompileError, ContinuationLayerProgram,
    ContinuationProgramBundle,
};
pub use r0::{compile_r0, R0CompileError, R0LayerProgram, R0ProgramBundle};

pub const MAX_BACKWARD_COEFFICIENT_RECIPES: usize = common::limits::LEAN_MAX_COEFFICIENT_RECIPES;
pub const MAX_BACKWARD_SOURCES: usize = common::limits::LEAN_MAX_SOURCES;

#[cfg(test)]
mod corpus_tests;
