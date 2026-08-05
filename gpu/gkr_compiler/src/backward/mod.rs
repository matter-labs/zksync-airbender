pub(crate) mod common;
pub mod continuation;
pub mod r0;

pub use common::interp::{
    CoeffResolver, LeanInterpError, interpret_coeff_layer as interpret_coefficient_layer,
};
pub use common::lean::{
    LEAN_BYTES_PER_TERM, LEAN_CLASS_MASK, LEAN_CLASS_SHIFT, LEAN_COEFFICIENT_MASK,
    LEAN_COEFFICIENT_SHIFT, LEAN_CONT_OPCODES, LEAN_GROUP_FLAG_C0, LEAN_GROUP_FLAG_C2,
    LEAN_GROUP_FLAG_MASK, LEAN_R0_OPCODES, LEAN_WORDS_PER_TERM, LeanAtom, LeanAtomRef,
    LeanCodecError, LeanProgram, LeanTerm, SOURCE_NONE,
};
pub use common::lean_bind::{
    LEAN_PROCEDURAL_KINDS, LeanBindError, LeanBoundColumn, LeanBoundWindow, LeanSourceBinding,
    LeanSourceSlot,
};
pub use common::limits::{
    CONTINUATION_LIVE_OPCODES, CONTINUATION_OPCODE_TABLE, DESCRIPTOR_ALIGNMENT_BYTES,
    HEADER_COEFFICIENT_BITS, HEADER_OPCODE_BITS, KERNEL_ARGUMENT_CEILING_BYTES,
    LEAN_CONT_GROUP_HEADER_CLASS, LEAN_DESCRIPTOR_PROGRAM_BYTES, LEAN_DESCRIPTOR_PROGRAM_WORDS,
    LEAN_MAX_IMMEDIATES, LEAN_MAX_REALIZED_PROGRAM_WORDS, MAX_COEFFICIENT_ENCODINGS,
    MAX_SOURCE_WINDOWS, PUBLISH_TARGET_DEPTH, R0_LIVE_OPCODES, R0_OPCODE_TABLE,
    SOURCE_WINDOW_COLUMNS, TermCategory, category_arity, continuation_opcode, is_move, r0_opcode,
    term_category,
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
    ContinuationCompileError, ContinuationLayerProgram, ContinuationProgramBundle,
    compile_continuations, interpret_continuation_program,
};
pub use r0::{R0CompileError, R0LayerProgram, R0ProgramBundle, compile_r0, interpret_r0_program};

pub const MAX_BACKWARD_RECORDS: usize = common::limits::in_scope::MAX_RECORDS;
pub const MAX_BACKWARD_COEFFICIENT_RECIPES: usize =
    common::limits::in_scope::MAX_COEFFICIENT_RECIPES;
pub const MAX_BACKWARD_SOURCES: usize = common::limits::in_scope::MAX_SOURCES;
pub const MAX_BACKWARD_TERMS: usize = common::limits::in_scope::MAX_TERMS;
