pub(crate) mod common;
pub(crate) mod continuation;
pub mod main_continuation_partitions;
pub mod main_continuation_window;
pub mod main_continuation_window_manifest;
pub mod main_tail;
pub(crate) mod r0;
pub mod window;
pub mod window_dr;

pub use common::lean::{
    LeanAtom, LeanCodecError, LeanProgram, LeanTerm, LEAN_CLASS_SHIFT, LEAN_COEFFICIENT_SHIFT,
    LEAN_CONT_OPCODES, LEAN_GROUP_FLAG_C0, LEAN_GROUP_FLAG_C2, LEAN_WORDS_PER_TERM, SOURCE_NONE,
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

pub use continuation::{
    compile_continuations, ContinuationCompileError, ContinuationLayerProgram,
    ContinuationProgramBundle,
};
pub use main_continuation_partitions::{
    select_main_continuation_partition, MainContinuationPartitionPlan,
};
pub use main_continuation_window::{
    lower_main_continuation_window_program, CanonicalSourceIdentity,
    MainContinuationWindowLoweringError, MainContinuationWindowProgram,
    MainContinuationWindowShape, MainContinuationWindowSource,
    MAIN_CONTINUATION_WINDOW_COEFFICIENT_BANK_CAPACITY,
    MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY, MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY,
    MAIN_CONTINUATION_WINDOW_SHAPE_DEFINED_BITS, MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY,
    MAIN_CONTINUATION_WINDOW_SOURCE_WINDOW_CAPACITY,
};
pub use main_tail::{lower_main_tail_program, MainTailProgram};
pub use r0::{compile_r0, R0CompileError, R0Kernel, R0WindowProgram};
pub use window::{
    WindowCoefficientPlan, WindowProgram, WINDOW_COEFFICIENT_BANK_BIAS,
    WINDOW_MAX_COEFFICIENT_PLANS, WINDOW_SECTION_WORDS,
};
pub use window_dr::{
    lower_dr_window_program, project_dr_window_inputs, validate_dr_window_split_ownership,
    DrWindowInputOccurrence, DrWindowInputProjection, DrWindowLoweringError, DrWindowProgram,
    DrWindowSlotPlan,
};

pub const MAX_BACKWARD_COEFFICIENT_RECIPES: usize = common::limits::LEAN_MAX_COEFFICIENT_RECIPES;
pub const MAX_BACKWARD_SOURCES: usize = common::limits::LEAN_MAX_SOURCES;

#[cfg(test)]
mod corpus_tests;
