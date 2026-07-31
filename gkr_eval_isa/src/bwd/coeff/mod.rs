//! Backward coefficient-term ISA: the semantic core (design §4-§6, §8).
//!
//! This module owns the BACKWARD-ONLY coefficient IR and nothing else:
//!
//!   * [`model`] — stable identities ([`TermId`], [`SourceId`], [`ProjectionId`],
//!     [`CoefficientRecipeId`]), the three semantic terms ([`CoeffTerm`]),
//!     normalized coefficient recipes, and [`CoeffError`];
//!   * [`lower`] — [`lower_coeff_layer`], the normalized lowering from a canonical
//!     `DagLayer` plus its `DistilledLayer`;
//!   * [`interp`] — the scalar `(acc_c0, acc_c2)` semantic oracle and the lean
//!     segmented interpreter stated against it;
//!   * [`stats`] — the per-`(circuit, layer, regime)` census and the two
//!     schedule-independent stream bounds; and
//!   * [`group`] — the coefficient GROUPING transform: terms whose recipes differ
//!     only by a base-field scale collapse onto one shared challenge core;
//!   * [`limits`] — the FROZEN wire-format bounds, the regime opcode tables and
//!     the term-category classification, plus the exact corpus maxima the census
//!     measured.
//!
//! Everything physical is deliberately absent FROM THE IR: no source-window
//! binding and no wire encoding. Those are SCHEDULE concerns, and they live in
//! their own strictly later modules — [`order`] (the committed term order and the
//! physical K-split), [`lean`] (the segmented lean VM's fixed 8-byte term wire),
//! [`lean_bind`] (that VM's placement-free per-source binding) and
//! [`lean_artifact`] (the per-layer lean coordinate and its corpus). A
//! [`CoeffTerm`] must never grow to carry any of it.
//!
//! One backward production lineage: there is no format version, no compatibility
//! decoder, and no old/new switch here. The Plan-6 cell executor — its pager,
//! placement, u16 cell codec, cell interpreter and budget artifacts — was retired
//! wholesale in favour of the segmented lean VM; nothing of it is kept disabled.

pub mod group;
pub mod interp;
pub mod lean;
pub mod lean_artifact;
pub mod lean_bind;
pub mod limits;
pub mod lower;
pub mod model;
pub mod order;
pub mod stats;

pub use group::{factor, group_coeff_layer, immediate_value, rescale};
pub use interp::{CoeffResolver, LeanInterpError, interpret_coeff_layer, interpret_lean_program};
pub use lean::{
    LEAN_BYTES_PER_TERM, LEAN_CLASS_MASK, LEAN_CLASS_SHIFT, LEAN_COEFFICIENT_MASK,
    LEAN_COEFFICIENT_SHIFT, LEAN_CONT_OPCODES, LEAN_GROUP_FLAG_C0, LEAN_GROUP_FLAG_C2,
    LEAN_GROUP_FLAG_MASK, LEAN_R0_OPCODES, LEAN_WORDS_PER_TERM, LeanAtom, LeanAtomRef,
    LeanCodecError, LeanProgram, LeanTerm, SOURCE_NONE,
};
// The lean artifact helpers keep their `lean_` prefix — `lean_artifact_bytes`,
// `lean_artifact_file_name`, `write_lean_circuit_artifact`,
// `read_lean_circuit_artifact` — because that is the spelling the corpus, the GPU
// fixture bridge and the committed file names already use.
pub use lean_artifact::{
    ArtifactRegime, LeanArtifactError, LeanCircuitArtifact, LeanCoordinateArtifact,
    compile_lean_coordinate, lean_artifact_bytes, lean_artifact_file_name, lean_target_depth,
    lower_lean_layer, order_covers_layer, read_lean_circuit_artifact, write_lean_circuit_artifact,
};
pub use lean_bind::{
    LEAN_PROCEDURAL_KINDS, LeanBindError, LeanBoundColumn, LeanBoundWindow, LeanSourceBinding,
    LeanSourceSlot, bind_lean_sources,
};
pub use limits::{
    CONTINUATION_LIVE_OPCODES, CONTINUATION_OPCODE_TABLE, HEADER_COEFFICIENT_BITS,
    HEADER_OPCODE_BITS, KERNEL_ARGUMENT_CEILING_BYTES, LEAN_DESCRIPTOR_PROGRAM_BYTES,
    LEAN_DESCRIPTOR_PROGRAM_WORDS, LEAN_MAX_REALIZED_PROGRAM_WORDS, MAX_COEFFICIENT_ENCODINGS,
    MAX_SOURCE_WINDOWS, PUBLISH_TARGET_DEPTH, R0_LIVE_OPCODES, R0_OPCODE_TABLE,
    SOURCE_WINDOW_COLUMNS, TermCategory, category_arity, continuation_opcode, is_move, r0_opcode,
    term_category,
};
pub use lower::{LoweringTrace, lower_coeff_layer, lower_coeff_layer_traced};
pub use order::{order_terms, split_round_robin};
pub use stats::{
    CoeffCensus, CoeffCensusFailure, CoeffCensusRow, NegOneCensus, census_coeff_layer, census_csv,
    census_layer, compulsory_endpoint_reads, live_term_categories, neg_one_census,
    source_window_count,
};

pub use model::{
    CoeffChallenge, CoeffError, CoeffLayer, CoeffProduct, CoeffSource, CoeffTerm,
    CoefficientRecipeId, NormalizedCoefficientRecipe, Projection, ProjectionId, SourceId, TermId,
    sink_read_place, source_order_key,
};
