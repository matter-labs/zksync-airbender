//! Backward coefficient-term ISA: the semantic core (design §4-§6, §8).
//!
//! This module owns the BACKWARD-ONLY coefficient IR and nothing else:
//!
//!   * [`model`] — stable identities ([`TermId`], [`SourceId`], [`ProjectionId`],
//!     [`CoefficientRecipeId`]), the three semantic terms ([`CoeffTerm`]),
//!     normalized coefficient recipes, and [`CoeffError`];
//!   * [`lower`] — [`lower_coeff_layer`], the normalized lowering from a canonical
//!     `DagLayer` plus its `DistilledLayer`;
//!   * [`interp`] — the scalar `(acc_c0, acc_c2)` interpreter;
//!   * [`stats`] — the per-`(circuit, layer, regime)` census and the two
//!     schedule-independent stream bounds; and
//!   * [`limits`] — the FROZEN wire-format bounds and regime opcode tables, plus
//!     the exact corpus maxima the census measured.
//!
//! Everything physical is deliberately absent: no moves, no cells, no paging, no
//! source-window binding, no wire encoding, no artifact. Those are SCHEDULE
//! concerns layered on this IR later, and a [`CoeffTerm`] must never grow to carry
//! them.
//!
//! One backward production lineage: there is no format version, no compatibility
//! decoder, and no old/new switch here.

pub mod bind;
pub mod encode;
pub mod interp;
pub mod limits;
pub mod lower;
pub mod model;
pub mod place;
pub mod schedule;
pub mod stats;

pub use bind::{
    BoundColumn, BoundInput, BoundSourceWindow, CoeffSourceBinding, SourceBindError,
    SourceCertificateError, bind_coeff_sources, certify_source_binding,
};
pub use encode::{
    ACTION_DIRECT, ACTION_FILL, ACTION_INVALID, ACTION_USE_RESIDENT, CELL_DELTA_LANE_SHIFT,
    CELL_ENDPOINT0_LANE_SHIFT, CoeffCodecError, DecodedCell, DecodedInstr, DecodedUse,
    EncodedProgram, HEADER_COEFFICIENT_MASK, HEADER_COEFFICIENT_SHIFT, HEADER_OPCODE_MASK,
    HEADER_OPCODE_SHIFT, INPUT_COLUMN_MASK, INPUT_COLUMN_SHIFT, INPUT_FIRST_ACCESS_SHIFT,
    INPUT_MODE_MASK, INPUT_MODE_SHIFT, INPUT_WINDOW_MASK, INPUT_WINDOW_SHIFT, LANE_BITS, LANE_MASK,
    LANE_WORD_SHIFT, MODE_CELL, MODE_DIRECT_SOURCE, MODE_FILL_SOURCE, MODE_PLANNED_SOURCE,
    OperandRole, PLAN_ACTION_MASK, PLAN_DELTA_ACTION_SHIFT, PLAN_DELTA_LANE_SHIFT,
    PLAN_ENDPOINT0_ACTION_SHIFT, PLAN_ENDPOINT0_LANE_SHIFT, ShortestForm, SourceCoord,
    category_arity, category_of, category_role, certify_encoding, coord_source, decode_program,
    disassemble, encode_instrs, encode_program, is_move, move_width, opcode_of, opcode_table,
    operand_width, program_records, term_category, validate_program,
};
pub use interp::{CoeffResolver, interpret_coeff_layer, interpret_encoded_program};
pub use limits::{
    ASSUMED_MOVES_PER_REUSABLE_PROJECTION, CONTINUATION_LIVE_OPCODES, CONTINUATION_OPCODE_TABLE,
    HEADER_COEFFICIENT_BITS, HEADER_OPCODE_BITS, KERNEL_ARGUMENT_CEILING_BYTES,
    MAX_COEFFICIENT_ENCODINGS, MAX_SOURCE_WINDOWS, R0_LIVE_OPCODES, R0_OPCODE_TABLE,
    SOURCE_WINDOW_COLUMNS, TermCategory, continuation_opcode, r0_opcode,
};
pub use lower::{LoweringTrace, lower_coeff_layer, lower_coeff_layer_traced};
pub use place::{
    CellRead, CoeffPlacement, LivenessError, LivenessReport, PlacementError, PlacementFloor,
    PlacementStats, PlanAction, Residence, ScheduledInstr, ValueUse, certify_cell_liveness,
    place_paging_plan,
};
pub use schedule::{
    BudgetOutcome, BudgetSweep, CellBudget, OpCounts, PagingAction, PagingCertificateError,
    PagingCost, PagingPlan, PagingRequest, PagingScore, ProjectionAction, ProjectionOutcome,
    LANES_PER_CELL, RebuildPrice, ResolutionGroup, ScheduleError, SeedEvaluation, SeedKind,
    SlotKind, SourcePrice, ValueWidth, budget_aware_greedy_order, certify_paging_plan,
    default_target_depth, page_projections, select_paged_order, source_prices,
    stable_normalized_order, sweep_budgets, term_slots, validate_prices,
};
pub use stats::{
    CoeffCensus, CoeffCensusFailure, CoeffCensusRow, census_coeff_layer, census_csv, census_layer,
    live_term_categories, source_window_count,
};
pub use model::{
    CoeffChallenge, CoeffError, CoeffLayer, CoeffProduct, CoeffSource, CoeffTerm,
    CoefficientRecipeId, NormalizedCoefficientRecipe, Projection, ProjectionId, SourceId, TermId,
    sink_read_place, source_order_key,
};
