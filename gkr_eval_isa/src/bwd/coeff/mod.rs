//! Backward coefficient-term ISA: the semantic core (design §4-§6, §8).
//!
//! This module owns the BACKWARD-ONLY coefficient IR and nothing else:
//!
//!   * [`model`] — stable identities ([`TermId`], [`SourceId`], [`ProjectionId`],
//!     [`CoefficientRecipeId`]), the three semantic terms ([`CoeffTerm`]),
//!     normalized coefficient recipes, and [`CoeffError`];
//!   * [`lower`] — [`lower_coeff_layer`], the normalized lowering from a canonical
//!     `DagLayer` plus its `DistilledLayer`; and
//!   * [`interp`] — the scalar `(acc_c0, acc_c2)` interpreter.
//!
//! Everything physical is deliberately absent: no moves, no cells, no paging, no
//! source-window binding, no wire encoding, no artifact. Those are SCHEDULE
//! concerns layered on this IR later, and a [`CoeffTerm`] must never grow to carry
//! them.
//!
//! One backward production lineage: there is no format version, no compatibility
//! decoder, and no old/new switch here.

pub mod interp;
pub mod lower;
pub mod model;

pub use interp::{CoeffResolver, interpret_coeff_layer};
pub use lower::lower_coeff_layer;
pub use model::{
    CoeffChallenge, CoeffError, CoeffLayer, CoeffProduct, CoeffSource, CoeffTerm,
    CoefficientRecipeId, NormalizedCoefficientRecipe, Projection, ProjectionId, SourceId, TermId,
    sink_read_place, source_order_key,
};
