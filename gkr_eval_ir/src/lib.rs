//! Canonical, GPU-independent GKR evaluation DAG.

mod arena;
mod claim_cone;
mod field_infer;
mod lower;
mod model;
mod validate;

mod simplify;

pub use arena::ArenaBuilder;
pub use claim_cone::{
    analyze_claim_cone, claim_relation_units, claim_roots, CacheBoundary, ClaimCone,
};
pub use field_infer::{expr_field_with_resolver, read_place_field};
pub use lower::lower_dag;
pub use model::*;
