//! Canonical, GPU-independent GKR evaluation DAG.
//!
//! GPU scheduling policy is intentionally outside this crate:
//!
//! ```compile_fail
//! use gkr_eval_ir::SiteKey;
//! ```
//!
//! ```compile_fail
//! use gkr_eval_ir::BwdRegime;
//! ```

pub mod arena;
pub mod claim_cone;
pub mod eval;
pub mod field_infer;
pub mod lower;
pub mod model;
pub mod validate;

mod simplify;

pub use arena::ArenaBuilder;
pub use claim_cone::{
    analyze_claim_cone, claim_relation_units, claim_roots, CacheBoundary, ClaimCone,
};
pub use eval::*;
pub use field_infer::*;
pub use lower::{lower_dag, lower_dag_legacy};
pub use model::*;
pub use simplify::simplify_circuit;
pub use validate::{validate, validate_simplified};
