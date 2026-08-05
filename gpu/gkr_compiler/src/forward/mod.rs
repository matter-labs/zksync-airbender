//! Forward-eval VM (spec §1–§16). CPU compiler + interpreter + 16-bit-lane encoding.
//! Input IR: `gkr_eval_ir`. Replaces ISA-v2 + the per-circuit flat generator.
pub mod artifact;
pub mod binding;
pub mod compile;
pub mod context;
pub mod encode;
pub mod error;
pub mod interp;
pub mod isa;
pub mod peek;
pub(crate) mod search;
pub mod source;
pub mod stats;
pub mod validate;
