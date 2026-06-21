//! Forward-eval VM (spec §1–§16). CPU compiler + interpreter + 16-bit-lane encoding.
//! Input IR: `cs::gkr_compiler::dag_ir`. Replaces ISA-v2 + the per-circuit flat generator.
pub mod binding;
pub mod compile;
pub mod context;
pub mod encode;
pub mod error;
pub mod interp;
pub mod isa;
pub mod peek;
pub mod source;
pub mod stats;
pub mod validate;
