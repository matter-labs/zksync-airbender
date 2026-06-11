//! gkr_eval_isa: macro-op ISA compiler + CPU reference interpreter for the
//! GKR eval core. Spec: .agents/specs/2026-06-11-gkr-eval-isa-design.md.

pub mod compiler;
pub mod eval_ref;
pub mod interp;
pub mod isa;
pub mod report;
