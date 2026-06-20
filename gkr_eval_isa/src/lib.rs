//! gkr_eval_isa: macro-op ISA compiler + CPU reference interpreter for the
//! GKR eval core. Spec: .agents/specs/2026-06-11-gkr-eval-isa-design.md.

pub mod fwd;
pub mod compiler;
pub mod compiler_v2;
pub mod eval_ref;
pub mod interp;
pub mod interp_v2;
pub mod isa;
pub mod isa_v2;
pub mod report;
pub mod report_v2;
#[doc(hidden)]
pub mod test_support;
