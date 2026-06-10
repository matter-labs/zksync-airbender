//! Offline GKR kernel design-space analyzer (M1).
//!
//! Loads codegen-IR JSON (`cs::gkr_compiler::codegen_ir::CodegenCircuit`) and
//! produces steering numbers: working sets, reuse, depth/levels, scheduled
//! max-live. Spec: `.agents/specs/2026-06-10-gkr-design-space-analyzer-design.md`.

pub mod analysis;
pub mod graph;
pub mod import;
pub mod report;
