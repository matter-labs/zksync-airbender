//! This crate now intentionally exposes only the shared definitions that the
//! active transpiler-based proving path still imports.
//!
//! The old standalone simulator runtime, runner, and setup layers were removed
//! once the workspace stopped executing them directly.

pub mod abstractions;
pub mod cycle;
pub mod machine_mode_only_unrolled;
