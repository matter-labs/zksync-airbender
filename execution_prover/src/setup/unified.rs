//! The unified reduced-machine setup, built through the canonical upstream
//! constructor so the unified evaluator variant and table driver survive.

use super::CanonicalCircuitSetup;
use crate::upstream::unified_reduced_machine_circuit_setup;
use std::alloc::Global;
use worker::Worker;

pub fn build_unified_setup(
    binary_image: &[u32],
    text_section: &[u32],
    worker: &Worker,
) -> CanonicalCircuitSetup {
    CanonicalCircuitSetup::Riscv(unified_reduced_machine_circuit_setup::<Global>(
        binary_image,
        text_section,
        true,
        worker,
    ))
}
