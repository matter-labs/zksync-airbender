use super::geometry::cpu_tests::wrap_geometry;
use super::inputs::ALLOCATOR_BLOCK_BYTES;
use super::*;
use crate::proof::memory_policy::presets::INPUTS_RESERVE_BYTES;
use gpu_prover_context::ProverContextConfig;
use gpu_trace::witness::circuit_type::CircuitType;
use std::alloc::Global;

#[test]
fn cpu_l1_inputs_fit_reserve() {
    assert_eq!(
        ALLOCATOR_BLOCK_BYTES,
        1 << ProverContextConfig::default().allocator_block_log_size
    );
    let (geometry, _) = wrap_geometry(CircuitType::L1Wrap);
    let bytes = L1WrapInputs::<'static, Global>::phase_one_capacity_bytes(
        &geometry,
        crate::proof::memory_policy::presets::l1_wrap::PARTIAL_TREES.setup,
    );
    let mib = 1 << 20;
    // Tracing data, I&T pages/values/timestamps, decoder, transcript prefix,
    // then the setup's raw evaluations, packed monomials and depth-10 trees.
    assert_eq!(bytes, (112 + 1 + 16 + 32 + 3 + 1 + 320 + 512 + 64) * mib);
    assert!(bytes <= INPUTS_RESERVE_BYTES);
}
