use super::CircuitPrecomputations;
use gpu_core::allocator::host::ConcurrentStaticHostAllocator;
use gpu_trace::witness::circuit_type::CircuitType;
use gpu_trace::witness::circuit_type::DelegationCircuitType;
use gpu_trace::witness::circuit_type::UnrolledCircuitType::InitsAndTeardowns;

use era_cudart::result::CudaResult;

use crate::upstream::SecurityLevel;
use std::collections::BTreeMap;
use worker::Worker;

/// Build the binary-independent precomputations: every delegation circuit
/// and inits-and-teardowns. CPU-only — no GPU context needed; the
/// `GpuGKRSetupHost` for each circuit is materialized lazily on first GPU
/// worker use.
///
/// `whir_logs_for_circuit` is invoked per-`CircuitType` and must return
/// `(log_lde_factor, log_rows_per_leaf, log_tree_cap_size)` matching the
/// schedule the GPU worker will use at `prove()` time. Different circuits
/// use different WHIR schedules, so a single global triple is wrong for the
/// shared map.
pub(crate) fn get_common_precomputations<F>(
    whir_logs_for_circuit: F,
    worker: &Worker,
) -> CudaResult<BTreeMap<CircuitType, CircuitPrecomputations>>
where
    F: Fn(CircuitType) -> (u32, u32, u32),
{
    let mut out = BTreeMap::new();
    for delegation_type in DelegationCircuitType::get_all_delegation_types()
        .iter()
        .copied()
    {
        let setup = match delegation_type {
            DelegationCircuitType::BigIntWithControl => {
                crate::upstream::get_bigint_with_control_circuit_setup(true, worker)
            }
            DelegationCircuitType::Blake2WithCompression => {
                crate::upstream::get_blake2_with_compression_circuit_setup(true, worker)
            }
            DelegationCircuitType::Blake2GFunction => {
                crate::upstream::get_blake2_g_function_circuit_setup(true, worker)
            }
            DelegationCircuitType::KeccakSpecial5 => {
                crate::upstream::get_keccak_special5_circuit_setup(true, worker)
            }
        };
        let circuit_type = CircuitType::Delegation(delegation_type);
        let (log_lde_factor, log_rows_per_leaf, log_tree_cap_size) =
            whir_logs_for_circuit(circuit_type);
        let precomp = CircuitPrecomputations::new(
            circuit_type,
            setup.compiled_circuit,
            setup.setup,
            None,
            log_lde_factor,
            log_rows_per_leaf,
            log_tree_cap_size,
        )?;
        out.insert(circuit_type, precomp);
    }
    let it_setup = crate::upstream::inits_and_teardowns_circuit_setup::<
        ConcurrentStaticHostAllocator,
    >(true, worker);
    let circuit_type = CircuitType::Unrolled(InitsAndTeardowns);
    let (log_lde_factor, log_rows_per_leaf, log_tree_cap_size) =
        whir_logs_for_circuit(circuit_type);
    let precomp = CircuitPrecomputations::new(
        circuit_type,
        it_setup.compiled_circuit,
        it_setup.setup,
        None,
        log_lde_factor,
        log_rows_per_leaf,
        log_tree_cap_size,
    )?;
    out.insert(circuit_type, precomp);
    Ok(out)
}

pub(crate) fn get_common_precomputations_for_all(
    worker: &Worker,
    security_level: SecurityLevel,
) -> BTreeMap<CircuitType, CircuitPrecomputations> {
    get_common_precomputations(
        move |ct| config_logs_for_circuit(ct, security_level),
        worker,
    )
    .unwrap()
}

pub(crate) fn config_logs_for_circuit(
    circuit_type: CircuitType,
    security_level: SecurityLevel,
) -> (u32, u32, u32) {
    let prover_config = gpu_circuit_prover::config::prover_config(circuit_type, security_level)
        .expect("ExecutionProverConfiguration validated GPU security level before precomputation");
    (
        prover_config.lde_factor.trailing_zeros(),
        prover_config.base_oracles_values_per_leaf.trailing_zeros(),
        prover_config.cap_size.trailing_zeros(),
    )
}
