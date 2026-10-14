use crate::upstream::{ProverConfig, SecurityLevel};
use crate::ProofProfile;
use execution_prover_model::circuit_type::CircuitType;
use riscv_transpiler::jit::JitRunnerRam;

/// Commitments and proofs must use the same geometry on both backends.
pub fn prover_config(
    circuit_type: CircuitType,
    profile: ProofProfile,
    security_level: SecurityLevel,
) -> ProverConfig {
    profile.prover_config(circuit_type.get_domain_size_log2() as usize, security_level)
}

/// The packing of an L1 wrap proof: `(pack_log2, external_challenges_pow_bits)`
/// of the wrap version `circuit_type` names.
pub fn l1_wrap_packing(circuit_type: CircuitType) -> (usize, u32) {
    use ::prover::gkr::prover_config::example_configs::{l1_wrap_2p21, l1_wrap_2p22};
    match circuit_type {
        CircuitType::L1Wrap => (
            l1_wrap_2p22::PACK_LOG2,
            l1_wrap_2p22::EXTERNAL_CHALLENGES_POW_BITS,
        ),
        CircuitType::L1Wrap21 => (
            l1_wrap_2p21::PACK_LOG2,
            l1_wrap_2p21::EXTERNAL_CHALLENGES_POW_BITS,
        ),
        other => panic!("{other:?} is not an L1 wrap circuit"),
    }
}

pub trait BackendConfiguration: Copy + Send + Sync + 'static + Sized {
    fn execution_defaults() -> ExecutionProverConfiguration<Self>;
}

#[derive(Clone, Copy, Debug)]
pub struct ExecutionProverConfiguration<C> {
    /// Shared host-work pool, also used for CPU proving; simulation and replay
    /// run on their own threads.
    pub max_thread_pool_threads: Option<usize>,
    pub expected_concurrent_jobs: usize,
    pub replay_worker_threads_count: usize,
    pub host_allocator_backing_allocation_size: usize,
    pub host_allocators_per_job_count: usize,
    /// Free blocks the cache is trimmed back towards; pressure relief, not a bound.
    pub min_free_host_allocators_per_job: usize,
    pub security_level: SecurityLevel,
    pub ram_config: JitRunnerRam,
    /// Simulate the field operations (MOPs) without the reduction of their inputs
    /// (`MopField::BabyBearAssumeCanonical`). It is only valid for the programs that never
    /// feed a non-canonical value into a field operation: the simulated execution diverges
    /// from the replayed one otherwise.
    pub assume_canonical_mop_inputs: bool,
    pub backend: C,
}

impl<C: BackendConfiguration> Default for ExecutionProverConfiguration<C> {
    fn default() -> Self {
        C::execution_defaults()
    }
}

#[cfg(test)]
mod l1_wrap_tests {
    use super::*;
    use crate::ExecutionKind;
    use ::prover::gkr::prover_config::example_configs::{l1_wrap_2p21, l1_wrap_2p22};
    use common_constants::rom::{L1_WRAP_ROM, REGULAR_ROM};

    #[test]
    fn l1_wrap_identities_select_matching_config_and_rom() {
        for (kind, circuit, log, rom, expected) in [
            (
                ExecutionKind::L1Wrap,
                CircuitType::L1Wrap,
                22,
                REGULAR_ROM,
                l1_wrap_2p22::packed_prover_config(SecurityLevel::Sec100),
            ),
            (
                ExecutionKind::L1Wrap21,
                CircuitType::L1Wrap21,
                21,
                L1_WRAP_ROM,
                l1_wrap_2p21::packed_prover_config(SecurityLevel::Sec100),
            ),
        ] {
            assert!(kind.is_l1_wrap() && !kind.is_unified());
            assert_eq!(kind.unified_circuit(), Some(circuit));
            assert_eq!(kind.rom(), rom);
            assert_eq!(circuit.rom(), rom);
            assert_eq!(circuit.get_domain_size_log2(), log);
            let config = prover_config(circuit, ProofProfile::L1Wrap, SecurityLevel::Sec100);
            assert_eq!(config.trace_len_log2, log as usize);
            assert_eq!(config.lde_factor, expected.lde_factor);
            assert_eq!(config.whir_schedule, expected.whir_schedule);
        }
        assert_eq!(
            l1_wrap_packing(CircuitType::L1Wrap),
            (
                l1_wrap_2p22::PACK_LOG2,
                l1_wrap_2p22::EXTERNAL_CHALLENGES_POW_BITS
            )
        );
        assert_eq!(
            l1_wrap_packing(CircuitType::L1Wrap21),
            (
                l1_wrap_2p21::PACK_LOG2,
                l1_wrap_2p21::EXTERNAL_CHALLENGES_POW_BITS
            )
        );
        for kind in [
            ExecutionKind::Unrolled,
            ExecutionKind::Unified,
            ExecutionKind::Unified22,
        ] {
            assert!(!kind.is_l1_wrap());
            assert_eq!(kind.rom(), REGULAR_ROM);
        }
    }
}
