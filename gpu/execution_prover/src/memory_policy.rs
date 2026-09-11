//! Offline-measured arena thresholds. Selection performs no GPU work or search.
use crate::precomputations::CircuitPrecomputations;
use crate::upstream::SecurityLevel;
use era_cudart::result::CudaResult;
use era_cudart_sys::CudaError;
use gpu_circuit_prover::proof::memory_policy::ProofMemoryPolicy;
use gpu_prover_context::ProverContext;
use gpu_trace::witness::circuit_type::CircuitType;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "memory_sweep", derive(serde::Serialize, serde::Deserialize))]
pub(crate) struct PolicyGeometry {
    pub sweep_schema: u32,
    pub artifact_fingerprint: u64,
    pub allocator_block_log_size: u32,
    pub small_allocator_log_chunk_size: Option<u32>,
    pub small_allocator_pool_blocks: usize,
    pub trace_len: usize,
    pub setup_columns: usize,
    pub witness_columns: usize,
    pub memory_columns: usize,
    pub config_fingerprint: u64,
    pub final_trace_size_log_2: u32,
    pub eval_leaves: bool,
    // Measurement provenance. Arena policies are portable across GPU models;
    // device geometry is not part of the allocation compatibility key.
    pub sm_count: usize,
    pub l2_bytes: usize,
    pub cc_major: usize,
    pub cc_minor: usize,
}

impl PolicyGeometry {
    pub(crate) fn allocation_key(self) -> Self {
        Self {
            sm_count: 0,
            l2_bytes: 0,
            cc_major: 0,
            cc_minor: 0,
            ..self
        }
    }

    pub(crate) fn new(
        circuit: CircuitType,
        security: SecurityLevel,
        precomputations: &CircuitPrecomputations,
        context: &ProverContext,
    ) -> Self {
        let compiled = precomputations.gkr_programs.compiled_circuit();
        let config = gpu_circuit_prover::config::prover_config(circuit, security).unwrap();
        // A compatibility discriminator, not a cryptographic commitment. It
        // covers the complete schedule rather than only its base LDE factor.
        let config_fingerprint = stable_fingerprint(format!("{config:?}").as_bytes());
        let device = context.get_device_properties();
        Self {
            sweep_schema: SWEEP_SCHEMA,
            artifact_fingerprint: precomputations.artifact_fingerprint,
            allocator_block_log_size: context.config().allocator_block_log_size,
            small_allocator_log_chunk_size: context.config().small_allocator_log_chunk_size,
            small_allocator_pool_blocks: context.config().small_allocator_pool_blocks,
            trace_len: compiled.trace_len,
            setup_columns: precomputations
                .setup_host
                .get_initialized()
                .map_or(0, |s| s.columns_count),
            witness_columns: compiled.witness_layout.total_width,
            memory_columns: compiled.memory_layout.total_width,
            config_fingerprint,
            final_trace_size_log_2: crate::workers::gpu::FINAL_TRACE_SIZE_LOG_2,
            eval_leaves: cfg!(feature = "eval_leaves"),
            sm_count: device.sm_count,
            l2_bytes: device.l2_cache_size_bytes,
            cc_major: device.compute_capability_major,
            cc_minor: device.compute_capability_minor,
        }
    }
}

pub(crate) struct MemoryPolicyThreshold {
    pub circuit: CircuitType,
    pub geometry: PolicyGeometry,
    pub arena_bytes: usize,
    pub policy: ProofMemoryPolicy,
}

mod generated;

fn lookup(
    rows: &[MemoryPolicyThreshold],
    circuit: CircuitType,
    geometry: PolicyGeometry,
    arena_bytes: usize,
) -> CudaResult<Option<ProofMemoryPolicy>> {
    let mut matching = false;
    let mut best: Option<&MemoryPolicyThreshold> = None;
    for row in rows {
        if row.circuit != circuit || row.geometry.allocation_key() != geometry.allocation_key() {
            continue;
        }
        matching = true;
        if row.arena_bytes <= arena_bytes
            && best.is_none_or(|best| row.arena_bytes > best.arena_bytes)
        {
            best = Some(row);
        }
    }
    match best {
        Some(row) => Ok(Some(row.policy)),
        None if matching => Err(CudaError::ErrorMemoryAllocation),
        None => Ok(None),
    }
}

pub(crate) fn select(
    circuit: CircuitType,
    security: SecurityLevel,
    precomputations: &CircuitPrecomputations,
    context: &ProverContext,
) -> CudaResult<ProofMemoryPolicy> {
    if generated::THRESHOLDS.is_empty() && !context.has_exact_device_budget() {
        return Ok(ProofMemoryPolicy::default());
    }
    let geometry = PolicyGeometry::new(circuit, security, precomputations, context);
    select_measured(
        generated::THRESHOLDS,
        circuit,
        geometry,
        context.get_mem_size(),
        context.has_exact_device_budget(),
    )
}

// Maximum trace rows and full I&T page coverage; target plus largest follower,
// with completed proof input reservations retired before the next enqueue.
const SWEEP_SCHEMA: u32 = 2;

fn same_profile(a: PolicyGeometry, b: PolicyGeometry) -> bool {
    a.sweep_schema == b.sweep_schema
        && a.allocator_block_log_size == b.allocator_block_log_size
        && a.small_allocator_log_chunk_size == b.small_allocator_log_chunk_size
        && a.small_allocator_pool_blocks == b.small_allocator_pool_blocks
        && a.eval_leaves == b.eval_leaves
}

fn select_measured(
    rows: &[MemoryPolicyThreshold],
    circuit: CircuitType,
    geometry: PolicyGeometry,
    arena: usize,
    exact: bool,
) -> CudaResult<ProofMemoryPolicy> {
    match lookup(rows, circuit, geometry, arena)? {
        Some(policy) => Ok(policy),
        None if exact || rows.iter().any(|row| same_profile(row.geometry, geometry)) => {
            Err(CudaError::ErrorInvalidValue)
        }
        None => Ok(ProofMemoryPolicy::default()),
    }
}

pub(crate) fn stable_hash(value: &impl std::hash::Hash) -> u64 {
    struct Fnv(u64);
    impl std::hash::Hasher for Fnv {
        fn write(&mut self, bytes: &[u8]) {
            for byte in bytes {
                self.0 = (self.0 ^ u64::from(*byte)).wrapping_mul(0x100000001b3);
            }
        }
        fn finish(&self) -> u64 {
            self.0
        }
    }
    let mut hasher = Fnv(0xcbf29ce484222325);
    value.hash(&mut hasher);
    std::hash::Hasher::finish(&hasher)
}

// Fixed FNV-1a, avoiding toolchain-dependent DefaultHasher output in presets.
pub(crate) fn stable_fingerprint(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf29ce484222325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x100000001b3)
    })
}

/// Admit explicitly budgeted workers only on an offline-measured allocator/leaf
/// profile, before accepting transfers. The generator guarantees all-circuit
/// coverage at every table threshold.
pub(crate) fn validate_device_budget(context: &ProverContext) -> CudaResult<()> {
    let minimum = generated::THRESHOLDS
        .iter()
        .filter(|row| {
            let g = row.geometry;
            g.sweep_schema == SWEEP_SCHEMA
                && g.allocator_block_log_size == context.config().allocator_block_log_size
                && g.small_allocator_log_chunk_size
                    == context.config().small_allocator_log_chunk_size
                && g.small_allocator_pool_blocks == context.config().small_allocator_pool_blocks
                && g.eval_leaves == cfg!(feature = "eval_leaves")
        })
        .map(|row| row.arena_bytes)
        .min();
    match minimum {
        Some(bytes) if context.get_mem_size() >= bytes => Ok(()),
        Some(_) => {
            log::error!("requested arena is below the measured all-circuits minimum");
            Err(CudaError::ErrorMemoryAllocation)
        }
        None if !context.has_exact_device_budget() => {
            if !generated::THRESHOLDS.is_empty() {
                log::warn!("no offline policy profile matches this allocator/leaf geometry; using the default");
            }
            Ok(())
        }
        None => {
            log::error!(
                "no offline all-circuits budget measurements for this allocator/leaf profile"
            );
            Err(CudaError::ErrorInvalidValue)
        }
    }
}

#[cfg(test)]
pub(crate) mod cpu_tests {
    use super::*;
    use gpu_circuit_prover::proof::memory_policy::OpeningPolicy;
    use gpu_trace::witness::circuit_type::{CircuitType, DelegationCircuitType};
    pub(crate) fn geometry() -> PolicyGeometry {
        PolicyGeometry {
            sweep_schema: SWEEP_SCHEMA,
            artifact_fingerprint: 1,
            allocator_block_log_size: 20,
            small_allocator_log_chunk_size: Some(8),
            small_allocator_pool_blocks: 16,
            trace_len: 1 << 20,
            setup_columns: 1,
            witness_columns: 2,
            memory_columns: 3,
            config_fingerprint: 7,
            final_trace_size_log_2: 4,
            eval_leaves: false,
            sm_count: 148,
            l2_bytes: 128 << 20,
            cc_major: 12,
            cc_minor: 0,
        }
    }

    #[test]
    fn cpu_memory_preset_is_portable_across_gpu_geometry() {
        let circuit = CircuitType::Delegation(DelegationCircuitType::BigIntWithControl);
        let measured = geometry();
        let target = PolicyGeometry {
            sm_count: measured.sm_count + 1,
            l2_bytes: measured.l2_bytes / 2,
            cc_major: measured.cc_major + 1,
            cc_minor: measured.cc_minor + 1,
            ..measured
        };
        let rows = [MemoryPolicyThreshold {
            circuit,
            geometry: measured,
            arena_bytes: 30 << 30,
            policy: ProofMemoryPolicy::default(),
        }];
        assert!(same_profile(measured, target));
        assert_eq!(
            select_measured(&rows, circuit, target, 30 << 30, true),
            Ok(ProofMemoryPolicy::default())
        );
        assert_eq!(
            select_measured(&rows, circuit, target, (30 << 30) - 1, true),
            Err(CudaError::ErrorMemoryAllocation)
        );
        let changed = PolicyGeometry {
            artifact_fingerprint: target.artifact_fingerprint + 1,
            ..target
        };
        assert_eq!(
            select_measured(&rows, circuit, changed, 30 << 30, true),
            Err(CudaError::ErrorInvalidValue)
        );
    }

    #[test]
    #[cfg(feature = "memory_sweep")]
    fn cpu_default_budget_has_complete_portable_presets() {
        let config = crate::ExecutionProverConfiguration::default();
        let budget = config
            .prover_context_config
            .device_arena_budget_bytes
            .unwrap();
        let circuits = crate::memory_sweep::model::all_circuits();
        assert_eq!(generated::THRESHOLDS.len(), circuits.len());
        for circuit in circuits {
            let row = generated::THRESHOLDS
                .iter()
                .find(|row| row.circuit == circuit)
                .unwrap();
            assert_eq!(row.arena_bytes, budget);
            let target = PolicyGeometry {
                sm_count: row.geometry.sm_count + 1,
                l2_bytes: row.geometry.l2_bytes / 2,
                ..row.geometry
            };
            assert_eq!(
                select_measured(generated::THRESHOLDS, circuit, target, budget, true),
                Ok(ProofMemoryPolicy::default())
            );
        }
    }
    #[test]
    fn cpu_threshold_boundaries_and_geometry_isolation() {
        let c = CircuitType::Delegation(DelegationCircuitType::BigIntWithControl);
        let low = ProofMemoryPolicy {
            memory: OpeningPolicy::InPlace,
            ..Default::default()
        };
        let high = ProofMemoryPolicy::default();
        let rows = [
            MemoryPolicyThreshold {
                circuit: c,
                geometry: geometry(),
                arena_bytes: 34 << 30,
                policy: high,
            },
            MemoryPolicyThreshold {
                circuit: c,
                geometry: geometry(),
                arena_bytes: 32 << 30,
                policy: low,
            },
        ];
        assert_eq!(
            lookup(&rows, c, geometry(), (32 << 30) - 1),
            Err(CudaError::ErrorMemoryAllocation)
        );
        assert_eq!(lookup(&rows, c, geometry(), 32 << 30).unwrap(), Some(low));
        assert_eq!(
            lookup(&rows, c, geometry(), (34 << 30) - 1).unwrap(),
            Some(low)
        );
        assert_eq!(lookup(&rows, c, geometry(), 34 << 30).unwrap(), Some(high));
        assert_eq!(lookup(&rows, c, geometry(), 48 << 30).unwrap(), Some(high));
        assert_eq!(
            select_measured(&[], c, geometry(), 34 << 30, true),
            Err(CudaError::ErrorInvalidValue)
        );
        let mut artifact_changed = geometry();
        artifact_changed.artifact_fingerprint += 1;
        assert_eq!(
            select_measured(&rows, c, artifact_changed, 34 << 30, true),
            Err(CudaError::ErrorInvalidValue)
        );
        assert_eq!(
            select_measured(&rows, c, artifact_changed, 34 << 30, false),
            Err(CudaError::ErrorInvalidValue)
        );
        let mut different = geometry();
        different.config_fingerprint += 1;
        assert_eq!(lookup(&rows, c, different, 34 << 30).unwrap(), None);
    }
}
