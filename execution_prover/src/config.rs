//! Split execution configuration: shared execution/replay/buffer settings plus
//! one backend-specific block behind the `backend` field.

use crate::error::ExecutionProverError;
use crate::tracing::budget::{ProducerBudget, ProducerBudgetInputs};
use crate::upstream::{
    config_for_security_level_under_pessimistic_conjecture, ProverConfig, SecurityLevel,
};
use crate::ExecutionKind;
use crate::MachineType;
use execution_prover_model::circuit_type::CircuitType;
use execution_prover_model::trace::host_trace_row_layouts;
use riscv_transpiler::jit::JitRunnerRam;
use worker::Worker;

/// The prover configuration a circuit is committed and proven with.
///
/// Every backend must read geometry (LDE factor, cap size, WHIR schedule) from
/// this one function: a circuit's own accessors can disagree with it, and a
/// commitment produced under one geometry cannot be proven under another.
pub fn prover_config(circuit_type: CircuitType, security_level: SecurityLevel) -> ProverConfig {
    config_for_security_level_under_pessimistic_conjecture(
        circuit_type.get_domain_size_log2() as usize,
        security_level,
    )
}

/// The backend half of the configuration.
///
/// `execution_defaults` supplies the WHOLE configuration, not just the backend
/// block: the sensible shared defaults differ per backend.
pub trait BackendConfiguration: Copy + Send + Sync + 'static + Sized {
    /// Name used in backend-attributed errors.
    const BACKEND_NAME: &'static str;

    fn execution_defaults() -> ExecutionProverConfiguration<Self>;

    /// Backend-specific validation. Runs after shared validation and before any
    /// backend resource is created.
    fn validate(&self) -> Result<(), ExecutionProverError>;

    /// Maximum logical executions admitted at once, or `None` to keep the
    /// backend's existing unbounded admission.
    fn admission_limit(&self, expected_concurrent_jobs: usize) -> Option<usize>;
}

#[derive(Clone, Copy, Debug)]
pub struct ExecutionProverConfiguration<C> {
    /// Threads in the shared host-work pool (setup construction, I&T
    /// collection, transcript PoW). Not the CPU proving pool, and not a total
    /// OS-thread count: the simulator and replay workers run on their own
    /// dedicated threads.
    pub max_thread_pool_threads: Option<usize>,
    pub expected_concurrent_jobs: usize,
    pub replay_worker_threads_count: usize,
    /// Bytes one host trace block holds. Must be a power of two, large enough
    /// for one aligned unit of every row layout, and a legal `Layout` size.
    pub host_allocator_backing_allocation_size: usize,
    /// Blocks in this job's host allocator pool. Must be at least
    /// [`Self::minimum_host_allocators_per_job`]: the producer reserve plus
    /// one, so a producer holding the whole reserve can still append and make
    /// progress. Anything above that minimum is the trace cache's quota.
    pub host_allocators_per_job_count: usize,
    /// Floor on the producer reserve, independent of the derived `R`. The
    /// effective reserve is `max(R, this)`, so raising it shrinks the cache
    /// quota rather than the guarantee.
    pub min_free_host_allocators_per_job: usize,
    pub security_level: SecurityLevel,
    pub ram_config: JitRunnerRam,
    pub backend: C,
}

impl<C: BackendConfiguration> Default for ExecutionProverConfiguration<C> {
    fn default() -> Self {
        C::execution_defaults()
    }
}

impl<C: BackendConfiguration> ExecutionProverConfiguration<C> {
    /// Shared validation, then backend validation. Everything here is
    /// decidable without allocating, so an invalid configuration costs no
    /// device context, thread pool or buffer pool.
    pub fn validate(&self) -> Result<(), ExecutionProverError> {
        if self.expected_concurrent_jobs == 0 {
            return Err(ExecutionProverError::invalid_configuration(
                "expected_concurrent_jobs",
                "must be at least one",
            ));
        }
        if self.replay_worker_threads_count == 0 {
            return Err(ExecutionProverError::invalid_configuration(
                "replay_worker_threads_count",
                "must be at least one",
            ));
        }
        if self.replay_worker_threads_count > Worker::MAX_WORKER_SIZE {
            return Err(ExecutionProverError::invalid_configuration(
                "replay_worker_threads_count",
                format!(
                    "{} exceeds the maximum worker size {}",
                    self.replay_worker_threads_count,
                    Worker::MAX_WORKER_SIZE
                ),
            ));
        }
        if let Some(threads) = self.max_thread_pool_threads {
            if threads == 0 {
                return Err(ExecutionProverError::invalid_configuration(
                    "max_thread_pool_threads",
                    "must be at least one when set",
                ));
            }
            if threads > Worker::MAX_WORKER_SIZE {
                return Err(ExecutionProverError::invalid_configuration(
                    "max_thread_pool_threads",
                    format!(
                        "{threads} exceeds the maximum worker size {}",
                        Worker::MAX_WORKER_SIZE
                    ),
                ));
            }
        }
        if self.host_allocators_per_job_count == 0 {
            return Err(ExecutionProverError::invalid_configuration(
                "host_allocators_per_job_count",
                "must be at least one",
            ));
        }
        // The pool allocator derives its log chunk size from this value's
        // trailing zeros, so a non-power-of-two under-reports capacity.
        if !self
            .host_allocator_backing_allocation_size
            .is_power_of_two()
        {
            return Err(ExecutionProverError::invalid_configuration(
                "host_allocator_backing_allocation_size",
                format!(
                    "{} is not a power of two",
                    self.host_allocator_backing_allocation_size
                ),
            ));
        }
        for layout in host_trace_row_layouts() {
            let minimum = layout.minimum_block_bytes();
            if self.host_allocator_backing_allocation_size < minimum {
                return Err(ExecutionProverError::invalid_configuration(
                    "host_allocator_backing_allocation_size",
                    format!(
                        "{} bytes cannot hold one aligned unit of {} ({} bytes)",
                        self.host_allocator_backing_allocation_size, layout.name, minimum
                    ),
                ));
            }
        }
        // Power-of-two alone is not legality: `1 << (usize::BITS - 1)` is a
        // power of two and fails at `Layout` construction.
        if std::alloc::Layout::from_size_align(self.host_allocator_backing_allocation_size, 1)
            .is_err()
        {
            return Err(ExecutionProverError::invalid_configuration(
                "host_allocator_backing_allocation_size",
                format!(
                    "{} bytes is not a legal allocation size",
                    self.host_allocator_backing_allocation_size
                ),
            ));
        }
        // Derived counts are checked here, not at the allocation site: a wrap
        // there would silently produce an undersized pool.
        let total_blocks = self
            .expected_concurrent_jobs
            .checked_mul(self.host_allocators_per_job_count)
            .ok_or_else(|| {
                ExecutionProverError::invalid_configuration(
                    "host_allocators_per_job_count",
                    "expected_concurrent_jobs * host_allocators_per_job_count overflows",
                )
            })?;
        // The memory-holder and trace-chunk caches are sized one entry above
        // the admitted job count, two chunks per replay worker each.
        let cache_entries = self
            .expected_concurrent_jobs
            .checked_add(1)
            .ok_or_else(|| {
                ExecutionProverError::invalid_configuration(
                    "expected_concurrent_jobs",
                    "expected_concurrent_jobs + 1 overflows",
                )
            })?;
        let chunks_per_entry =
            self.replay_worker_threads_count
                .checked_mul(2)
                .ok_or_else(|| {
                    ExecutionProverError::invalid_configuration(
                        "replay_worker_threads_count",
                        "replay_worker_threads_count * 2 overflows",
                    )
                })?;
        if cache_entries.checked_mul(chunks_per_entry).is_none() {
            return Err(ExecutionProverError::invalid_configuration(
                "replay_worker_threads_count",
                "(expected_concurrent_jobs + 1) * 2 * replay_worker_threads_count overflows",
            ));
        }
        if total_blocks
            .checked_mul(self.host_allocator_backing_allocation_size)
            .is_none()
        {
            return Err(ExecutionProverError::invalid_configuration(
                "host_allocator_backing_allocation_size",
                format!(
                    "{total_blocks} blocks of {} bytes overflows the address space",
                    self.host_allocator_backing_allocation_size
                ),
            ));
        }
        if self.ram_config == JitRunnerRam::UninitPlaceholder {
            return Err(ExecutionProverError::invalid_configuration(
                "ram_config",
                "the placeholder RAM configuration cannot be used for execution",
            ));
        }
        // Last of the shared rules: the only one that needs a valid RAM
        // setting.
        let minimum = self.minimum_host_allocators_per_job()?;
        if self.host_allocators_per_job_count < minimum {
            return Err(ExecutionProverError::invalid_configuration(
                "host_allocators_per_job_count",
                format!(
                    "{} blocks cannot guarantee producer progress for {:?} RAM; \
                     at least {minimum} are needed ({} reserved plus one)",
                    self.host_allocators_per_job_count,
                    self.ram_config,
                    minimum - 1,
                ),
            ));
        }
        self.backend.validate()
    }

    /// Admitted logical executions, as decided by the backend.
    pub fn admission_limit(&self) -> Option<usize> {
        self.backend.admission_limit(self.expected_concurrent_jobs)
    }

    /// Smallest `host_allocators_per_job_count` that lets one execution
    /// finish: the producer reserve `R` plus one.
    ///
    /// With only `R` credits a producer holding the whole reserve would wait
    /// for a completion that cannot happen, because publishing is what
    /// produces completions. The extra block breaks that circle.
    pub fn minimum_host_allocators_per_job(&self) -> Result<usize, ExecutionProverError> {
        let effective = self.effective_reserve_blocks()?;
        effective.checked_add(1).ok_or_else(|| {
            ExecutionProverError::invalid_configuration(
                "host_allocators_per_job_count",
                "the producer reserve + 1 overflows",
            )
        })
    }

    /// `R_effective = max(R, min_free_host_allocators_per_job)`.
    ///
    /// `R` is the maximum over every registration kind this configuration
    /// could be asked to run, not the one a caller happens to use first: one
    /// prover instance serves whatever `add_binary` registers later.
    pub(crate) fn effective_reserve_blocks(&self) -> Result<usize, ExecutionProverError> {
        let mut reserve = 0usize;
        for (execution_kind, machine_type) in supported_registrations() {
            let inputs = ProducerBudgetInputs::new(
                execution_kind,
                machine_type,
                self.host_allocator_backing_allocation_size,
                self.ram_config.ram_size(),
            );
            reserve = reserve.max(ProducerBudget::compute(&inputs)?.reserve_blocks);
        }
        Ok(reserve.max(self.min_free_host_allocators_per_job))
    }

    /// Blocks one execution's trace cache may hold: everything above the
    /// reserve and the one progress block. Zero at the minimum pool size,
    /// which is correct — caching is an optimisation, progress is not.
    pub(crate) fn cache_quota_blocks(&self) -> Result<usize, ExecutionProverError> {
        let minimum = self.minimum_host_allocators_per_job()?;
        Ok(self.host_allocators_per_job_count.saturating_sub(minimum))
    }
}

/// Every `(kind, machine)` pair `add_binary` accepts.
///
/// Unified is defined for `Reduced` only — `UnifiedTracingDataProducers::new`
/// asserts it — so the other two are not enumerated for it.
fn supported_registrations() -> impl Iterator<Item = (ExecutionKind, MachineType)> {
    [
        (ExecutionKind::Unrolled, MachineType::Full),
        (ExecutionKind::Unrolled, MachineType::FullUnsigned),
        (ExecutionKind::Unrolled, MachineType::Reduced),
        (ExecutionKind::Unified, MachineType::Reduced),
    ]
    .into_iter()
}

#[cfg(test)]
mod tests;
