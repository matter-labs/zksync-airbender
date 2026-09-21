use super::*;
use crate::test_support::{FakeBackendConfiguration, FAKE_BLOCK_BYTES};
use execution_prover_model::circuit_type::{
    DelegationCircuitType, UnrolledCircuitType, UnrolledMemoryCircuitType,
    UnrolledNonMemoryCircuitType,
};

type Configuration = ExecutionProverConfiguration<FakeBackendConfiguration>;

fn valid() -> Configuration {
    Configuration::default()
}

fn field_of(error: ExecutionProverError) -> &'static str {
    match error {
        ExecutionProverError::InvalidConfiguration { field, .. } => field,
        other => panic!("expected an invalid-configuration error, got {other:?}"),
    }
}

#[test]
fn default_configuration_validates() {
    valid().validate().unwrap();
}

#[test]
fn rejects_zero_concurrent_jobs() {
    let mut config = valid();
    config.expected_concurrent_jobs = 0;

    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "expected_concurrent_jobs"
    );
}

#[test]
fn rejects_zero_replay_workers() {
    let mut config = valid();
    config.replay_worker_threads_count = 0;

    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "replay_worker_threads_count"
    );
}

#[test]
fn rejects_thread_counts_above_the_worker_maximum() {
    let mut config = valid();
    config.replay_worker_threads_count = Worker::MAX_WORKER_SIZE + 1;
    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "replay_worker_threads_count"
    );

    let mut config = valid();
    config.max_thread_pool_threads = Some(Worker::MAX_WORKER_SIZE + 1);
    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "max_thread_pool_threads"
    );

    let mut config = valid();
    config.max_thread_pool_threads = Some(0);
    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "max_thread_pool_threads"
    );

    // `None` means "size the pool from the machine", which stays valid.
    let mut config = valid();
    config.max_thread_pool_threads = None;
    config.validate().unwrap();
}

#[test]
fn rejects_zero_allocators_per_job() {
    let mut config = valid();
    config.host_allocators_per_job_count = 0;

    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "host_allocators_per_job_count"
    );
}

#[test]
fn rejects_non_power_of_two_block_size() {
    let mut config = valid();
    config.host_allocator_backing_allocation_size = FAKE_BLOCK_BYTES + 1;

    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "host_allocator_backing_allocation_size"
    );
}

#[test]
fn rejects_a_block_too_small_for_a_row_or_a_page() {
    // One byte is below every row size.
    let mut config = valid();
    config.host_allocator_backing_allocation_size = 1;
    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "host_allocator_backing_allocation_size"
    );

    // The binding constraint is the largest aligned unit, which is a whole page
    // of packed I&T timestamps rather than any single row. A block sized to the
    // largest row alone must still be rejected.
    let layouts = execution_prover_model::trace::host_trace_row_layouts();
    let largest_row = layouts.iter().map(|l| l.row_size).max().unwrap();
    let largest_unit = layouts
        .iter()
        .map(|l| l.minimum_block_bytes())
        .max()
        .unwrap();
    assert!(
        largest_unit > largest_row,
        "expected a page-aligned series to dominate the single-row bound"
    );

    let mut config = valid();
    config.host_allocator_backing_allocation_size = largest_row.next_power_of_two();
    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "host_allocator_backing_allocation_size"
    );

    let mut config = valid();
    config.host_allocator_backing_allocation_size = largest_unit.next_power_of_two();
    // Block-size legality and the producer reserve are separate rules, and a
    // block this small needs a correspondingly large pool. Size the pool from
    // the block so this test keeps testing the rule it is named for.
    config.host_allocators_per_job_count = config.minimum_host_allocators_per_job().unwrap();
    config.validate().unwrap();
}

#[test]
fn rejects_pool_arithmetic_overflow() {
    let mut config = valid();
    config.expected_concurrent_jobs = usize::MAX;
    config.host_allocators_per_job_count = 2;

    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "host_allocators_per_job_count"
    );
}

#[test]
fn rejects_the_placeholder_ram_configuration() {
    let mut config = valid();
    config.ram_config = JitRunnerRam::UninitPlaceholder;

    assert_eq!(field_of(config.validate().unwrap_err()), "ram_config");
}

#[test]
fn shared_validation_runs_before_backend_validation() {
    // A configuration invalid on both sides must report the shared failure, so
    // a backend never sees — or allocates against — nonsense shared settings.
    let mut config = valid();
    config.expected_concurrent_jobs = 0;
    config.backend.reject_validation_with = Some("backend should not be consulted");

    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "expected_concurrent_jobs"
    );
}

#[test]
fn backend_validation_rejects_after_shared_validation_passes() {
    let mut config = valid();
    config.backend.reject_validation_with = Some("unsupported backend setting");

    assert_eq!(field_of(config.validate().unwrap_err()), "backend");
}

#[test]
fn admission_limit_comes_from_the_backend() {
    let mut config = valid();
    config.expected_concurrent_jobs = 3;

    assert_eq!(config.admission_limit(), Some(3));
}

#[test]
fn prover_config_is_keyed_only_on_domain_size() {
    // Two circuits with the same domain size must get the same configuration:
    // the geometry a commitment binds comes from here, not from the circuit.
    let level = SecurityLevel::Sec100;
    let add_sub = CircuitType::Unrolled(UnrolledCircuitType::NonMemory(
        UnrolledNonMemoryCircuitType::AddSubLuiAuipcMop,
    ));
    let word_mem = CircuitType::Unrolled(UnrolledCircuitType::Memory(
        UnrolledMemoryCircuitType::LoadStoreWordOnly,
    ));
    assert_eq!(
        add_sub.get_domain_size_log2(),
        word_mem.get_domain_size_log2()
    );

    let a = prover_config(add_sub, level);
    let b = prover_config(word_mem, level);

    assert_eq!(a.lde_factor, b.lde_factor);
    assert_eq!(a.cap_size, b.cap_size);
    assert_eq!(
        a.whir_schedule.whir_steps_schedule,
        b.whir_schedule.whir_steps_schedule
    );
}

#[test]
fn prover_config_geometry_is_available_for_every_circuit() {
    let level = SecurityLevel::Sec100;
    let mut circuits = vec![
        CircuitType::Unrolled(UnrolledCircuitType::InitsAndTeardowns),
        CircuitType::Unrolled(UnrolledCircuitType::Unified),
    ];
    circuits.extend(
        DelegationCircuitType::get_all_delegation_types()
            .iter()
            .map(|d| CircuitType::Delegation(*d)),
    );
    for machine in [
        MachineType::Full,
        MachineType::FullUnsigned,
        MachineType::Reduced,
    ] {
        circuits.extend(
            UnrolledMemoryCircuitType::get_circuit_types_for_machine_type(machine)
                .iter()
                .map(|c| CircuitType::Unrolled(UnrolledCircuitType::Memory(*c))),
        );
        circuits.extend(
            UnrolledNonMemoryCircuitType::get_circuit_types_for_machine_type(machine)
                .iter()
                .map(|c| CircuitType::Unrolled(UnrolledCircuitType::NonMemory(*c))),
        );
    }

    for circuit in circuits {
        let config = prover_config(circuit, level);
        assert!(
            config.lde_factor.is_power_of_two() && config.lde_factor >= 1,
            "{circuit:?} has a non-power-of-two LDE factor"
        );
        assert!(
            config.cap_size.is_power_of_two() && config.cap_size >= config.lde_factor,
            "{circuit:?} cap size {} cannot be split across {} cosets",
            config.cap_size,
            config.lde_factor
        );
    }
}

#[test]
fn rejects_a_power_of_two_block_that_is_not_a_legal_allocation() {
    // `1 << (usize::BITS - 1)` passes the power-of-two test and the per-row
    // minimums, but no such allocation can exist.
    let mut config = valid();
    config.host_allocator_backing_allocation_size = 1usize << (usize::BITS - 1);

    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "host_allocator_backing_allocation_size"
    );
}

#[test]
fn rejects_total_pool_bytes_that_overflow() {
    // Block count and block size are each individually fine; their product is
    // not. Checked here rather than at the allocation site, where the wrap
    // would silently produce an undersized pool.
    let mut config = valid();
    config.expected_concurrent_jobs = 1;
    config.host_allocators_per_job_count = usize::MAX / FAKE_BLOCK_BYTES + 1;

    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "host_allocator_backing_allocation_size"
    );
}

#[test]
fn rejects_cache_entry_count_overflow() {
    // The memory-holder and trace-chunk caches are sized `jobs + 1`, so a job
    // count that multiplies cleanly can still wrap when incremented.
    let mut config = valid();
    config.expected_concurrent_jobs = usize::MAX;
    config.host_allocators_per_job_count = 1;
    config.host_allocator_backing_allocation_size = 1usize << 20;

    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "expected_concurrent_jobs"
    );
}

#[test]
fn rejects_snapshot_chunk_count_overflow() {
    // Two trace chunks per replay worker, per cache entry.
    let mut config = valid();
    config.replay_worker_threads_count = Worker::MAX_WORKER_SIZE;
    config.expected_concurrent_jobs = usize::MAX / Worker::MAX_WORKER_SIZE;
    config.host_allocators_per_job_count = 1;

    let field = field_of(config.validate().unwrap_err());
    assert!(
        field == "replay_worker_threads_count" || field == "expected_concurrent_jobs",
        "expected a snapshot-count overflow, got {field}"
    );
}

/// The shipping GPU geometry must admit its own default pool.
///
/// Wiring the reserve into `validate` turns the budget into a gate on every
/// construction, so the shipping numbers are pinned here rather than left to be
/// discovered by a user. 64 MiB blocks, 256 per job, 1 GiB RAM: the reviewed
/// reserve is 220 for unified/Reduced, so 221 blocks are needed and 256 fit,
/// leaving 35 for the cache.
#[test]
fn the_shipping_gpu_geometry_admits_its_default_pool() {
    let mut config = valid();
    config.host_allocator_backing_allocation_size = 1 << 26;
    config.host_allocators_per_job_count = 256;
    config.min_free_host_allocators_per_job = 32;
    config.ram_config = JitRunnerRam::Medium;

    assert_eq!(config.effective_reserve_blocks().unwrap(), 220);
    assert_eq!(config.minimum_host_allocators_per_job().unwrap(), 221);
    assert_eq!(config.cache_quota_blocks().unwrap(), 35);
    config
        .validate()
        .expect("the shipping GPU default must not be rejected by its own reserve");
}

/// 4 GiB unified needs a larger pool than the shipping default, and says so.
///
/// Not a defect: the reserve grows with the number of retained unified
/// instances, which scales with RAM. The contract is that this is refused
/// descriptively before any resource exists, not that every RAM size fits the
/// same pool.
#[test]
fn four_gigabyte_ram_needs_a_larger_pool_and_reports_it() {
    let mut config = valid();
    config.host_allocator_backing_allocation_size = 1 << 26;
    config.host_allocators_per_job_count = 256;
    config.min_free_host_allocators_per_job = 32;
    config.ram_config = JitRunnerRam::Full;

    assert_eq!(config.effective_reserve_blocks().unwrap(), 604);
    assert_eq!(config.minimum_host_allocators_per_job().unwrap(), 605);
    let error = config.validate().unwrap_err();
    assert_eq!(field_of_ref(&error), "host_allocators_per_job_count");
    let text = format!("{error:?}");
    assert!(
        text.contains("605"),
        "the rejection must name the pool size that would work; got: {text}"
    );
}

/// One block below the minimum is rejected; the minimum itself is accepted with
/// a zero cache quota.
#[test]
fn the_minimum_pool_is_accepted_and_one_below_it_is_not() {
    let mut config = valid();
    let minimum = config.minimum_host_allocators_per_job().unwrap();
    assert!(minimum > 1, "a real reserve must be more than one block");

    config.host_allocators_per_job_count = minimum;
    config.validate().unwrap();
    assert_eq!(
        config.cache_quota_blocks().unwrap(),
        0,
        "at the minimum pool there is nothing left to cache"
    );

    config.host_allocators_per_job_count = minimum - 1;
    assert_eq!(
        field_of(config.validate().unwrap_err()),
        "host_allocators_per_job_count"
    );
}

/// The reserve is the maximum over everything `add_binary` could register, not
/// the first kind a caller happens to use.
///
/// One prover instance serves whatever is registered later, so sizing for the
/// observed case would fail after construction rather than before it.
#[test]
fn the_reserve_covers_every_registration_kind() {
    let mut config = valid();
    config.host_allocator_backing_allocation_size = 1 << 26;
    config.ram_config = JitRunnerRam::Medium;
    config.min_free_host_allocators_per_job = 0;
    let reserve = config.effective_reserve_blocks().unwrap();

    for (execution_kind, machine_type) in supported_registrations() {
        let inputs = ProducerBudgetInputs::new(
            execution_kind,
            machine_type,
            config.host_allocator_backing_allocation_size,
            config.ram_config.ram_size(),
        );
        let one = ProducerBudget::compute(&inputs).unwrap().reserve_blocks;
        assert!(
            one <= reserve,
            "{execution_kind:?}/{machine_type:?} needs {one} blocks but the \
             reserve is only {reserve}"
        );
    }
    // Unified/Reduced is the binding case at this geometry; if that ever stops
    // being true the maximum above still holds, but this pins today's shape.
    let unrolled = ProducerBudget::compute(&ProducerBudgetInputs::new(
        ExecutionKind::Unrolled,
        MachineType::FullUnsigned,
        config.host_allocator_backing_allocation_size,
        config.ram_config.ram_size(),
    ))
    .unwrap()
    .reserve_blocks;
    assert!(unrolled < reserve, "unified must dominate at 1 GiB");
}

/// The configured free-block floor raises the reserve when it exceeds it.
#[test]
fn a_large_free_block_floor_raises_the_effective_reserve() {
    let mut config = valid();
    config.host_allocator_backing_allocation_size = 1 << 26;
    config.ram_config = JitRunnerRam::Medium;
    config.min_free_host_allocators_per_job = 1000;
    assert_eq!(config.effective_reserve_blocks().unwrap(), 1000);
    assert_eq!(config.minimum_host_allocators_per_job().unwrap(), 1001);
}

/// Prints the full P/S/U/I/R table for every supported combination.
///
/// Evidence, not an assertion: run with `--nocapture` when a geometry change
/// needs reviewing.
#[test]
fn production_geometry_table() {
    for ram in [
        JitRunnerRam::Tiny,
        JitRunnerRam::Small,
        JitRunnerRam::Medium,
        JitRunnerRam::Full,
    ] {
        for (execution_kind, machine_type) in supported_registrations() {
            let inputs =
                ProducerBudgetInputs::new(execution_kind, machine_type, 1 << 26, ram.ram_size());
            let budget = ProducerBudget::compute(&inputs).unwrap();
            println!(
                "{ram:?}/{execution_kind:?}/{machine_type:?}: P={} S={} U={} I={} R={}",
                budget.partial_stream_blocks,
                budget.unpublished_snapshot_blocks,
                budget.retained_unified_blocks,
                budget.inits_and_teardowns_blocks,
                budget.reserve_blocks,
            );
        }
    }
}

fn field_of_ref(error: &ExecutionProverError) -> &'static str {
    match error {
        ExecutionProverError::InvalidConfiguration { field, .. } => field,
        other => panic!("expected an invalid-configuration error, got {other:?}"),
    }
}

/// The cache quota is exactly what is left above the reserve and the one
/// progress block, and it is zero at the minimum pool rather than negative.
#[test]
fn the_cache_quota_is_what_remains_above_the_reserve() {
    let mut config = valid();
    let minimum = config.minimum_host_allocators_per_job().unwrap();

    config.host_allocators_per_job_count = minimum;
    assert_eq!(config.cache_quota_blocks().unwrap(), 0);

    config.host_allocators_per_job_count = minimum + 17;
    assert_eq!(config.cache_quota_blocks().unwrap(), 17);
}
