use super::*;
use crate::test_support::{TestConfiguration, BLOCK_BYTES};

type Configuration = ExecutionProverConfiguration<TestConfiguration>;

fn invalid_field(config: &Configuration) -> &'static str {
    match config.validate().unwrap_err() {
        ExecutionProverError::InvalidConfiguration { field, .. } => field,
        error => panic!("unexpected error: {error}"),
    }
}

#[test]
fn validates_shared_and_backend_configuration() {
    let mut config = Configuration::default();
    config.validate().unwrap();
    config.backend.reject_validation_with = Some("unsupported backend setting");
    assert_eq!(invalid_field(&config), "backend");
    config.expected_concurrent_jobs = 0;
    assert_eq!(invalid_field(&config), "expected_concurrent_jobs");
}

#[test]
fn rejects_invalid_resource_sizes() {
    let base = Configuration::default();
    for (field, config) in [
        (
            "expected_concurrent_jobs",
            Configuration {
                expected_concurrent_jobs: 0,
                ..base
            },
        ),
        (
            "replay_worker_threads_count",
            Configuration {
                replay_worker_threads_count: 0,
                ..base
            },
        ),
        (
            "replay_worker_threads_count",
            Configuration {
                replay_worker_threads_count: Worker::MAX_WORKER_SIZE + 1,
                ..base
            },
        ),
        (
            "max_thread_pool_threads",
            Configuration {
                max_thread_pool_threads: Some(0),
                ..base
            },
        ),
        (
            "max_thread_pool_threads",
            Configuration {
                max_thread_pool_threads: Some(Worker::MAX_WORKER_SIZE + 1),
                ..base
            },
        ),
        (
            "host_allocators_per_job_count",
            Configuration {
                host_allocators_per_job_count: 0,
                ..base
            },
        ),
        (
            "host_allocators_per_job_count",
            Configuration {
                expected_concurrent_jobs: usize::MAX,
                ..base
            },
        ),
        (
            "min_free_host_allocators_per_job",
            Configuration {
                min_free_host_allocators_per_job: base.host_allocators_per_job_count + 1,
                ..base
            },
        ),
        (
            "host_allocator_backing_allocation_size",
            Configuration {
                host_allocator_backing_allocation_size: 1,
                ..base
            },
        ),
        (
            "host_allocator_backing_allocation_size",
            Configuration {
                host_allocator_backing_allocation_size: BLOCK_BYTES + 1,
                ..base
            },
        ),
        (
            "host_allocator_backing_allocation_size",
            Configuration {
                host_allocator_backing_allocation_size: 1usize << (usize::BITS - 1),
                ..base
            },
        ),
        (
            "host_allocator_backing_allocation_size",
            Configuration {
                host_allocators_per_job_count: usize::MAX / BLOCK_BYTES + 1,
                ..base
            },
        ),
        (
            "ram_config",
            Configuration {
                ram_config: JitRunnerRam::UninitPlaceholder,
                ..base
            },
        ),
    ] {
        assert_eq!(invalid_field(&config), field);
    }
}
