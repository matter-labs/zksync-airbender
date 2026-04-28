#![feature(custom_test_frameworks)]
#![test_runner(criterion::runner)]

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use gpu_prover::execution::cpu_pipeline_model::{
    CpuPipelineMode, CpuPipelineModel, CpuPipelineModelConfig, CpuPipelineModelInput,
};
use gpu_prover::execution::prover::ExecutionKind;
use gpu_prover::machine_type::MachineType;
use setups::read_binary;
use std::path::PathBuf;
use std::time::{Duration, Instant};

fn hashed_fibonacci_input() -> CpuPipelineModelInput {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let app_dir = manifest_dir.join("../examples/hashed_fibonacci");
    let (_, binary_image) = read_binary(&app_dir.join("app.bin"));
    let (_, text_section) = read_binary(&app_dir.join("app.text"));
    CpuPipelineModelInput {
        binary_image,
        text_section,
    }
}

fn hashed_fibonacci_nondeterminism() -> Vec<u32> {
    // examples/hashed_fibonacci/input.txt encodes n = 15 and h = 1 as big-endian words.
    vec![15, 1]
}

fn model_config(mode: CpuPipelineMode, replay_threads: usize) -> CpuPipelineModelConfig {
    CpuPipelineModelConfig {
        execution_kind: ExecutionKind::Unrolled,
        machine_type: MachineType::FullUnsigned,
        mode,
        max_thread_pool_threads: Some((replay_threads + 2).max(4)),
        replay_worker_threads_count: replay_threads,
        // Keep the default production-sized memory model, but use fewer host buffers
        // because the null sink returns payloads immediately after the CPU side is done.
        host_allocators_count: 32,
        ..Default::default()
    }
}

fn bench_hashed_fibonacci(c: &mut Criterion) {
    let input = hashed_fibonacci_input();
    let nondeterminism = hashed_fibonacci_nondeterminism();

    let mut group = c.benchmark_group("cpu_pipeline/hashed_fibonacci");
    group.sample_size(10);
    group.warm_up_time(Duration::from_secs(1));
    group.measurement_time(Duration::from_secs(10));

    for mode in [CpuPipelineMode::SimulationOnly, CpuPipelineMode::Full] {
        for replay_threads in [1usize, 2, 4, 8] {
            if mode == CpuPipelineMode::SimulationOnly && replay_threads != 1 {
                continue;
            }

            let config = model_config(mode, replay_threads);
            let model: CpuPipelineModel = CpuPipelineModel::new(
                config,
                CpuPipelineModelInput {
                    binary_image: input.binary_image.clone(),
                    text_section: input.text_section.clone(),
                },
            );
            let benchmark_id = BenchmarkId::new(
                format!("{mode:?}"),
                format!("replay_threads={replay_threads}"),
            );

            group.bench_with_input(benchmark_id, &replay_threads, |b, _| {
                b.iter_custom(|iters| {
                    let start = Instant::now();
                    for _ in 0..iters {
                        let report = model.run(nondeterminism.clone());
                        black_box(report);
                    }
                    start.elapsed()
                });
            });
        }
    }

    group.finish();
}

criterion_group!(cpu_pipeline, bench_hashed_fibonacci);
criterion_main!(cpu_pipeline);
