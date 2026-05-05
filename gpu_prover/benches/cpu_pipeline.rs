#![feature(custom_test_frameworks)]
#![test_runner(criterion::runner)]

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use gpu_prover::execution::cpu_pipeline_model::{
    CpuPipelineMode, CpuPipelineModel, CpuPipelineModelConfig, CpuPipelineModelInput,
};
use gpu_prover::execution::prover::ExecutionKind;
use gpu_prover::machine_type::MachineType;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSourceState;
use riscv_transpiler::common_constants::ROM_WORD_SIZE;
use riscv_transpiler::jit::{
    Context, ContextImpl, JittedCode, MachineState, MemoryHolder, RamImage, TraceChunk,
};
use setups::read_binary;
use std::env;
use std::path::PathBuf;
use std::ptr::NonNull;
use std::time::{Duration, Instant};

#[allow(dead_code)]
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

#[allow(dead_code)]
fn hashed_fibonacci_nondeterminism() -> Vec<u32> {
    // examples/hashed_fibonacci/input.txt encodes n = 15 and h = 1 as big-endian words.
    vec![15, 1]
}

#[allow(dead_code)]
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

#[allow(dead_code)]
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

fn ethereum_block_input() -> CpuPipelineModelInput {
    let app_dir = PathBuf::from("/home/popzxc/workspace/airbender/ethereum-prover/artifacts");
    let (_, binary_image) = read_binary(&app_dir.join("app.bin"));
    let (_, text_section) = read_binary(&app_dir.join("app.text"));
    CpuPipelineModelInput {
        binary_image,
        text_section,
    }
}

fn ethereum_block_nondeterminism() -> Vec<u32> {
    let data = include_bytes!("/home/popzxc/workspace/airbender/24232546_witness.bin");

    let decoded: Vec<u32> =
        bincode::decode_from_slice(data.as_slice(), bincode::config::standard())
            .unwrap()
            .0;
    decoded
}

const ETHEREUM_BLOCK_REPLAY_THREAD_COUNTS: [usize; 1] = [4]; // 4 was kind of confirmed to be optimal on this machine
const ETHEREUM_BLOCK_HOST_ALLOCATORS: usize = 384;

fn zeroed_trace_chunk() -> Box<TraceChunk> {
    unsafe { Box::new_zeroed().assume_init() }
}

struct JitBenchmarkContext {
    oracle: Vec<u32>,
    read_pos: usize,
    write_state: QuasiUARTSourceState,
    final_state: Option<MachineState>,
    trace_chunks: [Box<TraceChunk>; 2],
    next_trace_chunk: usize,
    trace_len: usize,
}

impl JitBenchmarkContext {
    fn new(oracle: Vec<u32>) -> Self {
        Self {
            oracle,
            read_pos: 0,
            write_state: QuasiUARTSourceState::Ready,
            final_state: None,
            trace_chunks: [zeroed_trace_chunk(), zeroed_trace_chunk()],
            next_trace_chunk: 1,
            trace_len: 0,
        }
    }

    fn reset(&mut self) -> NonNull<TraceChunk> {
        self.read_pos = 0;
        self.write_state = QuasiUARTSourceState::Ready;
        self.final_state = None;
        self.next_trace_chunk = 1;
        self.trace_len = 0;
        for chunk in &mut self.trace_chunks {
            chunk.len = 0;
        }
        NonNull::from(self.trace_chunks[0].as_mut())
    }
}

impl ContextImpl for JitBenchmarkContext {
    fn read_nondeterminism(&mut self) -> u32 {
        let value = self.oracle[self.read_pos];
        self.read_pos += 1;
        value
    }

    fn write_nondeterminism(&mut self, value: u32, _memory: &RamImage) {
        self.write_state.process_write(value);
    }

    fn receive_trace(
        &mut self,
        trace_piece: NonNull<TraceChunk>,
        _machine_state: &MachineState,
    ) -> NonNull<TraceChunk> {
        let trace_piece = unsafe { trace_piece.as_ref() };
        self.trace_len += trace_piece.len as usize;

        let next = self.next_trace_chunk;
        self.next_trace_chunk ^= 1;
        self.trace_chunks[next].len = 0;
        NonNull::from(self.trace_chunks[next].as_mut())
    }

    fn receive_final_trace_piece(
        &mut self,
        trace_piece: NonNull<TraceChunk>,
        machine_state: &MachineState,
    ) {
        let trace_piece = unsafe { trace_piece.as_ref() };
        self.trace_len += trace_piece.len as usize;
        self.final_state = Some(*machine_state);
    }

    fn take_final_state(&mut self) -> Option<MachineState> {
        self.final_state.take()
    }

    fn final_state_ref(&'_ self) -> Option<&'_ MachineState> {
        self.final_state.as_ref()
    }
}

fn prepare_jit_memory(memory: &mut MemoryHolder, binary_image: &[u32], touched_words: &[usize]) {
    for &word_idx in touched_words {
        memory.timestamps[word_idx] = 0;
        memory.memory[word_idx] = binary_image.get(word_idx).copied().unwrap_or_default();
    }

    memory.memory[..binary_image.len()].copy_from_slice(binary_image);
    memory.memory[binary_image.len()..ROM_WORD_SIZE].fill(0);
}

fn collect_touched_words(memory: &MemoryHolder) -> Vec<usize> {
    memory
        .timestamps
        .iter()
        .enumerate()
        .filter_map(|(word_idx, timestamp)| (*timestamp != 0).then_some(word_idx))
        .collect()
}

fn ethereum_block_model_config(
    mode: CpuPipelineMode,
    replay_threads: usize,
) -> CpuPipelineModelConfig {
    CpuPipelineModelConfig {
        execution_kind: ExecutionKind::Unrolled,
        machine_type: MachineType::FullUnsigned,
        mode,
        max_thread_pool_threads: None,
        replay_worker_threads_count: replay_threads,
        // The full-block benchmark needs enough pinned host payload capacity to avoid
        // stalling before replay workers can release snapshot-dependent tracing data.
        // 384 x 64 MiB matches the default production reserve for one job and one GPU.
        host_allocators_count: ETHEREUM_BLOCK_HOST_ALLOCATORS,
        memory_holders_count: 1,
        replay_segment_cycle_limit: env_optional_usize("ZKSYNC_REPLAY_SEGMENT_CYCLES"),
        ..Default::default()
    }
}

fn env_optional_usize(name: &str) -> Option<usize> {
    env::var(name).ok().map(|value| {
        value
            .parse()
            .expect("numeric environment value should parse")
    })
}

fn bench_ethereum_block(c: &mut Criterion) {
    let input = ethereum_block_input();
    let nondeterminism = ethereum_block_nondeterminism();

    let mut group = c.benchmark_group("cpu_pipeline/ethereum_block");
    group.sample_size(10);
    group.warm_up_time(Duration::from_secs(5));
    group.measurement_time(Duration::from_secs(20));

    for mode in [CpuPipelineMode::SimulationOnly, CpuPipelineMode::Full] {
        for replay_threads in ETHEREUM_BLOCK_REPLAY_THREAD_COUNTS {
            if mode == CpuPipelineMode::SimulationOnly && replay_threads != 1 {
                continue;
            }

            let config = ethereum_block_model_config(mode, replay_threads);
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

            group.bench_function(benchmark_id, |b| {
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

fn bench_ethereum_block_jit(c: &mut Criterion) {
    let input = ethereum_block_input();
    let nondeterminism = ethereum_block_nondeterminism();
    let runner = JittedCode::<JitBenchmarkContext>::preprocess_bytecode(&input.text_section, None);
    let mut memory: Box<MemoryHolder> = unsafe { Box::new_zeroed().assume_init() };
    let mut context = Context::new(JitBenchmarkContext::new(nondeterminism));

    // The measured loop resets only words touched by a representative run. This
    // keeps the benchmark focused on JIT execution instead of the 3 GiB memory image.
    let initial_trace_chunk = context.implementation.reset();
    prepare_jit_memory(&mut memory, &input.binary_image, &[]);
    runner.run_over_prepared_memory(&mut context, &mut memory, initial_trace_chunk);
    let touched_words = collect_touched_words(&memory);

    let mut group = c.benchmark_group("jit/ethereum_block");
    group.sample_size(10);
    group.warm_up_time(Duration::from_secs(5));
    group.measurement_time(Duration::from_secs(20));

    group.bench_function("execute", |b| {
        b.iter_custom(|iters| {
            let mut elapsed = Duration::default();
            for _ in 0..iters {
                let initial_trace_chunk = context.implementation.reset();
                prepare_jit_memory(&mut memory, &input.binary_image, &touched_words);

                let start = Instant::now();
                runner.run_over_prepared_memory(&mut context, &mut memory, initial_trace_chunk);
                elapsed += start.elapsed();

                black_box(context.implementation.final_state_ref());
                black_box(context.implementation.trace_len);
            }
            elapsed
        });
    });

    group.finish();
}

// criterion_group!(cpu_pipeline, bench_hashed_fibonacci);
criterion_group!(cpu_pipeline, bench_ethereum_block_jit, bench_ethereum_block);
criterion_main!(cpu_pipeline);
