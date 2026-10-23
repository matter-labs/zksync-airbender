use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::stream::CudaStream;
use gpu_hash::bench::{bench_hash_count, bench_keccak256};
use gpu_hash::keccak256::Digest;
use sha3::{Digest as _, Keccak256};

const WARMUP_MS: u64 = 200;
const MEASUREMENT_MS: u64 = 500;
const SAMPLES: usize = 10;

fn keccak256(c: &mut Criterion) {
    for query in [
        "--query-gpu=name,driver_version,memory.total,memory.free,pstate,clocks.current.sm,clocks.current.memory,power.draw,power.limit,persistence_mode",
        "--query-compute-apps=pid,process_name,used_memory",
    ] {
        match std::process::Command::new("nvidia-smi")
            .args([query, "--format=csv"])
            .output()
        {
            Ok(output) => eprintln!("device state: {}{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr)),
            Err(error) => eprintln!("device state unavailable: {error}"),
        }
    }
    let stream = CudaStream::default();
    let count = bench_hash_count().unwrap();
    let mut out = DeviceAllocation::<Digest>::alloc(count).unwrap();
    let start = CudaEvent::create().unwrap();
    let end = CudaEvent::create().unwrap();
    let mut reversed = false;
    eprintln!("diagnostic keccak256: hashes={count}, block=128, warmup_ms={WARMUP_MS}, measurement_ms={MEASUREMENT_MS}, samples={SAMPLES}, CUDA event time, alternating AB/BA, raw totals in seconds");
    for (bytes, permutations) in [(40, 1), (64, 1), (256, 2), (448, 4)] {
        for round_loop in [false, true] {
            bench_keccak256(bytes, round_loop, &mut out, &stream).unwrap();
            let indexes = [0, 1, 7, 31, 32, 127, 128, count / 2, count - 1];
            let mut digests = [[0u32; 8]; 9];
            for (digest, index) in digests.iter_mut().zip(indexes) {
                memory_copy_async(
                    std::slice::from_mut(digest),
                    &out[index..index + 1],
                    &stream,
                )
                .unwrap();
            }
            stream.synchronize().unwrap();
            for (actual, index) in digests.iter().zip(indexes) {
                let input: Vec<u8> = (0..bytes)
                    .map(|i| (index as u64 * 31 + i as u64) as u8)
                    .collect();
                let expected = Keccak256::digest(&input);
                for (word, expected) in actual.iter().zip(expected.chunks_exact(4)) {
                    assert_eq!(
                        *word,
                        u32::from_be_bytes(expected.try_into().unwrap()),
                        "bytes={bytes}, loop={round_loop}, index={index}"
                    );
                }
            }
            eprintln!(
                "digest check PASS bytes={bytes} loop={round_loop} count={}",
                indexes.len()
            );
        }
        let mut group = c.benchmark_group(format!("keccak256/{bytes}B"));
        group.throughput(Throughput::Elements(count as u64 * permutations));
        for selected_loop in [false, true] {
            group.bench_function(if selected_loop { "loop_keccak_f" } else { "unroll_keccak_f" }, |b| {
                b.iter_custom(|iterations| {
                    let mut seconds = [0.0f64; 2];
                    for _ in 0..iterations {
                        let arms = if reversed { [true, false] } else { [false, true] };
                        reversed = !reversed;
                        for round_loop in arms {
                            start.record(&stream).unwrap();
                            bench_keccak256(bytes, round_loop, &mut out, &stream).unwrap();
                            end.record(&stream).unwrap();
                            end.synchronize().unwrap();
                            seconds[round_loop as usize] += elapsed_time(&start, &end).unwrap() as f64 / 1000.0;
                        }
                    }
                    eprintln!("raw bytes={bytes} selected_loop={selected_loop} iterations={iterations} permutations_per_hash={permutations} unroll_seconds={:.9} loop_seconds={:.9} unroll_keccak_f_per_second={:.3} loop_keccak_f_per_second={:.3}", seconds[0], seconds[1], iterations as f64 * count as f64 * permutations as f64 / seconds[0], iterations as f64 * count as f64 * permutations as f64 / seconds[1]);
                    Duration::from_secs_f64(seconds[selected_loop as usize])
                });
            });
        }
        group.finish();
    }
}

criterion_group!(
    name = benches;
    config = Criterion::default()
        .warm_up_time(Duration::from_millis(WARMUP_MS))
        .measurement_time(Duration::from_millis(MEASUREMENT_MS))
        .sample_size(SAMPLES);
    targets = keccak256
);
criterion_main!(benches);
