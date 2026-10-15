use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::memory::{memory_copy_async, memory_set_async, DeviceAllocation};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::PR;
use gpu_hash::bench::{bench_keccak_f_chain, bench_nodes, bench_partial_roots};
use gpu_hash::keccak256::Digest;
use sha3::{Digest as _, Keccak256};

const ITERATIONS: usize = 5;
const CHAIN: u32 = 64;
const CHAIN_THREADS: usize = 1 << 21;

const ROUND_CONSTANTS: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

const ROTATIONS: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

fn keccak_f1600(state: &mut [u64; 25]) {
    for constant in ROUND_CONSTANTS {
        let columns: [u64; 5] =
            std::array::from_fn(|x| (0..5).fold(0, |acc, y| acc ^ state[x + 5 * y]));
        for i in 0..25 {
            state[i] ^= columns[(i + 4) % 5] ^ columns[(i + 1) % 5].rotate_left(1);
        }
        let mut moved = [0u64; 25];
        for x in 0..5 {
            for y in 0..5 {
                moved[y + 5 * ((2 * x + 3 * y) % 5)] =
                    state[x + 5 * y].rotate_left(ROTATIONS[x + 5 * y]);
            }
        }
        for y in 0..5 {
            for x in 0..5 {
                state[x + 5 * y] =
                    moved[x + 5 * y] ^ (!moved[(x + 1) % 5 + 5 * y] & moved[(x + 2) % 5 + 5 * y]);
            }
        }
        state[0] ^= constant;
    }
}

fn device_state(label: &str) {
    for query in [
        "--query-gpu=name,uuid,driver_version,pstate,clocks.sm,clocks.mem,clocks.max.sm,clocks.max.mem,power.draw,power.limit,temperature.gpu",
        "--query-compute-apps=pid,process_name,used_memory",
    ] {
        match std::process::Command::new("nvidia-smi")
            .args([query, "--format=csv"])
            .output()
        {
            Ok(output) => eprint!(
                "device state {label}: {}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ),
            Err(error) => eprintln!("device state {label} unavailable: {error}"),
        }
    }
}

fn measure(
    name: &str,
    permutations: u64,
    stream: &CudaStream,
    mut launch: impl FnMut() -> CudaResult<()>,
) {
    let start = CudaEvent::create().unwrap();
    let end = CudaEvent::create().unwrap();
    launch().unwrap();
    stream.synchronize().unwrap();
    let mut ms = Vec::with_capacity(ITERATIONS);
    for _ in 0..ITERATIONS {
        start.record(stream).unwrap();
        launch().unwrap();
        end.record(stream).unwrap();
        end.synchronize().unwrap();
        ms.push(elapsed_time(&start, &end).unwrap() as f64);
    }
    let mut sorted = ms.clone();
    sorted.sort_by(f64::total_cmp);
    let rate = |ms: f64| permutations as f64 / ms / 1e6;
    eprintln!(
        "result {name}: permutations={permutations} ms={ms:.4?} min_ms={:.4} median_ms={:.4} keccak_f_per_s_median={:.3}G keccak_f_per_s_best={:.3}G",
        sorted[0],
        sorted[ITERATIONS / 2],
        rate(sorted[ITERATIONS / 2]),
        rate(sorted[0]),
    );
}

fn chain(stream: &CudaStream) {
    let mut out = DeviceAllocation::<u64>::alloc(CHAIN_THREADS).unwrap();
    for round_loop in [false, true] {
        bench_keccak_f_chain(CHAIN, round_loop, 128, &mut out, stream).unwrap();
        let indexes = [0, 1, 31, 32, 12345, CHAIN_THREADS / 2, CHAIN_THREADS - 1];
        let mut words = [0u64; 7];
        for (word, index) in words.iter_mut().zip(indexes) {
            memory_copy_async(std::slice::from_mut(word), &out[index..index + 1], stream).unwrap();
        }
        stream.synchronize().unwrap();
        for (actual, index) in words.iter().zip(indexes) {
            let mut state: [u64; 25] = std::array::from_fn(|lane| {
                (index as u64)
                    .wrapping_mul(0x9e3779b97f4a7c15)
                    .wrapping_add(lane as u64)
            });
            for _ in 0..CHAIN {
                keccak_f1600(&mut state);
            }
            assert_eq!(*actual, state[0], "chain loop={round_loop} index={index}");
        }
        eprintln!(
            "check PASS chain loop={round_loop} indexes={}",
            indexes.len()
        );
        for block in [64, 128, 256, 512] {
            measure(
                &format!(
                    "chain_{} block={block} threads={CHAIN_THREADS} chain={CHAIN}",
                    if round_loop { "loop" } else { "unroll" }
                ),
                CHAIN_THREADS as u64 * CHAIN as u64,
                stream,
                || bench_keccak_f_chain(CHAIN, round_loop, block, &mut out, stream),
            );
        }
    }
}

fn leaf_permutations(columns: u32, log_v: u32) -> u64 {
    (((columns << (log_v + 1)) / 17) + 1) as u64
}

fn leaves(stream: &CudaStream) {
    for (label, log_domain, log_v, columns) in [("today", 25, 2, 7), ("shape_d", 24, 1, 13)] {
        let mut values = DeviceAllocation::<PR>::alloc((columns as usize) << log_domain).unwrap();
        memory_set_async(unsafe { values.transmute_mut::<u8>() }, 0x5a, stream).unwrap();
        let log_leaves = log_domain - log_v;
        let per_leaf = leaf_permutations(columns, log_v);
        for skip_bottom in [0, 5] {
            let mut retained =
                DeviceAllocation::<Digest>::alloc(1 << (log_leaves - skip_bottom)).unwrap();
            let nodes = (1u64 << log_leaves) - (1u64 << (log_leaves - skip_bottom));
            measure(
                &format!(
                    "leaf_{label} partial_roots log_domain={log_domain} log_v={log_v} columns={columns} lanes={} keccak_f_per_leaf={per_leaf} skip_bottom={skip_bottom} block=256",
                    columns << (log_v + 1)
                ),
                (per_leaf << log_leaves) + nodes,
                stream,
                || {
                    bench_partial_roots(
                        &values,
                        log_domain,
                        log_v,
                        columns,
                        skip_bottom,
                        &mut retained,
                        stream,
                    )
                },
            );
        }
    }
}

fn nodes(stream: &CudaStream) {
    const LOG_PARENTS: u32 = 24;
    let mut src = DeviceAllocation::<Digest>::alloc(2 << LOG_PARENTS).unwrap();
    let mut dst = DeviceAllocation::<Digest>::alloc(1 << LOG_PARENTS).unwrap();
    memory_set_async(unsafe { src.transmute_mut::<u8>() }, 0x5a, stream).unwrap();
    bench_nodes(&src, &mut dst, stream).unwrap();
    let expected = Keccak256::digest([0x5au8; 64]);
    for index in [0, (1 << LOG_PARENTS) - 1] {
        let mut digest = [0u32; 8];
        memory_copy_async(
            std::slice::from_mut(&mut digest),
            &dst[index..index + 1],
            stream,
        )
        .unwrap();
        stream.synchronize().unwrap();
        for (word, expected) in digest.iter().zip(expected.chunks_exact(4)) {
            assert_eq!(
                *word,
                u32::from_be_bytes(expected.try_into().unwrap()),
                "node index={index}"
            );
        }
    }
    eprintln!("check PASS nodes indexes=2");
    measure(
        &format!("node nodes parents={} block=128", 1u64 << LOG_PARENTS),
        1 << LOG_PARENTS,
        stream,
        || bench_nodes(&src, &mut dst, stream),
    );
}

fn main() {
    if std::env::args().any(|arg| arg == "--list") {
        println!("keccak_f: benchmark");
        return;
    }
    if std::env::args().any(|arg| arg == "--test") {
        return;
    }
    device_state("before");
    eprintln!("keccak_f: iterations={ITERATIONS} after one warmup launch per variant, CUDA event time per launch");
    let stream = CudaStream::default();
    chain(&stream);
    leaves(&stream);
    nodes(&stream);
    device_state("after");
}
