use std::collections::HashMap;
use std::time::Instant;

use blake2s_u32::Blake2sState;
use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::memory::{memory_copy_async, memory_set_async, DeviceAllocation};
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use field::proth120::Proth120;
use gpu_core::primitives::nvtx::scoped_range;
use gpu_hash::bench::{
    bench_pow_arm_blocks, bench_pow_arm_kernel, bench_pow_arm_launcher,
    bench_production_pow_blocks, PowArm, PowHash,
};
use gpu_hash::blake2s::blake2s_pow;
use gpu_hash::keccak256::keccak256_pow;
use gpu_hash::pow::pow_chunk_steps;
use prover::definitions::USE_REDUCED_BLAKE2_ROUNDS;
use sha3::{Digest as _, Keccak256};
use transcript::{Keccak256Seed, Keccak256Transcript, Seed, Transcript};
use worker::Worker;

type Blake2sTranscript = prover::transcript::Blake2sTranscript<{ USE_REDUCED_BLAKE2_ROUNDS }>;

const ROOT: u64 = 0x706f_7762_656e_6368;
const BOUNDED_LOGS: [u32; 5] = [24, 26, 28, 30, 31];
const LAUNCHER_PLAN: [(u32, usize); 8] = [
    (1, 200),
    (16, 200),
    (17, 200),
    (20, 200),
    (24, 200),
    (25, 100),
    (27, 50),
    (30, 50),
];
const ORACLE_MAX_BITS: u32 = 24;
const CONTROL_BITS: [u32; 2] = [12, 27];
const CPU_BITS: [u32; 2] = [20, 24];
const CPU_SEEDS: usize = 20;
const HASHES: [PowHash; 2] = [PowHash::Keccak, PowHash::Blake2s];

#[derive(Clone, Copy)]
enum Arm {
    Bench(PowArm),
    Production,
}

impl Arm {
    fn name(self, hash: PowHash) -> String {
        let name = match self {
            Arm::Bench(arm) => format!("{arm:?}"),
            Arm::Production => format!(
                "Production{}",
                if production_returns_min(hash) {
                    "Min"
                } else {
                    "First"
                }
            ),
        };
        match hash {
            PowHash::Keccak => format!("K{name}"),
            PowHash::Blake2s => format!("B{name}"),
        }
    }

    fn returns_min(self, hash: PowHash) -> bool {
        match self {
            Arm::Bench(arm) => arm.is_min(),
            Arm::Production => production_returns_min(hash),
        }
    }
}

/// The production Keccak search returns the minimum in every build, Blake2s only with
/// `deterministic_pow`.
fn production_returns_min(hash: PowHash) -> bool {
    hash == PowHash::Keccak || cfg!(feature = "deterministic_pow")
}

fn bench_arms(_hash: PowHash) -> Vec<PowArm> {
    vec![
        PowArm::GridStrideMin,
        PowArm::GridStrideFirst,
        PowArm::CounterMin,
    ]
}

fn launcher_arms(hash: PowHash) -> Vec<Arm> {
    let mut arms: Vec<Arm> = bench_arms(hash).into_iter().map(Arm::Bench).collect();
    arms.push(Arm::Production);
    arms
}

fn hash_tag(hash: PowHash) -> u64 {
    match hash {
        PowHash::Keccak => 0x4b,
        PowHash::Blake2s => 0x42,
    }
}

fn splitmix(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e3779b97f4a7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

fn derived_seed(stream: u64, hash: PowHash, a: u64, b: u64) -> [u8; 32] {
    let mut state = ROOT ^ (stream << 56) ^ (hash_tag(hash) << 48) ^ (a << 24) ^ b;
    splitmix(&mut state);
    let mut out = [0u8; 32];
    for chunk in out.chunks_exact_mut(8) {
        chunk.copy_from_slice(&splitmix(&mut state).to_le_bytes());
    }
    out
}

fn launcher_seed(hash: PowHash, bits: u32, id: usize) -> [u8; 32] {
    derived_seed(1, hash, bits as u64, id as u64)
}

fn control_seed(hash: PowHash, bits: u32) -> [u8; 32] {
    derived_seed(2, hash, bits as u64, 0)
}

fn bounded_seed(hash: PowHash, attempt: u64) -> [u8; 32] {
    derived_seed(3, hash, attempt, 0)
}

fn cpu_seed(hash: PowHash, bits: u32, id: usize) -> [u8; 32] {
    derived_seed(4, hash, bits as u64, id as u64)
}

fn warmup_seed(hash: PowHash) -> [u8; 32] {
    derived_seed(5, hash, 0, 0)
}

/// Williams square and its reverse: every arm takes every position equally often and every
/// ordered pair of arms appears in both directions equally often over the 2k rows.
fn balanced_orders(k: usize) -> Vec<Vec<usize>> {
    let first: Vec<usize> = (0..k)
        .map(|i| match i {
            0 => 0,
            i if i % 2 == 1 => i.div_ceil(2),
            i => k - i / 2,
        })
        .collect();
    let square: Vec<Vec<usize>> = (0..k)
        .map(|r| first.iter().map(|&a| (a + r) % k).collect())
        .collect();
    let mut rows = square.clone();
    rows.extend(
        square
            .into_iter()
            .map(|row| row.into_iter().rev().collect()),
    );
    rows
}

fn words(seed: &[u8; 32]) -> [u32; 8] {
    std::array::from_fn(|i| u32::from_le_bytes(seed[4 * i..4 * i + 4].try_into().unwrap()))
}

fn keccak_digest(seed: &[u8; 32], nonce: u64) -> [u8; 32] {
    let mut hash = Keccak256::new();
    hash.update(seed);
    hash.update(nonce.to_be_bytes());
    hash.finalize().into()
}

fn valid(hash: PowHash, seed: &[u8; 32], nonce: u64, bits: u32) -> bool {
    match hash {
        PowHash::Keccak => {
            let digest = keccak_digest(seed, nonce);
            u128::from_be_bytes(digest[..16].try_into().unwrap()).leading_zeros() >= bits
        }
        PowHash::Blake2s => {
            let mut block = [0u32; 16];
            block[..8].copy_from_slice(&words(seed));
            block[8] = nonce as u32;
            block[9] = (nonce >> 32) as u32;
            let mut digest = [0u32; 8];
            Blake2sState::new().absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
                &block,
                10,
                &mut digest,
            );
            digest[0].leading_zeros() >= bits
        }
    }
}

fn cpu_search(hash: PowHash, seed: &[u8; 32], bits: u32, worker: &Worker) -> u64 {
    match hash {
        PowHash::Keccak => {
            <Keccak256Transcript as Transcript<Proth120, Proth120>>::search_pow(
                &Keccak256Seed(*seed),
                bits,
                worker,
            )
            .1
        }
        PowHash::Blake2s => Blake2sTranscript::search_pow(&Seed(words(seed)), bits, worker).1,
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn device_state(label: &str) {
    match std::process::Command::new("nvidia-smi")
        .args([
            "--query-gpu=uuid,pstate,clocks.sm,clocks.mem,temperature.gpu,power.draw",
            "--format=csv,noheader",
        ])
        .output()
    {
        Ok(output) => eprintln!(
            "device_state {label}: {}",
            String::from_utf8_lossy(&output.stdout).trim()
        ),
        Err(error) => eprintln!("device_state {label}: unavailable {error}"),
    }
}

struct Buffers {
    seed: DeviceAllocation<u8>,
    result: DeviceAllocation<u64>,
    counter: DeviceAllocation<u64>,
    start: CudaEvent,
    end: CudaEvent,
}

impl Buffers {
    fn new() -> Self {
        Self {
            seed: DeviceAllocation::alloc(32).unwrap(),
            result: DeviceAllocation::alloc(1).unwrap(),
            counter: DeviceAllocation::alloc(1).unwrap(),
            start: CudaEvent::create().unwrap(),
            end: CudaEvent::create().unwrap(),
        }
    }

    fn set_seed(&mut self, seed: &[u8; 32], stream: &CudaStream) {
        memory_copy_async(&mut self.seed, seed, stream).unwrap();
        stream.synchronize().unwrap();
    }

    fn read(&self, stream: &CudaStream) -> (u64, [u8; 32]) {
        let mut result = [0u64];
        let mut seed = [0u8; 32];
        memory_copy_async(&mut result, &self.result, stream).unwrap();
        memory_copy_async(&mut seed, &self.seed, stream).unwrap();
        stream.synchronize().unwrap();
        (result[0], seed)
    }

    fn vars(&mut self) -> (&mut DeviceVariable<u64>, &mut DeviceVariable<u64>) {
        unsafe {
            (
                DeviceVariable::from_raw_parts_mut(self.counter.as_mut_ptr()),
                DeviceVariable::from_raw_parts_mut(self.result.as_mut_ptr()),
            )
        }
    }

    /// Kernel only between the events; result = u64::MAX (no hit), counter = 0 before.
    fn bounded(
        &mut self,
        hash: PowHash,
        arm: PowArm,
        bits: u32,
        max_nonce: u64,
        stream: &CudaStream,
    ) -> (f64, u64) {
        let blocks = bench_pow_arm_blocks(hash, arm).unwrap();
        unsafe {
            memory_set_async(self.result.transmute_mut::<u8>(), 0xff, stream).unwrap();
            memory_set_async(self.counter.transmute_mut::<u8>(), 0, stream).unwrap();
        }
        stream.synchronize().unwrap();
        let seed = self.seed.as_ptr();
        self.start.record(stream).unwrap();
        let (counter, result) = self.vars();
        bench_pow_arm_kernel(
            hash, arm, seed, bits, max_nonce, blocks, counter, result, stream,
        )
        .unwrap();
        self.end.record(stream).unwrap();
        self.end.synchronize().unwrap();
        let ms = elapsed_time(&self.start, &self.end).unwrap() as f64;
        (ms, self.read(stream).0)
    }

    /// The full production launch sequence between the events.
    fn launcher(
        &mut self,
        hash: PowHash,
        arm: Arm,
        seed: &[u8; 32],
        bits: u32,
        stream: &CudaStream,
    ) -> (f64, u64, [u8; 32]) {
        self.set_seed(seed, stream);
        self.start.record(stream).unwrap();
        let seed_slice = unsafe { DeviceSlice::from_raw_parts_mut(self.seed.as_mut_ptr(), 32) };
        let (counter, result) = unsafe {
            (
                DeviceVariable::from_raw_parts_mut(self.counter.as_mut_ptr()),
                DeviceVariable::from_raw_parts_mut(self.result.as_mut_ptr()),
            )
        };
        match (arm, hash) {
            (Arm::Bench(arm), _) => {
                bench_pow_arm_launcher(hash, arm, seed_slice, bits, counter, result, stream)
                    .unwrap()
            }
            (Arm::Production, PowHash::Keccak) => {
                keccak256_pow(seed_slice, bits, result, counter, stream).unwrap()
            }
            (Arm::Production, PowHash::Blake2s) => {
                let seed_words = unsafe { seed_slice.transmute::<u32>() };
                blake2s_pow(seed_words, bits, result, counter, stream).unwrap()
            }
        }
        self.end.record(stream).unwrap();
        self.end.synchronize().unwrap();
        let ms = elapsed_time(&self.start, &self.end).unwrap() as f64;
        let (nonce, after) = self.read(stream);
        (ms, nonce, after)
    }
}

fn range_name(hash: PowHash, arm: Arm, bits: u32) -> String {
    format!("pow.{}.bits{bits}", arm.name(hash))
}

type Oracle = HashMap<(String, u32, usize), u64>;

fn oracle_key(hash: PowHash, bits: u32, id: usize) -> (String, u32, usize) {
    (format!("{hash:?}"), bits, id)
}

fn load_oracle() -> Oracle {
    let path = std::env::var("POW_ORACLE").expect("POW_ORACLE=<oracle.jsonl> required");
    let mut oracle = Oracle::new();
    for line in std::fs::read_to_string(&path).unwrap().lines() {
        let value: serde_json::Value = serde_json::from_str(line).unwrap();
        if value["kind"] != "oracle" {
            continue;
        }
        let hash = value["hash"].as_str().unwrap().to_owned();
        let bits = value["bits"].as_u64().unwrap() as u32;
        let id = value["seed_id"].as_u64().unwrap() as usize;
        let nonce = value["nonce"].as_u64().unwrap();
        oracle.insert((hash, bits, id), nonce);
    }
    eprintln!("oracle: {} entries from {path}", oracle.len());
    oracle
}

const CONTROL_ID: usize = usize::MAX;

/// Correctness smoke only (POW_SMOKE=1): one bounded round, 4 seeds per difficulty; not a protocol run.
fn smoke() -> bool {
    std::env::var("POW_SMOKE").is_ok_and(|v| v == "1")
}

fn oracle_phase() {
    let worker = Worker::new();
    eprintln!("oracle: worker threads={}", worker.num_cores);
    let started = Instant::now();
    for hash in HASHES {
        for bits in CONTROL_BITS {
            let seed = control_seed(hash, bits);
            let nonce = cpu_search(hash, &seed, bits, &worker);
            assert!(valid(hash, &seed, nonce, bits));
            println!(
                "{{\"kind\":\"oracle\",\"hash\":\"{hash:?}\",\"bits\":{bits},\"seed_id\":{CONTROL_ID},\"nonce\":{nonce}}}"
            );
        }
        for (bits, seeds) in LAUNCHER_PLAN {
            if bits > ORACLE_MAX_BITS {
                continue;
            }
            for id in 0..seeds {
                let seed = launcher_seed(hash, bits, id);
                let nonce = cpu_search(hash, &seed, bits, &worker);
                assert!(valid(hash, &seed, nonce, bits));
                println!(
                    "{{\"kind\":\"oracle\",\"hash\":\"{hash:?}\",\"bits\":{bits},\"seed_id\":{id},\"nonce\":{nonce}}}"
                );
            }
        }
    }
    eprintln!("oracle: done in {:.1} s", started.elapsed().as_secs_f64());
}

fn controls(
    buffers: &mut Buffers,
    oracle: &Oracle,
    hashes: &[PowHash],
    arms_of: fn(PowHash) -> Vec<PowArm>,
    stream: &CudaStream,
) {
    for &hash in hashes {
        for bits in CONTROL_BITS {
            let seed = control_seed(hash, bits);
            let min = oracle[&oracle_key(hash, bits, CONTROL_ID)];
            buffers.set_seed(&seed, stream);
            for arm in arms_of(hash) {
                let (_, upto) = buffers.bounded(hash, arm, bits, min + 1, stream);
                let (_, below) = buffers.bounded(hash, arm, bits, min, stream);
                let blocks = bench_pow_arm_blocks(hash, arm).unwrap();
                println!(
                    "{{\"kind\":\"control\",\"hash\":\"{hash:?}\",\"arm\":\"{}\",\"bits\":{bits},\"min\":{min},\"chunk_steps\":{},\"result_max_min_plus_1\":{upto},\"result_max_min\":{below}}}",
                    Arm::Bench(arm).name(hash),
                    pow_chunk_steps(bits, blocks)
                );
                assert_eq!(upto, min, "{hash:?} {arm:?} bits={bits}: control upto min");
                assert_eq!(
                    below,
                    u64::MAX,
                    "{hash:?} {arm:?} bits={bits}: control below min"
                );
            }
        }
    }
}

fn bounded_phase(
    buffers: &mut Buffers,
    hashes: &[PowHash],
    arms_of: fn(PowHash) -> Vec<PowArm>,
    stream: &CudaStream,
) {
    let n_max = 1u64 << BOUNDED_LOGS[BOUNDED_LOGS.len() - 1];
    for &hash in hashes {
        let bits = match hash {
            PowHash::Keccak => 64,
            PowHash::Blake2s => 32,
        };
        let mut attempt = 0u64;
        let seed = loop {
            let seed = bounded_seed(hash, attempt);
            buffers.set_seed(&seed, stream);
            let (_, result) = buffers.bounded(hash, PowArm::GridStrideMin, bits, n_max, stream);
            let accepted = result == u64::MAX;
            println!(
                "{{\"kind\":\"screen\",\"hash\":\"{hash:?}\",\"attempt\":{attempt},\"seed\":\"{}\",\"n\":{n_max},\"accepted\":{accepted},\"hit\":{result}}}",
                hex(&seed)
            );
            if accepted {
                break seed;
            }
            assert!(
                valid(hash, &seed, result, bits),
                "screening hit failed CPU validation"
            );
            attempt += 1;
        };
        buffers.set_seed(&seed, stream);
        let arms = arms_of(hash);
        let orders = balanced_orders(arms.len());
        for arm in &arms {
            let blocks = bench_pow_arm_blocks(hash, *arm).unwrap();
            eprintln!(
                "bounded {hash:?} {arm:?}: blocks={blocks} chunk_steps={}",
                pow_chunk_steps(bits, blocks)
            );
            for _ in 0..3 {
                let (_, result) = buffers.bounded(hash, *arm, bits, n_max, stream);
                assert_eq!(result, u64::MAX, "{hash:?} {arm:?}: certified seed hit");
            }
        }
        device_state(&format!("bounded {hash:?} start"));
        for round in 0..if smoke() { 1 } else { orders.len() } {
            let logs: Vec<u32> = if round % 2 == 0 {
                BOUNDED_LOGS.to_vec()
            } else {
                BOUNDED_LOGS.iter().rev().copied().collect()
            };
            let order = &orders[round];
            for log in logs {
                for (pos, &a) in order.iter().enumerate() {
                    let arm = arms[a];
                    let (ms, result) = buffers.bounded(hash, arm, bits, 1 << log, stream);
                    assert_eq!(
                        result,
                        u64::MAX,
                        "{hash:?} {arm:?} log={log}: certified seed hit"
                    );
                    println!(
                        "{{\"kind\":\"bounded\",\"hash\":\"{hash:?}\",\"arm\":\"{}\",\"log_n\":{log},\"round\":{round},\"pos\":{pos},\"ms\":{ms:.6}}}",
                        Arm::Bench(arm).name(hash)
                    );
                }
            }
        }
        device_state(&format!("bounded {hash:?} end"));
    }
}

fn launcher_phase(buffers: &mut Buffers, oracle: &Oracle, stream: &CudaStream) {
    for hash in HASHES {
        let arms = launcher_arms(hash);
        let orders = balanced_orders(arms.len());
        for arm in &arms {
            {
                let blocks = match arm {
                    Arm::Bench(bench) => bench_pow_arm_blocks(hash, *bench).unwrap(),
                    Arm::Production => bench_production_pow_blocks(hash).unwrap(),
                };
                println!(
                    "{{\"kind\":\"arm\",\"hash\":\"{hash:?}\",\"arm\":\"{}\",\"blocks\":{blocks},\"chunk_steps\":[{}]}}",
                    arm.name(hash),
                    LAUNCHER_PLAN
                        .iter()
                        .map(|(bits, _)| pow_chunk_steps(*bits, blocks).to_string())
                        .collect::<Vec<_>>()
                        .join(",")
                );
            }
        }
        let warmup = warmup_seed(hash);
        for arm in &arms {
            for _ in 0..10 {
                buffers.launcher(hash, *arm, &warmup, 20, stream);
            }
        }
        device_state(&format!("launcher {hash:?} start"));
        for (bits, seeds) in LAUNCHER_PLAN {
            let seeds = if smoke() { 4 } else { seeds };
            for id in 0..seeds {
                let seed = launcher_seed(hash, bits, id);
                let cpu_min =
                    (bits <= ORACLE_MAX_BITS).then(|| oracle[&oracle_key(hash, bits, id)]);
                let mut min_nonce: Option<u64> = None;
                let order = &orders[id % orders.len()];
                for (pos, &a) in order.iter().enumerate() {
                    let arm = arms[a];
                    let (ms, nonce, after) = {
                        let _range = scoped_range(None, &range_name(hash, arm, bits));
                        buffers.launcher(hash, arm, &seed, bits, stream)
                    };
                    assert!(
                        valid(hash, &seed, nonce, bits)
                            && (hash != PowHash::Keccak || after == keccak_digest(&seed, nonce)),
                        "{hash:?} {} bits={bits} seed={id}: invalid nonce {nonce}",
                        arm.name(hash)
                    );
                    if arm.returns_min(hash) {
                        if let Some(cpu) = cpu_min {
                            assert_eq!(
                                nonce,
                                cpu,
                                "{hash:?} {} bits={bits} seed={id}: not the CPU minimum",
                                arm.name(hash)
                            );
                        }
                        assert_eq!(
                            *min_nonce.get_or_insert(nonce),
                            nonce,
                            "{hash:?} {} bits={bits} seed={id}: min arms disagree",
                            arm.name(hash)
                        );
                    }
                    println!(
                        "{{\"kind\":\"launcher\",\"hash\":\"{hash:?}\",\"arm\":\"{}\",\"bits\":{bits},\"seed_id\":{id},\"seed\":\"{}\",\"order\":{},\"pos\":{pos},\"nonce\":{nonce},\"ms\":{ms:.6}}}",
                        arm.name(hash),
                        hex(&seed),
                        id % orders.len()
                    );
                }
            }
            device_state(&format!("launcher {hash:?} bits {bits} done"));
        }
    }
}

/// `POW_PROFILE=<arm>:<bits>` (e.g. `KProductionMin:30`): three warmup launches, then three
/// launches inside the `pow.<arm>.bits<bits>` range, for a profiler to select one of them.
fn profile_phase(target: &str, stream: &CudaStream) {
    let (name, bits) = target.split_once(':').expect("POW_PROFILE=<arm>:<bits>");
    let bits: u32 = bits.parse().unwrap();
    let (hash, arm) = HASHES
        .iter()
        .flat_map(|&hash| launcher_arms(hash).into_iter().map(move |arm| (hash, arm)))
        .find(|(hash, arm)| arm.name(*hash) == name)
        .unwrap_or_else(|| panic!("unknown arm {name}"));
    let mut buffers = Buffers::new();
    let warmup = warmup_seed(hash);
    for _ in 0..3 {
        buffers.launcher(hash, arm, &warmup, bits, stream);
    }
    for id in 0..3 {
        let seed = launcher_seed(hash, bits, id);
        let (ms, nonce, _) = {
            let _range = scoped_range(None, &range_name(hash, arm, bits));
            buffers.launcher(hash, arm, &seed, bits, stream)
        };
        assert!(valid(hash, &seed, nonce, bits));
        println!(
            "{{\"kind\":\"profile\",\"hash\":\"{hash:?}\",\"arm\":\"{name}\",\"bits\":{bits},\"seed_id\":{id},\"nonce\":{nonce},\"ms\":{ms:.6}}}"
        );
    }
}

fn cpu_phase() {
    let worker = Worker::new();
    eprintln!(
        "cpu: worker threads={} host search mode=min (the transcript dev-dependency enables deterministic_pow in every build)",
        worker.num_cores
    );
    for hash in HASHES {
        for _ in 0..2 {
            cpu_search(hash, &warmup_seed(hash), 20, &worker);
        }
        for bits in CPU_BITS {
            for id in 0..CPU_SEEDS {
                let seed = cpu_seed(hash, bits, id);
                let started = Instant::now();
                let nonce = cpu_search(hash, &seed, bits, &worker);
                let ms = started.elapsed().as_secs_f64() * 1e3;
                assert!(valid(hash, &seed, nonce, bits));
                println!(
                    "{{\"kind\":\"cpu\",\"hash\":\"{hash:?}\",\"bits\":{bits},\"seed_id\":{id},\"threads\":{},\"nonce\":{nonce},\"ms\":{ms:.6}}}",
                    worker.num_cores
                );
            }
        }
    }
}

fn main() {
    if std::env::args().any(|a| a == "--list") {
        println!("pow: benchmark");
        return;
    }
    if std::env::args().any(|a| a == "--test") {
        return;
    }
    if let Ok(target) = std::env::var("POW_PROFILE") {
        profile_phase(&target, &CudaStream::default());
        return;
    }
    let phases: Vec<String> = std::env::args()
        .skip(1)
        .filter(|a| !a.starts_with("--"))
        .collect();
    for phase in &phases {
        assert!(
            ["oracle", "gpu", "cpu"].contains(&phase.as_str()),
            "unknown phase {phase} (oracle | gpu | cpu)"
        );
    }
    assert!(!phases.is_empty(), "phases required: oracle | gpu | cpu");
    eprintln!(
        "pow bench: deterministic_pow={} root={ROOT:#x} phases={phases:?} smoke={}",
        cfg!(feature = "deterministic_pow"),
        smoke()
    );
    if phases.iter().any(|p| p == "oracle") {
        oracle_phase();
    }
    if phases.iter().any(|p| p == "gpu") {
        let oracle = load_oracle();
        device_state("gpu start");
        let stream = CudaStream::default();
        let mut buffers = Buffers::new();
        controls(&mut buffers, &oracle, &HASHES, bench_arms, &stream);
        bounded_phase(&mut buffers, &HASHES, bench_arms, &stream);
        launcher_phase(&mut buffers, &oracle, &stream);
        device_state("gpu end");
    }
    if phases.iter().any(|p| p == "cpu") {
        cpu_phase();
    }
}
