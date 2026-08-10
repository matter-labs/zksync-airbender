//! LDC-divergence rider (v3 R4 spec §8): does a lane-divergent constant load serialize per
//! unique address on sm_120?
//!
//! Two regimes, both reported in WALL CYCLES (`clock64` around the loop, on the device):
//! a single warp running a true loop-carried dependency through the constant cache, priced
//! against the same loop with the load removed, and a saturated many-warp arm. `K` is
//! runtime data in every arm, so the instruction stream is identical across the sweep.

use clap::Parser;
use era_cudart::device::{get_device, get_device_properties};
use era_cudart::event::{elapsed_time, CudaEvent};
use era_cudart::memory::{memory_copy, DeviceAllocation};
use era_cudart::result::CudaResult;
use era_cudart::stream::CudaStream;
use gpu_gkr_uniskip_bench::ldc_probe::{self, Chase, Probe, LDC_PROBE_CHAINS, LDC_PROBE_WORDS};

#[derive(Parser)]
#[command(name = "uniskip_ldc_divergence", version, about, long_about = None)]
struct Cli {
    /// Distinct constant addresses per warp, per load.
    #[arg(long, value_delimiter = ',', default_values_t = [1u32, 2, 4, 8, 16, 32])]
    k: Vec<u32>,

    /// Word distance between two of those addresses: 1 = a contiguous 128 B run at K = 32,
    /// 16 = one 64 B line each, 32 = one 128 B line each. Separates per-address
    /// serialization from per-line serialization.
    #[arg(long, value_delimiter = ',', default_values_t = [1u32, 16, 32])]
    stride_words: Vec<u32>,

    /// Dependent loads per thread in the latency and baseline arms.
    #[arg(long, default_value_t = 50_000)]
    iters: u32,

    /// Outer iterations in the throughput arm; each runs `LDC_PROBE_CHAINS` loads.
    #[arg(long, default_value_t = 2_000)]
    throughput_iters: u32,

    /// Blocks per SM in the throughput arm.
    #[arg(long, default_value_t = 6)]
    blocks_per_sm: u32,

    /// Threads per block in the throughput arm.
    #[arg(long, default_value_t = 256)]
    threads: u32,

    /// Untimed launches before each measured point.
    #[arg(long, default_value_t = 2)]
    warmup: u32,

    /// Timed launches per point; the median is reported.
    #[arg(long, default_value_t = 7)]
    reps: u32,
}

struct Point {
    cycles: u64,
    millis: f32,
}

struct Probes {
    stream: CudaStream,
    sink: DeviceAllocation<u32>,
    cycles: DeviceAllocation<u64>,
    table: DeviceAllocation<u32>,
    events: [CudaEvent; 2],
    warmup: u32,
    reps: u32,
}

impl Probes {
    fn new(threads: usize, warmup: u32, reps: u32) -> CudaResult<Self> {
        Ok(Self {
            stream: CudaStream::create()?,
            sink: DeviceAllocation::alloc(threads)?,
            cycles: DeviceAllocation::alloc(threads.div_ceil(32).max(1))?,
            table: DeviceAllocation::alloc(LDC_PROBE_WORDS)?,
            events: [CudaEvent::create()?, CudaEvent::create()?],
            warmup,
            reps,
        })
    }

    /// Upload the chase and read bank 3 back through the device's own view of it, so the
    /// K under measurement is the K the kernels walk.
    fn install(&mut self, chase: Chase) -> CudaResult<()> {
        let table = chase.table();
        ldc_probe::upload_table(&table)?;
        ldc_probe::readback(&mut self.table, &self.stream)?;
        self.stream.synchronize()?;
        let mut host = vec![0u32; LDC_PROBE_WORDS];
        memory_copy(&mut host[..], &self.table[..])?;
        assert_eq!(
            host, table,
            "constant bank 3 does not hold the uploaded chase"
        );
        Ok(())
    }

    /// Median over `reps` of the longest block's device cycle count, plus the matching
    /// wall time. Every rep re-runs the same launch; the table is already uploaded.
    fn measure(
        &mut self,
        probe: Probe,
        chase: Chase,
        iters: u32,
        blocks: u32,
        threads: u32,
    ) -> CudaResult<Point> {
        for _ in 0..self.warmup {
            ldc_probe::launch(
                probe,
                chase,
                iters,
                blocks,
                threads,
                &mut self.sink,
                &mut self.cycles,
                &self.stream,
            )?;
        }
        self.stream.synchronize()?;
        let mut samples = Vec::with_capacity(self.reps as usize);
        let mut millis = Vec::with_capacity(self.reps as usize);
        let mut host = vec![0u64; blocks as usize];
        for _ in 0..self.reps {
            self.events[0].record(&self.stream)?;
            ldc_probe::launch(
                probe,
                chase,
                iters,
                blocks,
                threads,
                &mut self.sink,
                &mut self.cycles,
                &self.stream,
            )?;
            self.events[1].record(&self.stream)?;
            self.stream.synchronize()?;
            memory_copy(&mut host[..], &self.cycles[..blocks as usize])?;
            samples.push(*host.iter().max().expect("at least one block"));
            millis.push(elapsed_time(&self.events[0], &self.events[1])?);
        }
        samples.sort_unstable();
        millis.sort_by(f32::total_cmp);
        Ok(Point {
            cycles: samples[samples.len() / 2],
            millis: millis[millis.len() / 2],
        })
    }

    /// The live sink pins the WALK: a thread's final chase position is a pure function of
    /// its lane, its chain count and the trip count, so a wrong table, a wrong `K` or a
    /// retargeted load lands on the wrong endpoint. It is NOT a loop-elision oracle — the
    /// endpoint is periodic in `K`, and the default trip counts are divisible by every
    /// `K <= 16`, so an elided loop would return the start and read as correct there. That
    /// the loop and its `LDC` survive is what the SASS capture shows.
    fn check_sink(
        &self,
        chase: Chase,
        iters: u32,
        blocks: u32,
        threads: u32,
        chains: u32,
    ) -> CudaResult<()> {
        let mut host = vec![0u32; (blocks * threads) as usize];
        memory_copy(&mut host[..], &self.sink[..(blocks * threads) as usize])?;
        for (thread, &got) in host.iter().enumerate() {
            let lane = thread as u32 % 32;
            let want: u32 = (0..chains)
                .map(|chain| chase.endpoint(lane, chain, iters))
                .sum();
            assert_eq!(
                got, want,
                "sink mismatch at thread {thread} (k = {}, stride {})",
                chase.k, chase.stride_words
            );
        }
        Ok(())
    }
}

fn main() -> CudaResult<()> {
    let cli = Cli::parse();
    let props = get_device_properties(get_device()?)?;
    let sms = props.multiProcessorCount as u32;
    let blocks = sms * cli.blocks_per_sm;
    println!(
        "device: {} sm_{}{} | {sms} SMs",
        String::from_utf8_lossy(
            &props
                .name
                .iter()
                .map(|&c| c as u8)
                .take_while(|&c| c != 0)
                .collect::<Vec<_>>()
        ),
        props.major,
        props.minor
    );
    println!(
        "latency/baseline: 1 block x 32 threads, {} dependent loads | throughput: {blocks} blocks x {} threads, {} chains x {} iters",
        cli.iters, cli.threads, LDC_PROBE_CHAINS, cli.throughput_iters
    );
    println!("K is runtime state (uploaded table + mask/step) — one instruction stream serves every column below.\n");

    let mut probes = Probes::new((blocks * cli.threads) as usize, cli.warmup, cli.reps)?;

    println!("== regime A: single-warp latency, true loop-carried dependency (cycles per dependent load)");
    println!(
        "{:>7}  {:>8}  {:>10}  {:>10}  {:>10}  {:>8}",
        "stride", "K", "latency", "baseline", "delta", "vs K=1"
    );
    let mut latency_rows: Vec<(u32, u32, f64, f64)> = Vec::new();
    let mut clock_ghz: Option<f64> = None;
    for &stride_words in &cli.stride_words {
        let mut first: Option<f64> = None;
        for &k in &cli.k {
            let chase = Chase::new(k, stride_words);
            probes.install(chase)?;
            let latency = probes.measure(Probe::Latency, chase, cli.iters, 1, 32)?;
            probes.check_sink(chase, cli.iters, 1, 32, 1)?;
            // Self-calibration: the same launch reports device cycles and host wall time,
            // so the achieved SM clock never has to be assumed.
            clock_ghz.get_or_insert(latency.cycles as f64 / (latency.millis as f64 * 1.0e6));
            let baseline = probes.measure(Probe::Baseline, chase, cli.iters, 1, 32)?;
            let per_load = latency.cycles as f64 / cli.iters as f64;
            let per_empty = baseline.cycles as f64 / cli.iters as f64;
            let base = *first.get_or_insert(per_load);
            println!(
                "{:>6}B  {k:>8}  {per_load:>10.2}  {per_empty:>10.2}  {:>10.2}  {:>8.2}x",
                stride_words * 4,
                per_load - per_empty,
                per_load / base
            );
            latency_rows.push((stride_words, k, per_load, per_empty));
        }
    }

    println!(
        "\nachieved SM clock over the latency arm: {:.3} GHz",
        clock_ghz.unwrap_or(f64::NAN)
    );
    println!("\n== regime B: saturated throughput ({blocks} blocks, {} chains/thread) — wall cycles of the longest block", LDC_PROBE_CHAINS);
    println!(
        "{:>7}  {:>8}  {:>12}  {:>10}  {:>12}  {:>8}",
        "stride", "K", "block cycles", "wall ms", "cyc/warp-LDC", "vs K=1"
    );
    let mut throughput_rows: Vec<(u32, u32, f64)> = Vec::new();
    let warps_per_sm = cli.blocks_per_sm * cli.threads / 32;
    for &stride_words in &cli.stride_words {
        let mut first: Option<f64> = None;
        for &k in &cli.k {
            let chase = Chase::new(k, stride_words);
            probes.install(chase)?;
            let point = probes.measure(
                Probe::Throughput,
                chase,
                cli.throughput_iters,
                blocks,
                cli.threads,
            )?;
            probes.check_sink(
                chase,
                cli.throughput_iters,
                blocks,
                cli.threads,
                LDC_PROBE_CHAINS,
            )?;
            let cycles = point.cycles as f64;
            let base = *first.get_or_insert(cycles);
            // Warp-level LDC instructions one SM retires over that span, if every resident
            // warp made equal progress: the per-SM issue cost of one divergent load.
            let per_warp_ldc = cycles
                / (warps_per_sm as f64 * cli.throughput_iters as f64 * LDC_PROBE_CHAINS as f64);
            println!(
                "{:>6}B  {k:>8}  {:>12.0}  {:>10.3}  {per_warp_ldc:>12.3}  {:>8.2}x",
                stride_words * 4,
                cycles,
                point.millis,
                cycles / base
            );
            throughput_rows.push((stride_words, k, cycles));
        }
    }

    println!("\n== verdict inputs (K = 32 against K = 1, per stride)");
    for &stride_words in &cli.stride_words {
        let row = |k: u32| {
            latency_rows
                .iter()
                .find(|r| r.0 == stride_words && r.1 == k)
                .copied()
        };
        let tput = |k: u32| {
            throughput_rows
                .iter()
                .find(|r| r.0 == stride_words && r.1 == k)
                .copied()
        };
        if let (Some(lo), Some(hi), Some(tlo), Some(thi)) = (row(1), row(32), tput(1), tput(32)) {
            println!(
                "stride {:>4}B: latency {:.2} -> {:.2} cyc/load ({:.2}x, baseline-corrected {:.2}x) | throughput {:.2}x",
                stride_words * 4,
                lo.2,
                hi.2,
                hi.2 / lo.2,
                (hi.2 - hi.3) / (lo.2 - lo.3),
                thi.2 / tlo.2
            );
        }
    }
    println!("serialization per unique address would read 32x on both axes; 1x means the constant path broadcasts K addresses at one address' cost.");
    Ok(())
}
