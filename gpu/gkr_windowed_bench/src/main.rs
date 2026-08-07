use clap::Parser;
use gpu_gkr_windowed_bench::abi::E4;
use gpu_gkr_windowed_bench::harness::{estimated_source_bytes, WindowedHarness};

#[derive(Parser)]
struct Args {
    #[arg(long, default_value_t = 24)]
    log_trace: u32,
    #[arg(long, default_value_t = 10)]
    warmup: u32,
    #[arg(long, default_value_t = 100)]
    iterations: u32,
    #[arg(long)]
    profile: bool,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    let mut harness = WindowedHarness::new(args.log_trace)?;
    let timings = harness.measure(args.warmup, args.iterations, args.profile)?;
    let output = harness.observe_final()?;
    let checksum = output_checksum(&output);
    let estimated_source_bytes = estimated_source_bytes(harness.artifact(), harness.plan())?;
    let estimated_partial_bytes = harness.plan().partial_elements * core::mem::size_of::<E4>();
    let estimated_output_bytes = estimated_partial_bytes * 2 + 27 * core::mem::size_of::<E4>();
    println!(
        "artifact: terms={} records={} coefficients={} sources={} windows={}",
        harness.artifact().term_count,
        harness.artifact().record_count,
        harness.artifact().coefficient_count,
        harness.artifact().source_slots.len(),
        harness.artifact().windows.len(),
    );
    println!("allocation: {:?}", harness.allocation_report());
    println!(
        "launch: vm_grid={} vm_block=288 finalize_grid=27 finalize_block=256 warmup={} iterations={} profile={}",
        harness.plan().num_blocks,
        args.warmup,
        timings.samples_ms.len(),
        args.profile,
    );
    println!(
        "timing_ms: min={:.6} median={:.6} samples={:?}",
        timings.minimum_ms, timings.median_ms, timings.samples_ms
    );
    println!(
        "estimated_bytes: source_load_floor={} partial_and_final={} (requested bytes before cache effects)",
        estimated_source_bytes, estimated_output_bytes,
    );
    println!(
        "result: observed_cells={} checksum=0x{checksum:016x}",
        output.len()
    );
    Ok(())
}

fn output_checksum(output: &[E4; 27]) -> u64 {
    output.iter().fold(0xcbf29ce484222325, |hash, value| {
        [
            value.c0.c0.raw_u32_value(),
            value.c0.c1.raw_u32_value(),
            value.c1.c0.raw_u32_value(),
            value.c1.c1.raw_u32_value(),
        ]
        .into_iter()
        .fold(hash, |hash, limb| {
            (hash ^ u64::from(limb)).wrapping_mul(0x100000001b3)
        })
    })
}
