use std::path::PathBuf;

use clap::Parser;
use gpu_gkr_windowed_bench::generator::{generate_add_sub_layer0, generate_bytes};

#[derive(Parser)]
struct Args {
    #[arg(long)]
    layout: Option<PathBuf>,
    #[arg(long)]
    output: Option<PathBuf>,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let layout = args.layout.unwrap_or_else(|| {
        manifest.join("../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_gkr.json")
    });
    let output = args
        .output
        .unwrap_or_else(|| manifest.join("artifacts/add_sub_layer0.bin"));
    let artifact = generate_add_sub_layer0(&layout)?;
    let bytes = generate_bytes(&layout)?;
    if let Some(parent) = output.parent() {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(&output, &bytes)?;
    let bf_windows = artifact
        .windows
        .iter()
        .filter(|window| {
            matches!(
                window.field,
                gpu_gkr_windowed_bench::artifact::FrozenField::Base
            )
        })
        .count();
    let e4_windows = artifact.windows.len() - bf_windows;
    let procedural = artifact
        .windows
        .iter()
        .filter(|window| window.family.is_procedural())
        .count();
    println!(
        "wrote {}: terms={} records={} program_bytes={} coefficients={} immediates={} sources={} windows={} bf_windows={} e4_windows={} procedural_windows={}",
        output.display(),
        artifact.term_count,
        artifact.record_count,
        artifact.program.len() * core::mem::size_of::<gpu_gkr_windowed_bench::abi::WindowInstruction>(),
        artifact.coefficient_count,
        artifact.immediates.len(),
        artifact.source_slots.len(),
        artifact.windows.len(),
        bf_windows,
        e4_windows,
        procedural,
    );
    Ok(())
}
