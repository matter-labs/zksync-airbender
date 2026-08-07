use std::path::PathBuf;

use clap::{Parser, ValueEnum};
use gpu_gkr_windowed_bench::artifact::encode_artifact;
use gpu_gkr_windowed_bench::generator::{
    generate_add_sub_layer0_with_options, schedule_census, ProgramSchedule,
};

#[derive(Clone, Copy, Debug, ValueEnum)]
enum ScheduleArg {
    Compiler,
    ControlAtoms,
    Control,
    Source,
}

impl From<ScheduleArg> for ProgramSchedule {
    fn from(schedule: ScheduleArg) -> Self {
        match schedule {
            ScheduleArg::Compiler => Self::Compiler,
            ScheduleArg::ControlAtoms => Self::ControlAtoms,
            ScheduleArg::Control => Self::Control,
            ScheduleArg::Source => Self::Source,
        }
    }
}

#[derive(Parser)]
struct Args {
    #[arg(long)]
    layout: Option<PathBuf>,
    #[arg(long)]
    output: Option<PathBuf>,
    #[arg(long, value_enum, default_value_t = ScheduleArg::Compiler)]
    schedule: ScheduleArg,
    #[arg(long)]
    lazy_bf_reduction: bool,
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
    let artifact = generate_add_sub_layer0_with_options(
        &layout,
        args.schedule.into(),
        args.lazy_bf_reduction,
    )?;
    let census = schedule_census(&artifact)?;
    let bytes = encode_artifact(&artifact)?;
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
        "wrote {}: schedule={:?} lazy_bf_reduction={} terms={} atoms={} records={} program_bytes={} coefficients={} immediates={} sources={} windows={} bf_windows={} e4_windows={} procedural_windows={} field_transitions={} shape_transitions={} class_transitions={} immediate_transitions={} same_source_a={} same_source_b={} bf_accesses={} procedural_bf_accesses={} lazy_bf_groups={} lazy_bf_products={} reduction_boundaries={}",
        output.display(),
        args.schedule,
        args.lazy_bf_reduction,
        artifact.term_count,
        census.atoms,
        artifact.record_count,
        artifact.program.len() * core::mem::size_of::<gpu_gkr_windowed_bench::abi::WindowInstruction>(),
        artifact.coefficient_count,
        artifact.immediates.len(),
        artifact.source_slots.len(),
        artifact.windows.len(),
        bf_windows,
        e4_windows,
        procedural,
        census.field_transitions,
        census.shape_transitions_within_field,
        census.class_transitions,
        census.group_immediate_transitions,
        census.adjacent_equal_source_a,
        census.adjacent_equal_source_b,
        census.projected_bf_accesses,
        census.projected_procedural_bf_accesses,
        census.lazy_bf_groups,
        census.lazy_bf_products,
        census.reduction_boundaries,
    );
    Ok(())
}
