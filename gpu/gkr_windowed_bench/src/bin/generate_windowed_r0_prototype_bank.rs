use std::path::Path;

use gpu_gkr_windowed_bench::r0_prototype_manifest::{
    parse_r0_prototype_generator_mode, sync_r0_prototype_generated_files_for_merge_policy,
    R0GeneratedMode, R0SectionedShapeMergePolicy,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mode = parse_r0_prototype_generator_mode(std::env::args().skip(1))?;
    let merge_policy = match std::env::var("GPU_GKR_WINDOWED_R0_SECTIONED_SHAPE_POLICY") {
        Ok(value) => R0SectionedShapeMergePolicy::parse(&value)?,
        Err(std::env::VarError::NotPresent) => R0SectionedShapeMergePolicy::Merged,
        Err(error) => return Err(error.into()),
    };
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let result =
        sync_r0_prototype_generated_files_for_merge_policy(crate_root, mode, merge_policy)?;
    let mode_name = match mode {
        R0GeneratedMode::Write => "write",
        R0GeneratedMode::Check => "check",
    };
    println!(
        "R0_PROTOTYPE_GENERATED mode={mode_name} shape_policy={} files={} manifest_sha256={}",
        merge_policy.as_str(),
        result.files,
        result.manifest_sha256
    );
    Ok(())
}
