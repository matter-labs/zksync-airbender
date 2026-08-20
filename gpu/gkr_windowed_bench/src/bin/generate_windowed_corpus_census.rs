use std::path::{Path, PathBuf};

use gpu_gkr_windowed_bench::census::{
    generate_corpus_census, workload_weights_from_log, WorkloadWeightsV1,
};

fn json_bytes<T: serde::Serialize>(value: &T) -> Result<Vec<u8>, serde_json::Error> {
    let mut bytes = serde_json::to_vec(value)?;
    bytes.push(b'\n');
    Ok(bytes)
}

fn check_file(path: &Path, expected: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
    let actual = std::fs::read(path)?;
    if actual != expected {
        return Err(format!("{} differs from deterministic regeneration", path.display()).into());
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let check = match std::env::args().skip(1).collect::<Vec<_>>().as_slice() {
        [] => false,
        [flag] if flag == "--check" => true,
        _ => return Err("usage: generate_windowed_corpus_census [--check]".into()),
    };
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let weights_path = manifest.join("artifacts/windowed_workload_weights_v1.json");
    let census_path = manifest.join("artifacts/windowed_corpus_census_v1.json");
    let weights = if check {
        serde_json::from_slice::<WorkloadWeightsV1>(&std::fs::read(&weights_path)?)?
    } else {
        let campaign = manifest.join("../../target/windowed-gkr-decode-compact-program/workloads");
        workload_weights_from_log(&campaign.join("current-recursion.debug.log"))?
    };
    weights.validate()?;
    let census = generate_corpus_census(weights.clone())?;
    let weights_bytes = json_bytes(&weights)?;
    let census_bytes = json_bytes(&census)?;
    if check {
        check_file(&weights_path, &weights_bytes)?;
        check_file(&census_path, &census_bytes)?;
        println!("windowed corpus census is byte-stable");
    } else {
        std::fs::write(&weights_path, weights_bytes)?;
        std::fs::write(&census_path, census_bytes)?;
        println!(
            "wrote {} coordinates to {}",
            census.coordinates.len(),
            census_path.display()
        );
    }
    Ok(())
}
