use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;

use gpu_gkr_windowed_bench::accumulator_census::{
    generate_accumulator_census, render_accumulator_report,
};
use gpu_gkr_windowed_bench::census::WorkloadWeightsV1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    Write,
    Check,
}

fn parse_mode(arguments: &[String]) -> Result<Mode, Box<dyn std::error::Error>> {
    match arguments {
        [flag] if flag == "--write" => Ok(Mode::Write),
        [flag] if flag == "--check" => Ok(Mode::Check),
        _ => Err("usage: generate_windowed_accumulator_census (--write|--check)".into()),
    }
}

fn generate_deliverables() -> Result<(Vec<u8>, Vec<u8>), Box<dyn std::error::Error>> {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let weights_bytes =
        std::fs::read(manifest.join("artifacts/windowed_workload_weights_v1.json"))?;
    let weights: WorkloadWeightsV1 = serde_json::from_slice(&weights_bytes)?;
    weights.validate()?;
    let census = generate_accumulator_census(weights)?;
    let mut json = serde_json::to_vec(&census)?;
    json.push(b'\n');
    let mut markdown = render_accumulator_report(&census)?.into_bytes();
    if !markdown.ends_with(b"\n") {
        markdown.push(b'\n');
    }
    Ok((json, markdown))
}

fn atomic_replace(path: &Path, bytes: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or("output path has no UTF-8 file name")?;
    let temporary = path.with_file_name(format!(".{file_name}.tmp-{}", std::process::id()));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)?;
    let result = (|| {
        file.write_all(bytes)?;
        file.sync_all()?;
        drop(file);
        std::fs::rename(&temporary, path)?;
        Ok::<_, Box<dyn std::error::Error>>(())
    })();
    if result.is_err() {
        let _ = std::fs::remove_file(&temporary);
    }
    result
}

fn apply_mode(
    mode: Mode,
    json_path: &Path,
    markdown_path: &Path,
    json: &[u8],
    markdown: &[u8],
) -> Result<(), Box<dyn std::error::Error>> {
    match mode {
        Mode::Write => {
            atomic_replace(json_path, json)?;
            atomic_replace(markdown_path, markdown)?;
        }
        Mode::Check => {
            if std::fs::read(json_path)? != json {
                return Err(format!("JSON output {} differs", json_path.display()).into());
            }
            if std::fs::read(markdown_path)? != markdown {
                return Err(format!("Markdown output {} differs", markdown_path.display()).into());
            }
        }
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mode = parse_mode(&std::env::args().skip(1).collect::<Vec<_>>())?;
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let json_path = manifest.join("artifacts/windowed_accumulator_census_v1.json");
    let markdown_path =
        manifest.join("../../.agents/audits/2026-08-15-windowed-gkr-r0-accumulator-census.md");
    let (json, markdown) = generate_deliverables()?;
    apply_mode(mode, &json_path, &markdown_path, &json, &markdown)?;
    match mode {
        Mode::Write => println!(
            "wrote accumulator census to {} and {}",
            json_path.display(),
            markdown_path.display()
        ),
        Mode::Check => println!("windowed accumulator census JSON and Markdown are byte-stable"),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    #[test]
    fn cli_requires_exactly_write_or_check() {
        assert_eq!(parse_mode(&["--write".into()]).unwrap(), Mode::Write);
        assert_eq!(parse_mode(&["--check".into()]).unwrap(), Mode::Check);
        for invalid in [
            vec![],
            vec!["--wat".into()],
            vec!["--write".into(), "--check".into()],
        ] {
            assert!(parse_mode(&invalid).is_err());
        }
    }

    #[test]
    fn in_memory_generation_is_deterministic_and_round_trips() {
        let first = generate_deliverables().unwrap();
        let second = generate_deliverables().unwrap();
        assert_eq!(first.0, second.0);
        assert_eq!(first.1, second.1);
        let parsed: gpu_gkr_windowed_bench::accumulator_census::AccumulatorCorpusCensusV1 =
            serde_json::from_slice(&first.0).unwrap();
        assert_eq!(parsed.coordinates.len(), 114);
        let mut rendered = render_accumulator_report(&parsed).unwrap().into_bytes();
        if !rendered.ends_with(b"\n") {
            rendered.push(b'\n');
        }
        assert_eq!(rendered, first.1);
        assert!(first
            .1
            .windows(b"114 coordinate rows".len())
            .any(|window| window == b"114 coordinate rows"));
    }

    #[test]
    fn check_mode_reports_json_and_markdown_mismatches_independently() {
        let root = std::env::temp_dir().join(format!(
            "windowed-accumulator-census-generator-{}",
            std::process::id()
        ));
        std::fs::create_dir(&root).unwrap();
        let json = root.join("census.json");
        let markdown = root.join("census.md");
        let expected_json = b"json\n";
        let expected_markdown = b"markdown\n";
        std::fs::write(&json, b"wrong\n").unwrap();
        std::fs::write(&markdown, expected_markdown).unwrap();
        let error = apply_mode(
            Mode::Check,
            &json,
            &markdown,
            expected_json,
            expected_markdown,
        )
        .unwrap_err()
        .to_string();
        assert!(error.contains("JSON"));
        std::fs::write(&json, expected_json).unwrap();
        std::fs::write(&markdown, b"wrong\n").unwrap();
        let error = apply_mode(
            Mode::Check,
            &json,
            &markdown,
            expected_json,
            expected_markdown,
        )
        .unwrap_err()
        .to_string();
        assert!(error.contains("Markdown"));
        std::fs::remove_dir_all(PathBuf::from(root)).unwrap();
    }
}
