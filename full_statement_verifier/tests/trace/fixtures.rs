use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProgram, SoundnessMode};

/// The file in a fixture directory naming the soundness mode its proofs were made in
/// (`SoundnessMode::cli_name`).
pub const SOUNDNESS_MODE_FILE: &str = "soundness_mode";

pub struct Fixture {
    pub name: String,
    pub program: FsvProgram,
    /// The guest that verifies this fixture's proof.
    pub descriptor: FsvDescriptor,
}

fn fixture_dir() -> std::path::PathBuf {
    std::env::var_os("COST_MODEL_FIXTURE_DIR")
        .expect("set COST_MODEL_FIXTURE_DIR")
        .into()
}

pub fn fixture_soundness_mode() -> SoundnessMode {
    let path = fixture_dir().join(SOUNDNESS_MODE_FILE);
    let name = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    SoundnessMode::from_cli_name(name.trim())
        .unwrap_or_else(|| panic!("{}: unknown soundness mode {name:?}", path.display()))
}

pub fn all_fixtures() -> Vec<Fixture> {
    let mode = fixture_soundness_mode();
    let mut fixtures: Vec<_> = std::fs::read_dir(fixture_dir())
        .expect("list calibration fixtures")
        .filter_map(|entry| {
            let file = entry.unwrap().file_name().into_string().unwrap();
            let name = file.strip_suffix("_proof.bin")?.to_owned();
            let program = if name.contains("recursion") {
                FsvProgram::UnrolledRecursionLayer
            } else {
                FsvProgram::UnrolledBaseLayer
            };
            let descriptor = FsvDescriptor::new(mode, program, BlakeMode::Compression);
            Some(Fixture {
                name,
                program,
                descriptor,
            })
        })
        .collect();
    fixtures.sort_by(|a, b| a.name.cmp(&b.name));
    assert!(!fixtures.is_empty(), "no calibration fixtures");
    fixtures
}

pub fn fixture(name: &str) -> Fixture {
    all_fixtures()
        .into_iter()
        .find(|fixture| fixture.name == name)
        .unwrap_or_else(|| panic!("no calibration fixture {name}"))
}
