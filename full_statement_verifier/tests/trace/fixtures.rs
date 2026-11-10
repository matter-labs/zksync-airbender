use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProgram, SoundnessMode};

/// The file naming a retained acceptance corpus's soundness mode (`SoundnessMode::cli_name`).
pub const SOUNDNESS_MODE_FILE: &str = "soundness_mode";

pub struct Fixture {
    pub name: String,
    pub program: FsvProgram,
    /// The guest that verifies this fixture's proof.
    pub descriptor: FsvDescriptor,
}

pub fn chain_fixture(mode: SoundnessMode, program: FsvProgram) -> Fixture {
    let chain = match program {
        FsvProgram::UnrolledBaseLayer => "base",
        FsvProgram::UnrolledRecursionLayer => "unrolled",
        _ => unreachable!(),
    };
    Fixture {
        name: format!("{}/{chain}", mode.file_suffix()),
        program,
        descriptor: FsvDescriptor::new(mode, program, BlakeMode::Compression),
    }
}

fn retained_fixtures() -> Vec<Fixture> {
    let Some(directory) = std::env::var_os("COST_MODEL_FIXTURE_DIR") else {
        return Vec::new();
    };
    let directory = std::path::PathBuf::from(directory);
    let path = directory.join(SOUNDNESS_MODE_FILE);
    let name = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let mode = SoundnessMode::from_cli_name(name.trim())
        .unwrap_or_else(|| panic!("{}: unknown soundness mode {name:?}", path.display()));
    let mut fixtures: Vec<_> = std::fs::read_dir(&directory)
        .expect("list acceptance fixtures")
        .filter_map(|entry| {
            let file = entry.unwrap().file_name().into_string().unwrap();
            let name = file.strip_suffix("_proof.bin")?.to_owned();
            let program = if name.contains("recursion") {
                FsvProgram::UnrolledRecursionLayer
            } else {
                FsvProgram::UnrolledBaseLayer
            };
            Some(Fixture {
                name,
                program,
                descriptor: FsvDescriptor::new(mode, program, BlakeMode::Compression),
            })
        })
        .collect();
    fixtures.sort_by(|a, b| a.name.cmp(&b.name));
    assert!(
        !fixtures.is_empty(),
        "no acceptance fixtures in {}",
        directory.display()
    );
    fixtures
}

pub fn all_fixtures() -> Vec<Fixture> {
    let mut fixtures = Vec::new();
    for &mode in SoundnessMode::ALL {
        for program in [
            FsvProgram::UnrolledBaseLayer,
            FsvProgram::UnrolledRecursionLayer,
        ] {
            fixtures.push(chain_fixture(mode, program));
        }
    }
    fixtures.extend(retained_fixtures());
    fixtures
}

#[allow(dead_code)]
pub fn fixture(name: &str) -> Fixture {
    all_fixtures()
        .into_iter()
        .find(|fixture| fixture.name == name)
        .unwrap_or_else(|| panic!("no calibration fixture {name}"))
}
