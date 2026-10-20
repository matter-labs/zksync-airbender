use verifier_common::fsv_binaries::FsvProgram;

pub struct Fixture {
    pub name: String,
    pub program: FsvProgram,
}

pub fn all_fixtures() -> Vec<Fixture> {
    let directory = std::env::var_os("COST_MODEL_FIXTURE_DIR").expect("set COST_MODEL_FIXTURE_DIR");
    let mut fixtures: Vec<_> = std::fs::read_dir(directory)
        .expect("list calibration fixtures")
        .filter_map(|entry| {
            let file = entry.unwrap().file_name().into_string().unwrap();
            let name = file.strip_suffix("_proof.bin")?.to_owned();
            let program = if name.contains("recursion") {
                FsvProgram::UnrolledRecursionLayer
            } else {
                FsvProgram::UnrolledBaseLayer
            };
            Some(Fixture { name, program })
        })
        .collect();
    fixtures.sort_by(|a, b| a.name.cmp(&b.name));
    assert!(!fixtures.is_empty(), "no calibration fixtures");
    fixtures
}
