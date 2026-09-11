use super::*;

fn row(circuit: CircuitType, arena_gib: usize) -> SweepRow {
    let policy = MemoryPolicy::default();
    let (setup, memory, witness_commitment, witness_opening) = policy_fields(policy);
    SweepRow {
        arena_bytes: arena_gib << 30,
        circuit: circuit_stable_name(circuit).into(),
        configuration: stable_name(policy),
        geometry: serde_json::to_string(&crate::memory_policy::cpu_tests::geometry()).unwrap(),
        setup,
        memory,
        witness_commitment,
        witness_opening,
        failure_stage: None,
        raw_samples_ms: "[1.0,2.0,3.0]".into(),
        proof_fingerprint: Some(42),
        fits: true,
        input_bytes: 123,
        peak_bytes: Some(20 << 30),
        timing_samples: 3,
        median_ms: Some(2.0),
        min_ms: Some(1.0),
        max_ms: Some(3.0),
        preferred: true,
    }
}
fn generate(rows: &[SweepRow]) -> Result<String, SweepModelError> {
    let mut csv = Vec::new();
    write_csv(&mut csv, rows)?;
    let mut output = Vec::new();
    generate_policy(csv.as_slice(), &mut output)?;
    Ok(String::from_utf8(output).unwrap())
}

#[test]
fn cpu_policy_universe_is_90_unique_valid_transitions() {
    let candidates: Vec<_> = MemoryPolicy::candidates().collect();
    assert_eq!(candidates.len(), 90);
    let names: BTreeSet<_> = candidates.iter().copied().map(stable_name).collect();
    assert_eq!(names.len(), 90);
    assert_eq!(all_circuits().len(), 12);
}

#[test]
fn cpu_csv_roundtrip_and_multi_budget_generation() {
    let rows: Vec<_> = [32, 34]
        .into_iter()
        .flat_map(|arena| all_circuits().into_iter().map(move |c| row(c, arena)))
        .collect();
    let mut csv = Vec::new();
    write_csv(&mut csv, &rows).unwrap();
    let read = csv::Reader::from_reader(csv.as_slice())
        .deserialize::<SweepRow>()
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    assert_eq!(rows, read);
    let generated = generate(&rows).unwrap();
    assert_eq!(
        generated
            .matches("MemoryPolicyThreshold { circuit:")
            .count(),
        24
    );
    assert!(generated.contains("arena_bytes: 34359738368"));
}

#[test]
fn cpu_incomplete_budget_rejected_even_when_every_circuit_fits_somewhere() {
    let mut rows: Vec<_> = all_circuits().into_iter().map(|c| row(c, 34)).collect();
    rows.push(row(all_circuits()[1], 32));
    assert!(generate(&rows)
        .unwrap_err()
        .to_string()
        .contains("every chosen budget"));
    rows.pop();
    assert!(generate(&rows).is_ok());
}

#[test]
fn cpu_duplicate_threshold_and_invalid_measurements_rejected() {
    let rows: Vec<_> = all_circuits().into_iter().map(|c| row(c, 34)).collect();
    let mut duplicate = rows.clone();
    duplicate.push(rows[0].clone());
    assert!(generate(&duplicate).is_err());
    for mutate in [
        |r: &mut SweepRow| r.fits = false,
        |r: &mut SweepRow| r.peak_bytes = Some(49 << 30),
        |r: &mut SweepRow| r.timing_samples = 9,
        |r: &mut SweepRow| r.proof_fingerprint = None,
        |r: &mut SweepRow| r.raw_samples_ms = "[1,-2,3]".into(),
        |r: &mut SweepRow| r.witness_opening = "invalid".into(),
    ] {
        let mut bad = rows.clone();
        mutate(&mut bad[0]);
        assert!(generate(&bad).is_err());
    }
}

#[test]
fn cpu_winner_is_fastest_fitting_with_stable_tie_break() {
    let c = all_circuits()[0];
    let mut rows = vec![row(c, 34), row(c, 34), row(c, 34)];
    rows[0].configuration = "z".into();
    rows[1].configuration = "a".into();
    rows[2].median_ms = Some(0.1);
    rows[2].fits = false;
    mark_preferred(&mut rows).unwrap();
    assert_eq!(
        rows.iter().map(|r| r.preferred).collect::<Vec<_>>(),
        [false, true, false]
    );
    assert!(TimingSummary::from_samples(&[0.0]).is_none());
    assert!(TimingSummary::from_samples(&[f32::NAN]).is_none());
}
