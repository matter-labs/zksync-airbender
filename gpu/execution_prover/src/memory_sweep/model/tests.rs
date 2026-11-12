use super::*;

fn row(circuit: CircuitType, arena_gib: usize) -> SweepRow {
    let policy = MemoryPolicy::default();
    let (setup, memory, witness_commitment, witness_post_commitment, witness_opening) =
        policy_fields(policy);
    SweepRow {
        arena_bytes: arena_gib << 30,
        circuit: circuit_stable_name(circuit).into(),
        configuration: stable_name(policy),
        gkr: gkr_name(policy),
        setup,
        memory,
        witness_commitment,
        witness_post_commitment,
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
fn generate(rows: &[SweepRow]) -> Result<String, Box<dyn Error>> {
    let mut csv = Vec::new();
    write_csv(&mut csv, rows)?;
    let mut output = Vec::new();
    generate_policy(csv.as_slice(), &mut output)?;
    Ok(String::from_utf8(output).unwrap())
}

#[test]
fn cpu_generation_requires_complete_coverage_at_each_budget() {
    let mut rows: Vec<_> = [21, 29]
        .into_iter()
        .flat_map(|arena| all_circuits().into_iter().map(move |c| row(c, arena)))
        .collect();
    assert!(generate(&rows)
        .unwrap()
        .contains("PRESET_ARENA_BYTES: &[usize] = &[22548578304, 31138512896]"));
    let mut missing_budget = rows.clone();
    for row in &mut missing_budget {
        if row.arena_bytes == 21 << 30 {
            row.preferred = false;
        }
    }
    assert!(generate(&missing_budget).is_err());
    rows[0].arena_bytes = 32 << 30;
    assert!(generate(&rows).is_err());
    rows.remove(0);
    assert!(generate(&rows).is_err());
    assert!(generate(&[]).is_err());
}

#[test]
fn cpu_duplicate_policy_and_invalid_measurements_rejected() {
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
        |r: &mut SweepRow| r.gkr = "invalid".into(),
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
