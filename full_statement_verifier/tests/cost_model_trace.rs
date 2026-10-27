#![cfg(all(feature = "host_utils", feature = "verifiers"))]

//! Manual calibration harness for `src/host_utils/cost_model/census.rs`. Every
//! test here needs freshly generated local recursion proofs, so all of them are
//! `#[ignore]`d. CI runs only `cost_model_drift.rs`; that detects verifier
//! codegen drift but does not validate the committed model's accuracy.
//!
//! Fixtures live in `$COST_MODEL_FIXTURE_DIR` as `<fixture>_proof.bin` /
//! `<fixture>_setups.bin`: zlib-compressed JSON of `ProgramProof` and `Setups`.
//! Generate the Sec100 Compression fixtures with the ignored GPU test
//! `test_generate_sec100_cost_model_fixtures` in
//! `gpu/execution_prover/tests/program.rs`. It
//! proves the recursion layers explicitly instead of depending on the production
//! scheduling threshold. From the repository root:
//!
//! ```text
//! cargo nextest run -p gpu_execution_prover --release --features verifiers --no-run
//! COST_MODEL_FIXTURE_DIR="$PWD/target/cost-model-fixtures/sec100" \
//!   .agents/bin/with_gpu_lock.sh cargo nextest run -p gpu_execution_prover \
//!   --release --features verifiers \
//!   -E 'test(=test_generate_sec100_cost_model_fixtures)' \
//!   --run-ignored only --no-capture
//! ```
//!
//! By default `base` is zkSync OS block 23620012; `base_alt` is hashed Fibonacci with
//! `(n=15, h=1_200_000)`; `recursion0` and `recursion1` explicitly prove the
//! Sec100 unrolled base and recursion verifiers. The synthetic `memory_windows`
//! (every base-machine family), `memory_windows_recursion` (every reduced-machine
//! family, for the recursion verifier) and `keccak_f1600` (each Keccak-f1600
//! circuit) repeat each circuit they run, so prices come from repeated proofs,
//! and touch enough address windows for two i&t proofs. The files are
//! non-authoritative local calibration inputs and must not be committed or
//! consumed by CI.
//! Optional local block corpora are described in the generator's doc comment.
//! Set `COST_MODEL_FIXTURE_DIR` to one generated output directory. The loader
//! discovers every `*_proof.bin` and its matching `*_setups.bin`; fixture names
//! containing `recursion` select the recursion verifier.
//!
//! `emit_census_tables` prints the fitted tables for `census.rs`. The total and
//! census acceptance gates allow the original 0.1% family / 0.05% delegation
//! and total budget on max(measured - V, 0), plus V = proof count times the
//! largest measured per-proof deviation from its circuit mean. The total row
//! measures deviations separately. The envelope is frozen in the table;
//! acceptance inputs do not set their own allowance. This empirical envelope
//! does not guarantee accuracy on unseen proofs.

mod trace;

use trace::fixtures::{all_fixtures, Fixture};
use trace::fsv_dir;
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

fn load_base_layer() -> (Vec<u32>, Vec<u32>) {
    full_statement_verifier::host_utils::load_fsv_program(
        fsv_dir(),
        FsvProgram::UnrolledBaseLayer,
        BlakeMode::Compression,
    )
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn marks_are_monotonic_and_one_per_stream_word() {
    let (bin, text) = load_base_layer();
    let (setups, proof) = trace::load_calibration_proof("base");
    let stream = full_statement_verifier::host_utils::build_unrolled_stream(
        &setups,
        &proof,
        BlakeMode::Compression,
    );
    let expected_reads = stream.len();

    let t = trace::trace_verifier(&bin, &text, stream);

    assert_eq!(
        t.marks.len(),
        expected_reads,
        "one ND read per stream word: read index is the stream word index"
    );
    assert!(
        t.marks.windows(2).all(|w| w[0] <= w[1]),
        "marks must be non-decreasing"
    );
    assert!(t.marks.last().copied().unwrap_or(0) <= t.total_cycles);
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn total_cycles_matches_the_uninstrumented_measurement() {
    let (bin, text) = load_base_layer();
    let (setups, proof) = trace::load_calibration_proof("base");
    let stream = full_statement_verifier::host_utils::build_unrolled_stream(
        &setups,
        &proof,
        BlakeMode::Compression,
    );

    let instrumented = trace::trace_verifier(&bin, &text, stream.clone()).total_cycles;
    let plain = trace::measure_verifier_cycles(&bin, &text, stream);

    assert_eq!(
        instrumented, plain,
        "instrumentation must not perturb the guest's cycle count"
    );
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn stream_plan_matches_the_actual_stream() {
    for Fixture {
        name: fixture,
        program,
        ..
    } in &all_fixtures()
    {
        let (setups, proof) = trace::load_calibration_proof(fixture);
        let stream = full_statement_verifier::host_utils::build_unrolled_stream(
            &setups,
            &proof,
            BlakeMode::Compression,
        );
        let plan = trace::plan::plan_unrolled_stream(&setups, &proof, *program);

        assert_eq!(
            plan.total_words,
            stream.len(),
            "{fixture}: planned length must match the stream"
        );

        for region in &plan.regions {
            let n = region.proof_first_words.len() as u32;
            assert_eq!(
                stream[region.count_word], n,
                "{fixture}: planned count word for {:?} must hold its proof count",
                region.circuit
            );
        }
        assert_eq!(
            stream[plan.inits_count_word] as usize,
            proof.inits_and_teardown_proofs.len()
        );

        let riscv: Vec<_> = plan
            .regions
            .iter()
            .filter(|r| r.section == trace::plan::Section::Riscv)
            .collect();
        assert_eq!(
            riscv.len(),
            full_statement_verifier::host_utils::cost_model::riscv_order(*program).len(),
            "{fixture}: one region per compiled RISC-V family"
        );
        assert_eq!(
            riscv.last().unwrap().end_word,
            plan.inits_count_word,
            "{fixture}: the last RISC-V region must close at the inits/teardowns count word, \
             not at the first delegation region"
        );
        let deleg: Vec<_> = plan
            .regions
            .iter()
            .filter(|r| r.section == trace::plan::Section::Delegation)
            .collect();
        assert_eq!(deleg.last().unwrap().end_word, plan.pow_word);
        assert!(deleg.last().unwrap().closes_at_epilogue);
        assert!(riscv.iter().all(|r| !r.closes_at_epilogue));

        let expected_pow_low = proof.pow_challenge as u32;
        assert_eq!(
            stream[plan.pow_word], expected_pow_low,
            "{fixture}: final sentinel must land on the first PoW word"
        );
    }
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn proof_counts_matches_the_planned_regions() {
    use full_statement_verifier::host_utils::cost_model::proof_counts;
    for Fixture {
        name: fixture,
        program,
        ..
    } in &all_fixtures()
    {
        let (setups, proof) = trace::load_calibration_proof(fixture);
        let plan = trace::plan::plan_unrolled_stream(&setups, &proof, *program);
        let mut from_api: Vec<_> = proof_counts(&proof)
            .into_iter()
            .filter(|(_, n)| *n > 0)
            .collect();
        let mut from_plan: Vec<_> = plan
            .regions
            .iter()
            .map(|r| (r.circuit, r.proof_first_words.len()))
            .filter(|(_, n)| *n > 0)
            .collect();
        from_api.sort();
        from_plan.sort();
        assert_eq!(
            from_api, from_plan,
            "{fixture}: proof_counts disagrees with the stream plan"
        );
    }
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn every_fixture_verifies_natively() {
    for Fixture { name, program, .. } in &all_fixtures() {
        let (setups, proof) = trace::load_calibration_proof(name);
        let stream = full_statement_verifier::host_utils::build_unrolled_stream(
            &setups,
            &proof,
            BlakeMode::Compression,
        );
        full_statement_verifier::host_utils::native_verify_unrolled(
            stream,
            *program == FsvProgram::UnrolledBaseLayer,
        );
    }
}

fn acceptance_budget(
    proof: &full_statement_verifier::program_proof::ProgramProof,
    program: FsvProgram,
    row: usize,
    measured: u64,
) -> u64 {
    use full_statement_verifier::host_utils::cost_model::{census::CENSUS_TABLES, proof_counts};
    let proofs = proof_counts(proof).iter().map(|(_, n)| *n as u64).sum();
    let table = &CENSUS_TABLES
        .iter()
        .find(|(p, mode, _)| *p == program && *mode == BlakeMode::Compression)
        .unwrap()
        .2;
    trace::calibrate::gate_budget(row, measured, proofs, table.per_proof_spread[row])
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn estimate_matches_measurement_on_every_fixture() {
    use full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles;

    for Fixture { name, program } in &all_fixtures() {
        let (bin, text) = full_statement_verifier::host_utils::load_fsv_program(
            fsv_dir(),
            *program,
            BlakeMode::Compression,
        );
        let (setups, proof) = trace::load_calibration_proof(name);
        let stream = full_statement_verifier::host_utils::build_unrolled_stream(
            &setups,
            &proof,
            BlakeMode::Compression,
        );
        let measured = trace::measure_verifier_cycles(&bin, &text, stream);
        let estimate = estimate_verifier_cycles(&proof, *program, BlakeMode::Compression).unwrap();
        let error = estimate.abs_diff(measured);
        let budget = acceptance_budget(&proof, *program, trace::calibrate::TOTAL_ROW, measured);
        assert!(
            error <= budget,
            "{name}: estimate {estimate} vs measured {measured}: {error} > {budget}"
        );
    }
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn emit_census_tables() {
    // Sharing a WHIR schedule does not guarantee identical per-proof
    // instruction counts across verifier programs. Fit each program separately.
    for program in [
        FsvProgram::UnrolledBaseLayer,
        FsvProgram::UnrolledRecursionLayer,
    ] {
        let cals: Vec<_> = all_fixtures()
            .iter()
            .filter(|f| f.program == program)
            .map(|f| trace::calibrate::calibrate_census_fixture(&f.name, f.program))
            .collect();
        let pooled = trace::calibrate::pool_census(&cals);
        println!(
            "{}",
            trace::calibrate::render_census_tables(program, &pooled)
        );
    }
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn census_family_cycles_sum_to_total() {
    for Fixture { name, program, .. } in &all_fixtures() {
        let (t, _) = trace::calibrate::trace_fixture(name, *program);
        let family_sum: u64 = t.total_census
            [..full_statement_verifier::host_utils::cost_model::census::NUM_FAMILY_DIMS]
            .iter()
            .sum();
        assert_eq!(
            family_sum, t.total_cycles,
            "{name}: per-family cycle counters must partition the total cycle count"
        );
    }
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn census_estimate_matches_measurement_on_every_fixture() {
    use full_statement_verifier::host_utils::cost_model::census::{
        estimate_verifier_census, CENSUS_DIMS, NUM_CENSUS_DIMS,
    };
    for Fixture { name, program } in &all_fixtures() {
        let (t, _) = trace::calibrate::trace_fixture(name, *program);
        let proof = trace::load_calibration_proof(name).1;
        let estimate = estimate_verifier_census(&proof, *program, BlakeMode::Compression).unwrap();
        assert_eq!(estimate.len(), NUM_CENSUS_DIMS);
        for (d, (dim, value)) in estimate.iter().enumerate() {
            assert_eq!(*dim, CENSUS_DIMS[d]);
            let measured = t.total_census[d];
            let error = value.abs_diff(measured);
            let budget = acceptance_budget(&proof, *program, d, measured);
            assert!(
                error <= budget,
                "{name} dim {d} ({dim:?}): estimate {value} vs measured {measured}: \
                 {error} > {budget}"
            );
        }
    }
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn per_proof_census_spans_agree_within_a_circuit() {
    use full_statement_verifier::host_utils::cost_model::census::NUM_CENSUS_DIMS;

    for Fixture {
        name: fixture,
        program,
        ..
    } in &all_fixtures()
    {
        let c = trace::calibrate::calibrate_census_fixture(fixture, *program);
        for trace::calibrate::RegionCensus { circuit, spans, .. } in &c.regions {
            if spans.len() < 2 {
                continue;
            }
            for d in 0..NUM_CENSUS_DIMS {
                let lo = spans.iter().map(|s| s[d]).min().unwrap();
                let hi = spans.iter().map(|s| s[d]).max().unwrap();
                // Coarse within-circuit consistency check; accuracy uses the measured spread.
                assert!(
                    hi - lo <= (hi / 64).max(2),
                    "{fixture}/{circuit:?} census dim {d}: per-proof spans vary beyond the \
                     bound (min {lo}, max {hi})"
                );
            }
        }
    }
}
