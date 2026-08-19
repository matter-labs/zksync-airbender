#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![cfg(all(feature = "host_utils", feature = "verifiers"))]

//! Calibration harness for `src/cost_model/census.rs`. Every test here needs real
//! recursion proofs, far too large to commit, so all of them are `#[ignore]`d and
//! run by hand when the table is recalibrated. `cost_model_drift.rs` needs only
//! committed artifacts, so it runs unignored in CI.
//!
//! Fixtures live in `$COST_MODEL_FIXTURE_DIR` as `<fixture>_proof.bin` /
//! `<fixture>_setups.bin`: zlib-compressed bincode of `ProgramProof` and `Setups`.
//! `circuit_defs/prover_examples`'s `test_recursive_proving_pipeline_zksync_os`
//! (itself `#[ignore]`d — hours, large RAM) writes exactly that format via
//! `serialize_compressed_to_file`, but under **different names**, so its output has
//! to be renamed:
//!
//! | fixture | producer output | role |
//! |---|---|---|
//! | `base` | `base_proofs.bin` / `base_setups.bin` (note the plural) | RISC-V, keccak and bigint coefficients |
//! | `base_alt` | the same two files from a second run, with the producer's hardcoded zksync_os guest swapped for one whose delegation set differs | a second base-layer delegation presence mask |
//! | `recursion0` | `recursion_layer_0_proof_<tag>.bin` / `recursion_layer_0_setups_<tag>.bin` | recursion-layer `c0`, blake2 coefficient |
//! | `recursion1` | `recursion_layer_1_proof_<tag>.bin` / `recursion_layer_1_setups_<tag>.bin` | steady recursion-chain path |
//!
//! `emit_census_tables` prints the tables to paste into `src/cost_model/census.rs`;
//! `estimate_matches_measurement_on_every_fixture` and its census sibling are
//! the acceptance gates.

mod trace;

use trace::calibrate::Fixture;
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
    let stream = full_statement_verifier::host_utils::build_unrolled_stream(&setups, &proof);
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
    let stream = full_statement_verifier::host_utils::build_unrolled_stream(&setups, &proof);

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
    } in trace::calibrate::ALL_FIXTURES
    {
        let (setups, proof) = trace::load_calibration_proof(fixture);
        let stream = full_statement_verifier::host_utils::build_unrolled_stream(&setups, &proof);
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
        assert_eq!(stream[plan.inits_count_word], 1);

        let riscv: Vec<_> = plan
            .regions
            .iter()
            .filter(|r| r.section == trace::plan::Section::Riscv)
            .collect();
        assert_eq!(
            riscv.len(),
            full_statement_verifier::cost_model::riscv_order(*program).len(),
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
    use full_statement_verifier::cost_model::proof_counts;
    for Fixture {
        name: fixture,
        program,
        ..
    } in trace::calibrate::ALL_FIXTURES
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
    for Fixture { name, program, .. } in trace::calibrate::ALL_FIXTURES {
        let (setups, proof) = trace::load_calibration_proof(name);
        let stream = full_statement_verifier::host_utils::build_unrolled_stream(&setups, &proof);
        full_statement_verifier::host_utils::native_verify_unrolled(
            stream,
            *program == FsvProgram::UnrolledBaseLayer,
        );
    }
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn estimate_matches_measurement_on_every_fixture() {
    use full_statement_verifier::cost_model::estimate_verifier_cycles;

    for Fixture { name, program, .. } in trace::calibrate::ALL_FIXTURES {
        let (bin, text) = full_statement_verifier::host_utils::load_fsv_program(
            fsv_dir(),
            *program,
            BlakeMode::Compression,
        );
        let (setups, proof) = trace::load_calibration_proof(name);
        let stream = full_statement_verifier::host_utils::build_unrolled_stream(&setups, &proof);

        let measured = trace::measure_verifier_cycles(&bin, &text, stream);
        let est = estimate_verifier_cycles(&proof, *program, BlakeMode::Compression).unwrap();

        let err = (est as i64 - measured as i64).unsigned_abs();
        let budget = measured / 2000;
        assert!(
            err <= budget,
            "{name}: estimate {est} vs measured {measured} exceeds the 0.05% budget \
             ({err} > {budget})"
        );
    }
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn emit_census_tables() {
    let cals: Vec<_> = trace::calibrate::calibration_fixtures()
        .map(|f| {
            (
                f.name,
                f.program,
                trace::calibrate::calibrate_census_fixture(f.name, f.program),
            )
        })
        .collect();
    let pooled = trace::calibrate::pool_census(&cals);
    println!("{}", trace::calibrate::render_census_tables(&pooled));
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn census_family_cycles_sum_to_total() {
    for Fixture { name, program, .. } in trace::calibrate::ALL_FIXTURES {
        let (t, _) = trace::calibrate::trace_fixture(name, *program);
        let family_sum: u64 = t.total_census
            [..full_statement_verifier::cost_model::census::NUM_FAMILY_DIMS]
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
    use full_statement_verifier::cost_model::census::{
        estimate_verifier_census, CENSUS_DIMS, NUM_CENSUS_DIMS,
    };

    for Fixture { name, program, .. } in trace::calibrate::ALL_FIXTURES {
        let (t, _) = trace::calibrate::trace_fixture(name, *program);
        let est = estimate_verifier_census(
            &trace::load_calibration_proof(name).1,
            *program,
            BlakeMode::Compression,
        )
        .unwrap();
        assert_eq!(est.len(), NUM_CENSUS_DIMS);
        for (d, (dim, est_v)) in est.iter().enumerate() {
            assert_eq!(*dim, CENSUS_DIMS[d]);
            let measured = t.total_census[d];
            let err = (*est_v as i64 - measured as i64).unsigned_abs();
            // Family dims get 2x slack; see CENSUS_REL_DIV in trace/calibrate.rs.
            let rel = if d < full_statement_verifier::cost_model::census::NUM_FAMILY_DIMS {
                measured / 1000
            } else {
                measured / 2000
            };
            let budget = rel.max(8);
            assert!(
                err <= budget,
                "{name} dim {d} ({dim:?}): estimate {est_v} vs measured {measured} exceeds \
                 the budget ({err} > {budget})"
            );
        }
    }
}

#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn per_proof_census_spans_agree_within_a_circuit() {
    use full_statement_verifier::cost_model::census::NUM_CENSUS_DIMS;

    for Fixture {
        name: fixture,
        program,
        ..
    } in trace::calibrate::calibration_fixtures()
    {
        let c = trace::calibrate::calibrate_census_fixture(fixture, *program);
        for (circuit, spans) in &c.spans {
            if spans.len() < 2 {
                continue;
            }
            for d in 0..NUM_CENSUS_DIMS {
                let lo = spans.iter().map(|s| s[d]).min().unwrap();
                let hi = spans.iter().map(|s| s[d]).max().unwrap();
                // Bound rationale: CENSUS_REL_DIV in trace/calibrate.rs.
                assert!(
                    hi - lo <= (hi / 64).max(2),
                    "{fixture}/{circuit:?} census dim {d}: per-proof spans vary beyond the \
                     bound (min {lo}, max {hi})"
                );
            }
        }
    }
}
