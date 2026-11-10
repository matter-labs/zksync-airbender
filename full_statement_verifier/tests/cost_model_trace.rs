#![cfg(all(feature = "host_utils", feature = "verifiers"))]

//! Census emission and acceptance gates on committed CPU fixtures.
//!
//! `emit_census_tables` traces the registered Compression guests in both modes.
//! Per-proof prices come only from transient streams of canonical circuit proofs,
//! stopped at the first PoW read. The two interior spans of each three-copy region
//! must be equal; i&t uses its single proof's region-end span. These streams are
//! never valid whole-program proofs and are never persisted.
//!
//! Full runs of `base` and `unrolled` supply each guest's tail, chain spread and
//! an intercept row. Prefix rows add that guest's complete tail census. The
//! interval solver fits c0 with prices frozen. Chain totals participate in the
//! intercept fit, so these are not fully held-out accuracy measurements.
//! Singleton chain spans end at their region end, excluding a singleton only
//! when its region ends at PoW (`closes_at_epilogue`). Regions with multiple
//! proofs contribute interior first-word-to-first-word spans only.
//!
//! The original 0.1% family / 0.05% delegation and total budgets stay unchanged.
//! One-copy, RISC-V-only and delegation-only prefix streams exercise header and
//! empty-region accounting, retaining exactly one i&t proof in each stream.
//! This does not reproduce the retained held-out workloads, which include up to
//! 15 proofs per family and several i&t proofs. Optional acceptance fixtures in
//! `$COST_MODEL_FIXTURE_DIR` use `<name>_proof.bin` / `<name>_setups.bin` and a
//! `soundness_mode` file; they are never used for fitting. Names containing
//! `recursion` select the recursion guest. The recursion fixed-point test still
//! requires that corpus and stays ignored. The empirical envelope does not
//! guarantee accuracy on unseen proofs.

mod trace;

use full_statement_verifier::host_utils::fsv_stream;
use trace::calibrate::load_guest;
use trace::fixtures::{all_fixtures, Fixture};
use verifier_common::fsv_binaries::FsvProgram;

/// The `base` fixture's guest and stream.
fn load_base_layer() -> ((Vec<u32>, Vec<u32>), Vec<u32>) {
    let base = trace::fixtures::chain_fixture(
        verifier_common::fsv_binaries::SoundnessMode::DEFAULT,
        FsvProgram::UnrolledBaseLayer,
    );
    let (setups, proof) = trace::load_calibration_proof(&base.name);
    let stream = fsv_stream(&setups, &proof, &base.descriptor);
    (load_guest(&base.descriptor), stream)
}

#[test]
fn marks_are_monotonic_and_one_per_stream_word() {
    let ((bin, text), stream) = load_base_layer();
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
fn total_cycles_matches_the_uninstrumented_measurement() {
    let ((bin, text), stream) = load_base_layer();

    let instrumented = trace::trace_verifier(&bin, &text, stream.clone()).total_cycles;
    let plain = trace::measure_verifier_cycles(&bin, &text, stream);

    assert_eq!(
        instrumented, plain,
        "instrumentation must not perturb the guest's cycle count"
    );
}

#[test]
fn stream_plan_matches_the_actual_stream() {
    for Fixture {
        name: fixture,
        program,
        descriptor,
    } in &all_fixtures()
    {
        let (setups, proof) = trace::load_calibration_proof(fixture);
        let stream = fsv_stream(&setups, &proof, descriptor);
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
fn every_fixture_verifies_natively() {
    for Fixture {
        name,
        program,
        descriptor,
    } in &all_fixtures()
    {
        let (setups, proof) = trace::load_calibration_proof(name);
        let stream = full_statement_verifier::host_utils::build_unrolled_stream(
            &setups,
            &proof,
            verifier_common::BLAKE_MODE,
        );
        full_statement_verifier::host_utils::native_verify_unrolled_in_mode(
            stream,
            *program == FsvProgram::UnrolledBaseLayer,
            descriptor.soundness_mode,
        )
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    }
}

fn acceptance_budget(
    proof: &full_statement_verifier::program_proof::ProgramProof,
    descriptor: &verifier_common::fsv_binaries::FsvDescriptor,
    row: usize,
    measured: u64,
) -> u64 {
    use full_statement_verifier::host_utils::cost_model::{census::census_table, proof_counts};
    let proofs = proof_counts(proof).iter().map(|(_, n)| *n as u64).sum();
    let table = census_table(descriptor);
    trace::calibrate::gate_budget(row, measured, proofs, table.per_proof_spread[row])
}

/// One row per fixture: measured and estimated cycles, error, budget and both switch
/// decisions. Fails on an error above the calibrated budget, or on a switch decision that differs
/// from the measured one while the measurement is farther than the budget from the threshold.
#[test]
fn estimate_matches_measurement_on_every_fixture() {
    use full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles_for;
    use full_statement_verifier::host_utils::unified_switch_cycles;

    let threshold = unified_switch_cycles();
    for Fixture {
        name, descriptor, ..
    } in &all_fixtures()
    {
        let (bin, text) = load_guest(descriptor);
        let (setups, proof) = trace::load_calibration_proof(name);
        let stream = fsv_stream(&setups, &proof, descriptor);
        let measured = trace::measure_verifier_cycles(&bin, &text, stream);
        let estimate = estimate_verifier_cycles_for(&proof, descriptor).unwrap();
        let error = estimate.abs_diff(measured);
        let budget = acceptance_budget(&proof, descriptor, trace::calibrate::TOTAL_ROW, measured);
        let unrolled = |cycles: u64| cycles >= threshold;
        println!(
            "{descriptor:?} {name}: measured {measured} estimate {estimate} error {error} \
             ({:.4}%) budget {budget}; unrolled at {threshold}: measured {} estimate {}",
            100.0 * error as f64 / measured as f64,
            unrolled(measured),
            unrolled(estimate),
        );
        assert!(
            error <= budget,
            "{name}: estimate {estimate} vs measured {measured}: {error} > {budget}"
        );
        assert!(
            unrolled(estimate) == unrolled(measured) || measured.abs_diff(threshold) <= budget,
            "{name}: the estimate decides the switch differently from the measurement"
        );
    }
}

#[test]
#[ignore = "writes the committed census tables; invoked by build.sh"]
fn emit_census_tables() {
    for &mode in verifier_common::fsv_binaries::SoundnessMode::ALL {
        let mut rows = String::new();
        for program in [
            FsvProgram::UnrolledBaseLayer,
            FsvProgram::UnrolledRecursionLayer,
        ] {
            let fixture = trace::fixtures::chain_fixture(mode, program);
            let pooled = trace::canonical::fit(&fixture);
            rows.push_str(&trace::calibrate::render_census_tables(
                &fixture.descriptor,
                &pooled,
            ));
        }
        trace::calibrate::write_census_tables(mode, &rows);
    }
}

#[test]
fn canonical_prefix_counts_match_the_census() {
    use full_statement_verifier::host_utils::cost_model::census::{
        census_table, NUM_CENSUS_DIMS, NUM_FAMILY_DIMS,
    };
    use trace::calibrate::{gate_budget, TOTAL_ROW};
    use trace::canonical::Counts;
    for &mode in verifier_common::fsv_binaries::SoundnessMode::ALL {
        for program in [
            FsvProgram::UnrolledBaseLayer,
            FsvProgram::UnrolledRecursionLayer,
        ] {
            let fixture = trace::fixtures::chain_fixture(mode, program);
            let (chain, plan) = trace::calibrate::trace_fixture(&fixture);
            let tail = core::array::from_fn(|d| {
                chain.total_census[d] - chain.census_marks[plan.pow_word][d]
            });
            let table = census_table(&fixture.descriptor);
            for counts in [Counts::One, Counts::RiscvOnly, Counts::DelegationsOnly] {
                let mut cal = trace::canonical::calibration(&fixture.descriptor, counts);
                trace::canonical::add_tail(&mut cal, &tail);
                let mut estimate = [0u64; NUM_CENSUS_DIMS + 1];
                estimate[..NUM_CENSUS_DIMS].copy_from_slice(&table.c0);
                let proofs = cal.regions.iter().map(|region| region.count as u64).sum();
                for region in cal.regions.iter().filter(|region| region.count > 0) {
                    let price = &table
                        .v
                        .iter()
                        .find(|(id, _)| *id == region.circuit)
                        .unwrap()
                        .1;
                    for d in 0..NUM_CENSUS_DIMS {
                        estimate[d] += region.count as u64 * price[d];
                    }
                }
                estimate[TOTAL_ROW] = estimate[..NUM_FAMILY_DIMS].iter().sum();
                let mut measured = [0; NUM_CENSUS_DIMS + 1];
                measured[..NUM_CENSUS_DIMS].copy_from_slice(&cal.total);
                measured[TOTAL_ROW] = cal.total[..NUM_FAMILY_DIMS].iter().sum();
                for d in 0..=NUM_CENSUS_DIMS {
                    let budget = gate_budget(d, measured[d], proofs, table.per_proof_spread[d]);
                    assert!(
                        estimate[d].abs_diff(measured[d]) <= budget,
                        "{:?} {counts:?} dim {d}: estimate {} measured {} budget {budget}",
                        fixture.descriptor,
                        estimate[d],
                        measured[d]
                    );
                }
            }
        }
    }
}

#[test]
fn census_family_cycles_sum_to_total() {
    for fixture in &all_fixtures() {
        let name = &fixture.name;
        let (t, _) = trace::calibrate::trace_fixture(fixture);
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
fn census_estimate_matches_measurement_on_every_fixture() {
    use full_statement_verifier::host_utils::cost_model::census::{
        estimate_verifier_census_for, CENSUS_DIMS, NUM_CENSUS_DIMS,
    };
    for fixture in &all_fixtures() {
        let (name, descriptor) = (&fixture.name, &fixture.descriptor);
        let (t, _) = trace::calibrate::trace_fixture(fixture);
        let proof = trace::load_calibration_proof(name).1;
        let estimate = estimate_verifier_census_for(&proof, descriptor).unwrap();
        assert_eq!(estimate.len(), NUM_CENSUS_DIMS);
        for (d, (dim, value)) in estimate.iter().enumerate() {
            assert_eq!(*dim, CENSUS_DIMS[d]);
            let measured = t.total_census[d];
            let error = value.abs_diff(measured);
            let budget = acceptance_budget(&proof, descriptor, d, measured);
            assert!(
                error <= budget,
                "{name} dim {d} ({dim:?}): estimate {value} vs measured {measured}: \
                 {error} > {budget}"
            );
        }
    }
}

#[test]
fn per_proof_census_spans_agree_within_a_circuit() {
    use full_statement_verifier::host_utils::cost_model::census::NUM_CENSUS_DIMS;

    for f in &all_fixtures() {
        let fixture = &f.name;
        let c = trace::calibrate::calibrate_census_fixture(f);
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

/// The unrolled loop stops at any allowed threshold only if verifying a recursion proof
/// costs less than the floor: each `recursion1` fixture proves the recursion verifier, so
/// verifying it bounds the loop's fixed point from above.
#[test]
#[ignore = "needs calibration fixtures in $COST_MODEL_FIXTURE_DIR; see this file's module docs"]
fn recursion_fixed_point_is_below_the_switch_floor() {
    use full_statement_verifier::host_utils::cost_model::estimate_verifier_cycles_for;
    use full_statement_verifier::host_utils::MIN_UNIFIED_SWITCH_CYCLES;
    let mut checked = 0;
    for fixture in all_fixtures()
        .iter()
        .filter(|f| f.name.starts_with("recursion1"))
    {
        let proof = trace::load_calibration_proof(&fixture.name).1;
        let estimate = estimate_verifier_cycles_for(&proof, &fixture.descriptor).unwrap();
        println!(
            "{:?} {}: next layer {estimate}",
            fixture.descriptor, fixture.name
        );
        assert!(
            estimate < MIN_UNIFIED_SWITCH_CYCLES,
            "{}: {estimate}",
            fixture.name
        );
        checked += 1;
    }
    assert!(checked > 0, "no recursion1 fixture");
}
